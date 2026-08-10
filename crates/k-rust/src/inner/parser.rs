//! A portable chart parser over lowered K productions.

mod disambiguation;
mod inference;

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

use regex::Regex as CompiledRegex;

use crate::definition::{
    AssociativityRelations, PartialOrder, ProductionItem, Regex as KRegex, RegexBody, Sentence,
    compute_associativities, compute_priorities, parse_regex,
};
use crate::kast::{Label, Sort, Term};

use self::disambiguation::parse_apply_priority;

const MAX_DERIVATIONS_PER_STATE: usize = 64;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParseError {
    InvalidRegex {
        regex: String,
        message: String,
    },
    NoParse {
        position: usize,
        expected: Vec<String>,
    },
    Ambiguous {
        parses: usize,
    },
    TooManyParses {
        limit: usize,
    },
    CircularPriorities {
        path: Vec<String>,
    },
    InvalidApplyPriority {
        value: String,
        position: String,
    },
    Priority {
        parent: String,
        child: String,
    },
    Associativity {
        parent: String,
        child: String,
        side: &'static str,
    },
    UnknownApplication {
        label: String,
        arity: usize,
    },
    SortInference {
        message: String,
    },
}

impl fmt::Display for ParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRegex { regex, message } => {
                write!(formatter, "invalid terminal regex {regex:?}: {message}")
            }
            Self::NoParse { position, expected } => {
                write!(formatter, "could not parse input at byte {position}")?;
                if !expected.is_empty() {
                    write!(formatter, "; expected {}", expected.join(", "))?;
                }
                Ok(())
            }
            Self::Ambiguous { parses } => write!(formatter, "input has {parses} parses"),
            Self::TooManyParses { limit } => write!(
                formatter,
                "parse forest exceeded the per-state limit of {limit} derivations"
            ),
            Self::CircularPriorities { path } => {
                write!(
                    formatter,
                    "illegal circular syntax priority: {}",
                    path.join(" > ")
                )
            }
            Self::InvalidApplyPriority { value, position } => write!(
                formatter,
                "invalid applyPriority value {position:?} in {value:?}"
            ),
            Self::Priority { parent, child } => write!(
                formatter,
                "cannot use {child} as an immediate child of {parent} because of syntax priority"
            ),
            Self::Associativity {
                parent,
                child,
                side,
            } => write!(
                formatter,
                "cannot use {child} as the immediate {side} child of {parent} because of associativity"
            ),
            Self::UnknownApplication { label, arity } => write!(
                formatter,
                "could not find a production for K label {label:?} with arity {arity}"
            ),
            Self::SortInference { message } => formatter.write_str(message),
        }
    }
}

impl std::error::Error for ParseError {}

#[derive(Clone, Debug)]
enum Item {
    NonTerminal(Sort),
    Terminal(String),
    Regex {
        source: String,
        pattern: CompiledRegex,
        precede: Option<CompiledRegex>,
        follow: Option<CompiledRegex>,
    },
}

impl Item {
    fn description(&self) -> String {
        match self {
            Self::NonTerminal(sort) => sort.to_string(),
            Self::Terminal(terminal) => format!("{terminal:?}"),
            Self::Regex { source, .. } => format!("r{source:?}"),
        }
    }
}

#[derive(Clone, Debug)]
struct Production {
    result: Sort,
    items: Vec<Item>,
    label: Option<Label>,
    token: bool,
    transparent: bool,
    bracket: bool,
    syntactic_subsort: bool,
    parse_label: Option<String>,
    apply_priority: Option<BTreeSet<usize>>,
    function: bool,
    macro_like: bool,
}

#[derive(Clone, Copy, Debug, Default)]
struct ProductionOptions<'a> {
    token: bool,
    transparent: bool,
    bracket: bool,
    bracket_label: Option<&'a str>,
    apply_priority: Option<&'a str>,
    function: bool,
    macro_like: bool,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ParsedTerm {
    Production {
        production: usize,
        children: Vec<ParsedTerm>,
    },
    Term(Term),
    Ambiguity(BTreeSet<ParsedTerm>),
}

/// A reusable inner grammar derived from visible, non-parametric productions.
#[derive(Clone, Debug)]
pub struct Grammar {
    productions: Vec<Production>,
    by_result: BTreeMap<Sort, Vec<usize>>,
    priorities: PartialOrder<String>,
    associativities: AssociativityRelations,
    subsort_relations: BTreeSet<(Sort, Sort)>,
}

impl Default for Grammar {
    fn default() -> Self {
        Self {
            productions: Vec::new(),
            by_result: BTreeMap::new(),
            priorities: PartialOrder::new([]).expect("an empty relation is acyclic"),
            associativities: AssociativityRelations::default(),
            subsort_relations: BTreeSet::new(),
        }
    }
}

impl Grammar {
    pub fn from_sentences<'a>(
        sentences: impl IntoIterator<Item = &'a Sentence>,
    ) -> Result<Self, ParseError> {
        let sentences = sentences.into_iter().collect::<Vec<_>>();
        let lexical = sentences
            .iter()
            .filter_map(|sentence| match sentence {
                Sentence::SyntaxLexical { name, regex, .. } => Some((name, regex)),
                _ => None,
            })
            .map(|(name, regex)| {
                parse_regex(regex)
                    .map(|regex| (name.clone(), regex))
                    .map_err(|error| ParseError::InvalidRegex {
                        regex: regex.clone(),
                        message: error.to_string(),
                    })
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let priorities = compute_priorities(sentences.iter().copied())
            .map_err(|cycle| ParseError::CircularPriorities { path: cycle.path })?;
        let associativities = compute_associativities(sentences.iter().copied());
        let mut grammar = Self {
            priorities,
            associativities,
            ..Self::default()
        };
        for sentence in sentences {
            let Sentence::Production {
                label,
                parameters,
                sort,
                items,
                attributes,
            } = sentence
            else {
                continue;
            };
            // RuleGrammarGenerator concretizes these before Earley parsing. The
            // configuration grammar adds the concrete bridge productions it needs.
            if !parameters.is_empty() {
                continue;
            }
            grammar.add_production_with_lexical(
                sort.clone(),
                items,
                label.clone(),
                ProductionOptions {
                    token: attributes.get("token").is_some(),
                    transparent: attributes.get("bracket").is_some(),
                    bracket: attributes.get("bracket").is_some(),
                    bracket_label: attributes.get_str("bracketLabel"),
                    apply_priority: attributes.get_str("applyPriority"),
                    function: attributes.get("function").is_some(),
                    macro_like: ["macro", "macro-rec", "alias", "alias-rec"]
                        .iter()
                        .any(|key| attributes.get(key).is_some()),
                },
                &lexical,
            )?;
        }
        Ok(grammar)
    }

    pub fn parse(&self, start: &Sort, input: &str) -> Result<Term, ParseError> {
        self.parse_with_context(start, input, false)
    }

    pub(crate) fn parse_with_context(
        &self,
        start: &Sort,
        input: &str,
        is_anywhere: bool,
    ) -> Result<Term, ParseError> {
        let mut charts = (0..=input.len())
            .map(|_| Chart::default())
            .collect::<Vec<_>>();
        let start_position = skip_layout(input, 0);
        for production in self.productions_for(start) {
            charts[start_position].add(
                State {
                    production,
                    dot: 0,
                    origin: start_position,
                },
                [Vec::new()],
            )?;
        }
        let mut first_violation = None;

        for position in start_position..=input.len() {
            while let Some(state) = charts[position].agenda.pop_front() {
                let Some(derivations) = charts[position].states.get(&state).cloned() else {
                    continue;
                };
                let production = &self.productions[state.production];
                let canonical = skip_layout(input, position);
                if state.dot < production.items.len() && canonical != position {
                    charts[canonical].add(state, derivations)?;
                    continue;
                }

                match production.items.get(state.dot) {
                    Some(Item::NonTerminal(sort)) => {
                        for predicted in self.productions_for(sort) {
                            charts[position].add(
                                State {
                                    production: predicted,
                                    dot: 0,
                                    origin: position,
                                },
                                [Vec::new()],
                            )?;
                        }

                        // Aycock/Horspool nullable fix: a completed nullable
                        // production may have been processed before this caller.
                        let (completed, violation) = completed_nodes(
                            &charts[position],
                            self,
                            sort,
                            position,
                            position,
                            input,
                        );
                        if first_violation.is_none() {
                            first_violation = violation;
                        }
                        if !completed.is_empty() {
                            let advanced = append_nodes(&derivations, &completed);
                            charts[position].add(
                                State {
                                    dot: state.dot + 1,
                                    ..state
                                },
                                advanced,
                            )?;
                        }
                    }
                    Some(item) => {
                        for end in match_item(item, input, position) {
                            charts[end].add(
                                State {
                                    dot: state.dot + 1,
                                    ..state
                                },
                                derivations.clone(),
                            )?;
                        }
                    }
                    None => {
                        let nodes = derivations
                            .iter()
                            .filter_map(|children| {
                                let term = build_parsed_term(
                                    state.production,
                                    production,
                                    children,
                                    input,
                                    state.origin,
                                    position,
                                );
                                if let Some(error) = self.priority_violation(&term) {
                                    first_violation.get_or_insert(error);
                                    None
                                } else {
                                    Some(term)
                                }
                            })
                            .collect::<BTreeSet<_>>();
                        let callers = charts[state.origin]
                            .states
                            .iter()
                            .filter_map(|(caller, caller_derivations)| {
                                let caller_production = &self.productions[caller.production];
                                matches!(
                                    caller_production.items.get(caller.dot),
                                    Some(Item::NonTerminal(sort)) if sort == &production.result
                                )
                                .then(|| (*caller, caller_derivations.clone()))
                            })
                            .collect::<Vec<_>>();
                        for (caller, caller_derivations) in callers {
                            charts[position].add(
                                State {
                                    dot: caller.dot + 1,
                                    ..caller
                                },
                                append_nodes(&caller_derivations, &nodes),
                            )?;
                        }
                    }
                }
            }
        }

        let mut parses = BTreeSet::new();
        for (position, chart) in charts.iter().enumerate().skip(start_position) {
            if chart.states.is_empty() {
                continue;
            }
            if skip_layout(input, position) != input.len() {
                continue;
            }
            let (completed, violation) =
                completed_nodes(chart, self, start, start_position, position, input);
            parses.extend(completed);
            if first_violation.is_none() {
                first_violation = violation;
            }
        }
        if parses.is_empty() {
            return Err(first_violation.unwrap_or_else(|| self.no_parse(&charts)));
        }
        let mut parsed = BTreeSet::new();
        for term in parses {
            if let Some(error) = self.priority_violation(&term) {
                first_violation.get_or_insert(error);
            } else {
                parsed.insert(self.resolve_applications(term)?);
            }
        }
        match parsed.len() {
            0 => Err(first_violation.unwrap_or_else(|| ParseError::NoParse {
                position: input.len(),
                expected: vec!["an expression respecting priority and associativity".into()],
            })),
            _ => {
                let forest = self.push_top_lhs_ambiguity_up(
                    self.factor_ambiguities(ParsedTerm::Ambiguity(parsed)),
                );
                let parses = Grammar::ambiguity_count(&forest);
                if parses > 1 {
                    Err(ParseError::Ambiguous { parses })
                } else {
                    Ok(self.lower(self.infer_sorts(forest, start, is_anywhere)?))
                }
            }
        }
    }

    pub(crate) fn add(
        &mut self,
        result: Sort,
        items: Vec<ProductionItem>,
        label: Option<Label>,
        token: bool,
        transparent: bool,
    ) -> Result<(), ParseError> {
        self.add_production(result, &items, label, token, transparent)
    }

    pub(crate) fn add_bracket(
        &mut self,
        result: Sort,
        items: Vec<ProductionItem>,
    ) -> Result<(), ParseError> {
        let bracket_label = format!("#bracket:{result}");
        self.add_production_with_lexical(
            result,
            &items,
            None,
            ProductionOptions {
                transparent: true,
                bracket: true,
                bracket_label: Some(&bracket_label),
                ..ProductionOptions::default()
            },
            &BTreeMap::new(),
        )
    }

    pub(crate) fn add_left_associative(&mut self, label: impl Into<String>) {
        let label = label.into();
        self.associativities.left.insert((label.clone(), label));
    }

    fn add_production(
        &mut self,
        result: Sort,
        items: &[ProductionItem],
        label: Option<Label>,
        token: bool,
        transparent: bool,
    ) -> Result<(), ParseError> {
        self.add_production_with_lexical(
            result,
            items,
            label,
            ProductionOptions {
                token,
                transparent,
                ..ProductionOptions::default()
            },
            &BTreeMap::new(),
        )
    }

    fn add_production_with_lexical(
        &mut self,
        result: Sort,
        items: &[ProductionItem],
        label: Option<Label>,
        options: ProductionOptions<'_>,
        lexical: &BTreeMap<String, KRegex>,
    ) -> Result<(), ParseError> {
        let items = items
            .iter()
            .filter(|item| !matches!(item, ProductionItem::Terminal(value) if value.is_empty()))
            .map(|item| compile_item(item, lexical))
            .collect::<Result<Vec<_>, _>>()?;
        let index = self.productions.len();
        let syntactic_subsort = label.is_none()
            && !options.bracket
            && matches!(items.as_slice(), [Item::NonTerminal(_)]);
        let parse_label = label
            .as_ref()
            .map(|label| label.name.clone())
            .or_else(|| options.bracket_label.map(str::to_owned))
            .or_else(|| {
                options
                    .bracket
                    .then(|| format!("#bracket:{result}:{index}"))
            });
        let apply_priority = options
            .apply_priority
            .map(parse_apply_priority)
            .transpose()?;
        if syntactic_subsort && let [Item::NonTerminal(child)] = items.as_slice() {
            self.subsort_relations
                .insert((child.clone(), result.clone()));
        }
        self.productions.push(Production {
            result: result.clone(),
            items,
            label,
            token: options.token,
            transparent: options.transparent,
            bracket: options.bracket,
            syntactic_subsort,
            parse_label,
            apply_priority,
            function: options.function,
            macro_like: options.macro_like,
        });
        self.by_result.entry(result).or_default().push(index);
        Ok(())
    }

    fn productions_for(&self, sort: &Sort) -> impl Iterator<Item = usize> + '_ {
        self.by_result.get(sort).into_iter().flatten().copied()
    }

    fn no_parse(&self, charts: &[Chart]) -> ParseError {
        let position = charts
            .iter()
            .rposition(|chart| !chart.states.is_empty())
            .unwrap_or(0);
        let expected = charts[position]
            .states
            .keys()
            .filter_map(|state| {
                self.productions[state.production]
                    .items
                    .get(state.dot)
                    .map(Item::description)
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        ParseError::NoParse { position, expected }
    }
}

fn compile_item(
    item: &ProductionItem,
    lexical: &BTreeMap<String, KRegex>,
) -> Result<Item, ParseError> {
    match item {
        ProductionItem::NonTerminal { sort, .. } => Ok(Item::NonTerminal(sort.clone())),
        ProductionItem::Terminal(terminal) => Ok(Item::Terminal(terminal.clone())),
        ProductionItem::RegexTerminal {
            precede_regex,
            regex,
            follow_regex,
        } => Ok(Item::Regex {
            source: regex.clone(),
            pattern: compile_regex(&expand_regex(regex, lexical)?, true)?,
            precede: precede_regex
                .as_deref()
                .map(|regex| {
                    expand_regex(regex, lexical).and_then(|regex| compile_regex(&regex, false))
                })
                .transpose()?,
            follow: follow_regex
                .as_deref()
                .map(|regex| {
                    expand_regex(regex, lexical).and_then(|regex| compile_regex(&regex, true))
                })
                .transpose()?,
        }),
    }
}

fn compile_regex(source: &str, start: bool) -> Result<CompiledRegex, ParseError> {
    let pattern = if start {
        format!(r"\A(?:{source})")
    } else {
        format!(r"(?:{source})\z")
    };
    CompiledRegex::new(&pattern).map_err(|error| ParseError::InvalidRegex {
        regex: source.to_owned(),
        message: error.to_string(),
    })
}

fn expand_regex(source: &str, lexical: &BTreeMap<String, KRegex>) -> Result<String, ParseError> {
    if lexical.is_empty() {
        return Ok(source.to_owned());
    }
    let parsed = parse_regex(source).map_err(|error| ParseError::InvalidRegex {
        regex: source.to_owned(),
        message: error.to_string(),
    })?;
    let body = expand_regex_body(&parsed.body, lexical, &mut Vec::new())?;
    Ok(KRegex {
        start_line: parsed.start_line,
        body,
        end_line: parsed.end_line,
    }
    .to_source_string())
}

fn expand_regex_body(
    body: &RegexBody,
    lexical: &BTreeMap<String, KRegex>,
    stack: &mut Vec<String>,
) -> Result<RegexBody, ParseError> {
    Ok(match body {
        RegexBody::Named(name) => {
            if stack.contains(name) {
                stack.push(name.clone());
                return Err(ParseError::InvalidRegex {
                    regex: format!("{{{name}}}"),
                    message: format!("recursive lexical reference: {}", stack.join(" -> ")),
                });
            }
            let Some(definition) = lexical.get(name) else {
                return Err(ParseError::InvalidRegex {
                    regex: format!("{{{name}}}"),
                    message: format!("undefined lexical identifier {name:?}"),
                });
            };
            stack.push(name.clone());
            let expanded = expand_regex_body(&definition.body, lexical, stack)?;
            stack.pop();
            expanded
        }
        RegexBody::Union { left, right } => RegexBody::Union {
            left: Box::new(expand_regex_body(left, lexical, stack)?),
            right: Box::new(expand_regex_body(right, lexical, stack)?),
        },
        RegexBody::Concat(members) => RegexBody::Concat(
            members
                .iter()
                .map(|member| expand_regex_body(member, lexical, stack))
                .collect::<Result<_, _>>()?,
        ),
        RegexBody::ZeroOrMore(body) => {
            RegexBody::ZeroOrMore(Box::new(expand_regex_body(body, lexical, stack)?))
        }
        RegexBody::ZeroOrOne(body) => {
            RegexBody::ZeroOrOne(Box::new(expand_regex_body(body, lexical, stack)?))
        }
        RegexBody::OneOrMore(body) => {
            RegexBody::OneOrMore(Box::new(expand_regex_body(body, lexical, stack)?))
        }
        RegexBody::Exactly { body, count } => RegexBody::Exactly {
            body: Box::new(expand_regex_body(body, lexical, stack)?),
            count: *count,
        },
        RegexBody::AtLeast { body, count } => RegexBody::AtLeast {
            body: Box::new(expand_regex_body(body, lexical, stack)?),
            count: *count,
        },
        RegexBody::Range {
            body,
            at_least,
            at_most,
        } => RegexBody::Range {
            body: Box::new(expand_regex_body(body, lexical, stack)?),
            at_least: *at_least,
            at_most: *at_most,
        },
        body @ (RegexBody::Char(_) | RegexBody::AnyChar | RegexBody::CharClass { .. }) => {
            body.clone()
        }
    })
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct State {
    production: usize,
    dot: usize,
    origin: usize,
}

#[derive(Clone, Debug, Default)]
struct Chart {
    states: BTreeMap<State, BTreeSet<Vec<ParsedTerm>>>,
    agenda: VecDeque<State>,
}

impl Chart {
    fn add(
        &mut self,
        state: State,
        derivations: impl IntoIterator<Item = Vec<ParsedTerm>>,
    ) -> Result<bool, ParseError> {
        let stored = self.states.entry(state).or_default();
        let old_len = stored.len();
        for derivation in derivations {
            stored.insert(derivation);
            if stored.len() > MAX_DERIVATIONS_PER_STATE {
                return Err(ParseError::TooManyParses {
                    limit: MAX_DERIVATIONS_PER_STATE,
                });
            }
        }
        let changed = stored.len() != old_len;
        if changed {
            self.agenda.push_back(state);
        }
        Ok(changed)
    }
}

fn completed_nodes(
    chart: &Chart,
    grammar: &Grammar,
    sort: &Sort,
    origin: usize,
    end: usize,
    input: &str,
) -> (BTreeSet<ParsedTerm>, Option<ParseError>) {
    let mut nodes = BTreeSet::new();
    let mut first_violation = None;
    for (state, derivations) in chart.states.iter().filter(|(state, _)| {
        let production = &grammar.productions[state.production];
        state.origin == origin && state.dot == production.items.len() && &production.result == sort
    }) {
        let production = &grammar.productions[state.production];
        for children in derivations {
            let term = build_parsed_term(
                state.production,
                production,
                children,
                input,
                state.origin,
                end,
            );
            if let Some(error) = grammar.priority_violation(&term) {
                first_violation.get_or_insert(error);
            } else {
                nodes.insert(term);
            }
        }
    }
    (nodes, first_violation)
}

fn append_nodes(
    derivations: &BTreeSet<Vec<ParsedTerm>>,
    nodes: &BTreeSet<ParsedTerm>,
) -> BTreeSet<Vec<ParsedTerm>> {
    derivations
        .iter()
        .flat_map(|derivation| {
            nodes.iter().map(move |node| {
                let mut combined = derivation.clone();
                combined.push(node.clone());
                combined
            })
        })
        .take(MAX_DERIVATIONS_PER_STATE + 1)
        .collect()
}

fn match_item(item: &Item, input: &str, position: usize) -> Vec<usize> {
    match item {
        Item::Terminal(terminal) => input[position..]
            .starts_with(terminal)
            .then_some(position + terminal.len())
            .into_iter()
            .collect(),
        Item::Regex {
            pattern,
            precede,
            follow,
            ..
        } => {
            if precede
                .as_ref()
                .is_some_and(|restriction| restriction.is_match(&input[..position]))
            {
                return Vec::new();
            }
            let Some(found) = pattern.find(&input[position..]) else {
                return Vec::new();
            };
            let end = position + found.end();
            if follow
                .as_ref()
                .is_some_and(|restriction| restriction.is_match(&input[end..]))
            {
                return Vec::new();
            }
            vec![end]
        }
        Item::NonTerminal(_) => Vec::new(),
    }
}

fn build_parsed_term(
    production_index: usize,
    production: &Production,
    children: &[ParsedTerm],
    input: &str,
    start: usize,
    end: usize,
) -> ParsedTerm {
    if production.token {
        if production.result.name == "#KVariable" {
            return ParsedTerm::Term(Term::Variable {
                name: input[start..end].to_owned(),
                sort: None,
            });
        }
        return ParsedTerm::Term(Term::Token {
            token: input[start..end].to_owned(),
            sort: production.result.clone(),
        });
    }
    if !production.bracket
        && (production.transparent || production.label.is_none())
        && let [child] = children
    {
        return child.clone();
    }
    ParsedTerm::Production {
        production: production_index,
        children: children.to_vec(),
    }
}

fn lower_term(production: &Production, children: &[Term]) -> Term {
    if production.transparent || production.label.is_none() && children.len() == 1 {
        return children[0].clone();
    }
    let label = production
        .label
        .clone()
        .unwrap_or_else(|| Label::new("#anonymous"));
    match (label.name.as_str(), children) {
        ("#EmptyK", []) => Term::Sequence(Vec::new()),
        ("#KSequence", items) => Term::sequence(items.iter().cloned()),
        ("#KRewrite", [left, right]) => Term::Rewrite {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        },
        ("#KAs", [pattern, alias]) => Term::As {
            pattern: Box::new(pattern.clone()),
            alias: Box::new(alias.clone()),
        },
        _ => Term::Apply {
            label,
            arguments: children.to_vec(),
        },
    }
}

fn skip_layout(input: &str, mut position: usize) -> usize {
    loop {
        let before = position;
        while let Some(character) = input[position..].chars().next() {
            if !matches!(character, ' ' | '\n' | '\r' | '\t') {
                break;
            }
            position += character.len_utf8();
        }
        if input[position..].starts_with("//") {
            position += 2;
            while let Some(character) = input[position..].chars().next() {
                if matches!(character, '\n' | '\r') {
                    break;
                }
                position += character.len_utf8();
            }
        } else if input[position..].starts_with("/*")
            && let Some(end) = input[position + 2..].find("*/")
        {
            position += 2 + end + 2;
        }
        if position == before {
            return position;
        }
    }
}
