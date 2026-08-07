//! A portable chart parser over lowered K productions.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

use regex::Regex as CompiledRegex;

use crate::definition::{ProductionItem, Regex as KRegex, RegexBody, Sentence, parse_regex};
use crate::kast::{Label, Sort, Term};

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
}

/// A reusable inner grammar derived from visible, non-parametric productions.
#[derive(Clone, Debug, Default)]
pub struct Grammar {
    productions: Vec<Production>,
    by_result: BTreeMap<Sort, Vec<usize>>,
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
        let mut grammar = Self::default();
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
                attributes.get("token").is_some(),
                attributes.get("bracket").is_some(),
                &lexical,
            )?;
        }
        Ok(grammar)
    }

    pub fn parse(&self, start: &Sort, input: &str) -> Result<Term, ParseError> {
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
                        let completed = completed_nodes(
                            &charts[position],
                            &self.productions,
                            sort,
                            position,
                            position,
                            input,
                        );
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
                            .map(|children| {
                                build_term(production, children, input, state.origin, position)
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
            parses.extend(completed_nodes(
                chart,
                &self.productions,
                start,
                start_position,
                position,
                input,
            ));
        }
        match parses.len() {
            0 => Err(self.no_parse(&charts)),
            1 => Ok(parses.pop_first().expect("length was one")),
            parses => Err(ParseError::Ambiguous { parses }),
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

    fn add_production(
        &mut self,
        result: Sort,
        items: &[ProductionItem],
        label: Option<Label>,
        token: bool,
        transparent: bool,
    ) -> Result<(), ParseError> {
        self.add_production_with_lexical(result, items, label, token, transparent, &BTreeMap::new())
    }

    fn add_production_with_lexical(
        &mut self,
        result: Sort,
        items: &[ProductionItem],
        label: Option<Label>,
        token: bool,
        transparent: bool,
        lexical: &BTreeMap<String, KRegex>,
    ) -> Result<(), ParseError> {
        let items = items
            .iter()
            .filter(|item| !matches!(item, ProductionItem::Terminal(value) if value.is_empty()))
            .map(|item| compile_item(item, lexical))
            .collect::<Result<Vec<_>, _>>()?;
        let index = self.productions.len();
        self.productions.push(Production {
            result: result.clone(),
            items,
            label,
            token,
            transparent,
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
    states: BTreeMap<State, BTreeSet<Vec<Term>>>,
    agenda: VecDeque<State>,
}

impl Chart {
    fn add(
        &mut self,
        state: State,
        derivations: impl IntoIterator<Item = Vec<Term>>,
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
    productions: &[Production],
    sort: &Sort,
    origin: usize,
    end: usize,
    input: &str,
) -> BTreeSet<Term> {
    chart
        .states
        .iter()
        .filter(|(state, _)| {
            let production = &productions[state.production];
            state.origin == origin
                && state.dot == production.items.len()
                && &production.result == sort
        })
        .flat_map(|(state, derivations)| {
            let production = &productions[state.production];
            derivations
                .iter()
                .map(move |children| build_term(production, children, input, state.origin, end))
        })
        .collect()
}

fn append_nodes(derivations: &BTreeSet<Vec<Term>>, nodes: &BTreeSet<Term>) -> BTreeSet<Vec<Term>> {
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

fn build_term(
    production: &Production,
    children: &[Term],
    input: &str,
    start: usize,
    end: usize,
) -> Term {
    if production.token {
        if production.result.name == "#KVariable" {
            return Term::Variable {
                name: input[start..end].to_owned(),
                sort: None,
            };
        }
        return Term::Token {
            token: input[start..end].to_owned(),
            sort: production.result.clone(),
        };
    }
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
