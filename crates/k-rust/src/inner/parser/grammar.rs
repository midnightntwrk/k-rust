//! ```toml algorithm
//! id = "parser.grammar.build"
//! name = "construction of a reusable inner-parser grammar"
//! sites = ["Grammar::from_collected_sentences", "Grammar::from_rule_sentences", "Grammar::from_program_sentences", "Grammar::from_configuration_sentences", "Grammar::from_sentences", "Grammar::add_production"]
//! variable = "S = visible sentences; I = production items"
//! counters = ["ParserGrammarBuilds"]
//! span = "per call"
//!
//! [[cost]]
//! mode = "one grammar"
//! bound = "O(S x I) plus declared relation and specialization work"
//! ```
//!
//! ```toml algorithm
//! id = "parser.grammar.unary_cycles"
//! name = "detection of productive unary grammar cycles"
//! sites = ["Grammar::identify_productive_unary_cycles", "unary_reachable"]
//! variable = "U = unary productions; V = sorts; E = unary edges"
//! counters = []
//! no_counter = "productive-cycle detection has no dedicated counter"
//!
//! [[cost]]
//! mode = "one grammar"
//! bound = "O(U x V x E)"
//! ```
//!
//! Construction of reusable parser grammars from visible K sentences.
//!
//! Production insertion is O(|sentences| * |items|), plus the declared relation computations and
//! the specialized parametric, list, and record expansions. Productive unary-cycle detection is
//! O(|unary productions| * |sorts| * |unary edges|) and runs once after construction.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::definition::ast::TransientWireValue;
use crate::definition::{
    AttributeKey, Attributes, PartialOrder, ProductionCatalog, ProductionItem, Regex as KRegex,
    Sentence, compute_associativities, compute_disambiguation_subsorts, compute_overloads,
    compute_priorities, compute_subsorts, parse_regex,
};
use crate::kast::{FrontendSort, Label, ProductionIdentity, Sort};

use super::disambiguation::parse_apply_priority;
use super::scanner::{Item, Layout, Scanner, compile_item};
use super::{
    Grammar, ParseError, ParserRole, Production, ProductionOptions, TokenPrecedenceDeclaration,
};

impl Grammar {
    pub(in crate::inner) fn from_program_sentences<'a>(
        sentences: impl IntoIterator<Item = &'a Sentence>,
        source_catalog: &ProductionCatalog<'_>,
    ) -> Result<Self, ParseError> {
        let mut sentences = sentences.into_iter().cloned().collect::<Vec<_>>();
        // Program grammars parse the empty list as the empty string rather than the
        // `.Sort` terminator. Record each erased terminator's source production at
        // the moment of erasure so the link survives the rewrite.
        let mut erased = Vec::new();
        for sentence in &mut sentences {
            let is_terminator = matches!(
                &*sentence,
                Sentence::Production { items, attributes, .. }
                    if matches!(
                        attributes.string(AttributeKey::UserList),
                        Some("*") | Some("+")
                    )
                        && !items
                            .iter()
                            .any(|item| matches!(item, ProductionItem::NonTerminal { .. }))
            );
            if !is_terminator {
                continue;
            }
            let source = catalog_production(source_catalog, sentence);
            if let Sentence::Production { items, .. } = sentence {
                items.clear();
            }
            if let Some(source) = source {
                erased.push((sentence.clone(), source));
            }
        }
        Self::from_collected_sentences(
            sentences.iter().collect(),
            Some(SourceLinks {
                catalog: source_catalog,
                erased,
            }),
            ParserRole::Program,
            false,
            None,
        )
    }

    pub fn from_sentences<'a>(
        sentences: impl IntoIterator<Item = &'a Sentence>,
    ) -> Result<Self, ParseError> {
        let sentences = sentences.into_iter().collect::<Vec<_>>();
        Self::from_collected_sentences(sentences, None, ParserRole::Rule, false, None)
    }

    pub(in crate::inner) fn from_configuration_sentences<'a>(
        sentences: impl IntoIterator<Item = &'a Sentence>,
    ) -> Result<Self, ParseError> {
        let sentences = sentences.into_iter().collect::<Vec<_>>();
        Self::from_collected_sentences(sentences, None, ParserRole::Rule, true, None)
    }

    pub(in crate::inner) fn from_rule_sentences<'a>(
        sentences: impl IntoIterator<Item = &'a Sentence>,
        source_catalog: &ProductionCatalog<'_>,
        scanner_seed: Option<&Scanner>,
    ) -> Result<Self, ParseError> {
        let sentences = sentences.into_iter().collect::<Vec<_>>();
        Self::from_collected_sentences(
            sentences,
            Some(SourceLinks::catalog(source_catalog)),
            ParserRole::Rule,
            true,
            scanner_seed,
        )
    }

    fn from_collected_sentences(
        sentences: Vec<&Sentence>,
        source_links: Option<SourceLinks<'_, '_>>,
        role: ParserRole,
        include_default_layout: bool,
        scanner_seed: Option<&Scanner>,
    ) -> Result<Self, ParseError> {
        let _span = measure::algorithm_span(Algorithm::ParserGrammarBuild);
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
        let layout_declared = sentences.iter().any(|sentence| match sentence {
            Sentence::SyntaxSort { sort, .. } | Sentence::Production { sort, .. } => {
                sort.is_frontend(FrontendSort::Layout)
            }
            _ => false,
        });
        let layout_sources = sentences
            .iter()
            .filter_map(|sentence| match sentence {
                Sentence::Production { sort, items, .. }
                    if sort.is_frontend(FrontendSort::Layout) =>
                {
                    Some(items)
                }
                _ => None,
            })
            .map(|items| match items.as_slice() {
                [
                    ProductionItem::RegexTerminal {
                        precede_regex: None,
                        regex,
                        follow_regex: None,
                    },
                ] => Ok(regex.clone()),
                _ => Err(ParseError::InvalidLayoutProduction),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let priorities = compute_priorities(sentences.iter().copied())
            .map_err(|cycle| ParseError::CircularPriorities { path: cycle.path })?;
        let associativities = compute_associativities(sentences.iter().copied());
        let semantic_subsorts = match role {
            ParserRole::Program => compute_subsorts(sentences.iter().copied(), false),
            ParserRole::Rule => compute_disambiguation_subsorts(&sentences),
        }
        .map_err(|cycle| ParseError::CircularSubsorts { path: cycle.path })?;
        let overloads =
            compute_overloads(sentences.iter().copied(), &semantic_subsorts).map_err(|cycle| {
                ParseError::CircularOverloads {
                    path: cycle.path.into_iter().map(|id| id.to_string()).collect(),
                }
            })?;
        let external = source_links.is_some();
        let source_links =
            source_links.unwrap_or_else(|| SourceLinks::catalog(overloads.catalog()));
        let source_production_texts = source_links
            .catalog
            .productions()
            .filter_map(|(id, sentence)| {
                render_production(sentence).map(|text| (source_links.catalog.identity(id), text))
            })
            .collect();
        let overload_order = {
            let relations = overloads
                .order()
                .direct_relations()
                .iter()
                .filter_map(|(lesser, greater)| {
                    let lesser = if external {
                        source_links.resolve(overloads.catalog().production(*lesser))?
                    } else {
                        overloads.catalog().identity(*lesser)
                    };
                    let greater = if external {
                        source_links.resolve(overloads.catalog().production(*greater))?
                    } else {
                        overloads.catalog().identity(*greater)
                    };
                    (lesser != greater).then_some((lesser, greater))
                })
                .collect::<BTreeSet<_>>();
            PartialOrder::new(relations).map_err(|cycle| ParseError::CircularOverloads {
                path: cycle.path.into_iter().map(|id| id.to_string()).collect(),
            })?
        };
        let mut grammar = Self {
            scanner: scanner_seed.cloned().unwrap_or_default(),
            source_production_texts,
            layout: if include_default_layout {
                Layout::compile_with_default(&layout_sources, &lexical)?
            } else if layout_declared {
                Layout::compile(&layout_sources, &lexical)?
            } else {
                Layout::default()
            },
            priorities,
            associativities,
            overloads: overload_order,
            role,
            ..Self::default()
        };
        for sentence in &sentences {
            let Sentence::Production {
                label,
                parameters,
                sort,
                items,
                attributes,
            } = *sentence
            else {
                continue;
            };
            if sort.is_frontend(FrontendSort::Layout) {
                continue;
            }
            // RuleGrammarGenerator concretizes these before Earley parsing. The
            // configuration grammar adds the concrete bridge productions it needs.
            if !parameters.is_empty() {
                continue;
            }
            let source_production = source_links.resolve(sentence);
            let source_production_text =
                source_production.and_then(|_| render_production(sentence));
            grammar.add_production_with_lexical(
                sort.clone(),
                items,
                label.clone(),
                ProductionOptions {
                    token: attributes.has(AttributeKey::Token),
                    transparent: attributes.has(AttributeKey::Bracket),
                    bracket: attributes.has(AttributeKey::Bracket),
                    bracket_label: attributes
                        .label(AttributeKey::BracketLabel)
                        .map(|label| label.name),
                    apply_priority: attributes.string(AttributeKey::ApplyPriority),
                    function: attributes.has(AttributeKey::Function),
                    macro_like: attributes.has_any(&AttributeKey::MACRO_LIKE),
                    prefer: attributes.has(AttributeKey::Prefer),
                    avoid: attributes.has(AttributeKey::Avoid),
                    source_production,
                    source_production_text: source_production_text.as_deref(),
                    source: attributes.source(),
                    location: attributes.location(),
                    user_list: attributes.has(AttributeKey::UserList),
                    user_list_nonempty: attributes.string(AttributeKey::UserList) == Some("+"),
                    precedence: attributes.string(AttributeKey::Prec),
                    hook: attributes.string(AttributeKey::Hook),
                    parsing_only_subsort: false,
                },
                &lexical,
            )?;
        }
        grammar.add_parametric_productions(&sentences, &lexical, source_links.catalog)?;
        grammar.initialize_user_lists()?;
        let original_productions = grammar.productions.len();
        for production in 0..original_productions {
            grammar.add_record_productions(production)?;
        }
        grammar.identify_productive_unary_cycles();
        measure::bump(Counter::ParserGrammarBuilds);
        Ok(grammar)
    }
}

impl Grammar {
    /// Let every argument position of sort `S` also recognize `rule_sorts[S]`, the rule
    /// scaffolding sort that derives `S`, `S #as V`, and a rewrite between two of those.
    ///
    /// A rewrite `L => R` whose sides have sort `S` stands for a term of sort `S` in a rule
    /// pattern, so it is admissible wherever an `S` is, and it lowers to the same untyped
    /// `#KRewrite` at any depth. The widened position only changes what the recognizer predicts;
    /// the declared item sort stays in `items` for inference, priorities, and list completion.
    ///
    /// Positions are left unchanged where widening would add a second derivation of the same
    /// rewrite or would change a production that is not a monomorphic constructor:
    /// - an unlabeled single-nonterminal production (a subsort or chain), because the rewrite is
    ///   already admitted at the result sort, whose `#Rule` sort is predicted there;
    /// - the productions of the `scaffolding` sorts (the `#Rule` sorts and the rewrite-side sorts
    ///   below them), so the operands of `=>` and `#as` stay plain `S` and a rewrite cannot be
    ///   the direct operand of another rewrite or of an `#as`;
    /// - the rule structure (`#RuleBody`, `#RuleContent`): the body is already a `#Rule` position
    ///   and side conditions are not patterns;
    /// - token productions and concretized parametric productions.
    ///
    /// Generated record-field productions are widened like their source production, so a named
    /// field `name: S` admits the same rewrites as the positional argument.
    #[cfg(not(feature = "z3-inference"))]
    pub(in crate::inner) fn admit_rewrites_in_argument_positions(
        &mut self,
        rule_sorts: &BTreeMap<Sort, Sort>,
        scaffolding: &BTreeSet<Sort>,
    ) {
        let rule_sort_ids = rule_sorts
            .iter()
            .filter_map(|(sort, rule_sort)| Some((self.sort_id(sort)?, self.sort_id(rule_sort)?)))
            .collect::<BTreeMap<_, _>>();
        let scaffolding = scaffolding
            .iter()
            .filter_map(|sort| self.sort_id(sort))
            .collect::<BTreeSet<_>>();
        let mut changed = false;
        for production in &mut self.productions {
            let unary_chain = production.label.is_none()
                && !production.bracket
                && matches!(production.items.as_slice(), [Item::NonTerminal(_)]);
            if unary_chain
                || production.token
                || production.parametric_origin.is_some()
                || scaffolding.contains(&production.result_id)
                || production.result.is_frontend(FrontendSort::RuleBody)
                || production.result.is_frontend(FrontendSort::RuleContent)
            {
                continue;
            }
            for sort_id in production.item_sort_ids.iter_mut().flatten() {
                if let Some(rule_sort_id) = rule_sort_ids.get(sort_id) {
                    *sort_id = *rule_sort_id;
                    changed = true;
                }
            }
        }
        if changed {
            self.invalidate_prediction_analysis();
        }
    }

    /// Add `result ::= items` where every operand declared `declared` is recognized as
    /// `recognized`, a scaffolding sort that derives `declared` and further patterns of it.
    ///
    /// As at a widened argument position, the declared sort stays in `items` for inference,
    /// priorities, and list completion; only what the recognizer predicts at the operand changes.
    #[cfg(not(feature = "z3-inference"))]
    pub(in crate::inner) fn add_with_recognized_operands(
        &mut self,
        result: Sort,
        items: Vec<ProductionItem>,
        label: Option<Label>,
        declared: &Sort,
        recognized: &Sort,
    ) -> Result<(), ParseError> {
        self.add_production(result, &items, label, false, false)?;
        let recognized = self.intern_sort(recognized);
        let production = self
            .productions
            .last_mut()
            .expect("add_production pushed a production");
        for (item, sort_id) in production.items.iter().zip(&mut production.item_sort_ids) {
            if matches!(item, Item::NonTerminal(sort) if sort == declared) {
                *sort_id = Some(recognized);
            }
        }
        self.invalidate_prediction_analysis();
        Ok(())
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

    pub(crate) fn add_with_source_text(
        &mut self,
        result: Sort,
        items: Vec<ProductionItem>,
        label: Option<Label>,
        token: bool,
        transparent: bool,
        source_production_text: &str,
    ) -> Result<(), ParseError> {
        self.add_production_with_lexical(
            result,
            &items,
            label,
            ProductionOptions {
                token,
                transparent,
                source_production_text: Some(source_production_text),
                ..ProductionOptions::default()
            },
            &BTreeMap::new(),
        )
    }

    pub(crate) fn add_token_with_precedence(
        &mut self,
        result: Sort,
        item: ProductionItem,
        precedence: &str,
    ) -> Result<(), ParseError> {
        self.invalidate_prediction_analysis();
        if self.has_equivalent_production(&result, std::slice::from_ref(&item), true) {
            let compiled = compile_item(&item, &BTreeMap::new())?;
            self.scanner.register(
                &compiled,
                Some(precedence),
                TokenPrecedenceDeclaration {
                    source: None,
                    location: None,
                    production: render_added_production(
                        &result,
                        std::slice::from_ref(&item),
                        true,
                        Some(precedence),
                    ),
                    precedence: 0,
                },
            )?;
            return Ok(());
        }
        self.add_production_with_lexical(
            result,
            &[item],
            None,
            ProductionOptions {
                token: true,
                precedence: Some(precedence),
                ..ProductionOptions::default()
            },
            &BTreeMap::new(),
        )
    }

    pub(crate) fn add_token_subsort(
        &mut self,
        result: impl Into<String>,
        child: impl Into<String>,
    ) -> Result<(), ParseError> {
        let result = Sort::new(result);
        let item = ProductionItem::NonTerminal {
            sort: Sort::new(child),
            name: None,
        };
        if self.has_equivalent_production(&result, std::slice::from_ref(&item), true) {
            return Ok(());
        }
        self.add_production_with_lexical(
            result,
            &[item],
            None,
            ProductionOptions {
                token: true,
                ..ProductionOptions::default()
            },
            &BTreeMap::new(),
        )
    }

    pub(crate) fn has_equivalent_production(
        &self,
        result: &Sort,
        items: &[ProductionItem],
        token: bool,
    ) -> bool {
        self.productions.iter().any(|production| {
            &production.result == result
                && production.declared_items == items
                && production.token == token
        })
    }

    #[cfg(test)]
    pub(crate) fn equivalent_production_count(
        &self,
        result: &Sort,
        items: &[ProductionItem],
        token: bool,
    ) -> usize {
        self.productions
            .iter()
            .filter(|production| {
                &production.result == result
                    && production.declared_items == items
                    && production.token == token
            })
            .count()
    }

    pub(in crate::inner) fn scanner(&self) -> &Scanner {
        &self.scanner
    }

    pub(crate) fn add_bracket(
        &mut self,
        result: Sort,
        items: Vec<ProductionItem>,
        source_attributes: Option<&Attributes>,
    ) -> Result<(), ParseError> {
        // Parametric source brackets have already been instantiated in this grammar.
        // Preserve their parse label and applyPriority contract: an untagged fallback
        // with the same syntax would keep alternatives that the source bracket rejects.
        if self.productions_for(&result).any(|index| {
            let production = &self.productions[index];
            production.bracket && production.declared_items == items
        }) {
            return Ok(());
        }
        let bracket_label = source_attributes
            .and_then(|attributes| attributes.label(AttributeKey::BracketLabel))
            .map_or_else(|| format!("#bracket:{result}"), |label| label.name);
        self.add_production_with_lexical(
            result,
            &items,
            None,
            ProductionOptions {
                transparent: true,
                bracket: true,
                bracket_label: Some(bracket_label),
                apply_priority: source_attributes
                    .and_then(|attributes| attributes.string(AttributeKey::ApplyPriority)),
                ..ProductionOptions::default()
            },
            &BTreeMap::new(),
        )
    }

    pub(crate) fn add_left_associative(&mut self, label: impl Into<String>) {
        let label = label.into();
        self.associativities.left.insert((label.clone(), label));
    }

    #[cfg(test)]
    pub(crate) fn add_right_associative(&mut self, label: impl Into<String>) {
        let label = label.into();
        self.associativities.right.insert((label.clone(), label));
    }

    pub(in crate::inner) fn add_matching_terminal_tokens(
        &mut self,
        result: Sort,
        predicate: impl Fn(&str) -> bool,
    ) -> Result<(), ParseError> {
        let terminals = self
            .productions
            .iter()
            .flat_map(|production| &production.items)
            .filter_map(|item| match item {
                Item::Terminal(value) if predicate(value) => Some(value.clone()),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        for terminal in terminals {
            self.add(
                result.clone(),
                vec![ProductionItem::Terminal(terminal)],
                None,
                true,
                false,
            )?;
        }
        Ok(())
    }

    fn identify_productive_unary_cycles(&mut self) {
        let edges = self
            .productions
            .iter()
            .filter_map(|production| match production.items.as_slice() {
                [Item::NonTerminal(child)] => Some((production.result.clone(), child.clone())),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        self.productive_unary_cycles = self
            .productions
            .iter()
            .enumerate()
            .filter_map(|(index, production)| {
                let [Item::NonTerminal(child)] = production.items.as_slice() else {
                    return None;
                };
                (production.label.is_some()
                    && !production.transparent
                    && unary_reachable(child, &production.result, &edges))
                .then_some(index)
            })
            .collect();
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

    pub(super) fn add_production_with_lexical(
        &mut self,
        result: Sort,
        items: &[ProductionItem],
        label: Option<Label>,
        options: ProductionOptions<'_>,
        lexical: &BTreeMap<String, KRegex>,
    ) -> Result<(), ParseError> {
        // Registration of an earlier item can survive a later compile/attribute failure.
        self.invalidate_prediction_analysis();
        let declared_items = items
            .iter()
            .filter(|item| !matches!(item, ProductionItem::Terminal(value) if value.is_empty()))
            .cloned()
            .collect();
        let field_names = items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { name, .. } => Some(name.clone()),
                ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
            })
            .collect();
        let declaration = TokenPrecedenceDeclaration {
            source: options.source.map(str::to_owned),
            location: options.location,
            production: options.source_production_text.map_or_else(
                || render_added_production(&result, items, options.token, options.precedence),
                str::to_owned,
            ),
            precedence: 0,
        };
        let mut compiled_items = Vec::new();
        for item in items
            .iter()
            .filter(|item| !matches!(item, ProductionItem::Terminal(value) if value.is_empty()))
        {
            let item = compile_item(item, lexical)?;
            self.scanner
                .register(&item, options.precedence, declaration.clone())?;
            compiled_items.push(item);
        }
        let items = compiled_items;
        let index = self.productions.len();
        let result_id = self.intern_sort(&result);
        let item_sort_ids = items
            .iter()
            .map(|item| match item {
                Item::NonTerminal(sort) => Some(self.intern_sort(sort)),
                Item::Terminal(_) | Item::Regex { .. } => None,
            })
            .collect::<Vec<_>>();
        // Java's `Production.isSyntacticSubsort` is purely shape-based; unlike `isSubsort`,
        // it does not require the production to be unlabeled. Priority filtering uses the
        // former, while the semantic subsort relation uses the latter.
        let syntactic_subsort =
            !options.bracket && matches!(items.as_slice(), [Item::NonTerminal(_)]);
        let parse_label = label
            .as_ref()
            .map(|label| label.name.clone())
            .or_else(|| options.bracket_label.clone())
            .or_else(|| {
                options
                    .bracket
                    .then(|| format!("#bracket:{result}:{index}"))
            });
        let apply_priority = options
            .apply_priority
            .map(parse_apply_priority)
            .transpose()?;
        if label.is_none()
            && syntactic_subsort
            && !options.parsing_only_subsort
            && let [Item::NonTerminal(child)] = items.as_slice()
        {
            self.subsort_relations
                .insert((child.clone(), result.clone()));
        }
        if !options.bracket
            && !options.parsing_only_subsort
            && let [Item::NonTerminal(child)] = items.as_slice()
        {
            self.syntactic_subsort_relations
                .insert((child.clone(), result.clone()));
        }
        self.productions.push(Production {
            result: result.clone(),
            result_id,
            declared_items,
            items,
            item_sort_ids,
            label,
            token: options.token,
            transparent: options.transparent,
            bracket: options.bracket,
            syntactic_subsort,
            parse_label,
            apply_priority,
            function: options.function,
            macro_like: options.macro_like,
            prefer: options.prefer,
            avoid: options.avoid,
            source_production: options.source_production,
            source_production_text: options.source_production_text.map(str::to_owned),
            user_list: options.user_list,
            user_list_nonempty: options.user_list_nonempty,
            field_names,
            record: None,
            parametric_origin: None,
            term_production: None,
            hook: options.hook.map(str::to_owned),
        });
        self.by_result[result_id].push(index);
        Ok(())
    }
}

struct SourceLinks<'c, 'a> {
    catalog: &'c ProductionCatalog<'a>,
    /// Sentences rewritten by the program grammar, paired with the source
    /// production they were derived from.
    erased: Vec<(Sentence, ProductionIdentity)>,
}

impl<'c, 'a> SourceLinks<'c, 'a> {
    fn catalog(catalog: &'c ProductionCatalog<'a>) -> Self {
        Self {
            catalog,
            erased: Vec::new(),
        }
    }

    fn resolve(&self, sentence: &Sentence) -> Option<ProductionIdentity> {
        self.erased
            .iter()
            .find_map(|(erased, source)| (erased == sentence).then_some(*source))
            .or_else(|| catalog_production(self.catalog, sentence))
    }
}

/// `GenerateSortProjections.gen(Production)` as `RuleGrammarGenerator.getCombinedGrammar`
/// (RuleGrammarGenerator.java:400-401) applies it to every production of a parsing module,
/// rules and programs alike: one function production `Field ::= name "(" Sort ")"` labelled
/// `project:<klabel>:<name>` per named nonterminal of a labelled production that is neither a
/// function nor a macro, unless the module already defines one of those labels itself. The
/// projection rules are the kompile pass's; a parsing grammar needs only the syntax.
pub(in crate::inner) fn named_projection_productions<'a>(
    sentences: impl IntoIterator<Item = &'a Sentence>,
) -> Vec<Sentence> {
    let sentences = sentences.into_iter().collect::<Vec<_>>();
    let defined = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.name.as_str()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let mut generated = Vec::new();
    for sentence in &sentences {
        let Sentence::Production {
            label: Some(label),
            sort,
            items,
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        if attributes.has(AttributeKey::Function) || attributes.has_any(&AttributeKey::MACRO_LIKE) {
            continue;
        }
        let fields = items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal {
                    sort,
                    name: Some(name),
                } => Some((sort, name)),
                _ => None,
            })
            .collect::<Vec<_>>();
        if fields.is_empty()
            || fields.iter().any(|(_, name)| {
                defined.contains(
                    Label::field_projection(&label.name, name.as_str())
                        .name
                        .as_str(),
                )
            })
        {
            continue;
        }
        for (field_sort, name) in fields {
            let mut generated_attributes = Attributes::default();
            generated_attributes.mark(AttributeKey::Function);
            generated_attributes.mark(AttributeKey::GeneratedRuleSyntax);
            generated.push(Sentence::Production {
                label: Some(Label::field_projection(&label.name, name)),
                parameters: Vec::new(),
                sort: field_sort.clone(),
                items: vec![
                    ProductionItem::Terminal(name.clone()),
                    ProductionItem::Terminal("(".into()),
                    ProductionItem::NonTerminal {
                        sort: sort.clone(),
                        name: None,
                    },
                    ProductionItem::Terminal(")".into()),
                ],
                attributes: generated_attributes,
            });
        }
    }
    generated
}

pub(super) fn catalog_production(
    catalog: &ProductionCatalog<'_>,
    sentence: &Sentence,
) -> Option<ProductionIdentity> {
    if matches!(sentence, Sentence::Production { attributes, .. } if attributes.has(AttributeKey::GeneratedRuleSyntax))
    {
        return None;
    }
    catalog
        .find_equivalent(sentence)
        .map(|production| catalog.identity(production))
}

pub(super) fn render_production(sentence: &Sentence) -> Option<String> {
    let Sentence::Production {
        parameters,
        sort,
        items,
        attributes,
        ..
    } = sentence
    else {
        return None;
    };
    let parameters = if parameters.is_empty() {
        String::new()
    } else {
        format!(
            "{{{}}} ",
            parameters
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    let items = items
        .iter()
        .map(render_production_item)
        .collect::<Vec<_>>()
        .join(" ");
    // Production text is built for every production of every grammar; the shared origin receipt
    // is printed from its cached text, so its JSON tree is neither kept on the definition for
    // the rest of the compile nor rebuilt per production.
    let attributes = attributes
        .transient_wire_entries()
        .filter(|(key, _)| {
            !matches!(
                AttributeKey::from_name(key),
                Some(
                    AttributeKey::Source
                        | AttributeKey::Location
                        | AttributeKey::SourceId
                        | AttributeKey::SentenceStartOffset
                        | AttributeKey::SentenceEndOffset
                        | AttributeKey::InputAddresses
                )
            )
        })
        .map(|(key, value)| match value {
            // A record-backed receipt renders to a JSON object, whose compact text is what the
            // structured-value arm below prints; a receipt loaded from a stored value may hold any
            // JSON value and goes through that match like every other entry.
            TransientWireValue::Origin(origin) if origin.record().is_some() => {
                format!("{key}({})", origin.text())
            }
            value => match value.get().as_ref() {
                serde_json::Value::String(value) if value.is_empty() => key.to_owned(),
                serde_json::Value::Null => key.to_owned(),
                serde_json::Value::String(value) => format!("{key}({value})"),
                value => format!("{key}({value})"),
            },
        })
        .collect::<Vec<_>>();
    let attributes = if attributes.is_empty() {
        String::new()
    } else {
        format!(" [{}]", attributes.join(", "))
    };
    Some(format!("syntax {parameters}{sort} ::= {items}{attributes}"))
}

pub(super) fn render_added_production(
    result: &Sort,
    items: &[ProductionItem],
    token: bool,
    precedence: Option<&str>,
) -> String {
    let items = items
        .iter()
        .map(render_production_item)
        .collect::<Vec<_>>()
        .join(" ");
    let mut attributes = Vec::new();
    if token {
        attributes.push(AttributeKey::Token.as_str().to_owned());
    }
    if let Some(precedence) = precedence {
        attributes.push(format!("prec({precedence})"));
    }
    let attributes = if attributes.is_empty() {
        String::new()
    } else {
        format!(" [{}]", attributes.join(", "))
    };
    format!("syntax {result} ::= {items}{attributes}")
}

fn render_production_item(item: &ProductionItem) -> String {
    match item {
        ProductionItem::NonTerminal { sort, name } => name
            .as_ref()
            .map_or_else(|| sort.to_string(), |name| format!("{name}:{sort}")),
        ProductionItem::RegexTerminal { regex, .. } => {
            format!("r{}", crate::kast::string::quote(regex))
        }
        ProductionItem::Terminal(value) => crate::kast::string::quote(value),
    }
}

fn unary_reachable(start: &Sort, target: &Sort, edges: &BTreeSet<(Sort, Sort)>) -> bool {
    let mut pending = vec![start.clone()];
    let mut visited = BTreeSet::new();
    // Invariant: `visited` contains the explored unary closure and `pending` contains reachable
    // sorts whose outgoing edges have not yet been scanned.
    while let Some(sort) = pending.pop() {
        if &sort == target {
            return true;
        }
        if !visited.insert(sort.clone()) {
            continue;
        }
        pending.extend(
            edges
                .iter()
                .filter(|(from, _)| from == &sort)
                .map(|(_, to)| to.clone()),
        );
    }
    false
}

#[cfg(test)]
mod tests {
    use super::super::{PARSE_ATTEMPTS, ParseContext, ParseProvenance, ParsedTerm, PredictionMode};
    use super::*;
    use crate::kast::{Term, TermMetadata};
    use crate::provenance::SourceId;

    #[test]
    fn production_text_prints_a_stored_origin_value_like_any_attribute() {
        let text = |origin: serde_json::Value| {
            let attributes = Attributes::new(BTreeMap::from([(
                AttributeKey::Origin.as_str().to_owned(),
                origin,
            )]));
            render_production(&Sentence::Production {
                label: Some(Label::new("lbl")),
                parameters: vec![],
                sort: Sort::new("S"),
                items: vec![ProductionItem::Terminal("x".into())],
                attributes,
            })
            .expect("a production has a text")
        };
        let key = AttributeKey::Origin.as_str();
        assert_eq!(
            text(serde_json::json!("foo")),
            format!("syntax S ::= \"x\" [{key}(foo)]")
        );
        assert_eq!(
            text(serde_json::Value::Null),
            format!("syntax S ::= \"x\" [{key}]")
        );
        assert_eq!(
            text(serde_json::json!("")),
            format!("syntax S ::= \"x\" [{key}]")
        );
        assert_eq!(
            text(serde_json::json!({"pass": "p"})),
            format!("syntax S ::= \"x\" [{key}({{\"pass\":\"p\"}})]")
        );
    }

    #[test]
    fn retains_productive_cycles_after_a_viable_prefix() {
        fn nonterminal(name: &str) -> ProductionItem {
            ProductionItem::NonTerminal {
                sort: Sort::new(name),
                name: None,
            }
        }

        fn production(result: &str, items: Vec<ProductionItem>, label: &str) -> Sentence {
            Sentence::Production {
                label: Some(Label::new(label)),
                parameters: vec![],
                sort: Sort::new(result),
                items,
                attributes: Attributes::default(),
            }
        }

        fn unfiltered(grammar: &Grammar, start: &str, input: &str) -> Result<Term, ParseError> {
            grammar.parse_attempt(
                &Sort::new(start),
                input,
                ParseContext {
                    is_anywhere: false,
                    provenance: ParseProvenance {
                        source: SourceId(0),
                        base_offset: 0,
                    },
                    diagnostic_provenance: false,
                },
                PredictionMode::Unfiltered,
                &mut false,
            )
        }

        let grammar = Grammar::from_sentences(&[
            production(
                "Start",
                vec![ProductionItem::Terminal("x".into()), nonterminal("Tail")],
                "start",
            ),
            production(
                "Tail",
                vec![nonterminal("Cycle"), ProductionItem::Terminal("z".into())],
                "tail",
            ),
            production(
                "Tail",
                vec![ProductionItem::Terminal("dead".into())],
                "dead",
            ),
            production("Cycle", vec![nonterminal("Cycle")], "wrap"),
            production("Cycle", vec![], "unit"),
        ])
        .unwrap();
        for input in ["x", "x y"] {
            assert_eq!(
                unfiltered(&grammar, "Start", input),
                Err(ParseError::CyclicParseForest)
            );
            PARSE_ATTEMPTS.set(0);
            assert_eq!(
                grammar.parse(&Sort::new("Start"), input),
                Err(ParseError::CyclicParseForest)
            );
            assert_eq!(PARSE_ATTEMPTS.get(), 2);
        }
    }

    #[test]
    fn external_catalog_overloads_remain_in_source_production_id_space() {
        let production = |sort: &str,
                          child: Option<&str>,
                          terminal: Option<&str>,
                          label: Option<&str>,
                          attributes: Attributes| {
            let items = child
                .map(|child| ProductionItem::NonTerminal {
                    sort: Sort::new(child),
                    name: None,
                })
                .into_iter()
                .chain(terminal.map(|terminal| ProductionItem::Terminal(terminal.into())))
                .collect();
            Sentence::Production {
                label: label.map(Label::new),
                parameters: Vec::new(),
                sort: Sort::new(sort),
                items,
                attributes,
            }
        };
        let mut cell_attributes = Attributes::default();
        cell_attributes.mark(AttributeKey::Cell);
        let sentences = vec![
            production("Cell", None, Some("<cell>"), Some("cell"), cell_attributes),
            production("Big", Some("Small"), None, None, Attributes::default()),
            production(
                "Small",
                None,
                Some("x"),
                Some("value"),
                Attributes::default(),
            ),
            production("Big", None, Some("x"), Some("value"), Attributes::default()),
        ];
        let source_catalog = ProductionCatalog::from_visible(&sentences);
        let parsing_sentences = sentences
            .iter()
            .filter(|sentence| {
                !matches!(sentence, Sentence::Production { attributes, .. }
                if attributes.has(AttributeKey::Cell))
            })
            .collect::<Vec<_>>();
        let grammar =
            Grammar::from_rule_sentences(parsing_sentences, &source_catalog, None).unwrap();
        let source_id = |sort: &str| {
            source_catalog
                .productions()
                .find_map(|(id, sentence)| match sentence {
                    Sentence::Production {
                        label: Some(label),
                        sort: result,
                        ..
                    } if label.name == "value" && result.name == sort => Some(id),
                    _ => None,
                })
                .unwrap()
        };
        let small = source_catalog.identity(source_id("Small"));
        let big = source_catalog.identity(source_id("Big"));
        let cell = source_catalog
            .productions()
            .find_map(|(id, sentence)| match sentence {
                Sentence::Production {
                    label: Some(label), ..
                } if label.name == "cell" => Some(source_catalog.identity(id)),
                _ => None,
            })
            .unwrap();

        assert!(grammar.overloads.less_than(&small, &big));
        assert!(!grammar.overloads.contains(&cell));

        let parsed = |source| {
            let production = grammar
                .productions
                .iter()
                .position(|production| production.source_production == Some(source))
                .unwrap();
            ParsedTerm::Production {
                production,
                children: Vec::new(),
                metadata: TermMetadata::default(),
            }
        };
        let filtered =
            grammar.filter_overloads_prefer_avoid(ParsedTerm::Ambiguity(BTreeSet::from([
                parsed(small),
                parsed(big),
            ])));
        assert!(matches!(filtered, ParsedTerm::Production { production, .. }
            if grammar.productions[production].source_production == Some(small)));
    }
}
