use k_rust::{
    definition::{
        self as native_definition, Attributes as NativeAttributes, ProductionItem as NativeItem,
        Sentence as NativeSentence,
    },
    kast::{Label as NativeLabel, Sort as NativeSort, Term as NativeTerm},
};
use krs_ir::{
    BuiltinSort, CellAttribute, CellContentFrame, CellPost, ClaimModality, ConfigurationClause,
    ConfigurationRoot, FixedCell, FixedCellContent, FixedConfiguration, FixedConfigurationPattern,
    FixedConfigurationRewrite, FixedConfigurationVariable, FixedInitializerCell,
    FixedInitializerContent, FormatFragment, GrammarProductionItemKind, GroupAssociativity,
    MapOperation, NodeOrigin, ProductionGroupId, SemanticId, SentenceKind, StrictnessKind,
};
use krs_ir_levels::{
    ConfigurationSentence, ContextAliasSentence, DefinitionProductionAttribute,
    DefinitionScopedBinder, DefinitionSentence, DefinitionSortRef, DefinitionTerm,
    DefinitionTermKind, ProductionSentence, RuleBodyRef, RuleSentence, SymbolId,
    k_surface::{cell_sort_name, generated_variable_name},
};
use serde_json::json;

use super::{Adapter, AdapterError, SentenceNodeRole, attributes_for_origin, term::TermContext};

impl Adapter<'_> {
    pub(super) fn sentence(
        &mut self,
        sentence: &DefinitionSentence,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeSentence, AdapterError> {
        self.map_sentence_origin(
            sentence.origin(),
            module,
            sentence_index,
            SentenceNodeRole::Sentence,
        );
        match sentence {
            DefinitionSentence::SyntaxSort(sentence) => Ok(NativeSentence::SyntaxSort {
                parameters: Vec::new(),
                sort: NativeSort::new(sentence.symbol().emitted_name()),
                attributes: attributes_for_origin(sentence.origin()),
            }),
            DefinitionSentence::Subsort(sentence) => Ok(NativeSentence::Production {
                label: None,
                parameters: Vec::new(),
                sort: self.sort(sentence.supersort(), sentence.origin())?,
                items: vec![NativeItem::NonTerminal {
                    sort: self.sort(sentence.subsort(), sentence.origin())?,
                    name: None,
                }],
                attributes: attributes_for_origin(sentence.origin()),
            }),
            DefinitionSentence::Production(sentence) => {
                self.production(sentence, module, sentence_index)
            }
            DefinitionSentence::Precedence(sentence) => Ok(NativeSentence::SyntaxPriority {
                priorities: vec![
                    self.tags(sentence.higher(), sentence.origin())?,
                    self.tags(sentence.lower(), sentence.origin())?,
                ],
                attributes: attributes_for_origin(sentence.origin()),
            }),
            DefinitionSentence::Associativity(sentence) => {
                Ok(NativeSentence::SyntaxAssociativity {
                    associativity: match sentence.associativity() {
                        GroupAssociativity::Left => native_definition::Associativity::Left,
                        GroupAssociativity::Right => native_definition::Associativity::Right,
                        GroupAssociativity::NonAssociative => {
                            native_definition::Associativity::NonAssoc
                        }
                    },
                    tags: self.tags(sentence.groups(), sentence.origin())?,
                    attributes: attributes_for_origin(sentence.origin()),
                })
            }
            DefinitionSentence::Configuration(sentence) => {
                self.configuration(sentence, module, sentence_index)
            }
            DefinitionSentence::ContextAlias(sentence) => {
                self.context_alias(sentence, module, sentence_index)
            }
            DefinitionSentence::Rule(sentence) if sentence.kind() == SentenceKind::Context => {
                self.context(sentence, module, sentence_index)
            }
            DefinitionSentence::Rule(sentence) => self.rule(sentence, module, sentence_index),
            // K's outer syntax desugars `syntax lexical` and `#Layout`
            // privately; these are the flat sentences k-rust's outer lowering
            // builds from the emitted `.k` (KF-004).
            DefinitionSentence::Lexical(sentence) => Ok(NativeSentence::SyntaxLexical {
                name: sentence.name().to_owned(),
                regex: sentence.regex().to_owned(),
                attributes: attributes_for_origin(sentence.origin()),
            }),
            DefinitionSentence::Layout(sentence) => {
                let mut attributes = attributes_for_origin(sentence.origin());
                attributes.insert("token", json!(""));
                Ok(NativeSentence::Production {
                    label: None,
                    parameters: Vec::new(),
                    sort: NativeSort::new("#Layout"),
                    items: vec![NativeItem::RegexTerminal {
                        precede_regex: None,
                        regex: sentence.regex().to_owned(),
                        follow_regex: None,
                    }],
                    attributes,
                })
            }
            DefinitionSentence::Raw(sentence) => raw_sentence(sentence, module),
        }
    }

    /// The member labels a priority block or associativity sentence stands for, group by group in
    /// the authored order, as K's outer loader resolves the tags (see `group_tags`).
    fn tags<'g>(
        &self,
        groups: impl IntoIterator<Item = &'g ProductionGroupId>,
        origin: &NodeOrigin,
    ) -> Result<Vec<String>, AdapterError> {
        let mut tags = Vec::new();
        for group in groups {
            tags.extend(self.group_tags(group, origin)?);
        }
        Ok(tags)
    }

    pub(super) fn production(
        &mut self,
        sentence: &ProductionSentence,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeSentence, AdapterError> {
        let mut attributes = attributes_for_origin(sentence.origin());
        for (index, attribute) in sentence.attributes().iter().enumerate() {
            let index = u32::try_from(index).unwrap_or(u32::MAX);
            self.map_sentence_origin(
                attribute.origin(),
                module,
                sentence_index,
                SentenceNodeRole::ProductionAttribute(index),
            );
            self.production_attribute(
                attribute,
                sentence,
                &mut attributes,
                module,
                sentence_index,
                index,
            )?;
        }
        // A list without separator keeps an empty native separator item, so
        // its tail is the third native item.
        let list_gap = usize::from(
            sentence.attributes().iter().any(|attribute| {
                matches!(attribute, DefinitionProductionAttribute::ListCons { separator, .. } if separator.is_empty())
            }),
        );
        let items = sentence
            .items()
            .iter()
            .enumerate()
            .map(|(index, item)| {
                let index = if index == 0 { index } else { index + list_gap };
                self.map_sentence_origin(
                    item.origin(),
                    module,
                    sentence_index,
                    SentenceNodeRole::ProductionItem(u32::try_from(index).unwrap_or(u32::MAX)),
                );
                match item.kind() {
                    GrammarProductionItemKind::Terminal { text } => {
                        Ok(NativeItem::Terminal(text.clone()))
                    }
                    // Unnamed, as the emitted K writes it: K derives record
                    // productions (`sum(... items: I)`) from a named
                    // non-terminal of a prefix production, which Java K would
                    // then not parse, and k-rust prints through.
                    GrammarProductionItemKind::NonTerminal { sort, .. } => {
                        Ok(NativeItem::NonTerminal {
                            sort: self.sort(sort, item.origin())?,
                            name: None,
                        })
                    }
                    GrammarProductionItemKind::RegexTerminal {
                        precede_regex,
                        regex,
                        follow_regex,
                    } => Ok(NativeItem::RegexTerminal {
                        precede_regex: precede_regex.clone(),
                        regex: regex.clone(),
                        follow_regex: follow_regex.clone(),
                    }),
                }
            })
            .collect::<Result<Vec<_>, AdapterError>>()?;
        // K's outer syntax desugars `List{Elem, "sep"}` privately; this is
        // k-rust's `lower_user_list` (`bison_lists = false`) for the cons
        // sentence: `[Elem, Terminal(sep), List]`, unnamed, the separator kept
        // even when empty (KF-020).
        let items = match self.list_cons(sentence)? {
            Some(head) => vec![
                NativeItem::NonTerminal {
                    sort: head,
                    name: None,
                },
                NativeItem::Terminal(list_separator(sentence).to_owned()),
                NativeItem::NonTerminal {
                    sort: self.sort(sentence.result_sort(), sentence.origin())?,
                    name: None,
                },
            ],
            None => items,
        };
        // token-production-constructor: token values lower to KORE domain
        // values, never applications of their parser production. Omit the
        // unused label to match the source frontend's unlabelled-token form.
        // A parametric production declares its parameters on the production
        // and on its label, as k-rust's outer lowering of `syntax {S}` does
        // (KF-027); labels in terms never carry them (X9.1).
        let parameters = sentence
            .parameters()
            .iter()
            .map(|parameter| NativeSort::new(parameter.as_str()))
            .collect::<Vec<_>>();
        let label = attributes.get("token").is_none().then(|| {
            NativeLabel::with_parameters(sentence.symbol().emitted_name(), parameters.clone())
        });
        Ok(NativeSentence::Production {
            label,
            parameters,
            sort: self.sort(sentence.result_sort(), sentence.origin())?,
            items,
            attributes,
        })
    }

    /// The native element sort of a syntactic-list cons production.
    fn list_cons(&self, sentence: &ProductionSentence) -> Result<Option<NativeSort>, AdapterError> {
        if !sentence
            .attributes()
            .iter()
            .any(|attribute| matches!(attribute, DefinitionProductionAttribute::ListCons { .. }))
        {
            return Ok(None);
        }
        let head = sentence
            .items()
            .iter()
            .find_map(|item| match item.kind() {
                GrammarProductionItemKind::NonTerminal { sort, .. } => Some((sort, item.origin())),
                _ => None,
            })
            .ok_or_else(|| AdapterError::MissingSymbol {
                key: sentence.origin().key().clone(),
                symbol: sentence.symbol().id().clone(),
            })?;
        Ok(Some(self.sort(head.0, head.1)?))
    }

    #[expect(
        clippy::too_many_lines,
        reason = "Keeps exhaustive production attribute adaptation in one match."
    )]
    fn production_attribute(
        &mut self,
        attribute: &DefinitionProductionAttribute,
        sentence: &ProductionSentence,
        attributes: &mut NativeAttributes,
        module: &str,
        sentence_index: usize,
        attribute_index: u32,
    ) -> Result<(), AdapterError> {
        match attribute {
            DefinitionProductionAttribute::Documentation { .. } => {}
            DefinitionProductionAttribute::Function { .. } => {
                attributes.insert("function", json!(""));
            }
            DefinitionProductionAttribute::Total { .. } => {
                attributes.insert("total", json!(""));
            }
            DefinitionProductionAttribute::Hook { operation, .. } => {
                attributes.insert("hook", json!(operation.spec().k_hook));
            }
            DefinitionProductionAttribute::Alias { recursive, .. } => {
                attributes.insert(if *recursive { "alias-rec" } else { "alias" }, json!(""));
            }
            DefinitionProductionAttribute::Desugar { recursive, .. } => {
                attributes.insert(if *recursive { "macro-rec" } else { "macro" }, json!(""));
            }
            DefinitionProductionAttribute::Token {
                lexical_precedence, ..
            } => {
                attributes.insert("token", json!(""));
                if let Some(value) = lexical_precedence {
                    attributes.insert("prec", json!(value.to_string()));
                }
            }
            DefinitionProductionAttribute::Group { group, .. } => {
                attributes.insert("group", json!(self.group_name(group, attribute.origin())?));
            }
            DefinitionProductionAttribute::Bracket { .. } => {
                use std::fmt::Write as _;

                attributes.insert("bracket", json!(""));
                let format =
                    (1..=sentence.items().len()).fold(String::new(), |mut output, index| {
                        write!(output, "%{index}").expect("writing to String cannot fail");
                        output
                    });
                attributes.insert("format", json!(format));
            }
            DefinitionProductionAttribute::Avoid { .. } => {
                attributes.insert("avoid", json!(""));
            }
            DefinitionProductionAttribute::Prefer { .. } => {
                attributes.insert("prefer", json!(""));
            }
            DefinitionProductionAttribute::Private { .. } => {
                attributes.insert("private", json!(""));
            }
            DefinitionProductionAttribute::FreshGenerator { .. } => {
                attributes.insert("freshGenerator", json!(""));
            }
            DefinitionProductionAttribute::Smtlib { symbol, .. } => {
                attributes.insert("smtlib", json!(symbol));
            }
            DefinitionProductionAttribute::SmtHook { template, .. } => {
                attributes.insert(
                    "smt-hook",
                    json!(native_smt_hook(template, sentence, attribute.origin())?),
                );
            }
            DefinitionProductionAttribute::Memo { .. } => {
                attributes.insert("memo", json!(""));
            }
            DefinitionProductionAttribute::ListCons { non_empty, .. } => {
                attributes.insert("userList", json!(user_list_kind(*non_empty)));
            }
            DefinitionProductionAttribute::ListTerminator { cons, .. } => {
                let non_empty = self
                    .index
                    .production(cons)
                    .and_then(|cons| {
                        cons.attributes()
                            .iter()
                            .find_map(|attribute| match attribute {
                                DefinitionProductionAttribute::ListCons { non_empty, .. } => {
                                    Some(*non_empty)
                                }
                                _ => None,
                            })
                    })
                    .ok_or_else(|| AdapterError::MissingSymbol {
                        key: attribute.origin().key().clone(),
                        symbol: cons.clone(),
                    })?;
                attributes.insert("userList", json!(user_list_kind(non_empty)));
            }
            DefinitionProductionAttribute::RawHook {
                namespace, name, ..
            } => {
                attributes.insert("hook", json!(format!("{namespace}.{name}")));
            }
            DefinitionProductionAttribute::Overload { target, .. } => {
                attributes.insert(
                    "overload",
                    json!(self.symbol_name(target, attribute.origin())?),
                );
            }
            DefinitionProductionAttribute::Format { fragments, .. } => {
                attributes.insert("format", json!(native_format(fragments)));
            }
            DefinitionProductionAttribute::Color { value, .. } => {
                attributes.insert("color", json!(value));
            }
            DefinitionProductionAttribute::Colors { values, .. } => {
                attributes.insert("colors", json!(values.join(",")));
            }
            DefinitionProductionAttribute::Internal { .. }
            | DefinitionProductionAttribute::Program { .. } => {
                unreachable!("Definition IR validation rejects placement attributes")
            }
            DefinitionProductionAttribute::Strictness {
                kind,
                using,
                fields,
                result_sort,
                ..
            } => {
                let nonterminals = sentence
                    .items()
                    .iter()
                    .filter_map(|item| match item.kind() {
                        GrammarProductionItemKind::NonTerminal { field, .. } => Some(field),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                let positions = fields
                    .iter()
                    .map(|selected| {
                        nonterminals
                            .iter()
                            .position(|field| **field == *selected.field())
                            .map(|position| position + 1)
                            .ok_or_else(|| AdapterError::MissingReference {
                                key: selected.origin().key().clone(),
                                kind: "production field",
                                target: selected.field().as_str().to_owned(),
                            })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                for (index, selected) in fields.iter().enumerate() {
                    self.map_sentence_origin(
                        selected.origin(),
                        module,
                        sentence_index,
                        SentenceNodeRole::StrictnessField(u32::try_from(index).unwrap_or(u32::MAX)),
                    );
                }
                self.map_sentence_origin(
                    result_sort.origin(),
                    module,
                    sentence_index,
                    SentenceNodeRole::StrictnessResult,
                );
                let selected_all = positions.len() == nonterminals.len()
                    && positions.iter().copied().eq(1..=nonterminals.len());
                let positions = (!selected_all).then(|| {
                    positions
                        .iter()
                        .map(usize::to_string)
                        .collect::<Vec<_>>()
                        .join(",")
                });
                let value = if let Some(using) = using {
                    self.map_sentence_origin(
                        using.origin(),
                        module,
                        sentence_index,
                        SentenceNodeRole::StrictnessContextAlias,
                    );
                    let alias = self.context_alias_name(using.alias(), using.origin())?;
                    match positions {
                        Some(positions) => format!("{alias}; {positions}"),
                        None => alias,
                    }
                } else {
                    positions.unwrap_or_default()
                };
                attributes.insert(
                    match kind {
                        StrictnessKind::Strict => "strict",
                        StrictnessKind::SeqStrict => "seqstrict",
                    },
                    json!(value),
                );
                if using.is_none() {
                    attributes.insert(
                        "result",
                        json!(self.sort(result_sort.sort(), result_sort.origin())?.name),
                    );
                }
                let _ = attribute_index;
            }
        }
        Ok(())
    }

    pub(super) fn configuration(
        &mut self,
        configuration: &ConfigurationSentence,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeSentence, AdapterError> {
        self.variable_names = self.naming.configuration(configuration);
        self.initializer_variables.clear();
        for variable in configuration.variables() {
            self.initializer_variables
                .insert(variable.id().clone(), variable.external_name().to_owned());
            self.map_sentence_origin(
                variable.origin(),
                module,
                sentence_index,
                SentenceNodeRole::ConfigurationInitializer,
            );
        }
        self.map_sentence_origin(
            configuration.initializer_origin(),
            module,
            sentence_index,
            SentenceNodeRole::ConfigurationInitializer,
        );
        let body = self.fixed_configuration(configuration, module, sentence_index)?;
        self.initializer_variables.clear();
        Ok(NativeSentence::Configuration {
            body,
            ensures: truth(),
            attributes: attributes_for_origin(configuration.origin()),
        })
    }

    fn fixed_configuration(
        &mut self,
        configuration: &FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeTerm, AdapterError> {
        let forest = self.fixed_initializer_forest(
            configuration.cells(),
            configuration.initializer(),
            configuration.variables(),
            module,
            sentence_index,
        )?;
        Ok(match configuration.root() {
            ConfigurationRoot::GeneratedTop => native_cells(forest),
            ConfigurationRoot::Named { origin, name } => {
                self.map_sentence_origin(
                    origin,
                    module,
                    sentence_index,
                    SentenceNodeRole::ConfigurationCell,
                );
                native_config_cell(
                    name,
                    NativeTerm::apply("#cellPropertyListTerminator", Vec::new()),
                    native_cells(forest),
                )
            }
        })
    }

    fn fixed_initializer_forest(
        &mut self,
        cells: &[FixedCell<DefinitionSortRef, SymbolId>],
        initializer: &[FixedInitializerCell<SymbolId, DefinitionTerm>],
        variables: &[FixedConfigurationVariable<DefinitionSortRef>],
        module: &str,
        sentence_index: usize,
    ) -> Result<Vec<NativeTerm>, AdapterError> {
        cells
            .iter()
            .map(|cell| {
                let matching_initializer = initializer
                    .iter()
                    .find(|value| value.cell() == cell.id())
                    .ok_or_else(|| AdapterError::MissingReference {
                        key: cell.origin().key().clone(),
                        kind: "configuration initializer cell",
                        target: cell.id().as_str().to_owned(),
                    })?;
                self.fixed_initializer_cell(
                    cell,
                    matching_initializer,
                    variables,
                    module,
                    sentence_index,
                )
            })
            .collect()
    }

    fn fixed_initializer_cell(
        &mut self,
        cell: &FixedCell<DefinitionSortRef, SymbolId>,
        initializer: &FixedInitializerCell<SymbolId, DefinitionTerm>,
        variables: &[FixedConfigurationVariable<DefinitionSortRef>],
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeTerm, AdapterError> {
        self.map_sentence_origin(
            cell.origin(),
            module,
            sentence_index,
            SentenceNodeRole::ConfigurationCell,
        );
        self.map_sentence_origin(
            initializer.origin(),
            module,
            sentence_index,
            SentenceNodeRole::ConfigurationInitializer,
        );
        let contents = match (cell.content(), initializer.content()) {
            (FixedCellContent::Term { .. }, FixedInitializerContent::Term { term }) => self.term(
                term,
                module,
                sentence_index,
                Vec::new(),
                TermContext::ConfigurationInitializer,
            )?,
            (
                FixedCellContent::Children { children },
                FixedInitializerContent::Children {
                    children: initialized_children,
                },
            ) => native_cells(self.fixed_initializer_forest(
                children,
                initialized_children,
                variables,
                module,
                sentence_index,
            )?),
            _ => {
                return Err(AdapterError::MissingReference {
                    key: initializer.origin().key().clone(),
                    kind: "configuration initializer shape",
                    target: cell.id().as_str().to_owned(),
                });
            }
        };
        // The main cell is the leaf that holds `$PGM`, also below a nested
        // cell such as a collection instance (KF-023).
        let is_main = matches!(cell.content(), FixedCellContent::Term { .. })
            && variables.iter().any(|variable| {
                variable.is_main() && initializer_contains_variable(initializer, variable.id())
            });
        let properties = native_cell_properties(cell.attributes(), is_main);
        Ok(native_config_cell(cell.name(), properties, contents))
    }

    pub(super) fn context_alias(
        &mut self,
        sentence: &ContextAliasSentence,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeSentence, AdapterError> {
        self.variable_names = self.naming.context_alias(sentence);
        self.map_sentence_origin(
            sentence.name_origin(),
            module,
            sentence_index,
            SentenceNodeRole::ContextAliasName,
        );
        self.map_sentence_origin(
            sentence.here_origin(),
            module,
            sentence_index,
            SentenceNodeRole::ContextAliasHere,
        );
        self.context_here = Some(sentence.here().clone());
        let body = self.configuration_pattern(
            sentence.body(),
            module,
            sentence_index,
            TermContext::ContextAlias,
        )?;
        self.context_here = None;
        let mut attributes = attributes_for_origin(sentence.origin());
        attributes.insert("label", json!(sentence.name()));
        // `result = S`, K's `result(S)` (KF-021).
        if let Some(result) = sentence.result() {
            attributes.insert(
                "result",
                json!(self.sort(result.sort(), result.origin())?.name),
            );
        }
        // K's source frontend carries this internal marker from a named
        // computation-cell context alias into its generated cool rule.
        attributes.insert("cool-like", json!(""));
        Ok(NativeSentence::ContextAlias {
            body,
            requires: truth(),
            attributes,
        })
    }

    /// Adapts a context (KF-021): its pattern, hole named `HOLE` and at most
    /// one rewrite of it in place, becomes k-rust's `context`, which k-rust
    /// turns into a freezer and `<label>-heat` and `<label>-cool` rules.
    pub(super) fn context(
        &mut self,
        sentence: &RuleSentence,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeSentence, AdapterError> {
        self.variable_names = self.naming.rule(sentence);
        let body = match sentence.relational_body() {
            RuleBodyRef::Term(term) => {
                let local = term.local_term().unwrap_or_else(|| term.from());
                self.term(
                    local,
                    module,
                    sentence_index,
                    Vec::new(),
                    TermContext::Normal,
                )?
            }
            RuleBodyRef::Configuration { body, .. } => {
                self.configuration_rewrite(body, module, sentence_index, sentence)?
            }
            RuleBodyRef::Predicate(_) => {
                unreachable!("validated Definition IR gives a context a term or configuration body")
            }
        };
        let requires = sentence.requires().map_or_else(
            || Ok(truth()),
            |condition| {
                self.condition(
                    condition,
                    module,
                    sentence_index,
                    SentenceNodeRole::Requires,
                )
            },
        )?;
        let mut attributes = attributes_for_origin(sentence.origin());
        attributes.insert("label", json!(native_rule_label(module, sentence.label())));
        if let Some(result) = sentence.evaluation().and_then(|step| step.result()) {
            attributes.insert(
                "result",
                json!(self.sort(result.sort(), result.origin())?.name),
            );
        }
        Ok(NativeSentence::Context {
            body,
            requires,
            attributes,
        })
    }

    #[expect(
        clippy::too_many_lines,
        reason = "Keeps rule adaptation and native origin roles together."
    )]
    pub(super) fn rule(
        &mut self,
        sentence: &RuleSentence,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeSentence, AdapterError> {
        self.variable_names = self.naming.rule(sentence);
        let body = match sentence.relational_body() {
            RuleBodyRef::Term(term) => {
                // A single-body rule (KF-011) keeps its rewrites in place;
                // k-rust lifts them as K does. Its term is the body's root.
                let rewrite = if let Some(local) = term.local_term() {
                    self.term(
                        local,
                        module,
                        sentence_index,
                        Vec::new(),
                        TermContext::Normal,
                    )?
                } else {
                    self.map_sentence_origin(
                        term.origin(),
                        module,
                        sentence_index,
                        SentenceNodeRole::Term(Vec::new()),
                    );
                    self.rewrite(
                        term.from(),
                        term.to(),
                        module,
                        sentence_index,
                        Vec::new(),
                        TermContext::Normal,
                    )?
                };
                match sentence.function_context() {
                    // K's `[[ F => R ]] <cells>`: k-rust adds the hidden
                    // configuration argument and threads it to callers (KF-025).
                    Some(context) => NativeTerm::apply(
                        "#withConfig",
                        vec![
                            rewrite,
                            self.function_context(context, module, sentence_index)?,
                        ],
                    ),
                    None => rewrite,
                }
            }
            RuleBodyRef::Configuration { body: rewrite, .. } => {
                self.configuration_rewrite(rewrite, module, sentence_index, sentence)?
            }
            // A predicate simplification (KF-039): `P => Q` between
            // predicates, whose sort k-rust leaves a sort variable.
            RuleBodyRef::Predicate(rewrite) => {
                self.map_sentence_origin(
                    rewrite.origin(),
                    module,
                    sentence_index,
                    SentenceNodeRole::Term(Vec::new()),
                );
                NativeTerm::Rewrite {
                    left: Box::new(self.predicate(rewrite.lhs(), module, sentence_index, &[0])?),
                    right: Box::new(self.predicate(rewrite.rhs(), module, sentence_index, &[1])?),
                }
            }
        };
        let requires = sentence.requires().map_or_else(
            || Ok(truth()),
            |condition| {
                self.condition(
                    condition,
                    module,
                    sentence_index,
                    SentenceNodeRole::Requires,
                )
            },
        )?;
        let ensures = sentence.ensures().map_or_else(
            || Ok(truth()),
            |condition| {
                self.condition(condition, module, sentence_index, SentenceNodeRole::Ensures)
            },
        )?;
        let mut attributes = attributes_for_origin(sentence.origin());
        attributes.insert("label", json!(native_rule_label(module, sentence.label())));
        if sentence.anywhere().is_some() {
            attributes.insert("anywhere", json!(""));
        }
        // A heat or cool rule (KF-014): its hole is named `HOLE`, and
        // k-rust's heat/cool pass adds the result-sort condition on it.
        if let Some(step) = sentence.evaluation() {
            attributes.insert(step.kind().as_str(), json!(""));
            if let Some(result) = step.result() {
                attributes.insert(
                    "result",
                    json!(self.sort(result.sort(), result.origin())?.name),
                );
            }
        }
        if let Some(priority) = sentence.priority() {
            attributes.insert("priority", json!(priority.value().to_string()));
        }
        if let Some(simplification) = sentence.simplification() {
            attributes.insert(
                "simplification",
                json!(
                    simplification
                        .priority()
                        .map_or_else(String::new, |value| value.value().to_string())
                ),
            );
        }
        if let Some(restriction) = sentence.restriction() {
            self.insert_match_restriction(restriction, &mut attributes)?;
        }
        if let Some(unbound) = sentence.unbound_variables() {
            self.insert_unbound_variables(sentence, unbound, &mut attributes)?;
        }
        if let Some(claim) = sentence.claim() {
            self.map_sentence_origin(
                claim.modality_origin(),
                module,
                sentence_index,
                SentenceNodeRole::ClaimModality,
            );
            attributes.insert(claim_modality_attribute(claim.modality()), json!(""));
            if let Some(origin) = claim.circularity_origin() {
                self.map_sentence_origin(
                    origin,
                    module,
                    sentence_index,
                    SentenceNodeRole::ClaimCircularity,
                );
                attributes.insert("circularity", json!(""));
            }
            if let Some(origin) = claim.trusted_origin() {
                self.map_sentence_origin(
                    origin,
                    module,
                    sentence_index,
                    SentenceNodeRole::ClaimTrusted,
                );
                attributes.insert("trusted", json!(""));
            }
        }
        let universals = sentence
            .claim()
            .map_or(&[][..], krs_ir_levels::DefinitionClaim::universals);
        for (index, binder) in universals
            .iter()
            .chain(sentence.existentials())
            .chain(sentence.fresh())
            .enumerate()
        {
            self.map_claim_binder(binder, module, sentence_index, index);
        }
        if sentence.kind() == SentenceKind::Claim {
            Ok(NativeSentence::Claim {
                body,
                requires,
                ensures,
                attributes,
            })
        } else {
            Ok(NativeSentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            })
        }
    }

    /// Adapts one `requires` or `ensures` condition: an object Bool term,
    /// or a matching-logic predicate (KF-039).
    fn condition(
        &mut self,
        condition: &krs_ir_levels::DefinitionCondition,
        module: &str,
        sentence_index: usize,
        role: SentenceNodeRole,
    ) -> Result<NativeTerm, AdapterError> {
        match condition {
            krs_ir_levels::IrCondition::Bool(condition) => {
                self.map_sentence_origin(condition.origin(), module, sentence_index, role);
                self.term(
                    condition.term(),
                    module,
                    sentence_index,
                    Vec::new(),
                    TermContext::Normal,
                )
            }
            krs_ir_levels::IrCondition::Predicate(predicate) => {
                self.predicate(predicate, module, sentence_index, &[])
            }
        }
    }

    /// Inserts `concrete`, `symbolic` (`""` when bare, otherwise the listed
    /// binders' native names joined by `,`), and `smt-lemma` (KF-043).
    fn insert_match_restriction(
        &self,
        restriction: &krs_ir_levels::IrMatchRestriction,
        attributes: &mut NativeAttributes,
    ) -> Result<(), AdapterError> {
        for (key, attribute) in [
            (restriction.concrete(), "concrete"),
            (restriction.symbolic(), "symbolic"),
        ] {
            let Some(key) = key else {
                continue;
            };
            let names = key
                .variables()
                .iter()
                .map(|variable| {
                    self.variable_names.name(variable.id()).ok_or_else(|| {
                        AdapterError::MissingReference {
                            key: variable.origin().key().clone(),
                            kind: "sentence variable",
                            target: variable.id().as_str().to_owned(),
                        }
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            attributes.insert(attribute, json!(names.join(",")));
        }
        if restriction.smt_lemma().is_some() {
            attributes.insert("smt-lemma", json!(""));
        }
        Ok(())
    }

    /// Inserts `unboundVariables` (KF-046): the listed variables' native names
    /// joined by `,`. Natively a wildcard is a generated named variable, not
    /// K's anonymous `_`, so the `_` entry lists every wildcard of the
    /// right-hand side by name.
    fn insert_unbound_variables(
        &self,
        sentence: &RuleSentence,
        unbound: &krs_ir_levels::IrUnboundVariables,
        attributes: &mut NativeAttributes,
    ) -> Result<(), AdapterError> {
        let mut names = Vec::new();
        for variable in unbound.variables() {
            match variable.id() {
                Some(id) => names.push(self.native_variable_name(id, variable.origin())?),
                None => {
                    for id in &sentence.result_wildcards() {
                        names.push(self.native_variable_name(id, variable.origin())?);
                    }
                }
            }
        }
        attributes.insert("unboundVariables", json!(names.join(",")));
        Ok(())
    }

    fn native_variable_name(
        &self,
        id: &SemanticId,
        origin: &NodeOrigin,
    ) -> Result<String, AdapterError> {
        self.variable_names
            .name(id)
            .map(ToOwned::to_owned)
            .ok_or_else(|| AdapterError::MissingReference {
                key: origin.key().clone(),
                kind: "sentence variable",
                target: id.as_str().to_owned(),
            })
    }

    fn map_claim_binder(
        &mut self,
        binder: &DefinitionScopedBinder,
        module: &str,
        sentence_index: usize,
        index: usize,
    ) {
        let index = u32::try_from(index).unwrap_or(u32::MAX);
        for (origin, role) in [
            (binder.origin(), SentenceNodeRole::ClaimBinder(index)),
            (
                binder.name_origin(),
                SentenceNodeRole::ClaimBinderName(index),
            ),
            (
                binder.sort_origin(),
                SentenceNodeRole::ClaimBinderSort(index),
            ),
        ] {
            self.map_sentence_origin(origin, module, sentence_index, role);
        }
    }

    fn configuration_rewrite(
        &mut self,
        rewrite: &FixedConfigurationRewrite<SymbolId, DefinitionTerm>,
        module: &str,
        sentence_index: usize,
        sentence: &RuleSentence,
    ) -> Result<NativeTerm, AdapterError> {
        let mut cells = Vec::new();
        for (index, clause) in rewrite.clauses().iter().enumerate() {
            let index = u32::try_from(index).unwrap_or(u32::MAX);
            match clause {
                ConfigurationClause::Fixed(clause) => {
                    cells.push(self.fixed_clause(
                        clause,
                        module,
                        sentence_index,
                        index,
                        vec![index],
                    )?);
                }
                ConfigurationClause::Optional(clause) => {
                    cells.push(self.optional_clause(clause, module, sentence_index, index)?);
                }
                ConfigurationClause::Instances(clause) => {
                    cells.extend(self.instances_clause(clause, module, sentence_index, index)?);
                }
            }
        }
        if sentence.claim().is_some() {
            cells.push(native_claim_counter(sentence_index));
        }
        Ok(native_cells(cells))
    }

    /// One exactly-once clause (also a kept instance's child): the cell with
    /// its content, rewritten in place when replaced. `path` places its
    /// pattern; its replacement is at `path ++ [1]`.
    fn fixed_clause(
        &mut self,
        clause: &krs_ir::FixedCellClause<SymbolId, DefinitionTerm>,
        module: &str,
        sentence_index: usize,
        index: u32,
        path: Vec<u32>,
    ) -> Result<NativeTerm, AdapterError> {
        self.map_sentence_origin(
            clause.origin(),
            module,
            sentence_index,
            if path.len() == 1 {
                SentenceNodeRole::ConfigurationRuleCell(index)
            } else {
                SentenceNodeRole::Term([path.clone(), vec![u32::MAX]].concat())
            },
        );
        self.map_frame_origin(clause.frame(), module, sentence_index, index, &path);
        let before = self.term(
            clause.before(),
            module,
            sentence_index,
            path.clone(),
            TermContext::Normal,
        )?;
        let before = if matches!(clause.frame(), CellContentFrame::ListRemainder { .. }) {
            stdin_read_item(before)
        } else {
            before
        };
        let content = match clause.after() {
            // A single-body clause (KF-011) carries its rewrites
            // inside `before`; k-rust lifts them as K does.
            CellPost::Preserve | CellPost::Local => before,
            CellPost::Replace { term } => NativeTerm::Rewrite {
                left: Box::new(before),
                right: Box::new(self.term(
                    term,
                    module,
                    sentence_index,
                    [path, vec![1]].concat(),
                    TermContext::Normal,
                )?),
            },
        };
        if clause.kind() == krs_ir::CellClauseKind::Whole {
            // A whole group cell sits in `#cells` as a term of its
            // generated `<Name>Cell` sort, without brackets (KF-016).
            return Ok(content);
        }
        self.framed_cell(clause.cell(), content, clause.frame(), clause.origin())
    }

    fn map_frame_origin(
        &mut self,
        frame: &CellContentFrame,
        module: &str,
        sentence_index: usize,
        index: u32,
        path: &[u32],
    ) {
        if let CellContentFrame::KSequenceTail { origin, .. }
        | CellContentFrame::MapRemainder { origin, .. }
        | CellContentFrame::ListRemainder { origin } = frame
        {
            self.map_sentence_origin(
                origin,
                module,
                sentence_index,
                if path.len() == 1 {
                    SentenceNodeRole::ConfigurationRuleFrame(index)
                } else {
                    SentenceNodeRole::Term([path, &[u32::MAX - 1]].concat())
                },
            );
        }
    }

    /// One side of a cell: the framed cell with `content`, or a whole group.
    fn cell_image(
        &mut self,
        cell: &SymbolId,
        kind: krs_ir::CellClauseKind,
        content: NativeTerm,
        frame: &CellContentFrame,
        origin: &NodeOrigin,
    ) -> Result<NativeTerm, AdapterError> {
        if kind == krs_ir::CellClauseKind::Whole {
            return Ok(content);
        }
        self.framed_cell(cell, content, frame, origin)
    }

    /// An optional (`?`) cell (KF-023): read or updated in place, created as
    /// `Rewrite(#cells(), cell)`, deleted as `Rewrite(cell, #cells())`.
    fn optional_clause(
        &mut self,
        clause: &krs_ir::OptionalCellClause<SymbolId, DefinitionTerm>,
        module: &str,
        sentence_index: usize,
        index: u32,
    ) -> Result<NativeTerm, AdapterError> {
        self.map_sentence_origin(
            clause.origin(),
            module,
            sentence_index,
            SentenceNodeRole::ConfigurationRuleCell(index),
        );
        self.map_frame_origin(clause.frame(), module, sentence_index, index, &[index]);
        let term = |adapter: &mut Self, term: &DefinitionTerm, path: Vec<u32>| {
            adapter.term(term, module, sentence_index, path, TermContext::Normal)
        };
        Ok(match (clause.before(), clause.after()) {
            (krs_ir::Presence::Present { term: before }, after) => {
                let before = term(self, before, vec![index])?;
                match after {
                    None => self.cell_image(
                        clause.cell(),
                        clause.kind(),
                        before,
                        clause.frame(),
                        clause.origin(),
                    )?,
                    Some(krs_ir::Presence::Present { term: after }) => {
                        let after = term(self, after, vec![index, 1])?;
                        self.cell_image(
                            clause.cell(),
                            clause.kind(),
                            NativeTerm::Rewrite {
                                left: Box::new(before),
                                right: Box::new(after),
                            },
                            clause.frame(),
                            clause.origin(),
                        )?
                    }
                    Some(krs_ir::Presence::Absent) => NativeTerm::Rewrite {
                        left: Box::new(self.cell_image(
                            clause.cell(),
                            clause.kind(),
                            before,
                            clause.frame(),
                            clause.origin(),
                        )?),
                        right: Box::new(native_cells(Vec::new())),
                    },
                }
            }
            (krs_ir::Presence::Absent, Some(krs_ir::Presence::Present { term: after })) => {
                let after = term(self, after, vec![index, 1])?;
                NativeTerm::Rewrite {
                    left: Box::new(native_cells(Vec::new())),
                    right: Box::new(self.cell_image(
                        clause.cell(),
                        clause.kind(),
                        after,
                        &CellContentFrame::Exact,
                        clause.origin(),
                    )?),
                }
            }
            (krs_ir::Presence::Absent, _) => {
                return Err(AdapterError::MissingReference {
                    key: clause.origin().key().clone(),
                    kind: "created optional cell",
                    target: clause.cell().as_str().to_owned(),
                });
            }
        })
    }

    /// A collection (`*`) clause (KF-023): each matched instance in place,
    /// a removed one as `Rewrite(cell, #cells())`, a new one as
    /// `Rewrite(#cells(), cell)` with `open_right` so k-rust fills the
    /// template defaults. An open Set or Map clause leaves the parent cell
    /// to k-rust; an exact or List clause is written inside its parent. A
    /// List clause's back instances rewrite the tail after the other
    /// instances, named by a variable of the collection sort, since k-rust
    /// (like Java K) closes a parent cell on the right.
    fn instances_clause(
        &mut self,
        clause: &krs_ir::InstancesClause<SymbolId, DefinitionTerm>,
        module: &str,
        sentence_index: usize,
        index: u32,
    ) -> Result<Vec<NativeTerm>, AdapterError> {
        self.map_sentence_origin(
            clause.origin(),
            module,
            sentence_index,
            SentenceNodeRole::ConfigurationRuleCell(index),
        );
        let mut front = Vec::new();
        for (position, instance) in clause.front().iter().enumerate() {
            let position = u32::try_from(position).unwrap_or(u32::MAX);
            front.push(self.instance(
                instance,
                clause.cell(),
                module,
                sentence_index,
                index,
                position,
            )?);
        }
        let list = clause.ordering() == krs_ir::InstanceOrdering::List;
        if !list && clause.is_open() {
            return Ok(front);
        }
        let mut items = front;
        if !clause.back().is_empty() {
            let name = self.cell_name(clause.cell(), clause.origin())?.to_owned();
            let collection = format!("{}List", cell_sort_name(&name));
            let rest = NativeTerm::Variable {
                name: generated_variable_name(&format!("instances{sentence_index}x{index}")),
                sort: Some(NativeSort::new(collection.clone())),
            };
            let concat = format!("_{collection}_");
            let offset = u32::try_from(clause.front().len()).unwrap_or(u32::MAX);
            let (mut left, mut right) = (rest.clone(), rest);
            for (position, instance) in clause.back().iter().enumerate() {
                let position = offset.saturating_add(u32::try_from(position).unwrap_or(u32::MAX));
                let image = self.instance(
                    instance,
                    clause.cell(),
                    module,
                    sentence_index,
                    index,
                    position,
                )?;
                let NativeTerm::Rewrite {
                    left: removed,
                    right: created,
                } = image
                else {
                    return Err(AdapterError::MissingReference {
                        key: instance.origin().key().clone(),
                        kind: "back instance of a List collection (created or removed)",
                        target: clause.cell().as_str().to_owned(),
                    });
                };
                if !is_empty_cells(&removed) {
                    left = NativeTerm::apply(concat.clone(), vec![left, *removed]);
                }
                if !is_empty_cells(&created) {
                    right = NativeTerm::apply(concat.clone(), vec![right, *created]);
                }
            }
            items.push(NativeTerm::Rewrite {
                left: Box::new(left),
                right: Box::new(right),
            });
        }
        let parent = self
            .index
            .cell_parent(clause.cell())
            .cloned()
            .ok_or_else(|| AdapterError::MissingReference {
                key: clause.origin().key().clone(),
                kind: "collection parent cell",
                target: clause.cell().as_str().to_owned(),
            })?;
        let parent_name = self.cell_name(&parent, clause.origin())?.to_owned();
        let open_right = clause.is_open() && clause.back().is_empty();
        Ok(vec![incomplete_cell(
            &parent_name,
            native_cells(items),
            open_right,
        )])
    }

    /// One instance of a collection clause.
    fn instance(
        &mut self,
        instance: &krs_ir::InstanceClause<SymbolId, DefinitionTerm>,
        cell: &SymbolId,
        module: &str,
        sentence_index: usize,
        index: u32,
        position: u32,
    ) -> Result<NativeTerm, AdapterError> {
        self.map_sentence_origin(
            instance.origin(),
            module,
            sentence_index,
            SentenceNodeRole::Term(vec![index, 2, position]),
        );
        let name = self.cell_name(cell, instance.origin())?.to_owned();
        match instance {
            krs_ir::InstanceClause::Kept { children, open, .. } => {
                let mut cells = Vec::new();
                for (child_position, child) in children.iter().enumerate() {
                    let child_position = u32::try_from(child_position).unwrap_or(u32::MAX);
                    cells.push(self.fixed_clause(
                        child,
                        module,
                        sentence_index,
                        index,
                        vec![index, 3, position, child_position],
                    )?);
                }
                Ok(incomplete_cell(&name, native_cells(cells), *open))
            }
            krs_ir::InstanceClause::Removed { children, open, .. }
            | krs_ir::InstanceClause::Created {
                children,
                defaults: open,
                ..
            } => {
                let created = matches!(instance, krs_ir::InstanceClause::Created { .. });
                let mut cells = Vec::new();
                for (child_position, child) in children.iter().enumerate() {
                    let child_position = u32::try_from(child_position).unwrap_or(u32::MAX);
                    let path = vec![index, 3, position, child_position];
                    self.map_sentence_origin(
                        child.origin(),
                        module,
                        sentence_index,
                        SentenceNodeRole::Term([path.clone(), vec![u32::MAX]].concat()),
                    );
                    self.map_frame_origin(child.frame(), module, sentence_index, index, &path);
                    let content = self.term(
                        child.term(),
                        module,
                        sentence_index,
                        path,
                        TermContext::Normal,
                    )?;
                    cells.push(self.cell_image(
                        child.cell(),
                        child.kind(),
                        content,
                        child.frame(),
                        child.origin(),
                    )?);
                }
                let image = incomplete_cell(&name, native_cells(cells), *open);
                Ok(if created {
                    NativeTerm::Rewrite {
                        left: Box::new(native_cells(Vec::new())),
                        right: Box::new(image),
                    }
                } else {
                    NativeTerm::Rewrite {
                        left: Box::new(image),
                        right: Box::new(native_cells(Vec::new())),
                    }
                })
            }
        }
    }

    fn configuration_pattern(
        &mut self,
        pattern: &FixedConfigurationPattern<SymbolId, DefinitionTerm>,
        module: &str,
        sentence_index: usize,
        context: TermContext,
    ) -> Result<NativeTerm, AdapterError> {
        let cells = pattern
            .cells()
            .iter()
            .enumerate()
            .map(|(index, cell)| {
                let index = u32::try_from(index).unwrap_or(u32::MAX);
                self.map_sentence_origin(
                    cell.origin(),
                    module,
                    sentence_index,
                    SentenceNodeRole::ContextAliasCell(index),
                );
                if let CellContentFrame::KSequenceTail { origin, .. }
                | CellContentFrame::MapRemainder { origin, .. }
                | CellContentFrame::ListRemainder { origin } = cell.frame()
                {
                    self.map_sentence_origin(
                        origin,
                        module,
                        sentence_index,
                        SentenceNodeRole::ContextAliasFrame(index),
                    );
                }
                let cell_content =
                    self.term(cell.pattern(), module, sentence_index, vec![index], context)?;
                self.framed_cell(cell.cell(), cell_content, cell.frame(), cell.origin())
            })
            .collect::<Result<Vec<_>, AdapterError>>()?;
        Ok(native_cells(cells))
    }

    /// The `#cells` an equation's function context reads (KF-025); its term
    /// paths start at `2`, after the rewrite's endpoints.
    fn function_context(
        &mut self,
        context: &krs_ir_levels::DefinitionFunctionContext,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeTerm, AdapterError> {
        self.map_sentence_origin(
            context.origin(),
            module,
            sentence_index,
            SentenceNodeRole::FunctionContext,
        );
        let cells = context
            .cells()
            .cells()
            .iter()
            .enumerate()
            .map(|(index, cell)| {
                let index = u32::try_from(index).unwrap_or(u32::MAX);
                self.map_sentence_origin(
                    cell.origin(),
                    module,
                    sentence_index,
                    SentenceNodeRole::FunctionContextCell(index),
                );
                if let CellContentFrame::KSequenceTail { origin, .. }
                | CellContentFrame::MapRemainder { origin, .. }
                | CellContentFrame::ListRemainder { origin } = cell.frame()
                {
                    self.map_sentence_origin(
                        origin,
                        module,
                        sentence_index,
                        SentenceNodeRole::FunctionContextFrame(index),
                    );
                }
                let pattern = self.term(
                    cell.pattern(),
                    module,
                    sentence_index,
                    vec![2, index],
                    TermContext::Normal,
                )?;
                self.framed_cell(cell.cell(), pattern, cell.frame(), cell.origin())
            })
            .collect::<Result<Vec<_>, AdapterError>>()?;
        Ok(native_cells(cells))
    }

    fn framed_cell(
        &self,
        cell: &SymbolId,
        content: NativeTerm,
        frame: &CellContentFrame,
        origin: &NodeOrigin,
    ) -> Result<NativeTerm, AdapterError> {
        let name = self.cell_name(cell, origin)?;
        let (content, open_right) = match frame {
            CellContentFrame::Exact => (content, false),
            CellContentFrame::ListRemainder { .. } => (content, true),
            CellContentFrame::KSequenceTail { binding, .. } => match binding {
                None => (content, true),
                Some(binding) => (
                    NativeTerm::sequence([
                        content,
                        self.native_variable(
                            binding,
                            NativeSort::new(BuiltinSort::KSequence.k_name()),
                            origin,
                        )?,
                    ]),
                    false,
                ),
            },
            CellContentFrame::MapRemainder { binding, .. } => match binding {
                None => (content, true),
                Some(binding) => (
                    NativeTerm::apply(
                        MapOperation::CONCATENATION.k_label,
                        vec![
                            content,
                            self.native_variable(
                                binding,
                                NativeSort::new(BuiltinSort::Map.k_name()),
                                origin,
                            )?,
                        ],
                    ),
                    false,
                ),
            },
        };
        Ok(incomplete_cell(name, content, open_right))
    }
}

/// Spell the item a stdin stream read consumes, `ListItem(V:Sort)`, as K's parser does: a
/// semantic cast of the variable. k-rust generates the stream's unblocking rules only for a
/// read in that spelling (`kompile/passes/resolve_io.rs`), as Java K's `ResolveIOStreams` does.
fn stdin_read_item(term: NativeTerm) -> NativeTerm {
    match term {
        NativeTerm::Annotated { term, metadata } => NativeTerm::Annotated {
            term: Box::new(stdin_read_item(*term)),
            metadata,
        },
        NativeTerm::Apply { label, arguments } if label.name == "ListItem" => {
            let arguments = arguments
                .into_iter()
                .map(|argument| match argument.unannotated() {
                    NativeTerm::Variable {
                        name,
                        sort: Some(sort),
                    } => NativeTerm::apply(
                        format!("#SemanticCastTo{}", sort.name),
                        vec![NativeTerm::Variable {
                            name: name.clone(),
                            sort: None,
                        }],
                    ),
                    _ => argument,
                })
                .collect();
            NativeTerm::Apply { label, arguments }
        }
        other => other,
    }
}

/// K's `smt-hook` text of a template: each field becomes `#N`, its one-based
/// position among the production's nonterminals, as in the emitted `.k`.
fn native_smt_hook(
    template: &[krs_ir::SmtFragment],
    sentence: &ProductionSentence,
    origin: &NodeOrigin,
) -> Result<String, AdapterError> {
    let nonterminals = sentence
        .items()
        .iter()
        .filter_map(|item| match item.kind() {
            GrammarProductionItemKind::NonTerminal { field, .. } => Some(field),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut text = String::new();
    for fragment in template {
        match fragment {
            krs_ir::SmtFragment::Text(literal) => text.push_str(literal),
            krs_ir::SmtFragment::Field(field) => {
                let position = nonterminals
                    .iter()
                    .position(|candidate| *candidate == field)
                    .ok_or_else(|| AdapterError::MissingReference {
                        key: origin.key().clone(),
                        kind: "production field",
                        target: field.as_str().to_owned(),
                    })?;
                text.push('#');
                text.push_str(&(position + 1).to_string());
            }
        }
    }
    Ok(text)
}

fn native_format(fragments: &[FormatFragment]) -> String {
    use std::fmt::Write as _;

    let mut output = String::new();
    for fragment in fragments {
        match fragment {
            FormatFragment::Literal(text) => output.push_str(&text.replace('%', "%%")),
            FormatFragment::Item(index) => {
                write!(output, "%{index}").expect("writing to String cannot fail");
            }
            FormatFragment::Newline => output.push_str("%n"),
            FormatFragment::Indent => output.push_str("%i"),
            FormatFragment::Dedent => output.push_str("%d"),
            FormatFragment::ColorNext => output.push_str("%c"),
            FormatFragment::ColorReset => output.push_str("%r"),
        }
    }
    output
}

fn native_config_cell(name: &str, properties: NativeTerm, contents: NativeTerm) -> NativeTerm {
    let name_token = || NativeTerm::Token {
        token: name.to_owned(),
        sort: NativeSort::new("#CellName"),
    };
    NativeTerm::apply(
        "#configCell",
        vec![name_token(), properties, contents, name_token()],
    )
}

fn is_empty_cells(term: &NativeTerm) -> bool {
    matches!(term, NativeTerm::Apply { label, arguments } if label.name == "#cells" && arguments.is_empty())
}

fn native_cells(mut cells: Vec<NativeTerm>) -> NativeTerm {
    match cells.len() {
        0 => NativeTerm::apply("#cells", Vec::new()),
        1 => cells.pop().expect("length is one"),
        _ => NativeTerm::apply("#cells", cells),
    }
}

pub(super) fn native_claim_counter(sentence_index: usize) -> NativeTerm {
    let sort = Some(NativeSort::new(BuiltinSort::Int.k_name()));
    // The generated namespace keeps the counter apart from every binder of the claim.
    let name = generated_variable_name(&format!("counter{sentence_index}"));
    incomplete_cell(
        "generatedCounter",
        NativeTerm::Rewrite {
            left: Box::new(NativeTerm::Variable {
                name: format!("_{name}"),
                sort: sort.clone(),
            }),
            right: Box::new(NativeTerm::Variable {
                name: format!("?{name}"),
                sort,
            }),
        },
        false,
    )
}

fn native_cell_properties(attributes: &[CellAttribute], main: bool) -> NativeTerm {
    let mut properties = attributes
        .iter()
        .map(|attribute| match attribute {
            CellAttribute::Color { value, .. } => ("color", value.as_str()),
            CellAttribute::Multiplicity { value, .. } => ("multiplicity", value.as_str()),
            CellAttribute::CollectionType { value, .. } => ("type", value.as_str()),
            CellAttribute::Stream { value, .. } => ("stream", value.as_str()),
            CellAttribute::Exit { .. } => ("exit", ""),
            CellAttribute::Initial { .. } => ("initial", ""),
        })
        .collect::<Vec<_>>();
    if main {
        properties.push(("maincell", ""));
    }
    properties.into_iter().rev().fold(
        NativeTerm::apply("#cellPropertyListTerminator", Vec::new()),
        |tail, (key, value)| {
            NativeTerm::apply(
                "#cellPropertyList",
                vec![
                    NativeTerm::apply(
                        "#cellProperty",
                        vec![
                            NativeTerm::Token {
                                token: key.to_owned(),
                                sort: NativeSort::new("#CellName"),
                            },
                            NativeTerm::Token {
                                token: serde_json::to_string(value)
                                    .expect("serializing a string cannot fail"),
                                sort: NativeSort::new("KString"),
                            },
                        ],
                    ),
                    tail,
                ],
            )
        },
    )
}

fn initializer_contains_variable(
    initializer: &FixedInitializerCell<SymbolId, DefinitionTerm>,
    variable: &SemanticId,
) -> bool {
    match initializer.content() {
        FixedInitializerContent::Term { term } => term_contains_variable(term, variable),
        FixedInitializerContent::Children { children } => children
            .iter()
            .any(|child| initializer_contains_variable(child, variable)),
    }
}

fn term_contains_variable(term: &DefinitionTerm, variable: &SemanticId) -> bool {
    match term.kind() {
        DefinitionTermKind::Variable {
            variable: candidate,
        } => candidate == variable,
        DefinitionTermKind::Application { arguments, .. }
        | DefinitionTermKind::KSequence {
            items: arguments, ..
        } => arguments
            .iter()
            .any(|argument| term_contains_variable(argument, variable)),
        DefinitionTermKind::Map(operands) => operands
            .operands()
            .any(|operand| term_contains_variable(operand, variable)),
        DefinitionTermKind::List(operands) => operands
            .operands()
            .any(|operand| term_contains_variable(operand, variable)),
        DefinitionTermKind::Set(operands) => operands
            .operands()
            .any(|operand| term_contains_variable(operand, variable)),
        DefinitionTermKind::Cell { children, .. } => children
            .iter()
            .any(|child| term_contains_variable(child, variable)),
        DefinitionTermKind::Rewrite { from, to } => {
            term_contains_variable(from, variable) || term_contains_variable(to, variable)
        }
        DefinitionTermKind::As { alias, pattern } => {
            alias == variable || term_contains_variable(pattern, variable)
        }
        DefinitionTermKind::Or { alternatives } => alternatives
            .iter()
            .any(|alternative| term_contains_variable(alternative, variable)),
        DefinitionTermKind::Matches {
            subject, pattern, ..
        } => term_contains_variable(subject, variable) || term_contains_variable(pattern, variable),
        DefinitionTermKind::Let {
            pattern,
            value,
            body,
            ..
        } => {
            term_contains_variable(pattern, variable)
                || term_contains_variable(value, variable)
                || term_contains_variable(body, variable)
        }
        DefinitionTermKind::Token { .. } => false,
    }
}

fn incomplete_cell(name: &str, content: NativeTerm, open_right: bool) -> NativeTerm {
    NativeTerm::apply(
        format!("<{name}>"),
        vec![
            NativeTerm::apply("#noDots", Vec::new()),
            content,
            NativeTerm::apply(if open_right { "#dots" } else { "#noDots" }, Vec::new()),
        ],
    )
}

pub(super) fn native_rule_label(module: &str, label: &krs_ir_levels::LabelIdentity) -> String {
    let emitted_name = label.emitted_name();
    // Shared lowering emits this reserved fallback directly as a label
    // attribute. K therefore leaves it unqualified. Authored/named rules and
    // claims pass through K's named-sentence path and acquire the module.
    if label.is_fallback() {
        emitted_name.to_owned()
    } else {
        format!("{module}.{emitted_name}")
    }
}

pub(super) const fn claim_modality_attribute(modality: ClaimModality) -> &'static str {
    match modality {
        ClaimModality::OnePath => "one-path",
        ClaimModality::AllPaths => "all-path",
    }
}

fn truth() -> NativeTerm {
    NativeTerm::Token {
        token: "true".into(),
        sort: NativeSort::new(BuiltinSort::Bool.k_name()),
    }
}

/// k-rust's `userList` value: `+` for `NeList`, `*` for `List`.
const fn user_list_kind(non_empty: bool) -> &'static str {
    if non_empty { "+" } else { "*" }
}

fn list_separator(sentence: &ProductionSentence) -> &str {
    sentence
        .attributes()
        .iter()
        .find_map(|attribute| match attribute {
            DefinitionProductionAttribute::ListCons { separator, .. } => Some(separator.as_str()),
            _ => None,
        })
        .unwrap_or_default()
}

/// Lowers a `raw_k!` sentence (register X9.5): k-rust's public outer parser
/// reads `module <NS> <text> endmodule`, which must hold exactly one bubble of
/// the declared kind, and its own lowering yields the bubble with its label and
/// attributes. The structured loader then parses the bubble with the grammar
/// of the adapted `<NS>` module, so any outer or inner parse error fails the
/// build; nothing is skipped.
fn raw_sentence(raw: &krs_ir::RawSentence, module: &str) -> Result<NativeSentence, AdapterError> {
    let rejected = |message: String| AdapterError::RawK {
        key: raw.origin.key().clone(),
        message,
    };
    let source = format!("module {module}\n{}\nendmodule\n", raw.text);
    let file = k_rust::outer::parse(raw_source_name(raw), &source)
        .map_err(|error| rejected(error.to_string()))?;
    let expected = match raw.kind {
        krs_ir::RawSentenceKind::Rule => k_rust::outer::BubbleKind::Rule,
        krs_ir::RawSentenceKind::Claim => k_rust::outer::BubbleKind::Claim,
        krs_ir::RawSentenceKind::Context => k_rust::outer::BubbleKind::Context,
    };
    let [parsed] = file.modules.as_slice() else {
        return Err(rejected(
            "the text must not open or close a module".to_owned(),
        ));
    };
    match parsed.sentences.as_slice() {
        [k_rust::outer::Sentence::Bubble(bubble)] if bubble.kind == expected => {}
        _ => {
            return Err(rejected(format!(
                "the text must be exactly one `{}` sentence",
                raw.kind.keyword()
            )));
        }
    }
    let lowered = k_rust::outer::lower(&file, module).map_err(|diagnostics| {
        rejected(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.message.clone())
                .collect::<Vec<_>>()
                .join("; "),
        )
    })?;
    let sentence = lowered
        .modules
        .first()
        .and_then(|module| module.local_sentences.first())
        .ok_or_else(|| rejected("k-rust lowered no sentence".to_owned()))?;
    Ok(sentence.as_ref().clone())
}

/// The native source name of a raw sentence, `src/lib.rs (raw_k! 12:1)`: its
/// file and invocation position, under which k-rust reports a parse error in
/// it. Positions inside the text count from line 2 of a wrapper module.
pub(crate) fn raw_source_name(raw: &krs_ir::RawSentence) -> String {
    let file = raw.origin.origin().exact_authored_range().map_or_else(
        || "<unknown>".to_owned(),
        |range| range.file.package_relative_path().to_owned(),
    );
    format!("{file} (raw_k! {}:{})", raw.line, raw.column)
}
