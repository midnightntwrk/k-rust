use k_rust::{
    definition::{
        self as native_definition, Attributes as NativeAttributes, ProductionItem as NativeItem,
        Sentence as NativeSentence,
    },
    kast::{Label as NativeLabel, Sort as NativeSort, Term as NativeTerm},
};
use krs_ir::{
    BuiltinSort, CellAttribute, CellContentFrame, CellPost, ClaimModality, ConfigurationRoot,
    FixedCell, FixedCellContent, FixedConfiguration, FixedConfigurationPattern,
    FixedConfigurationRewrite, FixedConfigurationVariable, FixedInitializerCell,
    FixedInitializerContent, FormatFragment, GrammarProductionItemKind, GroupAssociativity,
    MapOperation, NodeOrigin, SemanticId, SentenceKind, StrictnessKind,
};
use krs_ir_levels::{
    ConfigurationSentence, ContextAliasSentence, DefinitionClaimBinder,
    DefinitionProductionAttribute, DefinitionSentence, DefinitionSortRef, DefinitionTerm,
    DefinitionTermKind, ProductionSentence, RuleBodyRef, RuleSentence, SymbolId,
};
use serde_json::json;

use super::{
    Adapter, AdapterError, SentenceNodeRole, attributes_for_origin,
    term::{TermContext, native_variable},
};

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
                    sentence
                        .higher()
                        .iter()
                        .map(|group| self.group_name(group, sentence.origin()))
                        .collect::<Result<Vec<_>, _>>()?,
                    sentence
                        .lower()
                        .iter()
                        .map(|group| self.group_name(group, sentence.origin()))
                        .collect::<Result<Vec<_>, _>>()?,
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
                    tags: sentence
                        .groups()
                        .iter()
                        .map(|group| self.group_name(group, sentence.origin()))
                        .collect::<Result<Vec<_>, _>>()?,
                    attributes: attributes_for_origin(sentence.origin()),
                })
            }
            DefinitionSentence::Configuration(sentence) => {
                self.configuration(sentence, module, sentence_index)
            }
            DefinitionSentence::ContextAlias(sentence) => {
                self.context_alias(sentence, module, sentence_index)
            }
            DefinitionSentence::Rule(sentence) => self.rule(sentence, module, sentence_index),
        }
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
        let items = sentence
            .items()
            .iter()
            .enumerate()
            .map(|(index, item)| {
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
                    GrammarProductionItemKind::NonTerminal { field, sort } => {
                        Ok(NativeItem::NonTerminal {
                            sort: self.sort(sort, item.origin())?,
                            name: Some(field.as_str().to_owned()),
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
        // token-production-constructor: token values lower to KORE domain
        // values, never applications of their parser production. Omit the
        // unused label to match the source frontend's unlabelled-token form.
        let label = attributes
            .get("token")
            .is_none()
            .then(|| NativeLabel::new(sentence.symbol().emitted_name()));
        Ok(NativeSentence::Production {
            label,
            parameters: Vec::new(),
            sort: self.sort(sentence.result_sort(), sentence.origin())?,
            items,
            attributes,
        })
    }

    #[allow(clippy::too_many_lines)]
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
            DefinitionProductionAttribute::Alias { .. } => {
                attributes.insert("alias", json!(""));
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
            DefinitionProductionAttribute::Format { fragments, .. } => {
                attributes.insert("format", json!(native_format(fragments)));
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
                None,
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
        let is_main = variables.iter().any(|variable| {
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
        // K's source frontend carries this internal marker from a named
        // computation-cell context alias into its generated cool rule.
        attributes.insert("cool-like", json!(""));
        Ok(NativeSentence::ContextAlias {
            body,
            requires: truth(),
            attributes,
        })
    }

    #[allow(clippy::too_many_lines)]
    pub(super) fn rule(
        &mut self,
        sentence: &RuleSentence,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeSentence, AdapterError> {
        let body = match sentence.relational_body() {
            RuleBodyRef::Term(term) => {
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
                    Some(sentence),
                )?
            }
            RuleBodyRef::Configuration { body: rewrite, .. } => {
                self.configuration_rewrite(rewrite, module, sentence_index, sentence)?
            }
        };
        let requires = sentence.requires().map_or_else(
            || Ok(truth()),
            |condition| {
                self.map_sentence_origin(
                    condition.origin(),
                    module,
                    sentence_index,
                    SentenceNodeRole::Requires,
                );
                self.term(
                    condition.term(),
                    module,
                    sentence_index,
                    Vec::new(),
                    TermContext::Normal,
                    Some(sentence),
                )
            },
        )?;
        let ensures = sentence
            .claim()
            .and_then(|claim| claim.ensures())
            .map_or_else(
                || Ok(truth()),
                |condition| {
                    self.map_sentence_origin(
                        condition.origin(),
                        module,
                        sentence_index,
                        SentenceNodeRole::Ensures,
                    );
                    self.term(
                        condition.term(),
                        module,
                        sentence_index,
                        Vec::new(),
                        TermContext::Normal,
                        Some(sentence),
                    )
                },
            )?;
        let mut attributes = attributes_for_origin(sentence.origin());
        attributes.insert("label", json!(native_rule_label(module, sentence.label())));
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
            for (index, binder) in claim
                .universals()
                .iter()
                .chain(claim.existentials())
                .enumerate()
            {
                self.map_claim_binder(binder, module, sentence_index, index);
            }
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

    fn map_claim_binder(
        &mut self,
        binder: &DefinitionClaimBinder,
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
        let mut cells = rewrite
            .clauses()
            .iter()
            .enumerate()
            .map(|(index, clause)| {
                let index = u32::try_from(index).unwrap_or(u32::MAX);
                self.map_sentence_origin(
                    clause.origin(),
                    module,
                    sentence_index,
                    SentenceNodeRole::ConfigurationRuleCell(index),
                );
                if let CellContentFrame::KSequenceTail { origin, .. }
                | CellContentFrame::MapRemainder { origin, .. } = clause.frame()
                {
                    self.map_sentence_origin(
                        origin,
                        module,
                        sentence_index,
                        SentenceNodeRole::ConfigurationRuleFrame(index),
                    );
                }
                let before = self.term(
                    clause.before(),
                    module,
                    sentence_index,
                    vec![index],
                    TermContext::Normal,
                    Some(sentence),
                )?;
                let content = match clause.after() {
                    CellPost::Preserve => before,
                    CellPost::Replace { term } => NativeTerm::Rewrite {
                        left: Box::new(before),
                        right: Box::new(self.term(
                            term,
                            module,
                            sentence_index,
                            vec![index, 1],
                            TermContext::Normal,
                            Some(sentence),
                        )?),
                    },
                };
                self.framed_cell(clause.cell(), content, clause.frame(), clause.origin())
            })
            .collect::<Result<Vec<_>, AdapterError>>()?;
        if sentence.claim().is_some() {
            cells.push(native_claim_counter(sentence_index));
        }
        Ok(native_cells(cells))
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
                | CellContentFrame::MapRemainder { origin, .. } = cell.frame()
                {
                    self.map_sentence_origin(
                        origin,
                        module,
                        sentence_index,
                        SentenceNodeRole::ContextAliasFrame(index),
                    );
                }
                let cell_content = self.term(
                    cell.pattern(),
                    module,
                    sentence_index,
                    vec![index],
                    context,
                    None,
                )?;
                self.framed_cell(cell.cell(), cell_content, cell.frame(), cell.origin())
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
            CellContentFrame::KSequenceTail { binding, .. } => {
                binding.as_ref().map_or((content.clone(), true), |binding| {
                    (
                        NativeTerm::sequence([
                            content,
                            native_variable(
                                binding,
                                Some(NativeSort::new(BuiltinSort::KSequence.k_name())),
                                false,
                            ),
                        ]),
                        false,
                    )
                })
            }
            CellContentFrame::MapRemainder { binding, .. } => {
                binding.as_ref().map_or((content.clone(), true), |binding| {
                    (
                        NativeTerm::apply(
                            MapOperation::CONCATENATION.k_label,
                            vec![
                                content,
                                native_variable(
                                    binding,
                                    Some(NativeSort::new(BuiltinSort::Map.k_name())),
                                    false,
                                ),
                            ],
                        ),
                        false,
                    )
                })
            }
        };
        Ok(incomplete_cell(name, content, open_right))
    }
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

fn native_cells(mut cells: Vec<NativeTerm>) -> NativeTerm {
    match cells.len() {
        0 => NativeTerm::apply("#cells", Vec::new()),
        1 => cells.pop().expect("length is one"),
        _ => NativeTerm::apply("#cells", cells),
    }
}

pub(super) fn native_claim_counter(sentence_index: usize) -> NativeTerm {
    let sort = Some(NativeSort::new(BuiltinSort::Int.k_name()));
    incomplete_cell(
        "generatedCounter",
        NativeTerm::Rewrite {
            left: Box::new(NativeTerm::Variable {
                name: format!("_KrsCounter{sentence_index}"),
                sort: sort.clone(),
            }),
            right: Box::new(NativeTerm::Variable {
                name: format!("?KrsCounter{sentence_index}"),
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
