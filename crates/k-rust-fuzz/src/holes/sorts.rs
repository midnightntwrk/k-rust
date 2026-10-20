//! The hole-sort rule (ARCHITECTURE 2.4, R-11, T-9): a hole is data, never a computation, a
//! piece of program syntax, or a name the program declares.

use std::collections::BTreeSet;

use k_rust::{
    definition::{AttributeKey, ProductionItem, ResolvedDefinition, Sentence},
    kast::{Sort as KastSort, parser::parse_sort},
    names::BuiltinSort,
};

use super::HoleDecl;
use crate::{
    error::{CampaignError, SortRefusal},
    spec::{CompiledDefinition, ProgramInput},
};

/// The facts of one definition the rule reads, by sort head name.
pub(super) struct SortRule {
    /// Sorts the main module declares, generated cell sorts included.
    declared: BTreeSet<String>,
    /// Sorts whose declaration carries `hook`: builtin sorts whose values the backend fixes.
    hooked: BTreeSet<String>,
    /// Sorts with a `token` declaration or production.
    tokens: BTreeSet<String>,
    /// Cell sorts and the sorts of generated cell fragments and collections.
    cells: BTreeSet<String>,
    /// Sorts in the closure of the start sort's productions in the syntax module.
    program_syntax: BTreeSet<String>,
}

impl SortRule {
    /// The rule for holes of `program` under `definition`.
    pub(super) fn new(
        program: &ProgramInput,
        definition: &CompiledDefinition,
    ) -> Result<Self, CampaignError> {
        let unresolved = |what: &str, error: &dyn std::fmt::Display| CampaignError::Definition {
            message: format!("the {what} definition does not resolve: {error}"),
        };
        let missing = |module: &str| CampaignError::Definition {
            message: format!("module `{module}` is not in the definition"),
        };
        let frontend = ResolvedDefinition::resolve(&definition.frontend_definition)
            .map_err(|error| unresolved("frontend", &error))?;
        let main = frontend
            .module_id(&definition.main_module)
            .ok_or_else(|| missing(&definition.main_module))?;
        let catalog = frontend.sort_catalog(main);
        let mut declared = catalog
            .defined_heads()
            .iter()
            .map(|head| head.as_str().to_owned())
            .collect::<BTreeSet<_>>();
        let hooked = catalog.hooks().keys().cloned().collect();
        let tokens = catalog
            .token_sorts()
            .iter()
            .map(|sort| sort.name.clone())
            .collect();

        // Cell sorts exist only once the configuration is compiled, so they are read from the
        // execution definition: the sorts of cell productions, of cell fragments and absent
        // optional cells, and of cell collections.
        let execution = ResolvedDefinition::resolve(&definition.execution_definition)
            .map_err(|error| unresolved("execution", &error))?;
        let execution_main = execution
            .module_id(&definition.main_module)
            .ok_or_else(|| missing(&definition.main_module))?;
        let mut cells = BTreeSet::from([
            BuiltinSort::GeneratedTopCell.k_name().to_owned(),
            BuiltinSort::GeneratedCounterCell.k_name().to_owned(),
        ]);
        for sentence in execution.sentences(execution_main) {
            let cell_sort = match sentence {
                Sentence::Production {
                    sort, attributes, ..
                } if [
                    AttributeKey::Cell,
                    AttributeKey::CellFragment,
                    AttributeKey::CellOptAbsent,
                    AttributeKey::CellCollection,
                ]
                .into_iter()
                .any(|key| attributes.has(key)) =>
                {
                    sort
                }
                Sentence::SyntaxSort {
                    sort, attributes, ..
                } if attributes.has(AttributeKey::CellCollection) => sort,
                _ => continue,
            };
            cells.insert(cell_sort.name.clone());
        }
        declared.extend(cells.iter().cloned());

        let start = match program {
            ProgramInput::Source(source) => match &source.program {
                Some(text) => Some(parse_sort(&text.start_sort).map_err(|error| {
                    CampaignError::InvalidOptions {
                        message: format!("start sort `{}`: {error}", text.start_sort),
                    }
                })?),
                None => definition.configuration_variables.get("PGM").cloned(),
            },
            ProgramInput::KoreTemplate(_) => definition.configuration_variables.get("PGM").cloned(),
        };
        let program_syntax = match start {
            Some(start) => {
                let syntax = frontend
                    .module_id(&definition.syntax_module)
                    .ok_or_else(|| missing(&definition.syntax_module))?;
                closure(frontend.sentences(syntax), &start)
            }
            None => BTreeSet::new(),
        };
        Ok(Self {
            declared,
            hooked,
            tokens,
            cells,
            program_syntax,
        })
    }

    /// Apply the rule to `decl` (see [`super::check_hole_sort`]).
    pub(super) fn check(&self, decl: &HoleDecl) -> Result<Option<SortRefusal>, CampaignError> {
        let refuse = |reason| CampaignError::RefusedHoleSort {
            hole: decl.name.clone(),
            sort: decl.sort.clone(),
            reason,
        };
        let Ok(sort) = parse_sort(&decl.sort) else {
            return Err(refuse(SortRefusal::Unknown));
        };
        let head = sort.name.as_str();
        let refusal = if head == BuiltinSort::K.k_name()
            || head == BuiltinSort::KItem.k_name()
            || self.cells.contains(head)
        {
            SortRefusal::Computation
        } else if self.hooked.contains(head) {
            // A builtin sort: its literals occur in programs, but its values are data. Whether
            // it has a generator is `resolve_value_sort`'s part of the rule.
            return Ok(None);
        } else if !self.declared.contains(head) {
            return Err(refuse(SortRefusal::Unknown));
        } else if self.tokens.contains(head) {
            SortRefusal::Token
        } else if self.program_syntax.contains(head) {
            SortRefusal::ProgramSyntax
        } else {
            return Ok(None);
        };
        if decl.allow_refused_sort {
            Ok(Some(refusal))
        } else {
            Err(refuse(refusal))
        }
    }
}

/// The sorts reachable from `start` through the productions among `sentences`: a production of
/// a reached sort reaches the sort of each of its non-terminals, and a subsort declaration
/// (`syntax AExp ::= Int`) is such a production. Sort parameters of parametric productions
/// stand for any sort and reach nothing.
fn closure(sentences: Vec<&Sentence>, start: &KastSort) -> BTreeSet<String> {
    let mut reached = BTreeSet::from([start.name.clone()]);
    let mut pending = vec![start.name.clone()];
    while let Some(sort) = pending.pop() {
        for sentence in &sentences {
            let Sentence::Production {
                parameters,
                sort: produced,
                items,
                ..
            } = sentence
            else {
                continue;
            };
            if produced.name != sort {
                continue;
            }
            for item in items {
                if let ProductionItem::NonTerminal { sort: argument, .. } = item
                    && !parameters.contains(argument)
                    && reached.insert(argument.name.clone())
                {
                    pending.push(argument.name.clone());
                }
            }
        }
    }
    reached
}
