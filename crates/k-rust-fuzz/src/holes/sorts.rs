//! The hole-sort rule (ARCHITECTURE 2.4 as amended by D17, R-11, T-9): a hole is data, never a
//! computation, a piece of program syntax, or a name the program declares, and neither is
//! anything a value of the hole's sort may contain.

use std::collections::{BTreeMap, BTreeSet};

use k_rust::{
    definition::{AttributeKey, ProductionItem, ResolvedDefinition, Sentence},
    kast::{Sort as KastSort, parser::parse_sort},
    names::BuiltinSort,
};

use super::HoleDecl;
use crate::{
    error::{CampaignError, SortRefusal},
    spec::{CompiledDefinition, ProgramInput},
    values::ElementSorts,
};

/// K's own sorts other than `K` and `KItem` whose values are computations or K internals, not
/// data (D17): a `KResult` is whatever the definition declares a result of evaluation.
const K_INTERNAL_SORTS: [&str; 3] = ["KResult", "KBott", "KConfigVar"];

/// The hooks of the builtin collections. Without declared element sorts their elements are
/// `KItem`s, which may be computations or program syntax.
const COLLECTION_HOOKS: [&str; 4] = ["LIST.List", "SET.Set", "MAP.Map", "RANGEMAP.RangeMap"];

/// The facts of one definition the rule reads, by sort head name.
pub(super) struct SortRule {
    /// Sorts the main module declares, generated cell sorts included.
    declared: BTreeSet<String>,
    /// Sorts whose declaration carries `hook`, with the hook: builtin sorts whose values the
    /// backend fixes.
    hooked: BTreeMap<String, String>,
    /// Sorts with a `token` declaration or production.
    tokens: BTreeSet<String>,
    /// Cell sorts and the sorts of generated cell fragments and collections.
    cells: BTreeSet<String>,
    /// The sorts programs are written in (see [`program_syntax`]).
    program_syntax: BTreeSet<String>,
    /// For each sort, the argument sorts of the main module's productions of that sort: the
    /// sorts a value of it may contain directly (a subsort declaration `syntax A ::= B` is such
    /// a production).
    contents: BTreeMap<String, BTreeSet<String>>,
}

/// What a sort is, as the rule sees it.
enum Kind {
    /// The sort is refused for this reason (before any override).
    Refused(SortRefusal),
    /// A hooked sort other than a collection: its values are builtin data; whether it has a
    /// generator is `resolve_value_sort`'s part of the rule.
    Builtin,
    /// A builtin collection: its values contain its element sorts.
    Collection,
    /// A user sort that is data in itself: its values contain what its productions take.
    Data,
    /// The definition does not declare the sort.
    Unknown,
}

/// An element sort the definition does not declare (or that does not parse).
struct Undeclared;

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
        let hooked = catalog.hooks().clone();
        let tokens = catalog
            .token_sorts()
            .iter()
            .map(|sort| sort.name.clone())
            .collect();
        let contents = productions(&frontend.sentences(main));

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
                program_syntax(&frontend.sentences(syntax), &start, &hooked)
            }
            None => BTreeSet::new(),
        };
        Ok(Self {
            declared,
            hooked,
            tokens,
            cells,
            program_syntax,
            contents,
        })
    }

    fn kind(&self, head: &str) -> Kind {
        if head == BuiltinSort::K.k_name()
            || head == BuiltinSort::KItem.k_name()
            || K_INTERNAL_SORTS.contains(&head)
            || self.cells.contains(head)
        {
            Kind::Refused(SortRefusal::Computation)
        } else if let Some(hook) = self.hooked.get(head) {
            if COLLECTION_HOOKS.contains(&hook.as_str()) {
                Kind::Collection
            } else {
                Kind::Builtin
            }
        } else if !self.declared.contains(head) {
            Kind::Unknown
        } else if self.tokens.contains(head) {
            Kind::Refused(SortRefusal::Token)
        } else if self.program_syntax.contains(head) {
            Kind::Refused(SortRefusal::ProgramSyntax)
        } else {
            Kind::Data
        }
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
        let contained = match self.kind(&sort.name) {
            Kind::Unknown => return Err(refuse(SortRefusal::Unknown)),
            Kind::Refused(reason) => Ok(Some(reason)),
            Kind::Builtin => Ok(None),
            // A collection without declared element sorts is refused by `resolve_value_sort`.
            Kind::Collection => match &decl.constraints.elements {
                None => Ok(None),
                Some(ElementSorts::Elements { element }) => self.contained(&[element]),
                Some(ElementSorts::Entries { key, value }) => self.contained(&[key, value]),
            },
            Kind::Data => self.contained(
                &self
                    .contents
                    .get(&sort.name)
                    .map(|sorts| sorts.iter().collect::<Vec<_>>())
                    .unwrap_or_default(),
            ),
        };
        match contained.map_err(|Undeclared| refuse(SortRefusal::Unknown))? {
            None => Ok(None),
            Some(reason) if decl.allow_refused_sort => Ok(Some(reason)),
            Some(reason) => Err(refuse(reason)),
        }
    }

    /// The first refusal among `sorts` and the sorts their values may contain, transitively: a
    /// refused sort ends the walk with its refusal, a builtin ends it without one, a collection
    /// reached here has no declared element sorts and so holds `KItem`s (a computation), and a
    /// data sort continues with what its productions take.
    fn contained<S: AsRef<str>>(&self, sorts: &[S]) -> Result<Option<SortRefusal>, Undeclared> {
        let mut seen = BTreeSet::new();
        let mut pending = sorts
            .iter()
            .map(|sort| {
                parse_sort(sort.as_ref())
                    .map(|sort| sort.name.clone())
                    .map_err(|_| Undeclared)
            })
            .collect::<Result<Vec<_>, _>>()?;
        while let Some(head) = pending.pop() {
            if !seen.insert(head.clone()) {
                continue;
            }
            match self.kind(&head) {
                Kind::Unknown => return Err(Undeclared),
                Kind::Refused(reason) => return Ok(Some(reason)),
                Kind::Collection => return Ok(Some(SortRefusal::Computation)),
                Kind::Builtin => {}
                Kind::Data => {
                    if let Some(sorts) = self.contents.get(&head) {
                        pending.extend(sorts.iter().cloned());
                    }
                }
            }
        }
        Ok(None)
    }
}

/// For each sort, the sorts of the non-terminals of its productions among `sentences`. Sort
/// parameters of parametric productions stand for any sort and are left out.
fn productions(sentences: &[&Sentence]) -> BTreeMap<String, BTreeSet<String>> {
    let mut contents = BTreeMap::<String, BTreeSet<String>>::new();
    for sentence in sentences {
        let Sentence::Production {
            parameters,
            sort,
            items,
            ..
        } = sentence
        else {
            continue;
        };
        if parameters.contains(sort) {
            continue;
        }
        let arguments = contents.entry(sort.name.clone()).or_default();
        for item in items {
            if let ProductionItem::NonTerminal { sort: argument, .. } = item
                && !parameters.contains(argument)
            {
                arguments.insert(argument.name.clone());
            }
        }
    }
    contents
}

/// The sorts programs are written in: those reachable from `start` through the productions of
/// the syntax module (`sentences`), where a production of a reached sort reaches the sorts of
/// its non-terminals and a subsort declaration (`syntax AExp ::= Int`) is such a production.
///
/// Every sort is a `KItem`, but the frontend writes no production for that subsorting. When the
/// start sort is `K` or `KItem`, or the closure reaches one of them, a program may therefore be
/// written in any sort of the syntax module, and every non-hooked sort it declares is taken
/// (D17).
fn program_syntax(
    sentences: &[&Sentence],
    start: &KastSort,
    hooked: &BTreeMap<String, String>,
) -> BTreeSet<String> {
    let contents = productions(sentences);
    let mut reached = BTreeSet::from([start.name.clone()]);
    let mut pending = vec![start.name.clone()];
    while let Some(sort) = pending.pop() {
        for argument in contents.get(&sort).into_iter().flatten() {
            if reached.insert(argument.clone()) {
                pending.push(argument.clone());
            }
        }
    }
    let any_item = [BuiltinSort::K, BuiltinSort::KItem].map(BuiltinSort::k_name);
    if any_item.iter().any(|sort| reached.contains(*sort)) {
        for sentence in sentences {
            if let Sentence::Production { sort, .. } | Sentence::SyntaxSort { sort, .. } = sentence
                && !hooked.contains_key(&sort.name)
            {
                reached.insert(sort.name.clone());
            }
        }
    }
    reached
}
