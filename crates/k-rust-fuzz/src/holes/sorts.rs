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
    /// For each sort, the argument sorts of the main module's constructors of that sort: the
    /// sorts a value of it may contain directly (a subsort declaration `syntax A ::= B` is such
    /// a production; functions, macros and aliases are not, since no value is built with them).
    contents: BTreeMap<String, BTreeSet<String>>,
}

/// The outcome of the rule for one hole, before its override is applied.
#[derive(Debug, Default)]
pub(super) struct SortVerdict {
    /// Why the hole's own sort is refused, if it is.
    pub(super) own: Option<SortRefusal>,
    /// Each refused sort a value of the hole's sort may contain, with its refusal, ordered by
    /// sort name. The walk does not continue past a refused sort.
    pub(super) contained: Vec<(String, SortRefusal)>,
}

impl SortVerdict {
    /// Every refusal, the own sort's first (under `own_sort`), then the contained ones.
    pub(super) fn all(&self, own_sort: &str) -> Vec<(String, SortRefusal)> {
        self.own
            .iter()
            .map(|reason| (own_sort.to_owned(), reason.clone()))
            .chain(self.contained.iter().cloned())
            .collect()
    }
}

/// Which productions [`productions`] reads.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Productions {
    /// Every production: the grammar programs may be written in.
    All,
    /// Constructors only: the productions values are built with.
    Constructors,
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
        let contents = productions(&frontend.sentences(main), Productions::Constructors);

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

    /// The K names of the sorts whose values are not data, which a data table must not enter
    /// (`TextSyntax::new`'s `excluded`): the program-syntax sorts as the rule computes them
    /// (builtins among them; the values module admits builtins before it reads this set), the
    /// cell sorts and K's internal sorts such as `KResult`.
    pub(super) fn excluded(&self) -> Vec<String> {
        self.program_syntax
            .iter()
            .chain(&self.cells)
            .cloned()
            .chain(K_INTERNAL_SORTS.map(str::to_owned))
            .collect()
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

    /// Apply the rule to `decl` (see [`super::check_hole_sort`]): every refusal, before the
    /// override.
    ///
    /// # Errors
    ///
    /// [`SortRefusal::Unknown`], which no override admits, for a hole sort or a declared element
    /// sort the definition does not declare.
    pub(super) fn verdict(&self, decl: &HoleDecl) -> Result<SortVerdict, CampaignError> {
        let unknown = || CampaignError::RefusedHoleSort {
            hole: decl.name.clone(),
            sort: decl.sort.clone(),
            reason: SortRefusal::Unknown,
        };
        let sort = parse_sort(&decl.sort).map_err(|_| unknown())?;
        let (own, contained) = match self.kind(&sort.name) {
            Kind::Unknown => return Err(unknown()),
            Kind::Refused(reason) => (Some(reason), Ok(Vec::new())),
            Kind::Builtin => (None, Ok(Vec::new())),
            // A collection without declared element sorts is refused by the value resolution.
            Kind::Collection => (
                None,
                match &decl.constraints.elements {
                    None => Ok(Vec::new()),
                    Some(ElementSorts::Elements { element }) => self.contained(&[element]),
                    Some(ElementSorts::Entries { key, value }) => self.contained(&[key, value]),
                },
            ),
            Kind::Data => (
                None,
                self.contained(
                    &self
                        .contents
                        .get(&sort.name)
                        .map(|sorts| sorts.iter().collect::<Vec<_>>())
                        .unwrap_or_default(),
                ),
            ),
        };
        Ok(SortVerdict {
            own,
            contained: contained.map_err(|Undeclared| unknown())?,
        })
    }

    /// [`Self::verdict`] with the override applied: `Ok(None)` when nothing is refused, the
    /// first refusal (the own sort's, else the first contained one) when the override admits
    /// it, and that refusal as the error otherwise.
    pub(super) fn check(&self, decl: &HoleDecl) -> Result<Option<SortRefusal>, CampaignError> {
        let verdict = self.verdict(decl)?;
        let Some((_, reason)) = verdict.all(&decl.sort).into_iter().next() else {
            return Ok(None);
        };
        if decl.allow_refused_sort {
            Ok(Some(reason))
        } else {
            Err(CampaignError::RefusedHoleSort {
                hole: decl.name.clone(),
                sort: decl.sort.clone(),
                reason,
            })
        }
    }

    /// Every refused sort among `sorts` and the sorts their values may contain, transitively,
    /// ordered by sort name: a refused sort is recorded and not walked into, a builtin ends the
    /// walk, a collection reached here has no declared element sorts and so holds `KItem`s (a
    /// computation), and a data sort continues with what its constructors take.
    fn contained<S: AsRef<str>>(
        &self,
        sorts: &[S],
    ) -> Result<Vec<(String, SortRefusal)>, Undeclared> {
        let mut seen = BTreeSet::new();
        let mut pending = sorts
            .iter()
            .map(|sort| {
                parse_sort(sort.as_ref())
                    .map(|sort| sort.name.clone())
                    .map_err(|_| Undeclared)
            })
            .collect::<Result<BTreeSet<_>, _>>()?;
        let mut refused = BTreeMap::new();
        while let Some(head) = pending.pop_first() {
            if !seen.insert(head.clone()) {
                continue;
            }
            match self.kind(&head) {
                Kind::Unknown => return Err(Undeclared),
                Kind::Refused(reason) => {
                    refused.insert(head, reason);
                }
                Kind::Collection => {
                    refused.insert(head, SortRefusal::Computation);
                }
                Kind::Builtin => {}
                Kind::Data => {
                    if let Some(sorts) = self.contents.get(&head) {
                        pending.extend(sorts.iter().filter(|sort| !seen.contains(*sort)).cloned());
                    }
                }
            }
        }
        Ok(refused.into_iter().collect())
    }
}

/// For each sort, the sorts of the non-terminals of its productions among `sentences` (with
/// [`Productions::Constructors`], of its constructors only). A non-terminal whose sort is or
/// mentions a parameter of a parametric production (`syntax {S} Box ::= box(S)`) may hold a
/// value of any sort, so it is recorded as `KItem`. A production whose result is a parameter
/// (`#if`, `#fun`, `#as`) builds no value of a particular sort and is left out.
fn productions(sentences: &[&Sentence], which: Productions) -> BTreeMap<String, BTreeSet<String>> {
    let not_constructor = [
        AttributeKey::Function,
        AttributeKey::Macro,
        AttributeKey::MacroRec,
        AttributeKey::Alias,
        AttributeKey::AliasRec,
    ];
    let mut contents = BTreeMap::<String, BTreeSet<String>>::new();
    for sentence in sentences {
        let Sentence::Production {
            parameters,
            sort,
            items,
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        if mentions(sort, parameters)
            || (which == Productions::Constructors
                && not_constructor.into_iter().any(|key| attributes.has(key)))
        {
            continue;
        }
        let arguments = contents.entry(sort.name.clone()).or_default();
        for item in items {
            if let ProductionItem::NonTerminal { sort: argument, .. } = item {
                arguments.insert(if mentions(argument, parameters) {
                    BuiltinSort::KItem.k_name().to_owned()
                } else {
                    argument.name.clone()
                });
            }
        }
    }
    contents
}

/// Whether `sort` is or has among its arguments one of `parameters`.
fn mentions(sort: &KastSort, parameters: &[KastSort]) -> bool {
    parameters.contains(sort)
        || sort
            .parameters
            .iter()
            .any(|argument| mentions(argument, parameters))
}

/// The sorts programs are written in: those reachable from `start` through the productions of
/// the syntax module (`sentences`), where a production of a reached sort reaches the sorts of
/// its non-terminals and a subsort declaration (`syntax AExp ::= Int`) is such a production.
///
/// The productions of a hooked sort are not followed: a builtin's literals are exempt, and its
/// operations over `K` (`size(Map)`, `K ==K K`) do not put a program in every sort.
///
/// Every sort is a `KItem`, but the frontend writes no production for that subsorting. When the
/// start sort is `K` or `KItem`, or the closure reaches one of them or a builtin collection
/// (which holds `KItem`s), a program may therefore be written in any sort of the syntax module,
/// and every non-hooked sort it declares is taken (D17).
fn program_syntax(
    sentences: &[&Sentence],
    start: &KastSort,
    hooked: &BTreeMap<String, String>,
) -> BTreeSet<String> {
    let contents = productions(sentences, Productions::All);
    let any_item = [BuiltinSort::K, BuiltinSort::KItem].map(BuiltinSort::k_name);
    let mut reached = BTreeSet::from([start.name.clone()]);
    let mut pending = vec![start.name.clone()];
    let mut every_sort = false;
    while let Some(sort) = pending.pop() {
        if any_item.contains(&sort.as_str()) {
            every_sort = true;
            continue;
        }
        // A builtin's literals are exempt, and its operations over `K` (`size(Map)`, `==K`) do
        // not make every sort a program sort: its productions are not followed. A collection
        // holds `KItem`s, so reaching one is reaching `KItem`.
        if let Some(hook) = hooked.get(&sort) {
            every_sort |= COLLECTION_HOOKS.contains(&hook.as_str());
            continue;
        }
        for argument in contents.get(&sort).into_iter().flatten() {
            if reached.insert(argument.clone()) {
                pending.push(argument.clone());
            }
        }
    }
    if every_sort {
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
