//! The parts of a lowered pattern and the patterns that leave one of them out (FB50-EXPLAIN): what
//! `query` asks to explain a failed answer ([`crate::query`], "Explanations").
//!
//! **Parts.** A pattern's parts are read on its compiled target `\and(body, P...)`
//! ([`super::LoweredPattern`]), never on its K text, so they are the constraints the matcher
//! applies:
//! - **A cell**: each cell the target gives a content of its own at the level a witness lists
//!   cells by (`crate::evidence`, "A query witness"). From the top cell down, a cell application
//!   with an argument that is neither a cell nor a variable the compiler minted is a part; one
//!   whose arguments are cells and minted variables is entered, its cell arguments read the same
//!   way. A cell of multiplicity `*` is held in a collection, which is no cell, so the cell
//!   holding the collection is the part.
//! - **A conjunct of the condition**: each predicate `P`, and inside a predicate
//!   `\equals(C, true)` each operand of the `_andBool_` applications on the spine of `C`, left to
//!   right. The compiler keeps a `requires` as one predicate whose term is an `_andBool_`
//!   application where `BOOL` declares the conjunction, and gives each conjunct its own predicate
//!   where it does not, so both shapes are read. A conjunct the sorts of its variables make true
//!   is no constraint and no part: the sort test `isS(X)` of a variable of sort `S`, which the
//!   compiler conjoins for each cast `X:S` a pattern writes ([`Conjunct::tautology`]).
//!
//! **Leaving a part out** ([`Parts::without`]) gives a pattern weaker than the original: every
//! state the original matches, the result matches too.
//! - A cell's application is replaced by a fresh variable of the sort its parent holds it at
//!   (`DeclaredCell::position_kore_sort`), what the compiler writes for a cell a pattern leaves
//!   out. Every conjunct that names a variable occurring nowhere else in the body (the variables
//!   only that cell binds, all variables counted, minted ones included) goes with it: kept, such
//!   a variable would occur in the condition alone, an existential the matcher decides only where
//!   its application evaluates, so the weaker pattern would be left undecided where the original
//!   was refuted. A variable a chain's earlier step binds (`carried`) is no such variable: its
//!   value is carried into the step, and a conjunct naming it stays decidable.
//! - A conjunct is dropped from its predicate; the operands left are conjoined again with the
//!   predicate's own `_andBool_`, and a predicate left with none is dropped. A condition left with
//!   no predicate is `\top`, as the compiler writes a pattern without `requires`. Since `A andBool
//!   B` is `true` only where both operands are, and `\and` holds only where every predicate does,
//!   dropping a conjunct only weakens the pattern.
//!
//! The fresh variable is recorded as generated, so it enters the derived pattern's digest, its
//! binding is in no witness and a chain never shares it. A derived pattern is checked by the
//! admission every lowered pattern passes ([`super::admit_target`]), and keyed and cached as a
//! pattern is: its answer is a function of its target, as any pattern's is.
//!
//! **A vacuous pattern** ([`vacuous`]): one whose condition is `\top` and whose body is the cell
//! structure with a distinct variable as every cell's content, each of the sort its cell holds.
//! It matches every configuration of the definition, so it says nothing about the pattern it was
//! derived from: an explanation names it and never asks it.

use super::{
    LoweredPattern, Lowering, admit_target, generated, pattern_digest, requires_only_variables,
};
use k_rust::{
    definition::configuration::{CellMultiplicity, declared_cells},
    k_rust_backend::definition::BackendDefinition,
    kast::identifier::label_or_name,
    kore::ast::{Pattern, Sort, Symbol, Variable, VariableKind},
};
use std::collections::{BTreeMap, BTreeSet};

/// The KORE symbol of `BOOL`'s conjunction, `_andBool_`.
pub const AND_BOOL: &str = "Lbl'Unds'andBool'Unds'";

/// The prefix of the fresh variables a derived pattern holds (`_Explain0`, ...), numbered past
/// every variable the target already names.
const FRESH_PREFIX: &str = "Var'Unds'Explain";

/// The cells of a configuration by KORE symbol: each cell's K label (`<k>`), the sort its parent
/// holds it at, and whether it is a part of the multiplicity `*` (held in a collection).
#[derive(Clone, Debug, Default)]
pub struct CellTable {
    cells: BTreeMap<String, CellEntry>,
}

#[derive(Clone, Debug)]
struct CellEntry {
    label: String,
    position: Sort,
    star: bool,
}

impl CellTable {
    fn get<'t>(&self, term: &'t Pattern) -> Option<(&CellEntry, &'t [Pattern])> {
        match term {
            Pattern::Application { symbol, arguments } => self
                .cells
                .get(&symbol.name)
                .map(|entry| (entry, arguments.as_slice())),
            _ => None,
        }
    }

    fn is_cell(&self, term: &Pattern) -> bool {
        self.get(term).is_some()
    }
}

impl Lowering {
    /// The configuration's cells as an explanation reads them ([`CellTable`]).
    #[must_use]
    pub fn cell_table(&self) -> CellTable {
        let module = self
            .execution
            .module_id(&self.module)
            .unwrap_or_else(|| self.execution.main_module_id());
        CellTable {
            cells: declared_cells(&self.execution, module)
                .into_iter()
                .map(|cell| {
                    (
                        cell.kore_symbol.clone(),
                        CellEntry {
                            label: label_or_name(&cell.kore_symbol),
                            position: cell.position_kore_sort.clone(),
                            star: cell.multiplicity == CellMultiplicity::Star,
                        },
                    )
                })
                .collect(),
        }
    }
}

/// A cell part of a pattern (module docs).
#[derive(Clone, Debug)]
pub struct CellPart {
    /// The cell's KORE symbol, as a witness's printer names it.
    pub symbol: String,
    /// The cell's K label, `<k>`.
    pub label: String,
    /// The argument indices from the body down to the cell's application.
    at: Vec<usize>,
    /// The sort the cell's parent holds it at.
    position: Sort,
    /// The conjuncts that go with the cell (indices into [`Parts::conjuncts`], in order): those
    /// naming a variable only the cell binds.
    pub dependent: Vec<usize>,
}

/// A conjunct of a pattern's condition (module docs).
#[derive(Clone, Debug)]
pub struct Conjunct {
    /// The conjunct: a Bool term (an operand of a predicate `\equals(C, true)`), or a predicate.
    pub term: Pattern,
    /// The KORE names of the variables free in it that the compiler did not mint, in name order.
    pub variables: Vec<String>,
    /// The KORE names of every variable free in it.
    all: BTreeSet<String>,
    /// Whether the sorts of its variables make it true ([`sort_test_of_its_variable`]): no
    /// constraint, so no part, though it goes with the cell its variable is bound in.
    pub tautology: bool,
}

/// One predicate of the condition and its conjuncts.
#[derive(Clone, Debug)]
enum Predicate {
    /// `\equals(C, true)`: the predicate, the conjunction symbol of `C`'s spine (none when `C` is
    /// no conjunction) and its conjuncts (indices into [`Parts::conjuncts`]), left to right.
    Bool {
        predicate: Pattern,
        and_bool: Option<Symbol>,
        conjuncts: Vec<usize>,
    },
    /// Any other predicate, one conjunct.
    Other(usize),
}

/// The parts of one lowered pattern (module docs): its cells in pre-order, then its conjuncts in
/// order.
#[derive(Clone, Debug)]
pub struct Parts {
    pub cells: Vec<CellPart>,
    pub conjuncts: Vec<Conjunct>,
    predicates: Vec<Predicate>,
}

/// The body and the predicates of a lowered target `\and(body, P...)`, `\top` left out.
fn split_target(target: &Pattern) -> (&Pattern, Vec<&Pattern>) {
    match target {
        Pattern::And { arguments, .. } => match arguments.split_first() {
            Some((body, predicates)) => (
                body,
                predicates
                    .iter()
                    .filter(|predicate| !matches!(predicate, Pattern::Top { .. }))
                    .collect(),
            ),
            None => (target, Vec::new()),
        },
        other => (other, Vec::new()),
    }
}

/// Whether `term` is the Bool domain value `true`.
fn is_true(term: &Pattern) -> bool {
    matches!(term, Pattern::DomainValue { sort, value }
        if *sort == Sort::Application { name: "SortBool".into(), arguments: Vec::new() }
            && value.as_bytes() == b"true")
}

/// Push onto `out`, left to right, the operands of the `_andBool_` applications on the spine of
/// `term`, or `term` itself when it is no conjunction; the conjunction's symbol, when it is one.
fn conjunction_operands<'t>(term: &'t Pattern, out: &mut Vec<&'t Pattern>) -> Option<Symbol> {
    match term {
        Pattern::Application { symbol, arguments }
            if symbol.name == AND_BOOL && arguments.len() == 2 =>
        {
            conjunction_operands(&arguments[0], out);
            conjunction_operands(&arguments[1], out);
            Some(symbol.clone())
        }
        _ => {
            out.push(term);
            None
        }
    }
}

/// Whether `term` is the sort test `isS(X)` of a variable `X` of the sort `S` (as the compiler
/// writes it, `isS(X ~> .K)`, `X` injected into `KItem`): true for every value of `X`, so no
/// constraint. The compiler conjoins such a test with the condition for each cast `X:S` a pattern
/// writes. A test of a variable of a strict subsort of `S` is true too, but is not recognized, so
/// it stays a part, whose answer is the pattern's own.
fn sort_test_of_its_variable(term: &Pattern) -> bool {
    let Pattern::Application { symbol, arguments } = term else {
        return false;
    };
    let (Some(tested), [argument]) = (symbol.name.strip_prefix("Lblis"), arguments.as_slice())
    else {
        return false;
    };
    let item = match argument {
        Pattern::Application { symbol, arguments }
            if symbol.name == "kseq"
                && matches!(arguments.as_slice(), [_, Pattern::Application { symbol, arguments }]
                    if symbol.name == "dotk" && arguments.is_empty()) =>
        {
            &arguments[0]
        }
        other => other,
    };
    let variable = match item {
        Pattern::Application { symbol, arguments }
            if symbol.name == "inj" && arguments.len() == 1 =>
        {
            &arguments[0]
        }
        other => other,
    };
    matches!(variable, Pattern::Variable(variable)
        if matches!(&variable.sort, Sort::Application { name, arguments }
            if arguments.is_empty() && name.strip_prefix("Sort") == Some(tested)))
}

fn names(term: &Pattern) -> BTreeSet<String> {
    term.free_variables()
        .into_iter()
        .map(|variable| variable.name)
        .collect()
}

/// The subterm of `body` at the argument indices `at`.
fn at<'t>(body: &'t Pattern, at: &[usize]) -> &'t Pattern {
    at.iter().fold(body, |term, index| match term {
        Pattern::Application { arguments, .. } => &arguments[*index],
        _ => unreachable!("a cell part's path runs through applications"),
    })
}

/// `body` with its subterm at `at` replaced by `with`.
fn replaced(body: &Pattern, at: &[usize], with: Pattern) -> Pattern {
    let mut body = body.clone();
    let mut term = &mut body;
    for index in at {
        term = match term {
            Pattern::Application { arguments, .. } => &mut arguments[*index],
            _ => unreachable!("a cell part's path runs through applications"),
        };
    }
    *term = with;
    body
}

impl Parts {
    /// The parts of `lowered` (module docs) on the configuration's cells `cells`; `carried` holds
    /// the KORE names of the variables whose values an earlier step of a chain carries into this
    /// one, which no cell binds alone.
    #[must_use]
    pub fn of(lowered: &LoweredPattern, cells: &CellTable, carried: &BTreeSet<String>) -> Self {
        let (body, predicates) = split_target(&lowered.target);
        let mut conjuncts = Vec::new();
        let mut read = Vec::new();
        for predicate in predicates {
            let conjunct = |term: &Pattern| Conjunct {
                term: term.clone(),
                variables: names(term)
                    .into_iter()
                    .filter(|name| !generated(lowered, name))
                    .collect(),
                all: names(term),
                tautology: sort_test_of_its_variable(term),
            };
            match predicate {
                Pattern::Equals { left, right, .. } if is_true(right) => {
                    let mut operands = Vec::new();
                    let and_bool = conjunction_operands(left, &mut operands);
                    let indices = operands
                        .into_iter()
                        .map(|operand| {
                            conjuncts.push(conjunct(operand));
                            conjuncts.len() - 1
                        })
                        .collect();
                    read.push(Predicate::Bool {
                        predicate: predicate.clone(),
                        and_bool,
                        conjuncts: indices,
                    });
                }
                other => {
                    conjuncts.push(conjunct(other));
                    read.push(Predicate::Other(conjuncts.len() - 1));
                }
            }
        }
        let minted = |term: &Pattern| matches!(term, Pattern::Variable(variable) if generated(lowered, &variable.name));
        let mut found = Vec::new();
        // Pre-order: a cell before the cells it holds, those in argument order.
        let mut pending = vec![(body, Vec::new())];
        while let Some((term, path)) = pending.pop() {
            let Some((entry, arguments)) = cells.get(term) else {
                continue;
            };
            let named = arguments
                .iter()
                .any(|argument| !cells.is_cell(argument) && !minted(argument));
            if named {
                if !entry.star && !path.is_empty() {
                    found.push((term, path, entry));
                }
                continue;
            }
            for (index, argument) in arguments.iter().enumerate().rev() {
                if cells.is_cell(argument) {
                    let mut below = path.clone();
                    below.push(index);
                    pending.push((argument, below));
                }
            }
        }
        let cells = found
            .into_iter()
            .map(|(term, path, entry)| {
                let symbol = match term {
                    Pattern::Application { symbol, .. } => symbol.name.clone(),
                    _ => unreachable!("a cell part is an application"),
                };
                let rest = names(&replaced(
                    body,
                    &path,
                    Pattern::Top {
                        sort: entry.position.clone(),
                    },
                ));
                let only = names(term)
                    .into_iter()
                    .filter(|name| !rest.contains(name) && !carried.contains(name))
                    .collect::<BTreeSet<_>>();
                let dependent = conjuncts
                    .iter()
                    .enumerate()
                    .filter(|(_, conjunct)| !conjunct.all.is_disjoint(&only))
                    .map(|(index, _)| index)
                    .collect();
                CellPart {
                    symbol,
                    label: entry.label.clone(),
                    at: path,
                    position: entry.position.clone(),
                    dependent,
                }
            })
            .collect();
        Self {
            cells,
            conjuncts,
            predicates: read,
        }
    }

    /// `lowered` with the cell `cell` (an index into [`Self::cells`]) replaced by a fresh
    /// variable, when given, and without the conjuncts `dropped` (indices into
    /// [`Self::conjuncts`]), checked by the admission of every pattern on `definition` (module
    /// docs).
    pub fn without(
        &self,
        lowered: &LoweredPattern,
        cell: Option<usize>,
        dropped: &BTreeSet<usize>,
        definition: &BackendDefinition,
    ) -> Result<LoweredPattern, String> {
        let derived = self.derived(lowered, cell, dropped)?;
        admit_target(definition, &derived.target)?;
        Ok(derived)
    }

    /// [`Self::without`] before the admission.
    fn derived(
        &self,
        lowered: &LoweredPattern,
        cell: Option<usize>,
        dropped: &BTreeSet<usize>,
    ) -> Result<LoweredPattern, String> {
        let (body, _) = split_target(&lowered.target);
        let sort = match &lowered.target {
            Pattern::And { sort, .. } => sort.clone(),
            _ => return Err("the pattern's target is no conjunction".to_owned()),
        };
        let mut generated = lowered.generated.clone();
        let mut minted = lowered.minted.clone();
        let body = match cell.map(|index| &self.cells[index]) {
            None => body.clone(),
            Some(part) => {
                let taken = names(&lowered.target);
                let name = (0..)
                    .map(|number| format!("{FRESH_PREFIX}{number}"))
                    .find(|name| !taken.contains(name))
                    .expect("some numbered name is free");
                generated.insert(name.clone());
                minted.insert(name.clone());
                debug_assert!(matches!(
                    at(body, &part.at),
                    Pattern::Application { symbol, .. } if symbol.name == part.symbol
                ));
                replaced(
                    body,
                    &part.at,
                    Pattern::Variable(Variable {
                        kind: VariableKind::Element,
                        name,
                        sort: part.position.clone(),
                    }),
                )
            }
        };
        let mut arguments = vec![body];
        for predicate in &self.predicates {
            match predicate {
                Predicate::Other(index) => {
                    if !dropped.contains(index) {
                        arguments.push(self.conjuncts[*index].term.clone());
                    }
                }
                Predicate::Bool {
                    predicate,
                    and_bool,
                    conjuncts,
                } => {
                    let kept = conjuncts
                        .iter()
                        .filter(|index| !dropped.contains(index))
                        .map(|index| self.conjuncts[*index].term.clone())
                        .collect::<Vec<_>>();
                    if kept.len() == conjuncts.len() {
                        arguments.push(predicate.clone());
                        continue;
                    }
                    let Some(term) = kept.into_iter().reduce(|left, right| Pattern::Application {
                        symbol: and_bool
                            .clone()
                            .expect("several conjuncts come from a conjunction"),
                        arguments: vec![left, right],
                    }) else {
                        continue;
                    };
                    let Pattern::Equals {
                        operand_sort,
                        result_sort,
                        right,
                        ..
                    } = predicate
                    else {
                        unreachable!("a Bool predicate is an equation")
                    };
                    arguments.push(Pattern::Equals {
                        operand_sort: operand_sort.clone(),
                        result_sort: result_sort.clone(),
                        left: Box::new(term),
                        right: right.clone(),
                    });
                }
            }
        }
        if arguments.len() == 1 {
            arguments.push(Pattern::Top { sort: sort.clone() });
        }
        let target = Pattern::And { sort, arguments };
        let digest = pattern_digest(&target, &generated)?;
        let requires_only = requires_only_variables(&target, &minted);
        Ok(LoweredPattern {
            target,
            generated,
            minted,
            split: lowered.split.clone(),
            digest,
            requires_only,
        })
    }
}

/// Whether `lowered` matches every configuration (module docs, "A vacuous pattern"): its
/// condition is `\top`, and its body is cells whose every content is a variable, no variable
/// twice. A variable of a well-sorted target has the sort of the position it holds, so each
/// matches every value there.
#[must_use]
pub fn vacuous(lowered: &LoweredPattern, cells: &CellTable) -> bool {
    let (body, predicates) = split_target(&lowered.target);
    if !predicates.is_empty() {
        return false;
    }
    let mut seen = BTreeSet::new();
    let mut pending = vec![body];
    while let Some(term) = pending.pop() {
        match term {
            Pattern::Variable(variable) if variable.kind == VariableKind::Element => {
                if !seen.insert(variable.name.as_str()) {
                    return false;
                }
            }
            _ => match cells.get(term) {
                Some((_, arguments)) => pending.extend(arguments),
                None => return false,
            },
        }
    }
    true
}

#[cfg(test)]
mod tests {
    //! The parts of hand-built targets and the patterns that leave each out.
    use super::*;
    use k_rust::kore::parser::parse_pattern;

    const TOP: &str = "Lbl'-LT-'generatedTop'-GT-'";
    const K: &str = "Lbl'-LT-'k'-GT-'";
    const BUS: &str = "Lbl'-LT-'bus'-GT-'";

    fn sort(name: &str) -> Sort {
        Sort::Application {
            name: name.into(),
            arguments: Vec::new(),
        }
    }

    fn table() -> CellTable {
        let entry = |label: &str, position: &str| CellEntry {
            label: label.into(),
            position: sort(position),
            star: false,
        };
        CellTable {
            cells: [
                (TOP, entry("<generatedTop>", "SortGeneratedTopCell")),
                (K, entry("<k>", "SortKCell")),
                (BUS, entry("<bus>", "SortBusCell")),
            ]
            .into_iter()
            .map(|(symbol, entry)| (symbol.to_owned(), entry))
            .collect(),
        }
    }

    fn lowered(text: &str, minted: &[&str]) -> LoweredPattern {
        let target = parse_pattern(text).unwrap();
        let minted = minted.iter().map(|name| (*name).to_owned()).collect();
        LoweredPattern {
            requires_only: requires_only_variables(&target, &minted),
            digest: pattern_digest(&target, &minted).unwrap(),
            target,
            generated: minted.clone(),
            minted,
            split: BTreeSet::new(),
        }
    }

    fn int(name: &str) -> String {
        format!("{name}:SortInt{{}}")
    }

    fn app(symbol: &str, arguments: &[String]) -> String {
        format!("{symbol}{{}}({})", arguments.join(", "))
    }

    fn holds(term: &str) -> String {
        format!(
            r#"\equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}({term}, \dv{{SortBool{{}}}}("true"))"#
        )
    }

    fn and_bool(left: &str, right: &str) -> String {
        app(AND_BOOL, &[left.to_owned(), right.to_owned()])
    }

    fn gt(left: &str, right: &str) -> String {
        app(
            "Lbl'Unds-GT-'Int'Unds'",
            &[left.to_owned(), right.to_owned()],
        )
    }

    /// `<k> K(A) </k> <bus> B(V) </bus>` with the predicates `predicates`.
    fn pattern(predicates: &[String]) -> String {
        let k = app(K, &[app("Lblf", &[int("VarA")])]);
        let bus = app(BUS, &[app("Lblg", &[int("VarV")])]);
        let mut arguments = vec![app(TOP, &[k, bus])];
        arguments.extend(predicates.iter().cloned());
        if predicates.is_empty() {
            arguments.push(r"\top{SortGeneratedTopCell{}}()".to_owned());
        }
        format!(
            r"\and{{SortGeneratedTopCell{{}}}}({})",
            arguments.join(", ")
        )
    }

    #[test]
    fn a_conjunction_splits_into_its_operands_and_each_predicate_is_one() {
        let a = gt(&int("VarA"), r#"\dv{SortInt{}}("0")"#);
        let v = gt(&int("VarV"), r#"\dv{SortInt{}}("1")"#);
        let both = gt(&int("VarV"), &int("VarA"));
        // One predicate whose term is a conjunction of three, left-nested.
        let one = lowered(&pattern(&[holds(&and_bool(&and_bool(&a, &v), &both))]), &[]);
        let parts = Parts::of(&one, &table(), &BTreeSet::new());
        assert_eq!(
            parts
                .conjuncts
                .iter()
                .map(|c| c.term.to_string())
                .collect::<Vec<_>>(),
            [a.clone(), v.clone(), both.clone()]
        );
        assert_eq!(parts.conjuncts[2].variables, ["VarA", "VarV"]);
        // Separate predicates, as the compiler writes them without BOOL's conjunction.
        let separate = lowered(&pattern(&[holds(&a), holds(&v), holds(&both)]), &[]);
        let split = Parts::of(&separate, &table(), &BTreeSet::new());
        assert_eq!(
            split
                .conjuncts
                .iter()
                .map(|c| c.term.to_string())
                .collect::<Vec<_>>(),
            [a.clone(), v.clone(), both.clone()]
        );
        // The cells: <k> and <bus>, in pre-order; <k>'s A goes with the conjuncts naming A.
        assert_eq!(
            parts
                .cells
                .iter()
                .map(|c| c.label.as_str())
                .collect::<Vec<_>>(),
            ["<k>", "<bus>"]
        );
        assert_eq!(parts.cells[0].dependent, [0, 2]);
        assert_eq!(parts.cells[1].dependent, [1, 2]);
        // A variable an earlier step carries in is bound outside the cell.
        let carried = ["VarA".to_owned()].into_iter().collect();
        assert_eq!(
            Parts::of(&one, &table(), &carried).cells[0].dependent,
            Vec::<usize>::new()
        );
        // Without <k> and the conjuncts that go with it: the fresh variable in its place, and the
        // one conjunct left as the predicate.
        let dropped = parts.cells[0].dependent.iter().copied().collect();
        let derived = parts.derived(&one, Some(0), &dropped).unwrap();
        let fresh = format!("{FRESH_PREFIX}0");
        assert_eq!(
            derived.target.to_string(),
            pattern(&[holds(&v)]).replace(
                &app(K, &[app("Lblf", &[int("VarA")])]),
                &format!("{fresh}:SortKCell{{}}")
            )
        );
        assert!(derived.generated.contains(&fresh) && derived.minted.contains(&fresh));
        assert_ne!(derived.digest, one.digest);
        // Without the middle conjunct: the other two conjoined again.
        let middle = parts
            .derived(&one, None, &[1].into_iter().collect())
            .unwrap();
        assert_eq!(
            middle.target.to_string(),
            pattern(&[holds(&and_bool(&a, &both))])
        );
        // Without every conjunct: `\top`.
        let none = parts
            .derived(&one, None, &[0, 1, 2].into_iter().collect())
            .unwrap();
        assert_eq!(none.target.to_string(), pattern(&[]));
        // Separate predicates: the dropped one is gone, the others kept as they were.
        let second = split
            .derived(&separate, None, &[1].into_iter().collect())
            .unwrap();
        assert_eq!(
            second.target.to_string(),
            pattern(&[holds(&a), holds(&both)])
        );
    }

    #[test]
    fn a_minted_content_is_no_part_and_leaving_every_part_out_is_vacuous() {
        // <k> _Gen0 </k> <bus> g(V) </bus>: only <bus> is a part.
        let gen0 = "Var'Unds'Gen0:SortK{}".to_owned();
        let text = format!(
            r"\and{{SortGeneratedTopCell{{}}}}({}, \top{{SortGeneratedTopCell{{}}}}())",
            app(
                TOP,
                &[app(K, &[gen0]), app(BUS, &[app("Lblg", &[int("VarV")])])]
            )
        );
        let only_bus = lowered(&text, &["Var'Unds'Gen0"]);
        let parts = Parts::of(&only_bus, &table(), &BTreeSet::new());
        assert_eq!(
            parts
                .cells
                .iter()
                .map(|c| c.label.as_str())
                .collect::<Vec<_>>(),
            ["<bus>"]
        );
        assert!(!vacuous(&only_bus, &table()));
        // <bus> replaced by a fresh variable: every cell's content is a distinct variable, no
        // condition.
        let fresh = format!("{FRESH_PREFIX}0:SortBusCell{{}}");
        let text = format!(
            r"\and{{SortGeneratedTopCell{{}}}}({}, \top{{SortGeneratedTopCell{{}}}}())",
            app(TOP, &[app(K, &["Var'Unds'Gen0:SortK{}".to_owned()]), fresh])
        );
        assert!(vacuous(&lowered(&text, &["Var'Unds'Gen0"]), &table()));
        // A variable twice is a constraint.
        let twice = format!(
            r"\and{{SortGeneratedTopCell{{}}}}({}, \top{{SortGeneratedTopCell{{}}}}())",
            app(
                TOP,
                &[
                    app(K, &["VarX:SortK{}".to_owned()]),
                    app(BUS, &["VarX:SortK{}".to_owned()])
                ]
            )
        );
        assert!(!vacuous(&lowered(&twice, &[]), &table()));
    }
}
