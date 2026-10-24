//! The written meanings of the hooks the evaluator applies before any equation, and the root
//! pairs of the equations at their symbols with them.
//!
//! The simplifier evaluates a hooked application by its builtin first, and applies the symbol's
//! executable equations only where the builtin gives no value (`builtin::evaluates`). An equation
//! at such a symbol is still an axiom: `M_NF` interprets the symbol through the builtin wherever
//! the builtin gives a value, and must satisfy the equation there. The obligation is a root
//! critical pair between the equation and the builtin's steps, once those steps are written as
//! equations: the hook's *written meaning*, a fixed table of identities of the builtin below,
//! independent of the definition. Each entry satisfies, from the meaning of the hook alone:
//!
//! - **truth**: each equation is an identity of the builtin's function on all normal-form
//!   arguments where the builtin is defined, definedness included (where the builtin is
//!   `\bottom`, so is the right-hand side), so pairing with it reads nothing as true beyond what
//!   the check already reads (the hooks' semantics, `CheckScope::All`);
//! - **coverage**: every step the builtin takes on normal-form arguments, also on arguments that
//!   are not literals (`BOOL.and(X, false)`, `KEQUAL.ite` on a literal condition and any branches),
//!   is an instance of some left-hand side whose `requires` holds there, and its right-hand side
//!   evaluates by builtin steps to the builtin's result, so the pairs cover every peak of a builtin
//!   step and an equation step.
//!
//! Each entry has a property test against a model of its hook (`builtin/hook_models/meanings.rs`).
//!
//! A written meaning is built at the symbol of the equation it is paired with: its sort arguments
//! and argument sorts are that equation's, and the other hooks it names are found by hook name and
//! signature among the definition's symbols ([`HookSymbols`]). A hook with no table entry, or whose
//! entry names a hook the definition does not declare at the needed signature, has no written
//! meaning there, and each executable equation at it is reported (`UnmodelledHook`).

use std::{collections::BTreeMap, sync::Arc};

use k_rust_kore::names::BuiltinSort;

use crate::{
    definition::BackendDefinition,
    rule::{Concreteness, Predicate, RewriteRule, RuleAttributes, RuleOrigin, RuleRhs, make_rule},
    term::{DomainKind, Name, Sort, Symbol, Term, TermKind, Variable},
};

use super::collapse_conjunctions;

/// The definition's hooked symbols without sort parameters, by hook, in name order.
pub(crate) struct HookSymbols<'d> {
    definition: &'d BackendDefinition,
    by_hook: BTreeMap<&'d str, Vec<&'d Arc<Symbol>>>,
}

impl<'d> HookSymbols<'d> {
    pub(crate) fn of(definition: &'d BackendDefinition) -> Self {
        let mut by_hook = BTreeMap::<&str, Vec<&Arc<Symbol>>>::new();
        for symbol in definition.symbols().values() {
            if let Some(hook) = symbol.attributes.hook.as_deref()
                && symbol.sort_variables.is_empty()
            {
                by_hook.entry(hook).or_default().push(symbol);
            }
        }
        Self {
            definition,
            by_hook,
        }
    }

    /// A symbol carrying `hook` with exactly the argument sorts `arguments` and the result sort
    /// `result`, the first by name among every such candidate, when the evaluator applies `hook`
    /// (`builtin::evaluates`). A helper of a written meaning must denote the builtin itself: a
    /// symbol whose hook takes no builtin step means whatever the definition's equations make it,
    /// which no fixed identity of a builtin may read. Every candidate with the signature denotes
    /// the builtin at it, so any of them states the same identity.
    fn find(&self, hook: &str, arguments: &[Sort], result: Sort) -> Option<Arc<Symbol>> {
        if !crate::builtin::evaluates(hook) {
            return None;
        }
        self.by_hook.get(hook)?.iter().find_map(|symbol| {
            (symbol.argument_sorts == arguments && symbol.result_sort == result)
                .then(|| Arc::clone(symbol))
        })
    }
}

/// What the table says of an equation's hook at its symbol.
pub(crate) enum Meaning {
    /// The table has no entry for the hook.
    Unwritten,
    /// The entry names a hook, sort or literal the definition does not provide at the needed
    /// signature.
    Unbuildable,
    /// The written meaning, as equations at the equation's symbol.
    Built(Vec<Arc<RewriteRule>>),
}

/// The hooks the table writes a meaning for.
pub(crate) const WRITTEN: [&str; 22] = [
    "BOOL.not",
    "BOOL.and",
    "BOOL.andThen",
    "BOOL.or",
    "BOOL.orElse",
    "BOOL.xor",
    "BOOL.ne",
    "BOOL.implies",
    "KEQUAL.ite",
    "KEQUAL.ne",
    "INT.ne",
    "INT.min",
    "INT.ediv",
    "INT.bitRange",
    "INT.signExtendBitRange",
    "STRING.ne",
    "STRING.le",
    "STRING.gt",
    "STRING.ge",
    "STRING.countAllOccurrences",
    "STRING.replaceAll",
    "SET.union",
];

/// The written meaning of `hook` at the symbol of `lhs`, the left-hand side of an executable
/// equation rooted at a symbol carrying `hook`.
pub(crate) fn meaning(symbols: &HookSymbols<'_>, hook: &str, lhs: &Term) -> Meaning {
    if !WRITTEN.contains(&hook) {
        return Meaning::Unwritten;
    }
    let root = collapse_conjunctions(lhs);
    let TermKind::Application {
        symbol,
        sort_arguments,
        arguments,
    } = root.kind()
    else {
        return Meaning::Unbuildable;
    };
    let mut builder = Builder {
        symbols,
        hook,
        symbol: Arc::clone(symbol),
        sort_arguments: sort_arguments.as_ref().to_vec(),
        arguments: arguments.iter().map(Term::sort).collect(),
        result: root.sort(),
        rules: Vec::new(),
    };
    match builder.build() {
        Some(()) => Meaning::Built(builder.rules.into_iter().map(Arc::new).collect()),
        None => Meaning::Unbuildable,
    }
}

struct Builder<'s, 'd> {
    symbols: &'s HookSymbols<'d>,
    hook: &'s str,
    symbol: Arc<Symbol>,
    sort_arguments: Vec<Sort>,
    /// The argument sorts of the paired equation's root, and its result sort.
    arguments: Vec<Sort>,
    result: Sort,
    rules: Vec<RewriteRule>,
}

impl Builder<'_, '_> {
    fn definition(&self) -> &BackendDefinition {
        self.symbols.definition
    }

    /// The variable `name` at the sort of argument `index` (the check renames a written meaning
    /// apart from the equation it is paired with, as any second equation).
    fn variable(&self, name: &str, index: usize) -> Option<Term> {
        let sort = *self.arguments.get(index)?;
        Some(Term::variable(Variable::new(
            format!("HookMeaning{name}"),
            sort,
        )))
    }

    /// The hooked symbol applied to `arguments` at the paired equation's sort arguments.
    fn own(&self, arguments: Vec<Term>) -> Term {
        Term::application(
            Arc::clone(&self.symbol),
            self.sort_arguments.clone(),
            arguments,
        )
    }

    /// `hook` applied to `arguments`, through a symbol of the definition with their sorts and the
    /// result sort `result` whose hook the evaluator applies ([`HookSymbols::find`]).
    fn call(&self, hook: &str, arguments: Vec<Term>, result: Sort) -> Option<Term> {
        let sorts = arguments.iter().map(Term::sort).collect::<Vec<_>>();
        let symbol = self.symbols.find(hook, &sorts, result)?;
        Some(Term::application(symbol, Vec::<Sort>::new(), arguments))
    }

    /// The domain value `text` of `sort`, when the sort's domain kind is `kind`.
    fn literal(&self, sort: Sort, kind: DomainKind, text: &str) -> Option<Term> {
        (self.definition().domain_kind(&sort) == Some(kind))
            .then(|| self.definition().domain_value(sort, text).ok())
            .flatten()
    }

    /// The sort of the Booleans the comparison builtins give their values in.
    fn booleans(&self) -> Option<Sort> {
        let sort = Sort::builtin(BuiltinSort::Bool);
        (self.definition().domain_kind(&sort) == Some(DomainKind::Bool)).then_some(sort)
    }

    fn boolean(&self, sort: Sort, value: bool) -> Option<Term> {
        self.literal(sort, DomainKind::Bool, if value { "true" } else { "false" })
    }

    fn integer(&self, sort: Sort, value: i64) -> Option<Term> {
        self.literal(sort, DomainKind::Int, &value.to_string())
    }

    /// The condition that `term`, of a sort of the Booleans, is `true`.
    fn holds(&self, term: Term) -> Option<Predicate> {
        let truth = self.boolean(term.sort(), true)?;
        Some(Predicate::Equals(term, truth))
    }

    /// Record the equation `lhs = rhs requires requires`, numbered from 1 in the table's order.
    fn equation(&mut self, lhs: Term, rhs: Term, requires: Vec<Predicate>) {
        let index = self.rules.len() + 1;
        let attributes = RuleAttributes {
            priority: 50,
            label: Some(format!("{} meaning {index}", self.hook)),
            unique_id: format!("hook-meaning:{}:{index}", self.hook),
            simplification: false,
            preserves_definedness: false,
            concreteness: Concreteness::Unconstrained,
            smt_lemma: false,
            executable: true,
            origins: vec![RuleOrigin {
                source: None,
                location: None,
                sentence: None,
            }],
            overload: None,
        };
        self.rules.push(make_rule(
            lhs,
            RuleRhs::Term(rhs),
            requires,
            Vec::new(),
            attributes,
            Default::default(),
            None,
        ));
    }

    /// The table. `None` when an entry cannot be built in this definition.
    fn build(&mut self) -> Option<()> {
        // A symbol hooked at another arity than the hook's is no application of the builtin
        // (it raises an arity error and takes no step), and gets no written meaning.
        let arity = match self.hook {
            "BOOL.not" => 1,
            "KEQUAL.ite" | "INT.bitRange" | "INT.signExtendBitRange" | "STRING.replaceAll" => 3,
            _ => 2,
        };
        if self.arguments.len() != arity {
            return None;
        }
        match self.hook {
            "BOOL.not" => {
                let sort = *self.arguments.first()?;
                for value in [true, false] {
                    let lhs = self.own(vec![self.boolean(sort, value)?]);
                    let rhs = self.boolean(self.result, !value)?;
                    self.equation(lhs, rhs, Vec::new());
                }
            }
            // On normal-form arguments the short-circuit makes no difference: conjunction.
            "BOOL.and" | "BOOL.andThen" => self.absorbing(false)?,
            "BOOL.or" | "BOOL.orElse" => self.absorbing(true)?,
            "BOOL.xor" | "BOOL.ne" => self.table(|left, right| left != right)?,
            "BOOL.implies" => {
                // implies(false, B) = true, implies(true, true) = true, implies(true, false) = false.
                let (left, right) = (*self.arguments.first()?, *self.arguments.get(1)?);
                let lhs = self.own(vec![self.boolean(left, false)?, self.variable("B", 1)?]);
                let rhs = self.boolean(self.result, true)?;
                self.equation(lhs, rhs, Vec::new());
                for value in [true, false] {
                    let lhs =
                        self.own(vec![self.boolean(left, true)?, self.boolean(right, value)?]);
                    let rhs = self.boolean(self.result, value)?;
                    self.equation(lhs, rhs, Vec::new());
                }
            }
            "KEQUAL.ite" => {
                // ite(true, A, B) = A, ite(false, A, B) = B: selection by a literal condition,
                // whatever the branches.
                let condition = *self.arguments.first()?;
                for value in [true, false] {
                    let (then, otherwise) = (self.variable("A", 1)?, self.variable("B", 2)?);
                    let lhs = self.own(vec![
                        self.boolean(condition, value)?,
                        then.clone(),
                        otherwise.clone(),
                    ]);
                    self.equation(lhs, if value { then } else { otherwise }, Vec::new());
                }
            }
            // ne(X, Y) = notBool eq(X, Y): each hook's `ne` is the complement of its `eq` on
            // defined operands (the builtins of `KEQUAL.ne` and `INT.ne` negate the very
            // decision of their `eq`, syntactically equal operands included).
            "KEQUAL.ne" => self.complement("KEQUAL.eq")?,
            "INT.ne" => self.complement("INT.eq")?,
            "STRING.ne" => self.complement("STRING.eq")?,
            "INT.min" => {
                // min(X, Y) = X requires X <Int Y; min(X, Y) = Y requires X >=Int Y.
                let (x, y) = (self.variable("X", 0)?, self.variable("Y", 1)?);
                let booleans = self.booleans()?;
                let less = self.call("INT.lt", vec![x.clone(), y.clone()], booleans)?;
                let at_least = self.call("INT.ge", vec![x.clone(), y.clone()], booleans)?;
                let lhs = self.own(vec![x.clone(), y.clone()]);
                let (less, at_least) = (self.holds(less)?, self.holds(at_least)?);
                self.equation(lhs.clone(), x, vec![less]);
                self.equation(lhs, y, vec![at_least]);
            }
            "INT.ediv" => {
                // ediv(X, Y) = (X -Int emod(X, Y)) tdiv Y: X - (X emod Y) is a multiple of Y, so
                // truncating division is exact and gives the Euclidean quotient; for Y = 0 both
                // sides are `\bottom` (emod and tdiv by 0).
                let (x, y) = (self.variable("X", 0)?, self.variable("Y", 1)?);
                let int = self.result;
                let modulus = self.call("INT.emod", vec![x.clone(), y.clone()], int)?;
                let difference = self.call("INT.sub", vec![x.clone(), modulus], int)?;
                let rhs = self.call("INT.tdiv", vec![difference, y.clone()], int)?;
                let lhs = self.own(vec![x, y]);
                self.equation(lhs, rhs, Vec::new());
            }
            "INT.bitRange" => {
                // bitRange(I, IDX, LEN) = (I >>Int IDX) emod (1 <<Int LEN): the LEN bits of I
                // from IDX, unsigned; a negative IDX or LEN is `\bottom` on both sides (a shift by
                // a negative amount is undefined).
                let (value, index, length) = (
                    self.variable("I", 0)?,
                    self.variable("IDX", 1)?,
                    self.variable("LEN", 2)?,
                );
                let rhs = self.bit_range(&value, &index, &length)?;
                let lhs = self.own(vec![value, index, length]);
                self.equation(lhs, rhs, Vec::new());
            }
            "INT.signExtendBitRange" => {
                // signExtendBitRange(I, IDX, LEN) = (bitRange(I, IDX, LEN) +Int H) emod
                // (1 <<Int LEN) -Int H, H = 1 <<Int (LEN -Int 1): the same bits read as a
                // LEN-bit two's-complement number; `\bottom` on both sides for a negative IDX or
                // a LEN below 1.
                let int = self.result;
                let (value, index, length) = (
                    self.variable("I", 0)?,
                    self.variable("IDX", 1)?,
                    self.variable("LEN", 2)?,
                );
                let bits = self.call(
                    "INT.bitRange",
                    vec![value.clone(), index.clone(), length.clone()],
                    int,
                )?;
                let one = self.integer(self.result, 1)?;
                let below = self.call("INT.sub", vec![length.clone(), one.clone()], int)?;
                let half = self.call("INT.shl", vec![one.clone(), below], int)?;
                let modulus = self.call("INT.shl", vec![one, length.clone()], int)?;
                let raised = self.call("INT.add", vec![bits, half.clone()], int)?;
                let residue = self.call("INT.emod", vec![raised, modulus], int)?;
                let rhs = self.call("INT.sub", vec![residue, half], int)?;
                let lhs = self.own(vec![value, index, length]);
                self.equation(lhs, rhs, Vec::new());
            }
            // Byte-lexicographic order is a strict total order: le(X, Y) = notBool lt(Y, X),
            // gt(X, Y) = lt(Y, X), ge(X, Y) = notBool lt(X, Y).
            "STRING.le" => self.ordered(true, true)?,
            "STRING.gt" => self.ordered(true, false)?,
            "STRING.ge" => self.ordered(false, true)?,
            "STRING.countAllOccurrences" => self.count()?,
            "STRING.replaceAll" => self.replace_all()?,
            "SET.union" => {
                // union(X, Y) = X (Y -Set X): X ∪ Y is the disjoint union of X and Y \ X.
                let (left, right) = (self.variable("X", 0)?, self.variable("Y", 1)?);
                let set = self.result;
                let rest = self.call("SET.difference", vec![right.clone(), left.clone()], set)?;
                let rhs = self.call("SET.concat", vec![left.clone(), rest], set)?;
                let lhs = self.own(vec![left, right]);
                self.equation(lhs, rhs, Vec::new());
            }
            _ => return None,
        }
        Some(())
    }

    /// `op(absorbing, B) = absorbing`, `op(B, absorbing) = absorbing`, `op(!absorbing,
    /// !absorbing) = !absorbing`: conjunction (`absorbing = false`) or disjunction.
    fn absorbing(&mut self, absorbing: bool) -> Option<()> {
        let (left, right) = (*self.arguments.first()?, *self.arguments.get(1)?);
        let lhs = self.own(vec![self.boolean(left, absorbing)?, self.variable("B", 1)?]);
        let value = self.boolean(self.result, absorbing)?;
        self.equation(lhs, value.clone(), Vec::new());
        let lhs = self.own(vec![
            self.variable("B", 0)?,
            self.boolean(right, absorbing)?,
        ]);
        self.equation(lhs, value, Vec::new());
        let lhs = self.own(vec![
            self.boolean(left, !absorbing)?,
            self.boolean(right, !absorbing)?,
        ]);
        let rhs = self.boolean(self.result, !absorbing)?;
        self.equation(lhs, rhs, Vec::new());
        Some(())
    }

    /// The four ground rows of a Boolean operation.
    fn table(&mut self, operation: impl Fn(bool, bool) -> bool) -> Option<()> {
        let (left, right) = (*self.arguments.first()?, *self.arguments.get(1)?);
        for first in [false, true] {
            for second in [false, true] {
                let lhs = self.own(vec![
                    self.boolean(left, first)?,
                    self.boolean(right, second)?,
                ]);
                let rhs = self.boolean(self.result, operation(first, second))?;
                self.equation(lhs, rhs, Vec::new());
            }
        }
        Some(())
    }

    /// `ne(X, Y) = notBool eq(X, Y)`, `eq` the hook `equal` at the same argument sorts.
    fn complement(&mut self, equal: &str) -> Option<()> {
        let (x, y) = (self.variable("X", 0)?, self.variable("Y", 1)?);
        let equal = self.call(equal, vec![x.clone(), y.clone()], self.result)?;
        let rhs = self.call("BOOL.not", vec![equal], self.result)?;
        let lhs = self.own(vec![x, y]);
        self.equation(lhs, rhs, Vec::new());
        Some(())
    }

    /// `X <String Y` (or `Y <String X` when `swapped`), negated when `negated`.
    fn ordered(&mut self, swapped: bool, negated: bool) -> Option<()> {
        let (x, y) = (self.variable("X", 0)?, self.variable("Y", 1)?);
        let operands = if swapped {
            vec![y.clone(), x.clone()]
        } else {
            vec![x.clone(), y.clone()]
        };
        let mut rhs = self.call("STRING.lt", operands, self.result)?;
        if negated {
            rhs = self.call("BOOL.not", vec![rhs], self.result)?;
        }
        let lhs = self.own(vec![x, y]);
        self.equation(lhs, rhs, Vec::new());
        Some(())
    }

    /// `(I >>Int IDX) emod (1 <<Int LEN)` at the result sort.
    fn bit_range(&self, value: &Term, index: &Term, length: &Term) -> Option<Term> {
        let int = self.result;
        let shifted = self.call("INT.shr", vec![value.clone(), index.clone()], int)?;
        let one = self.integer(self.result, 1)?;
        let modulus = self.call("INT.shl", vec![one, length.clone()], int)?;
        self.call("INT.emod", vec![shifted, modulus], int)
    }

    /// The condition `T =/=String ""`.
    fn nonempty(&self, target: &Term) -> Option<Predicate> {
        let empty = self.literal(target.sort(), DomainKind::String, "")?;
        let differs = self.call("STRING.ne", vec![target.clone(), empty], self.booleans()?)?;
        self.holds(differs)
    }

    /// `replaceAll(S, T, R)`, `S` with each non-overlapping occurrence of a nonempty `T` found
    /// from the left replaced by `R` (where `T` is `""` the builtin gives no value, and no
    /// equation is written): `replaceAll(S, T, R) = S requires find(S, T, 0) <Int 0 andBool T
    /// =/=String ""`, and `replaceAll(S, T, R) = substr(S, 0, find(S, T, 0)) +String R +String
    /// replaceAll(substr(S, find(S, T, 0) +Int length(T), length(S)), T, R) requires
    /// find(S, T, 0) >=Int 0 andBool T =/=String ""`: the first occurrence is replaced and the search goes on
    /// after it (non-overlapping), with valid `substr` indices. Only evaluated builtins and the
    /// hooked symbol itself occur.
    fn replace_all(&mut self) -> Option<()> {
        let (source, target, replacement) = (
            self.variable("S", 0)?,
            self.variable("T", 1)?,
            self.variable("R", 2)?,
        );
        let int = Sort::builtin(BuiltinSort::Int);
        let string = self.result;
        let zero = self.integer(int, 0)?;
        let found = self.call(
            "STRING.find",
            vec![source.clone(), target.clone(), zero.clone()],
            int,
        )?;
        let booleans = self.booleans()?;
        let absent = self.call("INT.lt", vec![found.clone(), zero.clone()], booleans)?;
        let present = self.call("INT.ge", vec![found.clone(), zero.clone()], booleans)?;
        let nonempty = self.nonempty(&target)?;
        let lhs = self.own(vec![source.clone(), target.clone(), replacement.clone()]);
        let (absent, present) = (self.holds(absent)?, self.holds(present)?);
        self.equation(lhs.clone(), source.clone(), vec![absent, nonempty.clone()]);
        let before = self.call(
            "STRING.substr",
            vec![source.clone(), zero, found.clone()],
            string,
        )?;
        let target_length = self.call("STRING.length", vec![target.clone()], int)?;
        let source_length = self.call("STRING.length", vec![source.clone()], int)?;
        let after = self.call("INT.add", vec![found, target_length], int)?;
        let rest = self.call("STRING.substr", vec![source, after, source_length], string)?;
        let replaced = self.own(vec![rest, target, replacement.clone()]);
        let head = self.call("STRING.concat", vec![before, replacement], string)?;
        let rhs = self.call("STRING.concat", vec![head, replaced], string)?;
        self.equation(lhs, rhs, vec![present, nonempty]);
        Some(())
    }

    /// `count(S, T)`, the non-overlapping occurrences of a nonempty `T` in `S` found from the
    /// left (where `T` is `""` the builtin gives no value, and no equation is written):
    /// `count(S, T) = 0 requires find(S, T, 0) <Int 0 andBool T =/=String ""`, and
    /// `count(S, T) = 1 +Int count(substr(S, find(S, T, 0) +Int length(T), length(S)), T)
    /// requires find(S, T, 0) >=Int 0 andBool T =/=String ""`; the `substr` indices are valid
    /// (an occurrence ends within `S`).
    fn count(&mut self) -> Option<()> {
        let (source, target) = (self.variable("S", 0)?, self.variable("T", 1)?);
        let int = self.result;
        let zero = self.integer(int, 0)?;
        let one = self.integer(int, 1)?;
        let found = self.call(
            "STRING.find",
            vec![source.clone(), target.clone(), zero.clone()],
            int,
        )?;
        let booleans = self.booleans()?;
        let absent = self.call("INT.lt", vec![found.clone(), zero.clone()], booleans)?;
        let present = self.call("INT.ge", vec![found.clone(), zero.clone()], booleans)?;
        let nonempty = self.nonempty(&target)?;
        let lhs = self.own(vec![source.clone(), target.clone()]);
        let (absent, present) = (self.holds(absent)?, self.holds(present)?);
        self.equation(lhs.clone(), zero, vec![absent, nonempty.clone()]);
        let target_length = self.call("STRING.length", vec![target.clone()], int)?;
        let source_length = self.call("STRING.length", vec![source.clone()], int)?;
        let after = self.call("INT.add", vec![found, target_length], int)?;
        let rest = self.call(
            "STRING.substr",
            vec![source.clone(), after, source_length],
            source.sort(),
        )?;
        let counted = self.own(vec![rest, target]);
        let rhs = self.call("INT.add", vec![one, counted], int)?;
        self.equation(lhs, rhs, vec![present, nonempty]);
        Some(())
    }
}

/// The hook of the symbol an executable equation is rooted at, when that symbol carries one.
pub(super) fn root_hook(lhs: &Term) -> Option<Name> {
    match collapse_conjunctions(lhs).kind() {
        TermKind::Application { symbol, .. } => symbol.attributes.hook.as_deref().map(Name::from),
        _ => None,
    }
}
