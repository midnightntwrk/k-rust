//! What a left-hand side's syntax says about the values it denotes.
//!
//! An equation `l = r` constrains the value every instance of `l` denotes. The instance-normal
//! scan and the simplifier's certificate conclude from a syntactic fact about `l` (it does not
//! unify with a subject, equation matching fails on it) that the equation does not apply to the
//! subject's value. Both read the evaluator's normal forms as distinct values. That reading
//! needs, for each equation, that no instance of a proper subterm of `l` is rewritten: otherwise
//! an instance of `l` has a reduct below its root (`w(h(1))` from `w(h(3))` under
//! `h(3) = h(1)`) that is a normal form the equation never matches, although the equation equates
//! its value with the right-hand side's. When the arguments of `l` are normal on every instance
//! ([`BackendDefinition::pattern_arguments_normal`]) there is no such reduct, and the syntactic
//! fact is a fact about values.
//!
//! For any other equation, the question is whether an instance of `l` can have the subject as a
//! reduct below its root, that is, whether each argument of an instance can reduce to the
//! subject's argument. That is ruled out at one argument position when no reduct of the pattern's
//! argument can have the subject argument's root ([`BackendDefinition::misses_values`]). A
//! reduct keeps the root of the term it comes from until an equation rewrites it at the root,
//! which gives the root of that equation's right-hand side, and so on ([`PatternFacts`]); a
//! right-hand side with an open root (a variable, a function application) leaves the roots
//! unbounded. This keeps FUN's overloaded application `P1 P2`, whose overload equation rewrites
//! some instances to an injection from `Val`, apart from an injected `Name`.
//!
//! Neither test covers the normal forms an equation identifies through its *overlaps*. A normal
//! form `s` is a value distinct from every other normal form when every term that reduces to `s`
//! has `s` as its only normal form (each term of a conversion between two normal forms then
//! reduces to both). A term with two normal forms contains a peak of two steps that do not
//! meet, and such a peak (steps at disjoint positions, or inside a variable's value, meet) is an
//! overlap at an instance `lσ` of some equation: its root step against another equation's root
//! step, or against a step at a non-variable position below the root. Every reduct of an
//! overlapped instance, through the equation's own root step as much as through the other step,
//! may be identified with another normal form; a reduct of an instance with no other step is
//! not identified through it, since there the equation's root step is the only step. So each
//! equation is also set aside only where no reduct of an overlapped instance of `l` is the
//! subject ([`BackendDefinition::overlaps_miss`], computed with the pattern facts). Peaks that
//! meet identify nothing and are not counted: an overload equation's step, which matching reads
//! through, and a peak of two equations without an `ensures` whose two sides meet under a few
//! steps of equations without a `requires` or an `ensures`. An equation with an `ensures`
//! identifies its instance with `\bottom` where the `ensures` fails, which pins whatever decides
//! it; no reduct shows that, so the reducts of an overlapped instance that such an equation may
//! rewrite are not bounded.
//!
//! The scan of an application asks the equations offered at its index, so it sees the overlaps of
//! equations with that head. The certificate assumes that a peak at an instance of an equation of
//! another head, one of whose sides (with its `ensures`) has the application's head, meets, and
//! that so do peaks at terms that equation matching matches up to the subsort or overload axioms
//! without being syntactic instances of `l`: under `g(5) = c1; f(c1) = k(0); f(g(X)) = mk(1 /Int
//! 0)`, `k(0)` is undefined while no `k` equation exists. It also reads a peak only for the normal
//! forms it identifies, not for what it says about the values the equations of its two paths bind:
//! the variables range over values, so where the two paths do not meet, one of the bound values is
//! undefined (`h(q(3, Y)) = 1 /Int 0` and `h(X) = 3` at `h(q(3, c))` make `q(3, c)`, and so `g(d)`
//! under `q(I, X) = g(d)`, undefined, while the scan of `g(d)` sees no `h` equation). The
//! certificate assumes no peak that does not meet binds, in its two steps or in the steps its sides
//! take, a value in which the application occurs.
//!
//! Nor does the certificate read the equations of other heads for what they say about the
//! application's definedness without a peak. A total symbol is defined on defined arguments,
//! so an equation of a total head whose left-hand side holds the application below total
//! symbols, and whose right-hand side is undefined there, makes the application undefined:
//! `e(f(X)) = m(1 /Int 0)`, `e` an `anywhere` head declared `total`, makes `f(c)` undefined,
//! while the scan of `f(c)` sees no `f` equation. The certificate assumes no such equation
//! instance exists.
//!
//! Each assumption is made for every application the certificate decides, the application
//! itself and those it decides on the way (in the arguments of left-hand sides and in the
//! reducts it reads). An equation binds each argument of its head by membership in its argument
//! pattern, so where an argument pattern's instance is undefined the equation states nothing:
//! under `g(X, 3) = f(c)` and `g(k(d), 3) = m(2 /Int 0)`, which make `f(c)` undefined,
//! `g(g(f(c), 0), 1) = k(g(g(d, 2), 0))` identifies nothing, and reading `f(c)` there as a value
//! only counts an identification that is not there.
//!
//! The questions nest: deciding a left-hand side's argument decides the instance normality of
//! the terms its reducts build, whose own equations are decided the same way. Their depth is
//! bounded (`super::VALUE_QUESTIONS`, [`NARROWING_DEPTH`]), their breadth too
//! ([`REPRESENTATIVES`], [`REPRESENTATIVE_SIZE`]), and so is their work: each narrowing step is
//! taken from a budget of the outermost question (`super::SCAN_WORK`) and, while the facts are
//! computed, of the whole computation (`super::PATTERN_FACTS_WORK`). So is the nesting across
//! the rounds of the facts' computation, in which each round reads the previous round's stored
//! overlaps ([`OVERLAP_CHANGES`]). Past any bound the term read stands for any value, the
//! conservative answer.
//!
//! Narrowing ([`BackendDefinition::narrow`]) asks which right-hand sides an equation gives a
//! reduct of a pattern, by matching the equation's left-hand side against the pattern. It reads
//! that left-hand side by its values as well: a subterm's syntax counts only where the subterm's
//! instances are normal forms (every subterm of a normal-argument equation's left-hand side, and
//! otherwise a subterm shown normal); any other subterm is read through the reducts of its own
//! instances ([`BackendDefinition::narrow_through_values`]). Injections are compared up to the
//! subsort axioms, under which they compose: `inj{B,T}(t)` with `B < A` is the value
//! `inj{A,T}(inj{B,A}(t))`, an instance of `inj{A,T}(X:A)`.
//!
//! Each axiom quantifies its variables on its own, and so does the pattern being read. A term
//! these facts build from two of them (an overlapped instance whose bindings come from another
//! left-hand side, a reduct whose bindings come from the read term, a stored representative
//! narrowed against a left-hand side) must denote every instance of the combination, so its
//! variables are either the read term's or minted for that one use. [`hygiene`] is the only
//! place that makes such names: a term from a second source enters a built term only as an
//! [`Apart`] copy, a reduct only through a [`Completion`] of the narrowing's bindings, and a
//! term kept across uses only as a [`Stored`] term, which is read through a fresh copy.

mod hygiene;

use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
    sync::Arc,
};

use rustc_hash::{FxHashMap, FxHashSet};

use self::hygiene::{
    Apart, Completion, Stored, add_most_general, minted, renamed_from, shape_hash,
};
use super::{
    SCAN, Scan, ScanScope, ValueQuestion, bounds, compared_by_root, facts_work_spent, separated,
    sorts_differ, take_work, token, work_spent,
};
use crate::substitution::{Substitution, substitute};
use crate::{
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rule::{RewriteRule, RuleRhs, TermIndex, Theory, term_index},
    term::{
        FunctionType, HeadRole, Sort, SymbolType, Term, TermKind, Variable,
        head::{
            Fixed, Head, NormalForms, PatternReading, Shape, classify_pattern, classify_value,
            compare_roots,
        },
    },
};

/// Facts about the left-hand sides of a definition's function and simplification equations,
/// computed once per definition ([`pattern_facts`]).
#[derive(Clone, Debug)]
pub(crate) struct PatternFacts {
    /// The equations whose left-hand side has instance-normal immediate subterms, by address
    /// ([`BackendDefinition::pattern_arguments_normal`]).
    normal_rules: FxHashSet<usize>,
    /// The roots the reducts of a term can have besides its own, by the term's index: the
    /// right-hand sides of the equations indexed there, and transitively those indexed by their
    /// roots. `None` when some such right-hand side has an open root, or some such equation an
    /// `ensures` ([`BackendDefinition::value_representatives`]). An index with no equations
    /// has none besides the term's own root.
    value_roots: Arc<BTreeMap<TermIndex, Option<Vec<Stored>>>>,
    /// Some equation is indexed by a bare variable, so it may rewrite a term of any root to
    /// anything: no reduct's root is bounded.
    unbounded: bool,
    /// What the overlapped instances of each equation's left-hand side reach, by the equation's
    /// address ([`BackendDefinition::overlaps_miss`]); `None` before the first round has
    /// computed them, when every equation's are [`Overlaps::Unbounded`]. An equation without an
    /// entry (one headed by a function, or a bare variable) has unbounded ones too.
    overlaps: Option<Arc<FxHashMap<usize, Overlaps>>>,
    /// Which sorts' terms can hold which sorts' terms at an exposed position
    /// ([`BackendDefinition::exposed_misses`]).
    exposed: Arc<ExposedSorts>,
}

/// The sorts whose terms can occur at an exposed position (below total symbols only,
/// [`total_root`]) of a term of a sort: an edge from a total symbol's result sort to each
/// argument sort, and from a sort to each sort below it. The edges follow every total symbol,
/// not only constructors: a reduct can hold a total function's application (`m(sz(t))`,
/// `sz : A -> Int` total), and that application is undefined only when an argument is.
///
/// A sort-parametric symbol stands for each of its instantiations, and each gives the edges of
/// its instance. With a result sort of fixed name `R`, an argument sort variable can be any
/// sort, so `R` reaches every sort (`opaque`). With a sort variable `T` for its result, the
/// instance at `T := X` gives `X` an edge to each argument sort with `T := X`: an argument of a
/// fixed name `S` gives every sort an edge to `S` (`universal`; `ite{T}(Bool, T, T) : T` gives
/// every sort an edge to `Bool`), an argument `T` gives `X` an edge to itself, and an argument
/// sort variable other than `T` makes every sort reach every sort (`every`). A hooked sort
/// without domain values (a collection) reaches every sort too.
///
/// In a kompiled definition these true edges connect every pair of sorts: `ite` gives every
/// sort an edge to `Bool`, `_==K_` and the sort predicates `isS : K -> Bool` (all `total`) give
/// `Bool` one to `K`, and `kseq : KItem, K -> K` with the subsorts of `KItem` lead to every
/// user sort. There the gate cuts nothing, and only the reading of the representatives
/// themselves does.
#[derive(Debug, Default)]
struct ExposedSorts {
    edges: BTreeMap<crate::term::Name, BTreeSet<crate::term::Name>>,
    opaque: BTreeSet<crate::term::Name>,
    /// The sorts every sort has an edge to.
    universal: BTreeSet<crate::term::Name>,
    every: bool,
}

impl ExposedSorts {
    fn of(definition: &BackendDefinition) -> Self {
        let mut exposed = Self::default();
        for (name, info) in definition.sorts() {
            if info.hook.is_some() && !info.has_domain_values {
                exposed.opaque.insert(name.clone());
            }
        }
        for (sup, subs) in definition.sort_graph().closures() {
            exposed
                .edges
                .entry(sup.head().clone())
                .or_default()
                .extend(subs.iter().map(|sub| sub.head().clone()));
        }
        for symbol in definition.symbols().values() {
            // The sort injection `inj{From, To}` is read through the subsort edges.
            if symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Partial)
                || &*symbol.name == "inj"
            {
                continue;
            }
            let result = match &symbol.result_sort {
                Sort::Application { name, .. } => name,
                Sort::Variable(result) => {
                    for argument in &symbol.argument_sorts {
                        match argument {
                            Sort::Application { name, .. } => {
                                exposed.universal.insert(name.clone());
                            }
                            Sort::Variable(variable) if variable == result => {}
                            Sort::Variable(_) => exposed.every = true,
                        }
                    }
                    continue;
                }
            };
            for argument in &symbol.argument_sorts {
                match argument {
                    Sort::Application { name, .. } => {
                        exposed
                            .edges
                            .entry(result.clone())
                            .or_default()
                            .insert(name.clone());
                    }
                    Sort::Variable(_) => {
                        exposed.opaque.insert(result.clone());
                    }
                }
            }
        }
        exposed
    }

    /// Whether a term of sort `holder` can hold a term of sort `held` at an exposed position
    /// (itself included).
    fn may_hold(&self, holder: &Sort, held: &Sort) -> bool {
        let (Sort::Application { name: holder, .. }, Sort::Application { name: held, .. }) =
            (holder, held)
        else {
            return true;
        };
        if self.every {
            return true;
        }
        // Every sort, the holder included, has an edge to each universal target.
        let mut seen = BTreeSet::from([holder]);
        seen.extend(&self.universal);
        let mut pending = seen.iter().copied().collect::<Vec<_>>();
        while let Some(sort) = pending.pop() {
            if sort == held || self.opaque.contains(sort) {
                return true;
            }
            for next in self.edges.get(sort).into_iter().flatten() {
                if seen.insert(next) {
                    pending.push(next);
                }
            }
        }
        false
    }
}

/// What the instances of an equation's left-hand side that have a step besides the equation's
/// own root step reach ([`BackendDefinition::overlaps_miss`]).
#[derive(Clone, Debug, Eq, PartialEq)]
enum Overlaps {
    /// No instance of the left-hand side has another step.
    Absent,
    /// Terms that cover every reduct of every such instance, as the representatives of
    /// [`BackendDefinition::value_representatives`] cover the reducts of a pattern.
    Reaching(Arc<[Stored]>),
    /// The reducts are not bounded.
    Unbounded,
}

thread_local! {
    /// While [`pattern_facts`] computes the facts on this thread, the ones it has shown so far:
    /// [`BackendDefinition::pattern_arguments_normal`] answers from them, so the computation
    /// neither waits on the definition's facts nor reaches for an answer it has not derived.
    static APPROXIMATION: RefCell<Option<Rc<PatternFacts>>> = const { RefCell::new(None) };
}

/// The key of a term equation of the definition: its address in the definition's theory, which
/// the definition's clones share (`Arc`).
fn rule_key(rule: &RewriteRule) -> usize {
    std::ptr::from_ref(rule).addr()
}

impl BackendDefinition {
    /// Whether every immediate subterm of the left-hand side of `rule`, a function or
    /// simplification equation of this definition (the arguments of its root, the elements of
    /// a collection, the operand of an injection, the conjuncts of an `\and`), is a normal
    /// pattern ([`Self::normal_pattern`]); `true` for a variable left-hand side. `false` for a
    /// rule that is not one of the definition's own term equations (a renamed copy included):
    /// the answer is looked up by the rule's address, so a caller asks with the rule equation
    /// selection returned.
    ///
    /// Where it holds, every instance of the left-hand side (variables ranging over values)
    /// has normal arguments, and so does every instance of an instance-normal subject, so an
    /// instance of the left-hand side and an instance of the subject that denote the same value
    /// at the same root are the same term. Then the syntactic answers about the left-hand side
    /// (it does not unify with the subject; equation matching refutes it; it matches the subject
    /// only at the substitution decomposition finds) are answers about the values it denotes.
    ///
    /// Deciding a left-hand side argument scans the equations that could reach it, whose own
    /// exclusion asks this question about their left-hand sides. The answers are therefore
    /// computed once per definition, in rounds, by [`pattern_facts`]: no equation's answer rests
    /// on itself, and, since every question of a round reads the previous round's facts, the
    /// set does not depend on the order equations are asked in while the computation's
    /// `super::PATTERN_FACTS_WORK` budget lasts. Once it is spent, the equations asked later in
    /// that round get the conservative answer, so past the budget the set depends on that order
    /// (deterministically for a given definition), which loses precision only.
    pub(crate) fn pattern_arguments_normal(&self, rule: &RewriteRule) -> bool {
        let key = rule_key(rule);
        self.with_pattern_facts(|facts| facts.normal_rules.contains(&key))
    }

    /// Whether a failed match of the equation `equation` on `subject`, a ground term whose
    /// arguments the simplifier has evaluated, shows that the equation does not identify the
    /// subject's value with another normal form: its left-hand side's arguments are normal
    /// patterns, or its values miss the subject at some argument ([`Self::misses_values`]), and
    /// no overlapped instance of its left-hand side reaches the subject
    /// ([`Self::overlaps_miss`]); the simplifier's value certificate is the evidence for the
    /// subject's roots.
    pub(crate) fn failed_match_is_about_values(
        &self,
        equation: &RewriteRule,
        subject: &Term,
    ) -> bool {
        let roots = &mut crate::term::head::CertifiedOnly;
        (self.pattern_arguments_normal(equation) || {
            let _scope = ScanScope::enter();
            self.misses_values(&equation.lhs, subject, roots)
        }) && {
            let _scope = ScanScope::enter();
            self.overlaps_miss(equation, subject, roots)
        }
    }

    /// Whether no instance of the left-hand side `pattern` has `subject`, an application with the
    /// same root whose arguments are normal forms, as a reduct below the root, because at some
    /// argument position no reduct of the pattern's argument is the subject's argument
    /// ([`Self::values_apart`]). `subject_roots` fixes the roots of the subject's equation-head
    /// subterms. Positions are compared one at a time, so variables shared between positions are
    /// not followed: that only answers `false` more often. Reducts that leave the root, or come
    /// back to it through other equations' root steps, are the overlaps' part
    /// ([`Self::overlaps_miss`]).
    ///
    /// The question is answered `false` when [`super::VALUE_QUESTIONS`] are already open on the
    /// thread (`super::ValueQuestion`).
    pub(super) fn misses_values(
        &self,
        pattern: &Term,
        subject: &Term,
        subject_roots: &mut dyn NormalForms,
    ) -> bool {
        let Some(_question) = ValueQuestion::open() else {
            return false;
        };
        self.misses_values_at(pattern, subject, subject_roots)
    }

    fn misses_values_at(
        &self,
        pattern: &Term,
        subject: &Term,
        subject_roots: &mut dyn NormalForms,
    ) -> bool {
        match (pattern.kind(), subject.kind()) {
            (TermKind::And(left, right), _) => {
                self.misses_values_at(left, subject, subject_roots)
                    || self.misses_values_at(right, subject, subject_roots)
            }
            (
                TermKind::Application {
                    symbol: pattern_symbol,
                    arguments: pattern_arguments,
                    ..
                },
                TermKind::Application {
                    symbol: subject_symbol,
                    arguments: subject_arguments,
                    ..
                },
            ) if pattern_symbol.name == subject_symbol.name
                && pattern_arguments.len() == subject_arguments.len() =>
            {
                pattern_arguments
                    .iter()
                    .zip(subject_arguments)
                    .any(|(pattern, subject)| self.values_apart(pattern, subject, subject_roots))
            }
            _ => false,
        }
    }

    /// Whether no reduct of an *overlapped* instance of the left-hand side of `rule` is `subject`,
    /// a term whose root `subject_roots` must fix: one at which another step than the
    /// equation's own root step applies (a step at a non-variable position below the root, or
    /// another equation's root step). That is where an equation can identify two normal forms:
    /// at an instance with no other step, its root step is the only one, so the instance's
    /// normal forms are those of the right-hand side and nothing else; at an overlapped one, the
    /// two steps may lead to different normal forms, each of which the equation then identifies
    /// with the other, whichever path (the equation's own root step included) reaches it. The
    /// reducts are the definition's `Overlaps` of the equation ([`overlaps_of`], computed with
    /// the pattern facts); `false` when they are unbounded or past [`super::VALUE_QUESTIONS`].
    pub(super) fn overlaps_miss(
        &self,
        rule: &RewriteRule,
        subject: &Term,
        subject_roots: &mut dyn NormalForms,
    ) -> bool {
        let reaching = match self.previous_overlaps(rule) {
            Overlaps::Absent => return true,
            Overlaps::Unbounded => return false,
            Overlaps::Reaching(reaching) => reaching,
        };
        let Some(_question) = ValueQuestion::open() else {
            return false;
        };
        reaching.iter().all(|representative| {
            self.representative_misses(representative.fresh().term(), subject, subject_roots)
        })
    }

    /// Whether no reduct of an instance of `representative`, a term an equation may identify
    /// with another normal form, is `subject` or holds it at an exposed position (below total
    /// symbols only), `subject` being a term whose immediate subterms `subject_roots` must fix.
    /// The representative's root misses the subject when it is the subject's symbol and some
    /// pair of arguments is apart ([`Self::values_apart`]), or when it is another constructor,
    /// injection, collection, equation head or domain value (a reduct that changes the root is
    /// another representative); a function, residual or uninterpreted root, or a variable, does
    /// not. When the root is total ([`total_root`]), every argument's value must also miss the
    /// subject at an exposed position ([`Self::exposed_misses`]).
    ///
    /// The exposed positions count because a total symbol applied to defined arguments is
    /// defined: when the equation identifies `n(t)`, `n` total, with `\bottom`, `t` is undefined
    /// (`g(d) = k(e(g(j(c, d))))` beside `g(d) = m(1 /Int 0)`, with `k` a constructor and `e` a
    /// total equation head, make `g(j(c, d))` undefined). For a total head that is not a
    /// constructor, an identification with another normal form says nothing about `t`, but the
    /// representative does not record which of the two the other side is, so it is read as
    /// the identification with `\bottom`. Below a partial head the identification says nothing
    /// about the argument: the head itself may be undefined. A collection is read like a
    /// constructor, which only answers `false` more often.
    fn representative_misses(
        &self,
        representative: &Term,
        subject: &Term,
        subject_roots: &mut dyn NormalForms,
    ) -> bool {
        let TermKind::Application {
            symbol: subject_symbol,
            sort_arguments: subject_sorts,
            arguments: subject_arguments,
        } = subject.kind()
        else {
            return false;
        };
        let root_misses = match representative.kind() {
            TermKind::Application {
                symbol,
                sort_arguments,
                arguments,
            } if symbol.name == subject_symbol.name => {
                sort_arguments == subject_sorts
                    && arguments.len() == subject_arguments.len()
                    && arguments
                        .iter()
                        .zip(subject_arguments)
                        .any(|(pattern, subject)| {
                            self.values_apart(pattern, subject, subject_roots)
                        })
            }
            _ => matches!(
                representative.shape(),
                Shape::DomainValue
                    | Shape::Injection
                    | Shape::Collection(_)
                    | Shape::Application(HeadRole::FreeConstructor | HeadRole::EquationHead)
            ),
        };
        root_misses
            && (!total_root(representative)
                || token::every_immediate_subterm(representative, |argument| {
                    self.exposed_misses(argument, subject, subject_roots)
                }))
    }

    /// Whether the value of no instance of `argument`, an argument at an exposed position of a
    /// representative ([`Self::representative_misses`]), is `subject` or holds it at an exposed
    /// position: every representative of the argument's reducts
    /// ([`Self::value_representatives`]) misses it. `false` past [`super::VALUE_QUESTIONS`] (the
    /// question nests through the representatives' own exposed arguments) or when the
    /// representatives are not bounded.
    fn exposed_misses(
        &self,
        argument: &Term,
        subject: &Term,
        subject_roots: &mut dyn NormalForms,
    ) -> bool {
        if matches!(argument.kind(), TermKind::DomainValue { .. })
            || !self.with_pattern_facts(|facts| {
                facts.exposed.may_hold(&argument.sort(), &subject.sort())
            })
        {
            return true;
        }
        let Some(_question) = ValueQuestion::open() else {
            return false;
        };
        self.value_representatives(argument)
            .is_some_and(|representatives| {
                representatives.iter().all(|representative| {
                    self.representative_misses(representative, subject, subject_roots)
                })
            })
    }

    /// Whether no reduct of an instance of the pattern `pattern` is `subject`, a normal form whose
    /// root `subject_roots` must fix: no root a reduct can have
    /// ([`Self::value_representatives`]) leads to the subject ([`Self::representative_apart`]).
    fn values_apart(
        &self,
        pattern: &Term,
        subject: &Term,
        subject_roots: &mut dyn NormalForms,
    ) -> bool {
        if let TermKind::And(left, right) = pattern.kind() {
            return self.values_apart(left, subject, subject_roots)
                || self.values_apart(right, subject, subject_roots);
        }
        let Head::Fixed(subject_root) = classify_value(subject, subject_roots) else {
            return false;
        };
        self.value_representatives(pattern)
            .is_some_and(|representatives| {
                representatives.iter().all(|representative| {
                    self.representative_apart(representative, subject_root, subject_roots)
                })
            })
    }

    /// Terms that cover every reduct of an instance of `pattern`, read up to reducts: every such
    /// reduct is an instance of one of them in which each argument is a reduct of an instance of
    /// that term's argument. `None` when that is not bounded.
    ///
    /// A pattern whose instances are normal forms is its own only reduct. Otherwise a reduct
    /// keeps the pattern's root, with its arguments reduced, until an equation indexed by that
    /// root rewrites it; the result is an instance of that equation's right-hand side, whose
    /// variables are bound by matching its left-hand side against the reduct
    /// ([`Self::narrow`]), and it may be rewritten at its own root again. The representatives
    /// are the pattern and the right-hand sides so reached, up to [`REPRESENTATIVES`] terms of at
    /// most [`REPRESENTATIVE_SIZE`] nodes and [`NARROWING_DEPTH`] levels of nested patterns; past
    /// any of these bounds, or the scan's narrowing budget, they are the pattern and
    /// every right-hand side its root's equations reach (`PatternFacts::value_roots`), which
    /// covers the same reducts with fewer bindings. An as-pattern is covered by either conjunct.
    ///
    /// The representatives are also what an identification of an overlapped instance may
    /// concern ([`Self::overlaps_miss`]). An equation with an `ensures` identifies its instance
    /// with `\bottom` where the `ensures` fails, which pins whatever decides the `ensures`, and
    /// no reduct shows that; so a step it may take leaves the representatives unbounded, as a
    /// right-hand side that is not a term does.
    fn value_representatives(&self, pattern: &Term) -> Option<Vec<Term>> {
        self.representatives(pattern, bounds().narrowing_depth)
    }

    fn representatives(&self, pattern: &Term, depth: usize) -> Option<Vec<Term>> {
        match pattern.kind() {
            TermKind::And(left, right) => {
                let conjunct = if matches!(left.kind(), TermKind::Variable(_)) {
                    right
                } else {
                    left
                };
                return self.representatives(conjunct, depth);
            }
            TermKind::Variable(_) => return None,
            _ => {}
        }
        match pattern.shape() {
            Shape::DomainValue
            | Shape::Injection
            | Shape::Collection(_)
            | Shape::Application(HeadRole::FreeConstructor | HeadRole::EquationHead) => {}
            Shape::Variable
            | Shape::And
            | Shape::Application(
                HeadRole::Function { .. } | HeadRole::Uninterpreted | HeadRole::Residual,
            ) => return None,
        }
        if self.normal_pattern(pattern) {
            return Some(vec![pattern.clone()]);
        }
        if work_spent() {
            return None;
        }
        if depth == 0 {
            return self.reachable_representatives(pattern);
        }
        if self.with_pattern_facts(|facts| facts.unbounded) {
            return None;
        }
        let mut representatives = vec![pattern.clone()];
        // The pattern's own variables are shared with its context; the others are the names
        // minted for variables an equation left unbound, and reducts that differ only in those
        // are one representative.
        let pattern_variables = &pattern.attributes().variables;
        let kept = |variable: &Variable| !minted(variable) || pattern_variables.contains(variable);
        let mut shapes = vec![shape_hash(pattern, &kept)];
        let mut next = 0;
        while let Some(term) = representatives.get(next).cloned() {
            next += 1;
            let index = term_index(&term);
            let equations = [self.function_theory(), self.simplification_theory()]
                .into_iter()
                .filter_map(|theory| theory.get(&index))
                .flat_map(|groups| groups.values().flatten())
                .collect::<Vec<_>>();
            for equation in equations {
                let RuleRhs::Term(right) = &equation.rhs else {
                    return None;
                };
                let reading = if self.pattern_arguments_normal(equation) {
                    LeftReading::Values
                } else {
                    LeftReading::Checked
                };
                let Some(bindings) = self.narrow(&equation.lhs, &term, depth - 1, reading) else {
                    continue;
                };
                // Where its `ensures` fails, the equation identifies the instance with
                // `\bottom`, which pins whatever decides the `ensures`: no reduct shows that.
                if !equation.ensures.is_empty() {
                    return None;
                }
                for binding in bindings {
                    // A variable narrowing leaves unbound stands for any value, independent of
                    // the term's variables of the same name.
                    let reduct = Completion::of(binding, &right.attributes().variables)
                        .apply(right)
                        .into_term();
                    if !within_size(&reduct, bounds().representative_size) {
                        return self.reachable_representatives(pattern);
                    }
                    let shape = shape_hash(&reduct, &kept);
                    if representatives
                        .iter()
                        .zip(&shapes)
                        .any(|(known, known_shape)| {
                            *known_shape == shape && renamed_from(known, &reduct, &kept)
                        })
                    {
                        continue;
                    }
                    if representatives.len() >= bounds().representatives {
                        return self.reachable_representatives(pattern);
                    }
                    representatives.push(reduct);
                    shapes.push(shape);
                }
            }
        }
        Some(representatives)
    }

    /// The pattern and every right-hand side the equations of its root reach
    /// (`PatternFacts::value_roots`): representatives without bindings, each a fresh copy, so
    /// that the representatives of two argument positions share no variable.
    fn reachable_representatives(&self, pattern: &Term) -> Option<Vec<Term>> {
        let mut representatives =
            self.with_pattern_facts(|facts| match facts.value_roots.get(&term_index(pattern)) {
                Some(roots) => roots.as_ref().map(|roots| {
                    roots
                        .iter()
                        .map(|root| root.fresh().into_term())
                        .collect::<Vec<_>>()
                }),
                None => (!facts.unbounded).then(Vec::new),
            })?;
        representatives.push(pattern.clone());
        Some(representatives)
    }

    /// The bindings of the variables of an equation's left-hand side `left` under which a reduct
    /// of an instance of `term` (read up to reducts) that keeps `term`'s root has the value of an
    /// instance of `left`: one substitution per alternative, each binding a variable to a subterm
    /// of `term` (read up to reducts) or leaving it unbound (any value). `None` when no such
    /// reduct has such a value. A variable bound twice keeps its first binding: its value is a
    /// reduct of both subterms, so either covers it.
    ///
    /// `left` is read through its values (`reading`): a subterm of it is compared by its syntax
    /// only when its instances are normal forms, so that the instance is the value; any other
    /// subterm stands for any value and binds nothing ([`Self::narrow_argument`]).
    fn narrow(
        &self,
        left: &Term,
        term: &Term,
        depth: usize,
        reading: LeftReading,
    ) -> Option<Vec<Substitution>> {
        let unknown = || Some(vec![Substitution::new()]);
        if !take_work() {
            return unknown();
        }
        match (left.kind(), term.kind()) {
            (TermKind::Variable(variable), _) => {
                Some(vec![Substitution::from([(variable.clone(), term.clone())])])
            }
            (TermKind::And(first, second), _) => {
                let first = self.narrow(first, term, depth, reading)?;
                let second = self.narrow(second, term, depth, reading)?;
                combine(first, second)
            }
            (_, TermKind::Variable(_)) => unknown(),
            (_, TermKind::And(conjunct, other)) => {
                let conjunct = if matches!(conjunct.kind(), TermKind::Variable(_)) {
                    other
                } else {
                    conjunct
                };
                self.narrow(left, conjunct, depth, reading)
            }
            (
                TermKind::Application {
                    symbol: left_symbol,
                    sort_arguments: left_sorts,
                    arguments: left_arguments,
                },
                TermKind::Application {
                    symbol: term_symbol,
                    sort_arguments: term_sorts,
                    arguments: term_arguments,
                },
            ) if left_symbol.name == term_symbol.name => {
                if left_sorts != term_sorts || left_arguments.len() != term_arguments.len() {
                    return unknown();
                }
                let mut alternatives = vec![Substitution::new()];
                for (left_argument, term_argument) in left_arguments.iter().zip(term_arguments) {
                    let argument =
                        self.narrow_argument(left_argument, term_argument, depth, reading)?;
                    alternatives = combine(alternatives, argument)?;
                }
                Some(alternatives)
            }
            (
                TermKind::Injection {
                    source: left_source,
                    target: left_target,
                    term: left_operand,
                },
                TermKind::Injection {
                    source: term_source,
                    target: term_target,
                    term: term_operand,
                },
            ) if left_target == term_target => {
                if left_source == term_source {
                    return self.narrow_argument(left_operand, term_operand, depth, reading);
                }
                // By the subsort axioms injections compose: for `C < B < A`,
                // `inj{C,A}(x) = inj{B,A}(inj{C,B}(x))`. A reduct of `inj{S,T}(t)` is
                // `inj{S,T}(t')`, which is `inj{C,T}(u)` when `t'` is `inj{C,S}(u)`; it is
                // the value of an instance of `inj{L,T}(p)` exactly when it is
                // `inj{C,T}(u)` for a sort `C` below or equal to both `L` and `S`.
                let sorts = self.sort_graph();
                let below = |sub, sup| sorts.check_subsort(sub, sup).ok();
                match (
                    below(left_source, term_source),
                    below(term_source, left_source),
                ) {
                    // The reduct of `t` must be an injection from `L` or below.
                    (Some(true), _) => self.narrow_argument(
                        &Term::injection(
                            left_source.clone(),
                            term_source.clone(),
                            left_operand.clone(),
                        ),
                        term_operand,
                        depth,
                        reading,
                    ),
                    // Every reduct `inj{S,T}(t')` is `inj{L,T}(inj{S,L}(t'))`.
                    (_, Some(true)) => self.narrow_argument(
                        left_operand,
                        &Term::injection(
                            term_source.clone(),
                            left_source.clone(),
                            term_operand.clone(),
                        ),
                        depth,
                        reading,
                    ),
                    (Some(false), Some(false)) => {
                        if sorts.known_overlap(left_source, term_source) == Some(false) {
                            return None;
                        }
                        self.narrow_through_lower_injections(
                            left,
                            term_target,
                            term_operand,
                            depth,
                            reading,
                        )
                    }
                    _ => unknown(),
                }
            }
            (
                TermKind::DomainValue {
                    sort: left_sort,
                    value: left_value,
                },
                TermKind::DomainValue {
                    sort: term_sort,
                    value: term_value,
                },
            ) if left_sort == term_sort && left_value != term_value => None,
            _ => match (
                classify_pattern(PatternReading::AsWritten, left),
                classify_pattern(PatternReading::AsWritten, term),
            ) {
                (Head::Fixed(left_root), Head::Fixed(term_root)) => {
                    let apart = match (left.kind(), term.kind()) {
                        (TermKind::Injection { .. }, TermKind::Application { .. })
                        | (TermKind::Application { .. }, TermKind::Injection { .. }) => true,
                        _ => {
                            compared_by_root(left_root)
                                && compared_by_root(term_root)
                                && separated(compare_roots(left_root, term_root))
                        }
                    };
                    if apart { None } else { unknown() }
                }
                _ => unknown(),
            },
        }
    }

    /// [`Self::narrow`] for an argument position: the argument `term` is read up to reducts, so
    /// each of its representatives is matched. Under [`LeftReading::Checked`] the left-hand side
    /// subterm `left` is compared by its syntax only when it is a normal pattern
    /// ([`Self::normal_pattern`]), and then so is every subterm below it; otherwise it is read
    /// through its own values ([`Self::narrow_through_values`]).
    fn narrow_argument(
        &self,
        left: &Term,
        term: &Term,
        depth: usize,
        reading: LeftReading,
    ) -> Option<Vec<Substitution>> {
        if let TermKind::Variable(variable) = left.kind() {
            return Some(vec![Substitution::from([(variable.clone(), term.clone())])]);
        }
        let checked = reading == LeftReading::Checked && !self.normal_pattern(left);
        let Some(representatives) = self.representatives(term, depth) else {
            return Some(vec![Substitution::new()]);
        };
        if checked {
            return self.narrow_through_values(left, &representatives, depth);
        }
        let mut alternatives = Vec::new();
        for representative in &representatives {
            if let Some(found) = self.narrow(left, representative, depth, LeftReading::Values) {
                alternatives.extend(found);
            }
        }
        bounded_alternatives(alternatives)
    }

    /// The bindings of the variables of `left`, a left-hand side subterm that is not a normal
    /// pattern, under which the value of an instance of `left` may be the value of a reduct of an
    /// instance of a term whose representatives are `representatives`. An instance of `left`
    /// denotes the value of its normal forms, which are reached in three ways, each read here
    /// through narrowing:
    /// - keeping `left`'s root, with its arguments reduced: `left` against each representative,
    ///   its own arguments read the same way;
    /// - through a root step by an equation `e` offered at `left`'s index: the bindings under
    ///   which an instance of `left` is one of `e`'s left-hand side, composed with those under
    ///   which `e`'s right-hand side may have the term's value;
    /// - as one of the normal forms such an equation identifies with another (its `Overlaps`):
    ///   the bindings under which an instance of `left` is one of them.
    ///
    /// Any other reading (a function or bare-variable equation, unbounded overlaps, the nesting
    /// bound) binds nothing, so `left` stands for any value.
    fn narrow_through_values(
        &self,
        left: &Term,
        representatives: &[Term],
        depth: usize,
    ) -> Option<Vec<Substitution>> {
        let any = || Some(vec![Substitution::new()]);
        if depth == 0
            || !matches!(
                left.shape(),
                Shape::Application(HeadRole::EquationHead) | Shape::Collection(_)
            )
            || self.with_pattern_facts(|facts| facts.unbounded)
        {
            return any();
        }
        let mut alternatives = Vec::new();
        for representative in representatives {
            if let Some(found) = self.narrow(left, representative, depth, LeftReading::Checked) {
                alternatives.extend(found);
            }
        }
        for equation in self.offered_equations(left) {
            let RuleRhs::Term(right) = &equation.rhs else {
                return any();
            };
            if matches!(equation.lhs.kind(), TermKind::Variable(_)) {
                return any();
            }
            if let Some(instances) =
                self.narrow(left, &equation.lhs, depth - 1, LeftReading::Checked)
            {
                for representative in representatives {
                    let Some(reducts) = self.narrow_argument(
                        right,
                        representative,
                        depth - 1,
                        LeftReading::Checked,
                    ) else {
                        continue;
                    };
                    for reduct in &reducts {
                        // The equation's variables that the reduct leaves unbound stand for
                        // any value, apart from the term's and `left`'s.
                        let completion =
                            Completion::of(reduct.clone(), &equation.lhs.attributes().variables);
                        for instance in &instances {
                            alternatives.push(
                                instance
                                    .iter()
                                    .map(|(variable, bound)| {
                                        (variable.clone(), completion.apply(bound).into_term())
                                    })
                                    .collect(),
                            );
                        }
                    }
                }
            }
            match self.previous_overlaps(equation) {
                Overlaps::Absent => {}
                Overlaps::Unbounded => return any(),
                Overlaps::Reaching(identified) => {
                    for normal_form in identified.iter() {
                        if let Some(found) = self.narrow(
                            left,
                            normal_form.fresh().term(),
                            depth - 1,
                            LeftReading::Checked,
                        ) {
                            alternatives.extend(found);
                        }
                    }
                }
            }
        }
        bounded_alternatives(alternatives)
    }

    /// [`Self::narrow`] of the injection pattern `left`, from a sort `L`, against
    /// `inj{S,target}(operand)` where neither of `L` and `S` is below the other: a reduct is the
    /// value of an instance of `left` only through a reduct of `operand` that is an injection
    /// `inj{C,S}(u)` from a sort below `S`, which composes to `inj{C,target}(u)`. So each
    /// representative of `operand` that is an injection is narrowed in that composed form, one
    /// with another fixed root (an application of a constructor or equation head, a domain value,
    /// a collection: its reducts keep that root) gives nothing, and any other leaves the bindings
    /// unknown. Each step lowers the injection source strictly, so this ends.
    fn narrow_through_lower_injections(
        &self,
        left: &Term,
        target: &Sort,
        operand: &Term,
        depth: usize,
        reading: LeftReading,
    ) -> Option<Vec<Substitution>> {
        let unknown = || Some(vec![Substitution::new()]);
        let Some(representatives) = self.representatives(operand, depth) else {
            return unknown();
        };
        let mut alternatives = Vec::new();
        for representative in &representatives {
            match representative.shape() {
                Shape::Injection => {
                    let TermKind::Injection {
                        source,
                        term: inner,
                        ..
                    } = representative.kind()
                    else {
                        unreachable!("an injection shape is an injection")
                    };
                    let composed = Term::injection(source.clone(), target.clone(), inner.clone());
                    if let Some(found) = self.narrow(left, &composed, depth, reading) {
                        alternatives.extend(found);
                    }
                }
                Shape::DomainValue
                | Shape::Collection(_)
                | Shape::Application(HeadRole::FreeConstructor | HeadRole::EquationHead) => {}
                Shape::Variable
                | Shape::And
                | Shape::Application(
                    HeadRole::Function { .. } | HeadRole::Uninterpreted | HeadRole::Residual,
                ) => return unknown(),
            }
        }
        bounded_alternatives(alternatives)
    }

    /// Whether no reduct with the root of `representative` is the normal form `subject`. A reduct
    /// that keeps the representative's root has the representative's arguments reduced (a root
    /// step gives another representative), so an application of the subject's symbol is apart
    /// when some pair of arguments is. Two injections into one sort with one source compare
    /// their operands. With the subject's source strictly below, the representative's operand
    /// would have to reduce to the subject's operand injected into the representative's source;
    /// with it strictly above, the subject's operand would have to be an injection. With neither
    /// below the other, they are apart when the sources have no common subsort or the subject's
    /// operand is constructor-like, so that its value is of the subject's source sort and of no
    /// sort not above it. An injection and an application never share a value; two domain
    /// values of one sort are apart when they differ; other roots are apart when the root
    /// comparison separates them.
    fn representative_apart(
        &self,
        representative: &Term,
        subject: Fixed<'_>,
        subject_roots: &mut dyn NormalForms,
    ) -> bool {
        let Head::Fixed(representative_root) =
            classify_pattern(PatternReading::AsWritten, representative)
        else {
            return false;
        };
        match (representative.kind(), subject.term().kind()) {
            (
                TermKind::Application {
                    symbol: representative_symbol,
                    sort_arguments: representative_sorts,
                    arguments: representative_arguments,
                },
                TermKind::Application {
                    symbol: subject_symbol,
                    sort_arguments: subject_sorts,
                    arguments: subject_arguments,
                },
            ) if representative_symbol.name == subject_symbol.name => {
                representative_sorts == subject_sorts
                    && representative_arguments.len() == subject_arguments.len()
                    && representative_arguments.iter().zip(subject_arguments).any(
                        |(pattern, subject)| self.values_apart(pattern, subject, subject_roots),
                    )
            }
            (
                TermKind::Injection {
                    source: representative_source,
                    target: representative_target,
                    term: representative_operand,
                },
                TermKind::Injection {
                    source: subject_source,
                    target: subject_target,
                    term: subject_operand,
                },
            ) => {
                let sorts = self.sort_graph();
                let below = |sub, sup| sorts.check_subsort(sub, sup).ok();
                if representative_target != subject_target {
                    false
                } else if representative_source == subject_source {
                    self.values_apart(representative_operand, subject_operand, subject_roots)
                } else if below(subject_source, representative_source) == Some(true) {
                    // The subject is the injection from the representative's source of
                    // `inj{subject_source, representative_source}(subject_operand)`.
                    self.values_apart(
                        representative_operand,
                        &Term::injection(
                            subject_source.clone(),
                            representative_source.clone(),
                            subject_operand.clone(),
                        ),
                        subject_roots,
                    )
                } else if below(representative_source, subject_source) == Some(true) {
                    !matches!(subject_operand.kind(), TermKind::Injection { .. })
                } else {
                    below(subject_source, representative_source) == Some(false)
                        && below(representative_source, subject_source) == Some(false)
                        && (sorts.known_overlap(representative_source, subject_source)
                            == Some(false)
                            || subject_operand.attributes().constructor_like)
                }
            }
            (TermKind::Injection { .. }, TermKind::Application { .. })
            | (TermKind::Application { .. }, TermKind::Injection { .. }) => true,
            (
                TermKind::DomainValue {
                    sort: representative_sort,
                    value: representative_value,
                },
                TermKind::DomainValue {
                    sort: subject_sort,
                    value: subject_value,
                },
            ) => representative_sort == subject_sort && representative_value != subject_value,
            _ => {
                compared_by_root(representative_root)
                    && compared_by_root(subject)
                    && separated(compare_roots(representative_root, subject))
            }
        }
    }

    /// The test [`pattern_facts`] applies to one left-hand side: every immediate subterm is a
    /// normal pattern ([`Self::normal_pattern`]); for a conjunction, of each conjunct.
    fn left_hand_side_arguments_normal(&self, pattern: &Term) -> bool {
        match pattern.kind() {
            TermKind::And(left, right) => {
                self.left_hand_side_arguments_normal(left)
                    && self.left_hand_side_arguments_normal(right)
            }
            _ => token::every_immediate_subterm(pattern, |subterm| self.normal_pattern(subterm)),
        }
    }

    /// Whether every valuation of the pattern `pattern` that denotes a value denotes it by a
    /// normal form that instantiates every conjunct of `pattern` alike. A conjunction-free
    /// pattern has this when it is instance-normal. A conjunction `p /\ q` (an as-pattern)
    /// denotes a value where both conjuncts denote it; when both have the property, the two
    /// normal forms denote one value, so they are one term. A constructor application or an
    /// injection has it when its arguments do, since it is a normal form when they are. Any
    /// other pattern with a conjunction inside is answered `false`, which is always sound.
    fn normal_pattern(&self, pattern: &Term) -> bool {
        match pattern.kind() {
            TermKind::And(left, right) => self.normal_pattern(left) && self.normal_pattern(right),
            _ if !contains_conjunction(pattern) => self.instance_normal_memoized(pattern).is_some(),
            _ => {
                matches!(
                    pattern.shape(),
                    Shape::Injection | Shape::Application(HeadRole::FreeConstructor)
                ) && token::every_immediate_subterm(pattern, |subterm| self.normal_pattern(subterm))
            }
        }
    }

    /// The [`Overlaps`] of `rule`, a function or simplification equation whose left-hand side
    /// has a fixed root, under the facts of the current round ([`pattern_facts`]).
    ///
    /// An instance `lσ` of the left-hand side `l` is overlapped when it is an instance of
    /// another equation's left-hand side offered at its index (that equation also rewrites it at
    /// the root), or when, at some position below the root that is not a variable, the subterm
    /// `q` of `l` has an instance `qσ` that is not a value: a redex of an equation offered at
    /// `q`'s index, or one of the normal forms such an equation identifies with another (its own
    /// `Overlaps`, from the previous round). Either set of valuations is found by narrowing `l`
    /// (or `q`) against the other left-hand side (or normal form), which binds the variables of
    /// `l`; a subterm that is not a value for other reasons (a function application, a
    /// bare-variable equation of its sort, unbounded overlaps) makes every valuation count. The
    /// result covers every reduct of every such instance by its representatives
    /// ([`Self::value_representatives`]), which follow every equation, this one included.
    ///
    /// The other left-hand side and the other equation's normal forms are narrowed against as
    /// fresh copies ([`Apart`]): an instance is read through its variables' identity (the joins
    /// match the other left-hand side against it and compare the two sides, instance normality
    /// binds variables consistently), so a variable of `l` must not be merged with an
    /// independent one of the same name. The instances and the representatives are kept as
    /// [`Stored`] terms, and each list as its most general members ([`add_most_general`]): a
    /// term that is an instance of another covers nothing the other does not, and every reader
    /// of the cover answers for the instances of each member. Without that, an equation that
    /// overlaps itself below its root (`p(Y, p(Z, W)) = j(W, p(W, Z))`) would store, in each
    /// round, an instance one nesting deeper than the previous round's, and the rounds would
    /// not settle.
    fn overlaps_of(&self, rule: &RewriteRule) -> Overlaps {
        let mut alternatives = Vec::new();
        let mut every = false;
        let mut overlap = |found: Option<Vec<Substitution>>, every: &mut bool| {
            if let Some(found) = found {
                if found.iter().any(Substitution::is_empty) {
                    *every = true;
                } else {
                    alternatives.extend(found);
                }
            }
        };
        let left = &rule.lhs;
        for other in self.offered_equations(left) {
            if std::ptr::eq(other, rule) {
                continue;
            }
            match self.overlap_with(left, other) {
                Some(found) => {
                    let found = found
                        .into_iter()
                        .filter(|valuation| !self.peak_joins(rule, valuation, None, other))
                        .collect();
                    overlap(Some(found), &mut every);
                }
                None => every = true,
            }
        }
        for_each_subterm_below_root(left, &mut |subterm| {
            if every || self.normal_pattern(subterm) {
                return;
            }
            match subterm.shape() {
                Shape::Application(HeadRole::EquationHead) | Shape::Collection(_) => {}
                // Not a value only through a subterm, which is visited on its own.
                Shape::DomainValue
                | Shape::Injection
                | Shape::Application(HeadRole::FreeConstructor) => return,
                Shape::Variable
                | Shape::And
                | Shape::Application(
                    HeadRole::Function { .. } | HeadRole::Uninterpreted | HeadRole::Residual,
                ) => {
                    every = true;
                    return;
                }
            }
            for other in self.offered_equations(subterm) {
                // A step matching reads through rewrites no value (`reads_through`); the normal
                // forms `other` identifies below are still asked about.
                let redexes = if self.reads_through(subterm, other) {
                    Some(Vec::new())
                } else {
                    self.overlap_with(subterm, other)
                };
                match redexes {
                    Some(found) => {
                        let found = found
                            .into_iter()
                            .filter(|valuation| {
                                !self.peak_joins(rule, valuation, Some(subterm), other)
                            })
                            .collect();
                        overlap(Some(found), &mut every);
                    }
                    None => {
                        every = true;
                        return;
                    }
                }
                match self.previous_overlaps(other) {
                    Overlaps::Absent => {}
                    Overlaps::Unbounded => {
                        every = true;
                        return;
                    }
                    Overlaps::Reaching(reaching) => {
                        for normal_form in reaching.iter() {
                            overlap(
                                self.narrow(
                                    subterm,
                                    normal_form.fresh().term(),
                                    bounds().narrowing_depth,
                                    LeftReading::Values,
                                ),
                                &mut every,
                            );
                        }
                    }
                }
            }
        });
        if !every && alternatives.is_empty() {
            return Overlaps::Absent;
        }
        let mut instances = Vec::new();
        if !every && alternatives.len() <= bounds().representatives {
            for alternative in &alternatives {
                let instance = instantiate(left, &bind_aliases(left, alternative));
                // An instance past the size bound is covered by `left` itself, which every
                // overlapped instance is an instance of. Without the bound, a non-linear
                // left-hand side read against the previous round's representatives doubles
                // them each round.
                if !within_size(&instance, bounds().representative_size) {
                    instances.clear();
                    break;
                }
                add_most_general(&mut instances, Stored::new(&instance));
            }
        }
        if instances.is_empty() {
            instances.push(Stored::new(left));
        }
        let mut reaching = Vec::new();
        for instance in &instances {
            let Some(representatives) = self.value_representatives(instance.fresh().term()) else {
                return Overlaps::Unbounded;
            };
            for representative in representatives {
                add_most_general(&mut reaching, Stored::new(&representative));
            }
        }
        Overlaps::Reaching(reaching.into())
    }

    /// The [`Overlaps`] of `rule` that cover every instance of its left-hand side, overlapped
    /// or not, without reading the facts of any round: the left-hand side and every right-hand
    /// side the equations of its root reach (`PatternFacts::value_roots`), as the
    /// representatives are past their bounds; [`Overlaps::Unbounded`] when those are not
    /// bounded. [`pattern_facts`] fixes an equation's overlaps to these once they have changed
    /// in [`OVERLAP_CHANGES`] rounds.
    fn coarse_overlaps(&self, rule: &RewriteRule) -> Overlaps {
        match self.reachable_representatives(&rule.lhs) {
            Some(representatives) => {
                let mut reaching = Vec::new();
                for representative in representatives {
                    add_most_general(&mut reaching, Stored::new(&representative));
                }
                Overlaps::Reaching(reaching.into())
            }
            None => Overlaps::Unbounded,
        }
    }

    /// Whether the peak at `lσ` (`l` the left-hand side of `rule`, `σ` the valuation
    /// `valuation`) between `rule`'s root step and the step of `other` joins: at the subterm
    /// `inner` of `l` when given (its instance is a redex of `other`), at the root otherwise
    /// (`lσ` is an instance of `other`'s left-hand side too). A joining peak sends both of its
    /// sides to one term, so the instance identifies no two normal forms through it.
    ///
    /// Only equations without an `ensures` can join this way. An equation `l = r ensures E`
    /// states `lσ = rσ ∧ Eσ`: where `Eσ` fails it identifies `lσ` with `\bottom`. Two sides that
    /// meet as terms then still identify `rσ ∧ E1σ` with the other side conjoined with its own
    /// `ensures`, which pins whatever decides the `ensures`: `f(k(c)) = c ensures P` beside
    /// `f(k(c)) = c ensures Q` forces `P` and `Q` to agree, and so constrains the definedness of
    /// the applications in them. So the answer is `false` when either equation has an `ensures`.
    ///
    /// The proof is built from real steps: both sides (`rσ`, and `other`'s reduct in place) are
    /// reduced by up to [`JOIN_STEPS`] steps of unconditional equations (no `requires`, no
    /// `ensures`), innermost first, and must meet. A side that does not meet within them leaves
    /// the peak counted, which only keeps more terms from being certified. The instance and its
    /// two sides are read as one fresh copy ([`Apart::copies`]), apart from every equation, as
    /// matching needs.
    fn peak_joins(
        &self,
        rule: &RewriteRule,
        valuation: &Substitution,
        inner: Option<&Term>,
        other: &RewriteRule,
    ) -> bool {
        let (RuleRhs::Term(right), RuleRhs::Term(other_right)) = (&rule.rhs, &other.rhs) else {
            return false;
        };
        if !rule.ensures.is_empty() || !other.ensures.is_empty() {
            return false;
        }
        let valuation = &bind_aliases(&rule.lhs, valuation);
        let instance = instantiate(&rule.lhs, valuation);
        // The variables of `l` that the valuation leaves unbound are the instance's own.
        let reduct = substitute(right, valuation);
        let redex = match inner {
            Some(inner) => substitute(inner, valuation),
            None => instance.clone(),
        };
        let [instance, reduct, redex] =
            Apart::copies([&instance, &reduct, &redex]).map(Apart::into_term);
        let Some(other_reduct) = self.step_with(other, &redex, other_right) else {
            return false;
        };
        let other_side = match inner {
            Some(_) => replace_subterm(&instance, &redex, &other_reduct),
            None => other_reduct.clone(),
        };
        self.reduce_unconditionally(&reduct) == self.reduce_unconditionally(&other_side)
    }

    /// Whether equation matching reads through the steps of `other` at the left-hand side
    /// subterm `subterm`: `other` is an overload equation `g(inj(K1), …, inj(Kn)) =
    /// inj(s(K1, …, Kn))` (or without the outer injection) of a production `g` that the
    /// definition's overload relation makes overload `s`, and `subterm` is headed by `g`. Its
    /// step only rewrites how a value of `g` is written, and matching lifts `inj(s(a1, …, an))`
    /// back to `g(inj(a1), …, inj(an))` when it compares it with a `g` pattern (the
    /// overload resolution of `matching`). So wherever the left-hand side matched before the
    /// step it matches after it, at the valuation with the step done inside the values bound,
    /// and the peak with the equation's root step joins: it identifies no two normal forms.
    fn reads_through(&self, subterm: &Term, other: &RewriteRule) -> bool {
        let (
            TermKind::Application { symbol: head, .. },
            TermKind::Application {
                symbol: general, ..
            },
        ) = (subterm.kind(), other.lhs.kind())
        else {
            return false;
        };
        let RuleRhs::Term(right) = &other.rhs else {
            return false;
        };
        let specific = match right.kind() {
            TermKind::Injection { term, .. } => term,
            _ => right,
        };
        let (
            TermKind::Application {
                symbol: specific,
                arguments: specific_arguments,
                ..
            },
            TermKind::Application {
                arguments: general_arguments,
                ..
            },
        ) = (specific.kind(), other.lhs.kind())
        else {
            return false;
        };
        // The overload equation's own shape: each argument of `g` is a variable, or one under
        // an injection, and `s` takes those variables in order.
        let lifted = general_arguments.len() == specific_arguments.len()
            && general_arguments
                .iter()
                .zip(specific_arguments)
                .all(|(general, specific)| {
                    let general = match general.kind() {
                        TermKind::Injection { term, .. } => term,
                        _ => general,
                    };
                    matches!(general.kind(), TermKind::Variable(_)) && general == specific
                });
        head.name == general.name
            && lifted
            && other.requires.is_empty()
            && self
                .overloads()
                .is_overloading(&general.name, &specific.name)
    }

    /// `rule`'s step at the root of `term`, whose right-hand side is `right`: the instance of
    /// `right` at the valuation equation matching finds, when it succeeds and binds every
    /// variable of `right`.
    fn step_with(&self, rule: &RewriteRule, term: &Term, right: &Term) -> Option<Term> {
        if !rule
            .lhs
            .attributes()
            .variables
            .is_disjoint(&term.attributes().variables)
        {
            return None;
        }
        let MatchResult::Success(valuation) =
            match_terms_in_definition(MatchMode::Evaluate, self, &rule.lhs, term)
        else {
            return None;
        };
        right
            .attributes()
            .variables
            .iter()
            .all(|variable| valuation.contains_key(variable))
            .then(|| substitute(right, &valuation))
    }

    /// `term` after up to [`JOIN_STEPS`] steps of unconditional equations, each at the
    /// innermost, leftmost position one applies.
    fn reduce_unconditionally(&self, term: &Term) -> Term {
        let mut term = term.clone();
        for _ in 0..bounds().join_steps {
            match self.unconditional_step(&term) {
                Some(next) => term = next,
                None => break,
            }
        }
        term
    }

    fn unconditional_step(&self, term: &Term) -> Option<Term> {
        let mut stepped = false;
        let mapped = term
            .try_map_children(|child| {
                Ok::<_, std::convert::Infallible>(if stepped {
                    child.clone()
                } else if let Some(next) = self.unconditional_step(child) {
                    stepped = true;
                    next
                } else {
                    child.clone()
                })
            })
            .unwrap_or_else(|never| match never {});
        if stepped {
            return Some(mapped);
        }
        if matches!(term.kind(), TermKind::Variable(_)) {
            return None;
        }
        self.offered_equations(term).into_iter().find_map(|rule| {
            let RuleRhs::Term(right) = &rule.rhs else {
                return None;
            };
            (rule.requires.is_empty()
                && rule.ensures.is_empty()
                && !matches!(rule.lhs.kind(), TermKind::Variable(_)))
            .then(|| self.step_with(rule, term, right))
            .flatten()
        })
    }

    /// The function and simplification equations equation selection offers a term with the
    /// index of `pattern`, and those indexed by a bare variable.
    fn offered_equations(&self, pattern: &Term) -> Vec<&RewriteRule> {
        let index = term_index(pattern);
        [self.function_theory(), self.simplification_theory()]
            .into_iter()
            .flat_map(|theory| [theory.get(&index), theory.get(&TermIndex::Variable)])
            .flatten()
            .flat_map(|groups| groups.values().flatten().map(AsRef::as_ref))
            .collect()
    }

    /// The valuations of the variables of `pattern` under which an instance of it is also an
    /// instance of the left-hand side of `other` (narrowing; `Some(vec![])` when there is none);
    /// `None` when every valuation may be: `other` is a bare variable of `pattern`'s sort. The
    /// other left-hand side is renamed fresh, so the valuations bind `pattern`'s variables to
    /// terms whose variables are those of an independent copy of `other`, `other` being
    /// `pattern`'s own equation included.
    fn overlap_with(&self, pattern: &Term, other: &RewriteRule) -> Option<Vec<Substitution>> {
        if let TermKind::Variable(variable) = other.lhs.kind() {
            return sorts_differ(&variable.sort, &pattern.sort()).then(Vec::new);
        }
        Some(
            self.narrow(
                pattern,
                Apart::copy(&other.lhs).term(),
                bounds().narrowing_depth,
                LeftReading::Values,
            )
            .unwrap_or_default(),
        )
    }

    /// The [`Overlaps`] of `rule` in the facts the current round reads.
    fn previous_overlaps(&self, rule: &RewriteRule) -> Overlaps {
        let key = rule_key(rule);
        self.with_pattern_facts(|facts| {
            facts
                .overlaps
                .as_ref()
                .and_then(|overlaps| overlaps.get(&key))
                .cloned()
                .unwrap_or(Overlaps::Unbounded)
        })
    }

    fn with_pattern_facts<R>(&self, read: impl FnOnce(&PatternFacts) -> R) -> R {
        match APPROXIMATION.with(|approximation| approximation.borrow().clone()) {
            Some(facts) => read(&facts),
            None => read(self.pattern_facts()),
        }
    }
}

/// How [`BackendDefinition::narrow`] reads an equation's left-hand side.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LeftReading {
    /// Every subterm below the root is a normal pattern: the left-hand side of a normal-argument
    /// equation ([`BackendDefinition::pattern_arguments_normal`]), or a subterm of a normal
    /// pattern. Its syntax is its values.
    Values,
    /// Any other equation: each argument is checked before its syntax is used.
    Checked,
}

/// The alternatives one narrowing found: `None` when there are none, the one alternative that
/// binds nothing when there are more than [`REPRESENTATIVES`].
fn bounded_alternatives(alternatives: Vec<Substitution>) -> Option<Vec<Substitution>> {
    if alternatives.is_empty() {
        None
    } else if alternatives.len() > bounds().representatives {
        Some(vec![Substitution::new()])
    } else {
        Some(alternatives)
    }
}

/// The most representatives [`BackendDefinition::value_representatives`] keeps for one pattern,
/// and the most alternatives one narrowing keeps, before falling back to coarser ones.
pub(super) const REPRESENTATIVES: usize = 64;

/// The most nodes a representative [`BackendDefinition::value_representatives`] builds, or an
/// overlapped instance [`BackendDefinition::overlaps_of`] stores, may have, counting a shared
/// subterm at each occurrence, before falling back to coarser ones. A right-hand side that
/// repeats a variable doubles what is bound to it, so a chain of reducts can grow exponentially,
/// and every walk of a term (comparison up to minted names, canonical renaming) visits each
/// occurrence. FUN's reducts have about 100.
pub(super) const REPRESENTATIVE_SIZE: usize = 2048;

/// Whether `term`'s root is a total symbol: an application of `term` is defined whenever its
/// immediate subterms are. Constructors and sort injections are `functional`, and a symbol
/// declared `total` (or `functional`) is total whatever else it is, an `anywhere` equation
/// head included; a collection is counted as total, which only reads more of it. An
/// application of a symbol not declared total, and a variable, a domain value or an `\and`,
/// are not.
fn total_root(term: &Term) -> bool {
    match term.kind() {
        TermKind::Application { symbol, .. } => {
            symbol.attributes.symbol_type != SymbolType::Function(FunctionType::Partial)
        }
        TermKind::Injection { .. }
        | TermKind::Map { .. }
        | TermKind::List { .. }
        | TermKind::Set { .. } => true,
        TermKind::DomainValue { .. } | TermKind::Variable(_) | TermKind::And(..) => false,
    }
}

/// Whether `term` has at most `limit` nodes, counting a shared subterm at each occurrence; at
/// most `limit + 1` nodes are visited, and the recursion is at most that deep.
fn within_size(term: &Term, limit: usize) -> bool {
    fn count(term: &Term, left: &mut usize) -> bool {
        if *left == 0 {
            return false;
        }
        *left -= 1;
        token::every_immediate_subterm(term, |subterm| count(subterm, left))
    }
    count(term, &mut { limit })
}

/// The most steps each side of a peak takes in [`BackendDefinition::peak_joins`].
pub(super) const JOIN_STEPS: usize = 8;

/// The levels of nested patterns whose representatives narrowing computes before falling back
/// to coarser ones.
pub(super) const NARROWING_DEPTH: usize = 3;

/// Every pairing of an alternative of `first` with one of `second`, the first's binding kept
/// for a variable both bind; `None` when either has none. More than [`REPRESENTATIVES`]
/// pairings give the one alternative that binds nothing.
fn combine(first: Vec<Substitution>, second: Vec<Substitution>) -> Option<Vec<Substitution>> {
    if first.is_empty() || second.is_empty() {
        return None;
    }
    if first.len() * second.len() > bounds().representatives {
        return Some(vec![Substitution::new()]);
    }
    Some(
        first
            .iter()
            .flat_map(|first| {
                second.iter().map(move |second| {
                    let mut both = second.clone();
                    both.extend(
                        first
                            .iter()
                            .map(|(variable, term)| (variable.clone(), term.clone())),
                    );
                    both
                })
            })
            .collect(),
    )
}

/// `valuation` extended to the as-pattern variables of the left-hand side `left` that it leaves
/// unbound: `p #as V` binds `V` to the instance of `p`.
fn bind_aliases(left: &Term, valuation: &Substitution) -> Substitution {
    fn walk(term: &Term, valuation: &mut Substitution) {
        token::every_immediate_subterm(term, |subterm| {
            walk(subterm, valuation);
            true
        });
        if let TermKind::And(first, second) = term.kind() {
            for (pattern, alias) in [(first, second), (second, first)] {
                if let TermKind::Variable(variable) = alias.kind()
                    && !matches!(pattern.kind(), TermKind::Variable(_))
                    && !valuation.contains_key(variable)
                {
                    let bound = instantiate(pattern, valuation);
                    valuation.insert(variable.clone(), bound);
                }
            }
        }
    }
    let mut extended = valuation.clone();
    walk(left, &mut extended);
    extended
}

/// The instance of the pattern `pattern` at `valuation`, a conjunction of two equal instances
/// (an as-pattern whose variable is bound to its pattern's instance) written once.
fn instantiate(pattern: &Term, valuation: &Substitution) -> Term {
    fn collapse(term: &Term) -> Term {
        let term = term
            .try_map_children(|child| Ok::<_, std::convert::Infallible>(collapse(child)))
            .unwrap_or_else(|never| match never {});
        match term.kind() {
            TermKind::And(first, second) if first == second => first.clone(),
            _ => term,
        }
    }
    collapse(&substitute(pattern, valuation))
}

/// `term` with every occurrence of `from` replaced by `to`.
fn replace_subterm(term: &Term, from: &Term, to: &Term) -> Term {
    if term == from {
        return to.clone();
    }
    term.try_map_children(|child| {
        Ok::<_, std::convert::Infallible>(replace_subterm(child, from, to))
    })
    .unwrap_or_else(|never| match never {})
}

/// The scan memo's key of `term` when it holds names minted for copies: equal for two terms
/// that differ only in those names ([`same_up_to_minted_names`]); `None` for any other term,
/// which is looked up as it is.
pub(super) fn copy_key(term: &Term) -> Option<u64> {
    term.attributes()
        .variables
        .iter()
        .any(minted)
        .then(|| shape_hash(term, &|variable| !minted(variable)))
}

/// Whether `second` is `first` with the names minted for copies renamed one-to-one.
pub(super) fn same_up_to_minted_names(first: &Term, second: &Term) -> bool {
    first == second || renamed_from(first, second, &|variable| !minted(variable))
}

/// Calls `visit` on every subterm of the left-hand side `left` below its root that is not a
/// variable, outermost first; a conjunction (an as-pattern) is visited through its conjuncts,
/// at the root as below it.
fn for_each_subterm_below_root(left: &Term, visit: &mut dyn FnMut(&Term)) {
    match left.kind() {
        TermKind::And(first, second) => {
            for_each_subterm_below_root(first, visit);
            for_each_subterm_below_root(second, visit);
        }
        _ => {
            token::every_immediate_subterm(left, |subterm| {
                for_each_subterm(subterm, visit);
                true
            });
        }
    }
}

fn for_each_subterm(term: &Term, visit: &mut dyn FnMut(&Term)) {
    match term.kind() {
        TermKind::Variable(_) => {}
        TermKind::And(first, second) => {
            for_each_subterm(first, visit);
            for_each_subterm(second, visit);
        }
        _ => {
            visit(term);
            token::every_immediate_subterm(term, |subterm| {
                for_each_subterm(subterm, visit);
                true
            });
        }
    }
}

/// Whether `pattern`, a left-hand side subterm of the definition, has a conjunction at or
/// below its root.
fn contains_conjunction(pattern: &Term) -> bool {
    matches!(pattern.kind(), TermKind::And(..))
        || !token::every_immediate_subterm(pattern, |subterm| !contains_conjunction(subterm))
}

/// The [`PatternFacts`] of `definition`.
///
/// The value roots come first: they read only the equations' right-hand sides. The equations
/// with normal left-hand side arguments and the overlaps of every equation with a fixed root
/// ([`Overlaps`]) are then found in rounds. The first round reads the empty set and unbounded
/// overlaps; each round adds the equations whose left-hand side's immediate subterms are normal
/// patterns, and recomputes every equation's overlaps, when instance normality reads the
/// previous round's facts: an equation in the set is excluded from a scan by its syntax, any
/// other by the reducts of its arguments, and either only where its overlaps miss the subject
/// (`BackendDefinition::excluded`). Every answer given during a round reads sound facts, so
/// every fact the round derives is sound, and the set keeps every equation once added. Each
/// round's facts are a function of the previous round's, so the result does not depend on the
/// order of the equations (each left-hand side is tested, and each equation's overlaps computed,
/// in a scan scope of its own, from an empty memo). The rounds stop when one changes nothing,
/// after [`PATTERN_FACT_ROUNDS`], or after the round in which the computation's narrowing
/// budget (`super::PATTERN_FACTS_WORK`) is spent, whose facts are sound too: past the budget
/// every narrowing binds nothing.
///
/// The overlaps need not settle by themselves: an equation that overlaps itself below its root
/// can store, in each round, terms built from the previous round's. Kept as their most general
/// members, terms that only nest the previous ones deeper add nothing and the rounds settle;
/// for any other chain, an equation's overlaps that have changed in [`OVERLAP_CHANGES`] rounds
/// are fixed, at the next change, to the coarse cover
/// ([`BackendDefinition::coarse_overlaps`]), which reads no round's facts and so stays sound
/// and unchanged. Each equation's overlaps then change a bounded number of times and the
/// normal-argument set only grows, so a round that changes nothing comes after a number of
/// rounds bounded by the number of equations.
///
/// The exclusion of an equation outside the set decides the instance normality of terms that are
/// not subterms of the term asked: the arguments of other left-hand sides and right-hand sides
/// instantiated by narrowing ([`BackendDefinition::misses_values`]). Those decisions can come back
/// to a term being decided (`f(f(inj(k(X)))) = c` asks about `f(inj(k(X)))` while deciding it),
/// and narrowing builds new terms at each level. A term asked while being decided is answered
/// "not instance-normal", and at most `super::VALUE_QUESTIONS` such exclusions are open at once
/// (`super::ValueQuestion`); both answers are conservative, so every answer stays sound.
///
/// The computation starts its own scan memo (and restores the caller's afterwards): it runs on
/// first use, which may be inside a scan whose memo was filled before the facts existed.
pub(crate) fn pattern_facts(definition: &BackendDefinition) -> PatternFacts {
    let theories = [
        definition.function_theory(),
        definition.simplification_theory(),
    ];
    let unbounded = theories.iter().any(|theory| {
        theory
            .get(&TermIndex::Variable)
            .is_some_and(|groups| groups.values().any(|rules| !rules.is_empty()))
    });
    let value_roots = Arc::new(value_roots(&theories, unbounded));
    let rules = theories
        .into_iter()
        .flat_map(|theory| theory.values())
        .flat_map(|groups| groups.values().flatten())
        .map(AsRef::as_ref)
        .collect::<Vec<&RewriteRule>>();
    let _computing = Computing::start();
    let mut facts = PatternFacts {
        normal_rules: FxHashSet::default(),
        value_roots,
        unbounded,
        overlaps: None,
        exposed: Arc::new(ExposedSorts::of(definition)),
    };
    // How often each equation's overlaps have changed from one round to the next, and the
    // equations whose overlaps are fixed to their coarse cover.
    let mut changes = FxHashMap::<usize, usize>::default();
    let mut fixed = FxHashMap::<usize, Overlaps>::default();
    let mut rounds = 0;
    for _ in 0..bounds().pattern_fact_rounds {
        rounds += 1;
        let approximation = Rc::new(facts.clone());
        APPROXIMATION.with(|slot| *slot.borrow_mut() = Some(approximation));
        let added = rules
            .iter()
            .filter(|rule| !facts.normal_rules.contains(&rule_key(rule)))
            .filter(|rule| {
                let _scope = ScanScope::enter();
                definition.left_hand_side_arguments_normal(&rule.lhs)
            })
            .map(|rule| rule_key(rule))
            .collect::<Vec<_>>();
        let mut overlaps = rules
            .iter()
            .filter(|rule| has_fixed_root(&rule.lhs))
            .map(|rule| {
                let key = rule_key(rule);
                if let Some(fixed) = fixed.get(&key) {
                    return (key, fixed.clone());
                }
                let _scope = ScanScope::enter();
                (key, definition.overlaps_of(rule))
            })
            .collect::<FxHashMap<_, _>>();
        if let Some(previous) = facts.overlaps.as_deref() {
            for rule in &rules {
                let key = rule_key(rule);
                let Some(current) = overlaps.get_mut(&key) else {
                    continue;
                };
                if fixed.contains_key(&key) || previous.get(&key) == Some(&*current) {
                    continue;
                }
                let count = changes.entry(key).or_insert(0);
                *count += 1;
                if *count > bounds().overlap_changes {
                    *current = definition.coarse_overlaps(rule);
                    fixed.insert(key, current.clone());
                }
            }
        }
        let unchanged = added.is_empty()
            && facts
                .overlaps
                .as_deref()
                .is_some_and(|known| *known == overlaps);
        facts.normal_rules.extend(added);
        facts.overlaps = Some(Arc::new(overlaps));
        if unchanged || facts_work_spent() {
            break;
        }
    }
    #[cfg(test)]
    {
        let work = SCAN.with(|scan| scan.borrow().facts_work.unwrap_or_default());
        LAST_FACTS_COST.with(|cost| cost.set(Some(FactsCost { rounds, work })));
    }
    #[cfg(not(test))]
    let _ = rounds;
    facts
}

/// What one [`pattern_facts`] computation cost: its rounds and the narrowing steps they took
/// (tests).
#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct FactsCost {
    pub(crate) rounds: usize,
    pub(crate) work: usize,
}

#[cfg(test)]
thread_local! {
    /// The cost of the last [`pattern_facts`] computation on this thread.
    static LAST_FACTS_COST: std::cell::Cell<Option<FactsCost>> =
        const { std::cell::Cell::new(None) };
}

/// The cost of the last [`pattern_facts`] computation on this thread, if any.
#[cfg(test)]
pub(crate) fn last_facts_cost() -> Option<FactsCost> {
    LAST_FACTS_COST.with(std::cell::Cell::get)
}

/// Whether the left-hand side `left` has a root its instances keep: one whose equations the
/// instance-normal scan and the value certificate ask about.
fn has_fixed_root(left: &Term) -> bool {
    match left.kind() {
        TermKind::And(first, second) => has_fixed_root(first) || has_fixed_root(second),
        _ => matches!(
            left.shape(),
            Shape::DomainValue
                | Shape::Injection
                | Shape::Collection(_)
                | Shape::Application(HeadRole::FreeConstructor | HeadRole::EquationHead)
        ),
    }
}

/// The most rounds [`pattern_facts`] computes. Each round's facts are sound, so stopping before
/// they settle loses precision only.
pub(super) const PATTERN_FACT_ROUNDS: usize = 64;

/// The most rounds, after the first that computes them, in which [`pattern_facts`] lets an
/// equation's overlaps differ from the previous round's; a further change fixes them to the
/// coarse cover ([`BackendDefinition::coarse_overlaps`]). A change exists only because the
/// previous round's stored facts were read to build new terms, so a chain of changes is
/// nesting across rounds, bounded like the nesting inside one question ([`NARROWING_DEPTH`]);
/// and each round reads the whole stored set again, so a longer chain costs more per round.
/// The definitions measured (FUN, the krust-compiled KEVM, MIR and WASM) change an equation's
/// overlaps at most once.
pub(super) const OVERLAP_CHANGES: usize = 3;

/// [`PatternFacts::value_roots`] for every index of `theories` with a fixed root.
fn value_roots(
    theories: &[&Theory; 2],
    unbounded: bool,
) -> BTreeMap<TermIndex, Option<Vec<Stored>>> {
    theories
        .iter()
        .flat_map(|theory| theory.keys())
        .filter(|index| !matches!(index, TermIndex::Variable | TermIndex::And))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .map(|index| {
            let roots = if unbounded {
                None
            } else {
                reachable_roots(theories, index)
            };
            (index.clone(), roots)
        })
        .collect()
}

/// The right-hand sides of the equations indexed by `start`, and of those indexed by the roots
/// of the right-hand sides met, transitively; `None` when one has an open root or its equation
/// an `ensures`.
fn reachable_roots(theories: &[&Theory; 2], start: &TermIndex) -> Option<Vec<Stored>> {
    let mut visited = BTreeSet::from([start.clone()]);
    let mut pending = vec![start.clone()];
    let mut roots = Vec::new();
    while let Some(index) = pending.pop() {
        let equations = theories
            .iter()
            .filter_map(|theory| theory.get(&index))
            .flat_map(|groups| groups.values().flatten());
        for equation in equations {
            let RuleRhs::Term(right) = &equation.rhs else {
                return None;
            };
            if !equation.ensures.is_empty() {
                return None;
            }
            match right.shape() {
                Shape::DomainValue
                | Shape::Injection
                | Shape::Collection(_)
                | Shape::Application(HeadRole::FreeConstructor | HeadRole::EquationHead) => {
                    roots.push(Stored::new(right));
                    let next = term_index(right);
                    if visited.insert(next.clone()) {
                        pending.push(next);
                    }
                }
                Shape::Variable
                | Shape::And
                | Shape::Application(
                    HeadRole::Function { .. } | HeadRole::Uninterpreted | HeadRole::Residual,
                ) => return None,
            }
        }
    }
    Some(roots)
}

/// [`pattern_facts`] in progress on this thread: holds the caller's scan memo, and on drop
/// (also when the computation unwinds) clears the approximation and restores the memo.
struct Computing {
    caller_scan: Scan,
}

impl Computing {
    fn start() -> Self {
        Self {
            caller_scan: SCAN.with(|scan| {
                std::mem::replace(
                    &mut *scan.borrow_mut(),
                    Scan {
                        facts_work: Some(0),
                        ..Scan::default()
                    },
                )
            }),
        }
    }
}

impl Drop for Computing {
    fn drop(&mut self) {
        APPROXIMATION.with(|approximation| *approximation.borrow_mut() = None);
        let caller_scan = std::mem::take(&mut self.caller_scan);
        SCAN.with(|scan| *scan.borrow_mut() = caller_scan);
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;

    /// One sort `A`: constructors `k, s, m, m2 : A -> A`, `j : A x A -> A` and `c, d : A`;
    /// value productions `p, h, n, v : A x A -> A` or `A -> A` with the equations
    /// `{equations}`, each written `head(arguments) = right` over variables of sort `A`.
    fn definition(equations: &[(&str, &[&str], &str)]) -> BackendDefinition {
        let axioms = equations
            .iter()
            .map(|(head, arguments, right)| {
                let memberships = arguments
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| format!(r"\in{{SortA{{}}, R}}(X{index}:SortA{{}}, {argument})"))
                    .fold(r"\top{R}()".to_string(), |rest, membership| {
                        format!(r"\and{{R}}({membership}, {rest})")
                    });
                let variables = (0..arguments.len())
                    .map(|index| format!("X{index}:SortA{{}}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    r"axiom{{R}} \implies{{R}}(\and{{R}}(\top{{R}}(), {memberships}),
                        \equals{{SortA{{}}, R}}({head}{{}}({variables}), \and{{SortA{{}}}}({right}, \top{{SortA{{}}}}()))) [anywhere{{}}()]"
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        let constructor = |name: &str, arity: usize| {
            format!(
                "symbol {name}{{}}({}) : SortA{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]",
                vec!["SortA{}"; arity].join(", ")
            )
        };
        let production = |name: &str, arity: usize| {
            format!(
                "symbol {name}{{}}({}) : SortA{{}} [anywhere{{}}(), function{{}}(), value-production{{}}()]",
                vec!["SortA{}"; arity].join(", ")
            )
        };
        let source = format!(
            "[]\nmodule MAIN\nsort SortA{{}} []\n{}\nendmodule []",
            [
                constructor("k", 1),
                constructor("s", 1),
                constructor("m", 1),
                constructor("m2", 1),
                constructor("j", 2),
                constructor("c", 0),
                constructor("d", 0),
                production("p", 2),
                production("h", 2),
                production("n", 2),
                production("v", 1),
                axioms,
            ]
            .join("\n")
        );
        let syntax = parse_definition(&source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        definition
            .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
            .expect("term should internalize")
    }

    /// A sort-parametric total symbol stands for each of its instantiations: `ite{T}(Bool, T, T)
    /// : T` lets a term of any sort hold a `Bool` term (and one of its own sort) at an exposed
    /// position, and no other; only an argument sort variable absent from the result, as in
    /// `pick{T, U}(U) : T`, lets every sort hold every sort.
    #[test]
    fn a_parametric_total_symbol_exposes_the_sorts_of_its_instances() {
        let exposed = |extra: &str| {
            let source = format!(
                r#"[]
                module MAIN
                hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                sort SortA{{}} []
                sort SortB{{}} []
                symbol a{{}}() : SortA{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol b{{}}() : SortB{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol ka{{}}(SortA{{}}) : SortA{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                hooked-symbol ite{{T}}(SortBool{{}}, T, T) : T
                    [function{{}}(), functional{{}}(), total{{}}(), hook{{}}("KEQUAL.ite")]
                {extra}
                endmodule []"#
            );
            let syntax = parse_definition(&source).expect("definition should parse");
            let definition = BackendDefinition::internalize(&syntax, "MAIN")
                .expect("definition should internalize");
            ExposedSorts::of(&definition)
        };
        let sort = |name: &str| Sort::simple(name);
        let instances = exposed("");
        assert!(instances.may_hold(&sort("SortA"), &sort("SortBool")));
        assert!(instances.may_hold(&sort("SortB"), &sort("SortBool")));
        assert!(instances.may_hold(&sort("SortA"), &sort("SortA")));
        assert!(!instances.may_hold(&sort("SortA"), &sort("SortB")));
        assert!(!instances.may_hold(&sort("SortBool"), &sort("SortA")));
        let free = exposed("symbol pick{T, U}(U) : T [function{}(), total{}()]");
        assert!(free.may_hold(&sort("SortA"), &sort("SortB")));
    }

    /// Whether the ground term `ground` is an instance of `pattern`, each variable bound once.
    fn instance_of(pattern: &Term, ground: &Term, valuation: &mut Substitution) -> bool {
        match (pattern.kind(), ground.kind()) {
            (TermKind::Variable(variable), _) => match valuation.get(variable) {
                Some(bound) => bound == ground,
                None => {
                    valuation.insert(variable.clone(), ground.clone());
                    true
                }
            },
            (
                TermKind::Application {
                    symbol: pattern_symbol,
                    arguments: pattern_arguments,
                    ..
                },
                TermKind::Application {
                    symbol: ground_symbol,
                    arguments: ground_arguments,
                    ..
                },
            ) => {
                pattern_symbol.name == ground_symbol.name
                    && pattern_arguments.len() == ground_arguments.len()
                    && pattern_arguments
                        .iter()
                        .zip(ground_arguments)
                        .all(|(pattern, ground)| instance_of(pattern, ground, valuation))
            }
            _ => pattern == ground,
        }
    }

    /// `source` as a subterm of another equation's left-hand side: its variables carry the
    /// equation marker, as the definition's equation variables do, so they may share a name
    /// with the variables of the equations that narrowing applies to it.
    fn left_hand_side_subterm(definition: &BackendDefinition, source: &str) -> Term {
        let read = term(definition, source);
        let marked = read
            .attributes()
            .variables
            .iter()
            .map(|variable| {
                let marker = crate::term::names::VariableProvenance::Equation.marker();
                let marked = variable.with_name(format!("{marker}{}", variable.name));
                (variable.clone(), Term::variable(marked))
            })
            .collect::<Substitution>();
        substitute(&read, &marked)
    }

    /// Whether some representative of `pattern`, a left-hand side subterm, has the reduct
    /// `reduct` as an instance.
    fn covered(definition: &BackendDefinition, pattern: &str, reduct: &str) -> bool {
        let reduct = term(definition, reduct);
        definition
            .value_representatives(&left_hand_side_subterm(definition, pattern))
            .expect("the representatives should be bounded")
            .iter()
            .any(|representative| instance_of(representative, &reduct, &mut Substitution::new()))
    }

    /// `p(k(Z), V) = m(n(Z, V))`. The instance `p(k(c), s(d))` of `p(Y, s(Z))` has the reduct
    /// `m(n(c, s(d)))`. Narrowing leaves the equation's `Z` unbound (the pattern has `Y` where
    /// the equation has `k(Z)`) and binds `V` to the pattern's `s(Z)`; read as one variable,
    /// the two `Z` would give `m(n(Z, s(Z)))`, which does not cover that reduct.
    #[test]
    fn a_variable_narrowing_leaves_unbound_is_apart_from_the_terms_variables() {
        let definition = definition(&[(
            "p",
            &["k{}(Z:SortA{})", "V:SortA{}"],
            "m{}(n{}(Z:SortA{}, V:SortA{}))",
        )]);
        assert!(covered(
            &definition,
            "p{}(Y:SortA{}, s{}(Z:SortA{}))",
            "m{}(n{}(c{}(), s{}(d{}())))"
        ));
    }

    /// `v(k(Z)) = c` and `h(v(X), V) = m2(n(X, V))`. `h(c, s(Z))` at `Z = d` is the value of
    /// `h(v(k(c)), s(d))`, whose reduct is `m2(n(k(c), s(d)))`. Reading `h`'s argument `v(X)`
    /// through the `v` equation binds `X` to `k(Z)` with the `v` equation's `Z` unbound; read as
    /// the pattern's `Z`, it would give `m2(n(k(Z), s(Z)))`, which does not cover that reduct.
    #[test]
    fn a_variable_a_composed_narrowing_leaves_unbound_is_apart_from_the_terms_variables() {
        let definition = definition(&[
            ("v", &["k{}(Z:SortA{})"], "c{}()"),
            (
                "h",
                &["v{}(X:SortA{})", "V:SortA{}"],
                "m2{}(n{}(X:SortA{}, V:SortA{}))",
            ),
        ]);
        assert!(covered(
            &definition,
            "h{}(c{}(), s{}(Z:SortA{}))",
            "m2{}(n{}(k{}(c{}()), s{}(d{}())))"
        ));
    }

    /// `p(m(p(X, X)), c) = c` reads its argument `p(X, X)` through the previous round's overlap
    /// representatives of `p`, and the overlapped instance repeats what it binds `X` to, so each
    /// round would double the stored instances. Beside it, `p(k(Y), h(s(d), d)) = p(m(c), Y)`.
    /// The facts are computed within the size bound, so the question that asks for them ends
    /// (whatever it answers: this test is about the bound).
    #[test]
    fn a_non_linear_left_hand_side_does_not_double_the_stored_instances_each_round() {
        let definition = definition(&[
            ("p", &["m{}(p{}(X:SortA{}, X:SortA{}))", "c{}()"], "c{}()"),
            (
                "p",
                &["k{}(Y:SortA{})", "h{}(s{}(d{}()), d{}())"],
                "p{}(m{}(c{}()), Y:SortA{})",
            ),
        ]);
        let subject = term(&definition, "p{}(m{}(c{}()), c{}())");
        let _ = definition.instance_normal(&subject);
    }

    /// `p(p(Y, Z), Z) = p(p(c, Z), Z)` overlaps itself below its root, so each round of the
    /// pattern facts reads the previous round's overlap representatives of `p` and builds larger
    /// ones; beside it, `p(d, d) = m(d)`, `v(p(k(c), Z)) = v(k(p(d, d)))` and `v(m(d)) = c`. The
    /// facts are computed within their bounds, so the question that asks for them ends
    /// (whatever it answers: this test is about the bounds).
    #[test]
    fn an_equation_that_overlaps_itself_below_its_root_is_read_within_bounded_work() {
        let definition = definition(&[
            ("v", &["m{}(d{}())"], "c{}()"),
            (
                "v",
                &["p{}(k{}(c{}()), Z:SortA{})"],
                "v{}(k{}(p{}(d{}(), d{}())))",
            ),
            ("p", &["d{}()", "d{}()"], "m{}(d{}())"),
            (
                "p",
                &["p{}(Y:SortA{}, Z:SortA{})", "Z:SortA{}"],
                "p{}(p{}(c{}(), Z:SortA{}), Z:SortA{})",
            ),
        ]);
        let subject = term(&definition, "v{}(m{}(d{}()))");
        let _ = definition.instance_normal(&subject);
    }
}
