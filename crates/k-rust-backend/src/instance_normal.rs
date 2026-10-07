//! Instance normality: whether every instance of a term is a normal form of the equations.
//!
//! A production with `anywhere` equations (an anywhere rule or an overload equation) is not a
//! free constructor. Its equations may identify two of its applications with different
//! arguments: `wrap(s(z)) = wrap(z)` makes `wrap(s(X))` and `wrap(z)` equal for `X = z`. Such an
//! application denotes the value of its normal form under the equations, and the evaluator
//! treats that normal form as a constructor value: distinct normal forms are distinct values.
//! So the arguments of an anywhere head may be compared, and two different arguments may refute
//! an equality, only when the application is known to be a normal form for every valuation of
//! its variables, not merely for the valuation at hand.
//!
//! [`BackendDefinition::instance_normal`] decides that sufficient condition. A term is
//! instance-normal when every ground instance of it (each variable replaced by a normal-form
//! value of its sort) is a normal form:
//!
//! - a domain value or a variable is instance-normal, since a variable ranges over values;
//! - a constructor application or a sort injection is instance-normal when its arguments are:
//!   no equation is headed by a constructor or an injection, so it is normal when its parts are;
//! - an application of an `anywhere` symbol that is not a declared function is instance-normal
//!   when its arguments are and every equation the evaluator may apply to it (headed by that
//!   symbol or by a bare variable, of any priority, `requires` ignored) is excluded: its
//!   left-hand side has instance-normal arguments and either does not syntactically unify with
//!   the application or is refuted on it by equation matching, or, for a left-hand side with
//!   another argument, no reduct of that argument can be the application's at some position
//!   (`patterns.rs`); and in either case no reduct of an overlapped instance of its left-hand
//!   side (one that another step also rewrites, so that the equation may identify two normal
//!   forms) is the application (`patterns.rs`, which also states the peaks the scan assumes
//!   meet). An equation constrains the value its left-hand side denotes; with
//!   instance-normal arguments on both sides, a valuation of the left-hand side denotes an
//!   instance of the application only by being that instance as a term, an instance is one only
//!   if the two terms unify, and a refutation by equation matching holds for every instance. A
//!   left-hand side argument that is not instance-normal (`h(3)` under `h(3) = h(1)`) has
//!   instances whose reducts are other normal forms (`h(1)`), so a failed syntactic test proves
//!   nothing about such an equation. Ignoring `requires` only makes the test report more
//!   applications as possibly rewritten;
//! - a map, list or set term is instance-normal when its elements (keys, values, and the rest)
//!   are and no equation offered its collection index or a bare variable applies to it, as
//!   above: the collection axioms only identify representations of one collection value, which
//!   the matcher's collection matching compares as such, and equations over collection
//!   functions are headed by those functions, not by the collection term;
//! - a declared-function application, any other non-constructor application, and a conjunction
//!   are not instance-normal: their value is whatever their equations make it, so their shape
//!   does not determine their value.
//!
//! The equations scanned for an `anywhere` application or a collection are those equation
//! selection offers it, so the scan answers for every equation of the definition only when
//! selection reaches every term equation that could match an application
//! (`BackendDefinition::equation_selection_complete`). In a definition where it does not (a
//! simplification whose left-hand side is an `\and` of term patterns, filed apart), no
//! `anywhere` application and no collection is instance-normal.
//!
//! [`BackendDefinition::instance_normal`] scans ground terms too. That
//! [`Term::concrete_after_normalization`] holds is a syntactic fact (ground, every head a
//! constructor or an anywhere non-function production), not evidence that no equation applies:
//! the ground `wrap(s(z))` has it and is not a normal form. The answer is an [`InstanceNormal`]
//! token (`token.rs`). This module obtains one only from `InstanceNormal::decide`, which reads
//! the shape of the term it answers for itself and asks this module only for the answers about
//! the term's immediate subterms and for the test that excludes one candidate equation; for an
//! `anywhere` application or a collection it answers only through a scan that enumerates the
//! candidate equations itself, so no path can vouch for such a term without the scan.
//!
//! The syntactic unifiability test asks whether some instance of the subject could match the
//! equation's pattern, not whether two values are equal, so it decomposes every equal-name
//! application purely syntactically and does not recurse into instance normality. It reads the
//! roots through the rigidity classifier (`term::head`): the equation's left-hand side up to
//! equations, the subject as the values it denotes. It treats a pair as possibly unifiable
//! whenever its shape does not settle the question (a function or collection head, differing
//! injection sources, a sort mismatch it cannot interpret), so an answer of "does not unify" is
//! always a proof that the two terms have no common syntactic instance. That is a proof about
//! values only for a left-hand side with instance-normal arguments; the exclusion test uses it
//! only for those, and decides the other equations by the reducts of their arguments
//! (`patterns.rs`). Which equations have such arguments is computed once per definition, in
//! rounds (`patterns::pattern_facts`), since deciding one left-hand side's arguments scans
//! other equations.

mod patterns;
mod token;

use std::{cell::RefCell, collections::HashMap};

use rustc_hash::FxHashMap;

pub(crate) use patterns::{PatternFacts, pattern_facts};
pub(crate) use token::{InstanceNormal, NormalArguments};

use crate::{
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, SortGraph, match_terms_in_definition},
    rule::RewriteRule,
    term::{
        Sort, Term, TermKind, Variable,
        head::{
            Fixed, FixedRoot, Head, InheritedFromArguments, PatternReading, RootComparison,
            Scanned, classify_pattern, classify_value, compare_roots,
        },
    },
};

impl BackendDefinition {
    /// Whether every instance of `term` is a normal form of this definition's equations; see
    /// the [module documentation](self) for the definition and why it is sound to decompose or
    /// refute an `anywhere` head only on applications for which this holds. Makes no
    /// assumption about how `term` was produced.
    #[must_use]
    pub(crate) fn instance_normal(&self, term: &Term) -> Option<InstanceNormal> {
        let _scope = ScanScope::enter();
        self.instance_normal_memoized(term)
    }

    /// The memoized decision. A term asked again while it is being decided (the exclusion of a
    /// non-normal-argument equation decides terms that are not subterms of the scanned one,
    /// `patterns.rs`, and can come back to it) is answered "not instance-normal": the decision
    /// then assumes nothing it has not shown, and every reader of the answer is monotone in it
    /// (a term not shown normal gets more representatives, an equation not excluded leaves
    /// more applications non-normal), so the outer answer stays sound.
    fn instance_normal_memoized(&self, term: &Term) -> Option<InstanceNormal> {
        match ScanScope::known(term) {
            Some(Decision::Decided(normal)) => return normal,
            Some(Decision::Deciding) => return None,
            None => {}
        }
        ScanScope::record(term, Decision::Deciding);
        let normal = self.instance_normal_uncached(term);
        ScanScope::record(term, Decision::Decided(normal));
        normal
    }

    /// `InstanceNormal::decide` reads the shape of `term`; this module supplies the answers
    /// for its subterms, through the call's memo, and the exclusion test.
    fn instance_normal_uncached(&self, term: &Term) -> Option<InstanceNormal> {
        InstanceNormal::decide(
            self,
            term,
            |subterm| self.instance_normal_memoized(subterm),
            |rule, arguments| self.excluded(rule, arguments),
        )
    }

    /// The equations that may reduce some instance of the equation-head application `term`:
    /// those equation selection offers it, of every priority, less those whose left-hand side
    /// does not syntactically unify with `term` or is refuted on it by equation matching (the
    /// exclusion test of the scan). `None` when the list would not be complete or the test
    /// would not be sound: `term` is not an equation-head application, an immediate subterm is
    /// not instance-normal, or equation selection is not complete. With an empty list `term` is
    /// instance-normal; a caller that sets the listed equations aside by other evidence (a
    /// `requires` refuted under a path condition, `simplify::value_production_definedness`)
    /// knows that no equation reduces `term` where that evidence holds.
    pub(crate) fn equations_reaching(&self, term: &Term) -> Option<Vec<&RewriteRule>> {
        let _scope = ScanScope::enter();
        token::unexcluded_candidates(
            self,
            term,
            |subterm| self.instance_normal_memoized(subterm),
            |rule, arguments| self.excluded(rule, arguments),
        )
    }

    /// Whether the equation `rule`, which equation selection offers an application headed like
    /// the scanned subject (`NoEquationReaches::scan` enumerates the candidates), cannot apply
    /// to any instance of that subject. It is excluded when its left-hand side does not
    /// syntactically unify with the subject, or when equation matching, which decides for the
    /// evaluator whether an equation applies to a term, fails on the subject: a failure holds
    /// for every instance of the subject (`matching::match_terms_in_definition`). The second
    /// test knows what the first does not: the sorts of injections and the productions of an
    /// overload family.
    ///
    /// Both tests are about syntactic instances, and an equation constrains the value its
    /// left-hand side denotes. They answer for values when the left-hand side's arguments are
    /// instance-normal ([`Self::pattern_arguments_normal`]). For any other equation the test is
    /// whether the values its left-hand side's arguments can denote miss the subject's at some
    /// position ([`Self::misses_values`]), whatever the syntax says.
    ///
    /// Either way the equation must also not identify the subject with another normal form: no
    /// reduct of an overlapped instance of its left-hand side, one another step also rewrites,
    /// is the subject ([`Self::overlaps_miss`]).
    fn excluded(&self, rule: &RewriteRule, arguments: NormalArguments<'_>) -> bool {
        let subject = arguments.subject();
        let not_an_instance = if self.pattern_arguments_normal(rule) {
            !may_unify(self.sort_graph(), &rule.lhs, arguments)
                || self.matching_refutes(&rule.lhs, subject)
        } else {
            self.misses_values(&rule.lhs, subject, &mut Scanned(self))
        };
        not_an_instance && self.overlaps_miss(rule, subject, &mut Scanned(self))
    }

    /// Whether equation matching refutes the left-hand side `pattern` on `subject`. Matching
    /// needs the two sides' variables apart; renaming the equation would take names from the
    /// request's counter, so a pair that shares a name is not asked.
    fn matching_refutes(&self, pattern: &Term, subject: &Term) -> bool {
        pattern
            .attributes()
            .variables
            .is_disjoint(&subject.attributes().variables)
            && matches!(
                match_terms_in_definition(MatchMode::Evaluate, self, pattern, subject),
                MatchResult::Failed(_)
            )
    }
}

thread_local! {
    /// The state of the outermost [`BackendDefinition::instance_normal`] call on this thread,
    /// if one is open.
    static SCAN: RefCell<Scan> = RefCell::new(Scan::default());
}

/// The state one outermost scan shares with the scans nested in it.
#[derive(Default)]
struct Scan {
    /// The open [`ScanScope`]s.
    scopes: usize,
    /// The instance normality of the terms decided or being decided during the call. Equation
    /// matching inside the scan asks about the subterms of the scanned term again; the answer
    /// is a function of the term and the definition, so it is kept for the call. It is the same
    /// for two terms that differ only in the names of their variables (variables range over
    /// values, and only their identity within the term is read), so terms are looked up up to
    /// the names the pattern facts mint for their copies (`patterns::minted`): a question that
    /// comes back to a fresh copy of a term being decided is recognized as coming back.
    memo: FxHashMap<Term, Decision>,
    /// The entries of [`Self::memo`] whose terms hold names minted for copies, by a hash that
    /// ignores those names, for the lookups the exact table misses.
    copies: FxHashMap<u64, Vec<(Term, Decision)>>,
    /// The value questions (`patterns.rs` `misses_values`) open on this thread.
    open_value_questions: usize,
    /// The narrowing steps (`patterns.rs`) taken since the outermost scan opened.
    work: usize,
    /// While the pattern facts are computed (`patterns::pattern_facts`), the narrowing steps
    /// the whole computation has taken.
    facts_work: Option<usize>,
}

/// A term's entry in the scan memo.
#[derive(Clone, Copy)]
enum Decision {
    /// The term is being decided further up this thread's stack.
    Deciding,
    Decided(Option<InstanceNormal>),
}

/// One outermost [`BackendDefinition::instance_normal`] call; nested calls share its memo.
struct ScanScope(());

impl ScanScope {
    fn enter() -> Self {
        SCAN.with(|scan| {
            let mut scan = scan.borrow_mut();
            if scan.scopes == 0 {
                scan.work = 0;
            }
            scan.scopes += 1;
        });
        Self(())
    }

    fn known(term: &Term) -> Option<Decision> {
        SCAN.with(|scan| {
            let scan = scan.borrow();
            if let Some(decision) = scan.memo.get(term) {
                return Some(*decision);
            }
            let key = patterns::copy_key(term)?;
            scan.copies
                .get(&key)?
                .iter()
                .find(|(known, _)| patterns::same_up_to_minted_names(known, term))
                .map(|(_, decision)| *decision)
        })
    }

    fn record(term: &Term, decision: Decision) {
        SCAN.with(|scan| {
            let mut scan = scan.borrow_mut();
            scan.memo.insert(term.clone(), decision);
            if let Some(key) = patterns::copy_key(term) {
                let entries = scan.copies.entry(key).or_default();
                match entries
                    .iter_mut()
                    .find(|(known, _)| patterns::same_up_to_minted_names(known, term))
                {
                    Some((_, known)) => *known = decision,
                    None => entries.push((term.clone(), decision)),
                }
            }
        });
    }
}

impl Drop for ScanScope {
    fn drop(&mut self) {
        SCAN.with(|scan| {
            let mut scan = scan.borrow_mut();
            scan.scopes -= 1;
            if scan.scopes == 0 {
                scan.memo.clear();
                scan.copies.clear();
            }
        });
    }
}

/// One open value question (`patterns.rs` `misses_values`): while it is open, the questions
/// nested in it count against [`VALUE_QUESTIONS`].
struct ValueQuestion(());

impl ValueQuestion {
    /// Opens a question, unless [`VALUE_QUESTIONS`] are already open on this thread.
    fn open() -> Option<Self> {
        SCAN.with(|scan| {
            let mut scan = scan.borrow_mut();
            (scan.open_value_questions < bounds().value_questions).then(|| {
                scan.open_value_questions += 1;
                Self(())
            })
        })
    }
}

impl Drop for ValueQuestion {
    fn drop(&mut self) {
        SCAN.with(|scan| scan.borrow_mut().open_value_questions -= 1);
    }
}

/// The most value questions open at once on a thread. A question decides the instance
/// normality of terms built from left-hand sides and right-hand sides (not subterms of the
/// scanned term), whose scans can ask further questions; the memo's in-progress entries end
/// every chain that comes back to a term, and this bound ends every other chain. A question
/// asked past it answers "not excluded".
const VALUE_QUESTIONS: usize = 8;

/// Takes one narrowing step (`patterns.rs`) from the budgets of the outermost scan
/// ([`Bounds::scan_work`]) and of the pattern facts' computation when one is running
/// ([`Bounds::pattern_facts_work`]); `false`, taking nothing, once either is spent. A narrowing
/// that is refused a step answers as one past any other bound: it binds nothing, so the term
/// it reads stands for any value.
fn take_work() -> bool {
    let bounds = bounds();
    SCAN.with(|scan| {
        let mut scan = scan.borrow_mut();
        if scan.work >= bounds.scan_work
            || scan
                .facts_work
                .is_some_and(|work| work >= bounds.pattern_facts_work)
        {
            return false;
        }
        scan.work += 1;
        if let Some(work) = &mut scan.facts_work {
            *work += 1;
        }
        true
    })
}

/// Whether the narrowing budgets ([`take_work`]) are spent.
fn work_spent() -> bool {
    let bounds = bounds();
    SCAN.with(|scan| {
        let scan = scan.borrow();
        scan.work >= bounds.scan_work
            || scan
                .facts_work
                .is_some_and(|work| work >= bounds.pattern_facts_work)
    })
}

/// Whether the pattern facts' narrowing budget ([`take_work`]) is spent.
fn facts_work_spent() -> bool {
    let bounds = bounds();
    SCAN.with(|scan| {
        scan.borrow()
            .facts_work
            .is_some_and(|work| work >= bounds.pattern_facts_work)
    })
}

/// The most narrowing steps one outermost scan takes. The questions a scan asks nest (a value
/// question decides the instance normality of the terms it builds, each of which may ask
/// value questions) and their number grows with the product of the representatives at each
/// level, so [`VALUE_QUESTIONS`] alone bounds their depth but not their work. FUN's scans take a
/// few hundred steps.
const SCAN_WORK: usize = 20_000;

/// The most narrowing steps the pattern facts take over all their rounds. A round can build
/// larger representatives from the previous round's (an equation that overlaps itself below its
/// root), so the rounds need not settle before [`patterns::PATTERN_FACT_ROUNDS`], and each
/// costs more than the last. FUN's facts take about 3,300 steps in all.
const PATTERN_FACTS_WORK: usize = 200_000;

/// The bounds of the questions instance normality and the pattern facts ask. Past each bound
/// the answer is the conservative one ("not excluded", "not normal", representatives without
/// bindings, unbounded overlaps, a peak counted), so lowering any of them may only lose
/// precision. (The work bounds also end every computation the others leave exponential.)
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Bounds {
    /// [`VALUE_QUESTIONS`].
    pub(crate) value_questions: usize,
    /// `patterns::REPRESENTATIVES`.
    pub(crate) representatives: usize,
    /// `patterns::REPRESENTATIVE_SIZE`.
    pub(crate) representative_size: usize,
    /// `patterns::NARROWING_DEPTH`.
    pub(crate) narrowing_depth: usize,
    /// `patterns::JOIN_STEPS`.
    pub(crate) join_steps: usize,
    /// `patterns::PATTERN_FACT_ROUNDS`.
    pub(crate) pattern_fact_rounds: usize,
    /// [`SCAN_WORK`].
    pub(crate) scan_work: usize,
    /// [`PATTERN_FACTS_WORK`].
    pub(crate) pattern_facts_work: usize,
}

impl Bounds {
    /// The bounds every build uses.
    pub(crate) const DEFAULT: Self = Self {
        value_questions: VALUE_QUESTIONS,
        representatives: patterns::REPRESENTATIVES,
        representative_size: patterns::REPRESENTATIVE_SIZE,
        narrowing_depth: patterns::NARROWING_DEPTH,
        join_steps: patterns::JOIN_STEPS,
        pattern_fact_rounds: patterns::PATTERN_FACT_ROUNDS,
        scan_work: SCAN_WORK,
        pattern_facts_work: PATTERN_FACTS_WORK,
    };
}

/// The bounds in force.
fn bounds() -> Bounds {
    Bounds::DEFAULT
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Side {
    /// The equation's left-hand side.
    Pattern,
    /// The instance-normal subject application and its arguments.
    Subject,
}

/// A subterm together with the side it comes from: the two sides' variables are distinct even
/// when their names coincide, which renames the equation apart without rebuilding it.
type Sided<'a> = (Side, &'a Term);

/// Whether the equation pattern `pattern` and the scanned subject have a common syntactic
/// instance, as far as their shape decides it; `false` is a proof that none exists.
///
/// The subject is the one `arguments` names, and the precondition it carries is that the
/// subject's immediate subterms are instance-normal: a subject subterm headed by an `anywhere`
/// production denotes a value with that head, and the subject's own root is the root the
/// equation is tried on (`InheritedFromArguments`).
fn may_unify<'a>(sorts: &'a SortGraph, pattern: &'a Term, arguments: NormalArguments<'a>) -> bool {
    let subject = arguments.subject();
    if let TermKind::Variable(variable) = pattern.kind()
        && sorts_differ(&variable.sort, &subject.sort())
    {
        return false;
    }
    SyntacticUnifier {
        sorts,
        subject_values: InheritedFromArguments(arguments),
        bindings: HashMap::new(),
        pending: Vec::new(),
    }
    .run((Side::Pattern, pattern), (Side::Subject, subject))
}

struct SyntacticUnifier<'a> {
    sorts: &'a SortGraph,
    /// The oracle that fixes the subject side's equation-head roots.
    subject_values: InheritedFromArguments<'a>,
    bindings: HashMap<(Side, &'a Variable), Sided<'a>>,
    pending: Vec<(Sided<'a>, Sided<'a>)>,
}

impl<'a> SyntacticUnifier<'a> {
    fn run(mut self, left: Sided<'a>, right: Sided<'a>) -> bool {
        self.pending.push((left, right));
        while let Some((left, right)) = self.pending.pop() {
            if !self.unify_one(self.resolve(left), self.resolve(right)) {
                return false;
            }
        }
        true
    }

    /// Follow variable bindings until an unbound variable or a non-variable term.
    fn resolve(&self, mut term: Sided<'a>) -> Sided<'a> {
        while let TermKind::Variable(variable) = term.1.kind()
            && let Some(bound) = self.bindings.get(&(term.0, variable))
        {
            term = *bound;
        }
        term
    }

    /// Whether the variable `(side, variable)` occurs in `term` under the current bindings.
    /// Bindings are only added when this is false, so the bindings never form a cycle and the
    /// walk terminates.
    fn occurs(&self, side: Side, variable: &Variable, (term_side, term): Sided<'a>) -> bool {
        term.attributes().variables.iter().any(|other| {
            (term_side == side && other == variable)
                || self
                    .bindings
                    .get(&(term_side, other))
                    .is_some_and(|bound| self.occurs(side, variable, *bound))
        })
    }

    /// Unify one resolved pair; `false` only when the pair has no common instance. A pair whose
    /// shape does not decide the question is dropped, which keeps the answer an
    /// over-approximation of unifiability.
    ///
    /// The lint below covers a match on a single enum written here; it does not see the
    /// wildcard fallback arm of the `(TermKind, TermKind)` match, whose scrutinee is a tuple,
    /// and that arm is intentionally outside it. The match dispatches on structure only: every
    /// root decision in it is taken by `fixed`, `compared_by_root` and `separated`, which match
    /// one enum each under the same lint.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn unify_one(&mut self, left: Sided<'a>, right: Sided<'a>) -> bool {
        if left.0 == right.0 && left.1 == right.1 {
            return true;
        }
        if let TermKind::Variable(variable) = left.1.kind() {
            return self.bind(left.0, variable, right);
        }
        if let TermKind::Variable(variable) = right.1.kind() {
            return self.bind(right.0, variable, left);
        }
        match (left.1.kind(), right.1.kind()) {
            (TermKind::And(first, second), _) => {
                self.pending.push(((left.0, first), right));
                self.pending.push(((left.0, second), right));
                true
            }
            (_, TermKind::And(first, second)) => {
                self.pending.push((left, (right.0, first)));
                self.pending.push((left, (right.0, second)));
                true
            }
            (
                TermKind::DomainValue {
                    sort: left_sort,
                    value: left_value,
                },
                TermKind::DomainValue {
                    sort: right_sort,
                    value: right_value,
                },
            ) => left_sort != right_sort || left_value == right_value,
            (
                TermKind::Application {
                    symbol: left_symbol,
                    sort_arguments: left_sorts,
                    arguments: left_arguments,
                },
                TermKind::Application {
                    symbol: right_symbol,
                    sort_arguments: right_sorts,
                    arguments: right_arguments,
                },
            ) if left_symbol.name == right_symbol.name => {
                if left_arguments.len() != right_arguments.len()
                    || left_sorts
                        .iter()
                        .zip(right_sorts)
                        .any(|(left, right)| sorts_differ(left, right))
                {
                    return false;
                }
                self.pending
                    .extend(left_arguments.iter().zip(right_arguments).map(
                        |(left_argument, right_argument)| {
                            ((left.0, left_argument), (right.0, right_argument))
                        },
                    ));
                true
            }
            (
                TermKind::Injection {
                    source: left_source,
                    target: left_target,
                    term: left_term,
                },
                TermKind::Injection {
                    source: right_source,
                    target: right_target,
                    term: right_term,
                },
            ) if left_source == right_source && left_target == right_target => {
                self.pending
                    .push(((left.0, left_term), (right.0, right_term)));
                true
            }
            // Two injections into one sort from different sorts denote a common value only
            // through a value of both source sorts, that is of a common subsort.
            (
                TermKind::Injection {
                    source: left_source,
                    target: left_target,
                    ..
                },
                TermKind::Injection {
                    source: right_source,
                    target: right_target,
                    ..
                },
            ) => {
                left_target != right_target
                    || self.sorts.known_overlap(left_source, right_source) != Some(false)
            }
            // An injection denotes a value of its source sort, which no application with a
            // fixed root denotes: a free-constructor application is not an injection, and
            // neither is an equation-head application on the subject side, whose root is fixed
            // by the precondition of `may_unify`.
            (TermKind::Injection { .. }, TermKind::Application { .. })
            | (TermKind::Application { .. }, TermKind::Injection { .. }) => !self
                .fixed(left)
                .zip(self.fixed(right))
                .is_some_and(|(left, right)| separated(compare_roots(left, right))),
            // Two different fixed roots have no common instance. This test separates an
            // injection only from an application (the arm above) and a collection from no root:
            // answering "may unify" is always sound here, and equation matching, the scan's
            // second test, compares those pairs with the sort graph and the collection axioms.
            _ => !self
                .fixed(left)
                .zip(self.fixed(right))
                .is_some_and(|(left, right)| {
                    compared_by_root(left)
                        && compared_by_root(right)
                        && separated(compare_roots(left, right))
                }),
        }
    }

    /// The root of one side, when fixed: the equation's left-hand side is read up to equations,
    /// so its equation-head roots are open; the subject is read as the values it denotes.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn fixed(&mut self, (side, term): Sided<'a>) -> Option<Fixed<'a>> {
        let head = match side {
            Side::Pattern => classify_pattern(PatternReading::UpToEquations, term),
            Side::Subject => classify_value(term, &mut self.subject_values),
        };
        match head {
            Head::Fixed(fixed) => Some(fixed),
            Head::Open(_) | Head::Residual => None,
        }
    }

    fn bind(&mut self, side: Side, variable: &'a Variable, term: Sided<'a>) -> bool {
        if let TermKind::Variable(other) = term.1.kind()
            && term.0 == side
            && other == variable
        {
            return true;
        }
        // A cyclic binding has no finite syntactic solution, but a function or collection
        // head on the cycle may still denote it; stop and answer "may unify".
        if self.occurs(side, variable, term) {
            self.pending.clear();
            return true;
        }
        self.bindings.insert((side, variable), term);
        true
    }
}

/// Whether this test separates a fixed root from another fixed root by root alone. An injection
/// is separated only from an application, in the arm written for that pair, and a collection
/// from no root.
#[deny(clippy::wildcard_enum_match_arm)]
fn compared_by_root(fixed: Fixed<'_>) -> bool {
    match fixed.root() {
        FixedRoot::DomainValue | FixedRoot::FreeConstructor | FixedRoot::EquationHead(_) => true,
        FixedRoot::Injection | FixedRoot::Collection(_) => false,
    }
}

/// Whether two fixed roots, compared by root, have no common instance.
#[deny(clippy::wildcard_enum_match_arm)]
fn separated(comparison: RootComparison<'_>) -> bool {
    match comparison {
        RootComparison::Distinct(_) => true,
        // Equal names, two domain values and two injections have arms of their own in
        // `unify_one`; the root alone separates none of these pairs.
        RootComparison::SameApplication(_)
        | RootComparison::ArityMismatch
        | RootComparison::DomainValues
        | RootComparison::Injections
        | RootComparison::Collections(_) => false,
    }
}

/// Whether two sorts are certainly different: both are free of sort variables and unequal.
fn sorts_differ(left: &Sort, right: &Sort) -> bool {
    left != right && !has_sort_variable(left) && !has_sort_variable(right)
}

fn has_sort_variable(sort: &Sort) -> bool {
    match sort {
        Sort::Variable(_) => true,
        Sort::Application { arguments, .. } => arguments.iter().any(has_sort_variable),
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::term::HeadRole;

    /// `wrap` has the equation `wrap(s(z)) = wrap(z)`; `twin` the non-linear `twin(X, X) =
    /// wrap(z)`; `any` the unconditional `any(X) = wrap(z)`; `f` is a declared function.
    fn definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortNat{} []
                sort SortAddress{} []
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol f{}(SortNat{}) : SortNat{} [function{}(), total{}(), no-evaluators{}()]
                symbol wrap{}(SortNat{}) : SortAddress{}
                    [anywhere{}(), functional{}(), injective{}()]
                symbol twin{}(SortNat{}, SortNat{}) : SortAddress{}
                    [anywhere{}(), functional{}(), injective{}()]
                symbol any{}(SortNat{}) : SortAddress{}
                    [anywhere{}(), functional{}(), injective{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(\in{SortNat{}, R}(X0:SortNat{}, s{}(z{}())), \top{R}())
                    ),
                    \equals{SortAddress{}, R}(
                        wrap{}(X0:SortNat{}),
                        \and{SortAddress{}}(wrap{}(z{}()), \top{SortAddress{}}())
                    )
                ) [anywhere{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(
                            \in{SortNat{}, R}(X0:SortNat{}, X:SortNat{}),
                            \and{R}(\in{SortNat{}, R}(X1:SortNat{}, X:SortNat{}), \top{R}())
                        )
                    ),
                    \equals{SortAddress{}, R}(
                        twin{}(X0:SortNat{}, X1:SortNat{}),
                        \and{SortAddress{}}(wrap{}(z{}()), \top{SortAddress{}}())
                    )
                ) [anywhere{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(\in{SortNat{}, R}(X0:SortNat{}, X:SortNat{}), \top{R}())
                    ),
                    \equals{SortAddress{}, R}(
                        any{}(X0:SortNat{}),
                        \and{SortAddress{}}(wrap{}(z{}()), \top{SortAddress{}}())
                    )
                ) [anywhere{}(), owise{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn normal(definition: &BackendDefinition, source: &str) -> bool {
        let term = definition
            .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
            .expect("term should internalize");
        definition.instance_normal(&term).is_some()
    }

    /// Equations whose left-hand side arguments hold as-patterns, as compiled anywhere rules
    /// write them: `wrap(s(z #as G)) = wrap(G)`, `h(3) = h(1)`, and `w(k(h(3) #as G)) = mk(G)`.
    /// An equation is excluded from a scan only when its left-hand side's arguments are normal
    /// patterns: a conjunction is one when both conjuncts are, so `s(z #as G)` is (`wrap(z)` and
    /// `wrap(s(s(z)))` stay instance-normal), while `h(3) #as G` is not, since `h(3)` reduces to
    /// `h(1)`: `w(k(h(1)))`, which that equation makes `mk(h(3))`, is not instance-normal
    /// although the equation does not unify with it as a term. `w(k(h(2)))` is: the reducts of
    /// `h(3)` are `h(3)` and `h(1)`, and neither is `h(2)`.
    #[test]
    fn as_patterns_are_normal_when_their_conjuncts_are() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortNat{} []
                sort SortAddress{} []
                sort SortH{} []
                sort SortK{} []
                sort SortS{} []
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol wrap{}(SortNat{}) : SortAddress{} [anywhere{}(), function{}(), value-production{}()]
                symbol h{}(SortInt{}) : SortH{} [anywhere{}(), function{}(), value-production{}()]
                symbol k{}(SortH{}) : SortK{} [constructor{}(), functional{}(), injective{}()]
                symbol mk{}(SortH{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
                symbol w{}(SortK{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(
                            \in{SortNat{}, R}(X0:SortNat{}, s{}(\and{SortNat{}}(z{}(), G:SortNat{}))),
                            \top{R}()
                        )
                    ),
                    \equals{SortAddress{}, R}(
                        wrap{}(X0:SortNat{}),
                        \and{SortAddress{}}(wrap{}(G:SortNat{}), \top{SortAddress{}}())
                    )
                ) [anywhere{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(\in{SortInt{}, R}(X0:SortInt{}, \dv{SortInt{}}("3")), \top{R}())
                    ),
                    \equals{SortH{}, R}(
                        h{}(X0:SortInt{}),
                        \and{SortH{}}(h{}(\dv{SortInt{}}("1")), \top{SortH{}}())
                    )
                ) [anywhere{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(
                            \in{SortK{}, R}(
                                X0:SortK{},
                                k{}(\and{SortH{}}(h{}(\dv{SortInt{}}("3")), G:SortH{}))
                            ),
                            \top{R}()
                        )
                    ),
                    \equals{SortS{}, R}(
                        w{}(X0:SortK{}),
                        \and{SortS{}}(mk{}(G:SortH{}), \top{SortS{}}())
                    )
                ) [anywhere{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        assert!(normal(&definition, "wrap{}(z{}())"));
        assert!(normal(&definition, "wrap{}(s{}(s{}(z{}())))"));
        assert!(!normal(&definition, "wrap{}(s{}(z{}()))"));
        assert!(normal(&definition, r#"h{}(\dv{SortInt{}}("1"))"#));
        assert!(!normal(
            &definition,
            r#"w{}(k{}(h{}(\dv{SortInt{}}("1"))))"#
        ));
        assert!(normal(&definition, r#"w{}(k{}(h{}(\dv{SortInt{}}("2"))))"#));
    }

    /// `app` is overloaded: `app(inj{V, E}(K0), inj{V, E}(K1)) = inj{V, E}(appV(K0, K1))`, so the
    /// pattern `app(P1, P2)` is not normal on every instance, and
    /// `cur(app(P1, P2), B) = cur(P1, B)` is not excluded from a scan by its syntax alone. The reducts of `app(P1, P2)` are `app`
    /// applications and injections from `V` of `appV` applications, so none is `inj{N, E}(n)`
    /// when `N` and `V` have no common subsort, nor when `N` is below `V` (an injection from `V`
    /// of something other than an injection is not one from `N`). The instances that both
    /// equations rewrite, `cur(app(inj{V, E}(k0), inj{V, E}(k1)), b)`, have the two normal forms
    /// `cur(inj{V, E}(k0), b)` and `cur(inj{V, E}(appV(k0, k1)), b)`, which the equations
    /// identify. With `N` and `V` unrelated neither is `cur(inj{N, E}(n), B)`, which is
    /// instance-normal. With `N` below `V`, `k0 = inj{N, V}(n)` makes the first one
    /// `cur(inj{N, E}(n), b)` (injections compose), equal to
    /// `cur(inj{V, E}(appV(inj{N, V}(n), k1)), b)`: it is not instance-normal. When the `app`
    /// equation's right-hand side is `inj{V, E}(K0)` instead and `N` is below `V`,
    /// `K0 = inj{N, V}(n)` gives the reduct `inj{N, E}(n)`, and it is not either.
    #[test]
    fn a_reducible_pattern_argument_misses_the_roots_its_values_cannot_have() {
        let definition = |subsort: &str, right: &str| {
            let source = format!(
                r#"[]
            module MAIN
                sort SortE{{}} []
                sort SortV{{}} []
                sort SortN{{}} []
                sort SortS{{}} []
                symbol inj{{From, To}}(From) : To [sortInjection{{}}(), injective{{}}()]
                symbol n{{}}() : SortN{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol appV{{}}(SortV{{}}, SortV{{}}) : SortV{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol app{{}}(SortE{{}}, SortE{{}}) : SortE{{}} [anywhere{{}}(), function{{}}(), value-production{{}}()]
                symbol cur{{}}(SortE{{}}, SortE{{}}) : SortS{{}} [anywhere{{}}(), function{{}}(), value-production{{}}()]
                axiom{{R}} \exists{{R}}(V:SortE{{}}, \equals{{SortE{{}}, R}}(V:SortE{{}}, inj{{SortN{{}}, SortE{{}}}}(F:SortN{{}})))
                    [subsort{{SortN{{}}, SortE{{}}}}()]
                axiom{{R}} \exists{{R}}(V:SortE{{}}, \equals{{SortE{{}}, R}}(V:SortE{{}}, inj{{SortV{{}}, SortE{{}}}}(F:SortV{{}})))
                    [subsort{{SortV{{}}, SortE{{}}}}()]
                {subsort}
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        \top{{R}}(),
                        \and{{R}}(
                            \in{{SortE{{}}, R}}(X0:SortE{{}}, inj{{SortV{{}}, SortE{{}}}}(K0:SortV{{}})),
                            \and{{R}}(
                                \in{{SortE{{}}, R}}(X1:SortE{{}}, inj{{SortV{{}}, SortE{{}}}}(K1:SortV{{}})),
                                \top{{R}}()
                            )
                        )
                    ),
                    \equals{{SortE{{}}, R}}(
                        app{{}}(X0:SortE{{}}, X1:SortE{{}}),
                        \and{{SortE{{}}}}(
                            inj{{SortV{{}}, SortE{{}}}}({right}),
                            \top{{SortE{{}}}}()
                        )
                    )
                ) [anywhere{{}}()]
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        \top{{R}}(),
                        \and{{R}}(
                            \in{{SortE{{}}, R}}(X0:SortE{{}}, app{{}}(P1:SortE{{}}, P2:SortE{{}})),
                            \and{{R}}(\in{{SortE{{}}, R}}(X1:SortE{{}}, B:SortE{{}}), \top{{R}}())
                        )
                    ),
                    \equals{{SortS{{}}, R}}(
                        cur{{}}(X0:SortE{{}}, X1:SortE{{}}),
                        \and{{SortS{{}}}}(cur{{}}(P1:SortE{{}}, B:SortE{{}}), \top{{SortS{{}}}}())
                    )
                ) [anywhere{{}}()]
            endmodule []"#
            );
            let syntax = parse_definition(&source).expect("definition should parse");
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
        };
        let subject = "cur{}(inj{SortN{}, SortE{}}(n{}()), B:SortE{})";
        let constructed = "appV{}(K0:SortV{}, K1:SortV{})";
        let apart = definition("", constructed);
        assert!(normal(&apart, subject));
        assert!(!normal(
            &apart,
            "cur{}(app{}(P:SortE{}, Q:SortE{}), B:SortE{})"
        ));
        let n_below_v = r"axiom{R} \exists{R}(V:SortV{}, \equals{SortV{}, R}(V:SortV{}, inj{SortN{}, SortV{}}(F:SortN{})))
                [subsort{SortN{}, SortV{}}()]";
        assert!(!normal(&definition(n_below_v, constructed), subject));
        assert!(!normal(&definition(n_below_v, "K0:SortV{}"), subject));
    }

    /// The overloaded list constructor
    /// `consE(inj{N, E}(K0), inj{Ns, Es}(K1)) = inj{Ns, Es}(consN(K0, K1))` makes `consE(E1, consE(E2, Es))` reducible, so `w(consE(E1, consE(E2, Es))) = mk` is
    /// decided by the reducts of its argument. Those are `consE` applications and, by the overload
    /// equation applied below and then at the root, injections of `consN(K0, consN(K0', K1'))`:
    /// lists of at least two elements. So the equation misses `w(inj{Ns, Es}(consN(n, nilN)))`,
    /// which is instance-normal, and reaches `w(inj{Ns, Es}(consN(n, consN(n, nilN))))`, which
    /// is not.
    #[test]
    fn narrowing_follows_the_reducts_of_a_pattern_argument_through_its_subterms() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortN{} []
                sort SortNs{} []
                sort SortE{} []
                sort SortEs{} []
                sort SortS{} []
                symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                axiom{R} \exists{R}(V:SortE{}, \equals{SortE{}, R}(V:SortE{}, inj{SortN{}, SortE{}}(F:SortN{})))
                    [subsort{SortN{}, SortE{}}()]
                axiom{R} \exists{R}(V:SortEs{}, \equals{SortEs{}, R}(V:SortEs{}, inj{SortNs{}, SortEs{}}(F:SortNs{})))
                    [subsort{SortNs{}, SortEs{}}()]
                symbol n{}() : SortN{} [constructor{}(), functional{}(), injective{}()]
                symbol nilN{}() : SortNs{} [constructor{}(), functional{}(), injective{}()]
                symbol consN{}(SortN{}, SortNs{}) : SortNs{} [constructor{}(), functional{}(), injective{}()]
                symbol consE{}(SortE{}, SortEs{}) : SortEs{} [anywhere{}(), function{}(), value-production{}()]
                symbol mk{}() : SortS{} [constructor{}(), functional{}(), injective{}()]
                symbol w{}(SortEs{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(
                            \in{SortE{}, R}(X0:SortE{}, inj{SortN{}, SortE{}}(K0:SortN{})),
                            \and{R}(
                                \in{SortEs{}, R}(X1:SortEs{}, inj{SortNs{}, SortEs{}}(K1:SortNs{})),
                                \top{R}()
                            )
                        )
                    ),
                    \equals{SortEs{}, R}(
                        consE{}(X0:SortE{}, X1:SortEs{}),
                        \and{SortEs{}}(
                            inj{SortNs{}, SortEs{}}(consN{}(K0:SortN{}, K1:SortNs{})),
                            \top{SortEs{}}()
                        )
                    )
                ) [anywhere{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(
                            \in{SortEs{}, R}(
                                X0:SortEs{},
                                consE{}(E1:SortE{}, consE{}(E2:SortE{}, Es:SortEs{}))
                            ),
                            \top{R}()
                        )
                    ),
                    \equals{SortS{}, R}(w{}(X0:SortEs{}), \and{SortS{}}(mk{}(), \top{SortS{}}()))
                ) [anywhere{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        assert!(normal(
            &definition,
            "w{}(inj{SortNs{}, SortEs{}}(consN{}(n{}(), nilN{}())))"
        ));
        assert!(!normal(
            &definition,
            "w{}(inj{SortNs{}, SortEs{}}(consN{}(n{}(), consN{}(n{}(), nilN{}()))))"
        ));
    }

    /// `w(s(X)) = w(X)` and `w(s(s(X))) = {right}` both rewrite `w(s(s(X)))` at the root. With
    /// `{right}` = `w(X)` the two steps meet (`w(s(X))` reaches `w(X)` in one more step), so the
    /// overlap identifies no two normal forms and `w(z)` is instance-normal. With `{right}` =
    /// `w(c)` they do not: `w(z) = w(s(s(z))) = w(c)` identifies two normal forms, and neither
    /// `w(z)` nor `w(c)` is.
    #[test]
    fn a_root_overlap_identifies_normal_forms_only_when_its_steps_do_not_meet() {
        let definition = |right: &str| {
            let equation = |pattern: &str, right: &str| {
                format!(
                    r"axiom{{R}} \implies{{R}}(
                        \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortNat{{}}, R}}(X0:SortNat{{}}, {pattern}), \top{{R}}())),
                        \equals{{SortAddress{{}}, R}}(w{{}}(X0:SortNat{{}}), \and{{SortAddress{{}}}}({right}, \top{{SortAddress{{}}}}()))
                    ) [anywhere{{}}()]"
                )
            };
            let source = format!(
                r"[]
            module MAIN
                sort SortNat{{}} []
                sort SortAddress{{}} []
                symbol z{{}}() : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol c{{}}() : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol s{{}}(SortNat{{}}) : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol w{{}}(SortNat{{}}) : SortAddress{{}} [anywhere{{}}(), function{{}}(), value-production{{}}()]
                {}
                {}
            endmodule []",
                equation("s{}(X:SortNat{})", "w{}(X:SortNat{})"),
                equation("s{}(s{}(X:SortNat{}))", right),
            );
            let syntax = parse_definition(&source).expect("definition should parse");
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
        };
        let joining = definition("w{}(X:SortNat{})");
        assert!(normal(&joining, "w{}(z{}())"));
        assert!(normal(&joining, "w{}(c{}())"));
        assert!(!normal(&joining, "w{}(s{}(z{}()))"));
        let apart = definition("w{}(c{}())");
        assert!(!normal(&apart, "w{}(z{}())"));
        assert!(!normal(&apart, "w{}(c{}())"));
    }

    /// `cur(app(P1, P2), B) = cur(P1, B)` with `app(inj{V, E}(K0), inj{V, E}(K1)) =
    /// inj{V, E}(appV(K0, K1))`. As a plain anywhere equation, the `app` step and the `cur` step
    /// at `cur(app(inj{V, E}(k0), inj{V, E}(k1)), b)` lead to the distinct normal forms
    /// `cur(inj{V, E}(k0), b)` and `cur(inj{V, E}(appV(k0, k1)), b)`, so `cur(inj{V, E}(v), B)` is
    /// not instance-normal. Declared as the overload equation of `app` over `appV`, it only
    /// rewrites how a value of `app` is written, and matching reads `inj{V, E}(appV(k0, k1))` as
    /// `app(inj{V, E}(k0), inj{V, E}(k1))` again: the `cur` equation applies after the step too,
    /// the two steps meet, and `cur(inj{V, E}(v), B)` is instance-normal.
    #[test]
    fn an_overload_step_below_a_left_hand_side_identifies_no_normal_forms() {
        let definition = |app: &str| {
            let source = format!(
                r#"[]
            module MAIN
                sort SortE{{}} []
                sort SortV{{}} []
                sort SortS{{}} []
                symbol inj{{From, To}}(From) : To [sortInjection{{}}(), injective{{}}()]
                symbol v{{}}() : SortV{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol appV{{}}(SortV{{}}, SortV{{}}) : SortV{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol app{{}}(SortE{{}}, SortE{{}}) : SortE{{}} [anywhere{{}}(), function{{}}(), value-production{{}}()]
                symbol cur{{}}(SortE{{}}, SortE{{}}) : SortS{{}} [anywhere{{}}(), function{{}}(), value-production{{}}()]
                axiom{{R}} \exists{{R}}(V:SortE{{}}, \equals{{SortE{{}}, R}}(V:SortE{{}}, inj{{SortV{{}}, SortE{{}}}}(F:SortV{{}})))
                    [subsort{{SortV{{}}, SortE{{}}}}()]
                {app}
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        \top{{R}}(),
                        \and{{R}}(
                            \in{{SortE{{}}, R}}(X0:SortE{{}}, app{{}}(P1:SortE{{}}, P2:SortE{{}})),
                            \and{{R}}(\in{{SortE{{}}, R}}(X1:SortE{{}}, B:SortE{{}}), \top{{R}}())
                        )
                    ),
                    \equals{{SortS{{}}, R}}(
                        cur{{}}(X0:SortE{{}}, X1:SortE{{}}),
                        \and{{SortS{{}}}}(cur{{}}(P1:SortE{{}}, B:SortE{{}}), \top{{SortS{{}}}}())
                    )
                ) [anywhere{{}}()]
            endmodule []"#
            );
            let syntax = parse_definition(&source).expect("definition should parse");
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
        };
        let subject = "cur{}(inj{SortV{}, SortE{}}(v{}()), B:SortE{})";
        let anywhere = r"axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(
                            \in{SortE{}, R}(X0:SortE{}, inj{SortV{}, SortE{}}(K0:SortV{})),
                            \and{R}(\in{SortE{}, R}(X1:SortE{}, inj{SortV{}, SortE{}}(K1:SortV{})), \top{R}())
                        )
                    ),
                    \equals{SortE{}, R}(
                        app{}(X0:SortE{}, X1:SortE{}),
                        \and{SortE{}}(inj{SortV{}, SortE{}}(appV{}(K0:SortV{}, K1:SortV{})), \top{SortE{}}())
                    )
                ) [anywhere{}()]";
        let overload = r"axiom{} \equals{SortE{}, SortE{}}(
                    app{}(inj{SortV{}, SortE{}}(K0:SortV{}), inj{SortV{}, SortE{}}(K1:SortV{})),
                    inj{SortV{}, SortE{}}(appV{}(K0:SortV{}, K1:SortV{}))
                ) [symbol-overload{}(app{}(), appV{}())]";
        assert!(!normal(&definition(anywhere), subject));
        assert!(normal(&definition(overload), subject));
    }

    /// 5104f81b: the ground `wrap(s(z))` is concrete after normalization but not a normal form,
    /// so ground terms are scanned like any other.
    #[test]
    fn ground_terms_are_scanned_whatever_their_shape() {
        let definition = definition();
        let term = |source: &str| {
            definition
                .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
                .expect("term should internalize")
        };
        let redex = term("wrap{}(s{}(z{}()))");
        assert!(redex.concrete_after_normalization());
        assert_eq!(definition.instance_normal(&redex), None);
        let normal = definition.instance_normal(&term("wrap{}(s{}(s{}(z{}())))"));
        assert!(normal.is_some());
        // Its subterm `s(s(z))` inherits the token.
        assert_eq!(
            normal.map(InstanceNormal::argument),
            definition.instance_normal(&term("s{}(s{}(z{}()))"))
        );
        assert_eq!(definition.instance_normal(&term("any{}(z{}())")), None);
    }

    /// ece6117d, B4: a simplification whose left-hand side is an `\and` of term patterns is filed
    /// in the predicate theory, which equation selection never offers an application; here
    /// `\and(tag(s(X)), tag(s(X))) = tag(X)` rewrites `tag(s(z))`, which no offered equation
    /// reaches. With selection incomplete no equation head and no collection is instance-normal;
    /// without the axiom `tag(s(z))` is.
    #[test]
    fn an_equation_selection_does_not_offer_leaves_no_equation_head_instance_normal() {
        let source = |lemma: &str| {
            format!(
                r#"[]
            module MAIN
                sort SortNat{{}} []
                sort SortAddress{{}} []
                hooked-sort SortMap{{}}
                    [hook{{}}("MAP.Map"), unit{{}}(mapUnit{{}}()), element{{}}(mapItem{{}}()), concat{{}}(mapConcat{{}}())]
                symbol z{{}}() : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol s{{}}(SortNat{{}}) : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol tag{{}}(SortNat{{}}) : SortAddress{{}} [anywhere{{}}(), functional{{}}()]
                hooked-symbol mapUnit{{}}() : SortMap{{}} [function{{}}(), total{{}}(), hook{{}}("MAP.unit")]
                hooked-symbol mapItem{{}}(SortNat{{}}, SortNat{{}}) : SortMap{{}}
                    [function{{}}(), total{{}}(), hook{{}}("MAP.element")]
                hooked-symbol mapConcat{{}}(SortMap{{}}, SortMap{{}}) : SortMap{{}}
                    [function{{}}(), hook{{}}("MAP.concat"), assoc{{}}(), comm{{}}()]
                {lemma}
            endmodule []"#
            )
        };
        let lemma = r#"axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortAddress{}, R}(
                        \and{SortAddress{}}(tag{}(s{}(X:SortNat{})), tag{}(s{}(X:SortNat{}))),
                        \and{SortAddress{}}(tag{}(X:SortNat{}), \top{SortAddress{}}())
                    )
                ) [simplification{}()]"#;
        let internalize = |source: String| {
            let syntax = parse_definition(&source).expect("definition should parse");
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
        };
        let incomplete = internalize(source(lemma));
        assert!(incomplete.equation_selection_complete().is_none());
        assert!(!normal(&incomplete, "tag{}(s{}(z{}()))"));
        assert!(!normal(&incomplete, "mapItem{}(z{}(), z{}())"));
        assert!(normal(&incomplete, "s{}(z{}())"));
        let complete = internalize(source(""));
        assert!(complete.equation_selection_complete().is_some());
        assert!(normal(&complete, "tag{}(s{}(z{}()))"));
        assert!(normal(&complete, "mapItem{}(z{}(), z{}())"));
    }

    #[test]
    fn values_variables_and_constructors_over_them_are_instance_normal() {
        let definition = definition();
        assert!(normal(&definition, "X:SortNat{}"));
        assert!(normal(&definition, "s{}(s{}(X:SortNat{}))"));
        assert!(!normal(&definition, "s{}(f{}(X:SortNat{}))"));
        assert!(!normal(&definition, "f{}(z{}())"));
    }

    #[test]
    fn an_anywhere_application_is_normal_when_no_equation_unifies_with_it() {
        let definition = definition();
        assert!(!normal(&definition, "wrap{}(s{}(X:SortNat{}))"));
        assert!(!normal(&definition, "wrap{}(X:SortNat{})"));
        assert!(normal(&definition, "wrap{}(s{}(s{}(X:SortNat{})))"));
        assert!(normal(&definition, "wrap{}(z{}())"));
        assert!(!normal(&definition, "wrap{}(f{}(X:SortNat{}))"));
    }

    /// The equation variables are renamed apart from the subject's, and a non-linear pattern
    /// binds consistently: `twin(z, s(Y))` has no instance with equal arguments.
    #[test]
    fn non_linear_patterns_bind_consistently_and_apart_from_the_subject() {
        let definition = definition();
        assert!(normal(&definition, "twin{}(z{}(), s{}(Y:SortNat{}))"));
        assert!(!normal(&definition, "twin{}(Y:SortNat{}, z{}())"));
        assert!(!normal(&definition, "twin{}(X:SortNat{}, X:SortNat{})"));
    }

    /// A collection argument is a value when its elements are: an anywhere application over a
    /// map stays instance-normal, and a function element in the map does not.
    #[test]
    fn collections_are_instance_normal_when_their_elements_are() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortNat{} []
                sort SortBox{} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol f{}(SortNat{}) : SortNat{} [function{}(), total{}(), no-evaluators{}()]
                symbol box{}(SortMap{}) : SortBox{} [anywhere{}(), functional{}(), injective{}()]
                hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortNat{}, SortNat{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        assert!(normal(&definition, "box{}(mapItem{}(z{}(), z{}()))"));
        assert!(normal(
            &definition,
            "box{}(mapConcat{}(mapItem{}(z{}(), z{}()), M:SortMap{}))"
        ));
        assert!(!normal(&definition, "box{}(mapItem{}(z{}(), f{}(z{}())))"));
    }

    /// Priority and `requires` are ignored: an `owise` equation still rewrites some instances.
    #[test]
    fn every_equation_counts_whatever_its_priority() {
        let definition = definition();
        assert!(!normal(&definition, "any{}(s{}(X:SortNat{}))"));
    }

    /// `lift`, `pick` and `tagged` are anywhere heads with one equation each,
    /// `lift(1) = lift(0)`, `pick(s(X) #as Y) = pick(z)` (an as-pattern is a conjunction) and
    /// `tagged(inj{SortA, SortTop}(X)) = pick(z)`. An application is instance-normal only when
    /// no instance of it is an instance of the equation's left-hand side: a different domain
    /// value, a `z` against `s(X)`, and an injection from a sort with no common subsort with
    /// `SortA`; with `SortC` below both `SortA` and `SortB`, an injection from `SortB` may
    /// denote an injection from `SortA`.
    #[test]
    fn domain_values_conjunctions_and_injection_sources_decide_unifiability() {
        let definition = |overlap: bool| {
            let below_both = if overlap {
                [("SortC", "SortA"), ("SortC", "SortB"), ("SortC", "SortTop")]
                    .map(|(sub, sup)| {
                        format!(
                            r"axiom{{R}} \exists{{R}}(V:{sup}{{}},
                                \equals{{{sup}{{}}, R}}(V:{sup}{{}}, inj{{{sub}{{}}, {sup}{{}}}}(F:{sub}{{}})))
                                [subsort{{{sub}{{}}, {sup}{{}}}}()]"
                        )
                    })
                    .join("\n")
            } else {
                String::new()
            };
            let equation = |head: &str, argument_sort: &str, left: &str, right: &str| {
                format!(
                    r"axiom{{R}} \implies{{R}}(
                        \and{{R}}(
                            \top{{R}}(),
                            \and{{R}}(\in{{{argument_sort}{{}}, R}}(X0:{argument_sort}{{}}, {left}), \top{{R}}())
                        ),
                        \equals{{SortAddress{{}}, R}}(
                            {head}{{}}(X0:{argument_sort}{{}}),
                            \and{{SortAddress{{}}}}({right}, \top{{SortAddress{{}}}}())
                        )
                    ) [anywhere{{}}()]"
                )
            };
            let source = format!(
                r#"[]
                module MAIN
                    sort SortNat{{}} []
                    sort SortAddress{{}} []
                    sort SortTop{{}} []
                    sort SortA{{}} []
                    sort SortB{{}} []
                    sort SortC{{}} []
                    hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                    symbol inj{{From, To}}(From) : To [sortInjection{{}}(), injective{{}}()]
                    symbol z{{}}() : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol s{{}}(SortNat{{}}) : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol a{{}}() : SortA{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol b{{}}() : SortB{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol c{{}}() : SortC{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol lift{{}}(SortInt{{}}) : SortAddress{{}} [anywhere{{}}(), functional{{}}(), injective{{}}()]
                    symbol pick{{}}(SortNat{{}}) : SortAddress{{}} [anywhere{{}}(), functional{{}}(), injective{{}}()]
                    symbol tagged{{}}(SortTop{{}}) : SortAddress{{}} [anywhere{{}}(), functional{{}}(), injective{{}}()]
                    axiom{{R}} \exists{{R}}(V:SortTop{{}},
                        \equals{{SortTop{{}}, R}}(V:SortTop{{}}, inj{{SortA{{}}, SortTop{{}}}}(F:SortA{{}})))
                        [subsort{{SortA{{}}, SortTop{{}}}}()]
                    axiom{{R}} \exists{{R}}(V:SortTop{{}},
                        \equals{{SortTop{{}}, R}}(V:SortTop{{}}, inj{{SortB{{}}, SortTop{{}}}}(F:SortB{{}})))
                        [subsort{{SortB{{}}, SortTop{{}}}}()]
                    {below_both}
                    {lift}
                    {pick}
                    {tagged}
                endmodule []"#,
                lift = equation(
                    "lift",
                    "SortInt",
                    r#"\dv{SortInt{}}("1")"#,
                    r#"lift{}(\dv{SortInt{}}("0"))"#
                ),
                pick = equation(
                    "pick",
                    "SortNat",
                    r"\and{SortNat{}}(s{}(X:SortNat{}), Y:SortNat{})",
                    "pick{}(z{}())"
                ),
                tagged = equation(
                    "tagged",
                    "SortTop",
                    r"inj{SortA{}, SortTop{}}(X:SortA{})",
                    "pick{}(z{}())"
                ),
            );
            let syntax = parse_definition(&source).expect("definition should parse");
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
        };
        let apart = definition(false);
        assert!(normal(&apart, r#"lift{}(\dv{SortInt{}}("2"))"#));
        assert!(normal(&apart, r#"lift{}(\dv{SortInt{}}("0"))"#));
        assert!(!normal(&apart, r#"lift{}(\dv{SortInt{}}("1"))"#));
        assert!(!normal(&apart, "lift{}(I:SortInt{})"));
        assert!(normal(&apart, "pick{}(z{}())"));
        assert!(!normal(&apart, "pick{}(s{}(z{}()))"));
        assert!(!normal(&apart, "pick{}(N:SortNat{})"));
        let from = |sort: &str| format!("tagged{{}}(inj{{{sort}{{}}, SortTop{{}}}}(V:{sort}{{}}))");
        assert!(normal(&apart, &from("SortB")));
        assert!(!normal(&apart, &from("SortA")));
        assert!(!normal(&apart, "tagged{}(T:SortTop{})"));
        let overlapping = definition(true);
        assert!(!normal(&overlapping, &from("SortB")));
        assert!(!normal(&overlapping, &from("SortC")));

        // Unification decomposes an anywhere head only on instance-normal applications, so it
        // keeps as one equation each pair the equations may identify: `pick(s(N))` is
        // `pick(z)` for every `N`, and `lift(I)` is `lift(0)` for `I = 0` and, through the
        // equation `lift(1) = lift(0)`, for `I = 1`; the substitution `I = 0` alone loses
        // `I = 1`.
        let term = |source: &str| {
            apart
                .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
                .expect("term should internalize")
        };
        for (left, right) in [
            ("pick{}(s{}(N:SortNat{}))", "pick{}(z{}())"),
            ("lift{}(I:SortInt{})", r#"lift{}(\dv{SortInt{}}("0"))"#),
        ] {
            let result = crate::unification::unify_term_pairs(
                &apart,
                crate::substitution::Substitution::new(),
                [(term(left), term(right))],
            );
            let crate::unification::UnificationResult::Unified(unified) = &result else {
                panic!("{left} = {right} is satisfiable: {result:?}");
            };
            assert!(unified.substitution.is_empty(), "{left}: {result:?}");
            assert_eq!(unified.constraints.len(), 1, "{left}: {result:?}");
        }
    }

    /// The classifier arms of the syntactic test separate two roots exactly where the rigidity
    /// predicate the test had before them did (`rigid` below is that predicate, transcribed): a
    /// domain value, a free-constructor application and, on the subject side only, an
    /// equation-head application; an injection only from such an application; a collection from
    /// nothing. Checked for every pair of root kinds those arms decide, on every combination of
    /// sides a resolved pair can have.
    #[test]
    fn the_classifier_arms_separate_the_roots_the_rigidity_predicate_did() {
        fn rigid((side, term): Sided<'_>) -> bool {
            match term.kind() {
                TermKind::DomainValue { .. } => true,
                TermKind::Application { symbol, .. } => match symbol.attributes.head_role() {
                    HeadRole::FreeConstructor => true,
                    HeadRole::EquationHead => side == Side::Subject,
                    HeadRole::Function { .. } | HeadRole::Uninterpreted | HeadRole::Residual => {
                        false
                    }
                },
                TermKind::Injection { .. }
                | TermKind::Variable(_)
                | TermKind::And(..)
                | TermKind::Map { .. }
                | TermKind::List { .. }
                | TermKind::Set { .. } => false,
            }
        }
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortNat{} []
                sort SortAddress{} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol f{}(SortNat{}) : SortNat{} [function{}(), total{}(), no-evaluators{}()]
                symbol wrap{}(SortNat{}) : SortAddress{} [anywhere{}(), functional{}()]
                symbol tag{}(SortNat{}) : SortAddress{} [anywhere{}(), functional{}()]
                symbol label{}(SortNat{}) : SortAddress{} [constructor{}(), functional{}(), macro{}()]
                hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortNat{}, SortNat{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let term = |source: &str| {
            definition
                .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
                .expect("term should internalize")
        };
        let zero = term("z{}()");
        let terms = [
            Term::domain_value(Sort::simple("SortNat"), "1"),
            Term::injection(
                Sort::simple("SortNat"),
                Sort::simple("SortAddress"),
                zero.clone(),
            ),
            term("mapItem{}(z{}(), z{}())"),
            zero.clone(),
            term("s{}(z{}())"),
            term("wrap{}(z{}())"),
            term("tag{}(z{}())"),
            term("f{}(z{}())"),
            term("label{}(z{}())"),
        ];
        let arguments = NormalArguments::of_subterms_for_test(&definition, &zero)
            .expect("a constant has no subterms");
        let sides = [Side::Pattern, Side::Subject];
        let mut checked = 0;
        for left in &terms {
            for right in &terms {
                let other_arm = match (left.kind(), right.kind()) {
                    (TermKind::DomainValue { .. }, TermKind::DomainValue { .. })
                    | (TermKind::Injection { .. }, TermKind::Injection { .. }) => true,
                    (
                        TermKind::Application { symbol: left, .. },
                        TermKind::Application { symbol: right, .. },
                    ) => left.name == right.name,
                    _ => false,
                };
                if other_arm {
                    continue;
                }
                for left_side in sides {
                    for right_side in sides {
                        let (left, right) = ((left_side, left), (right_side, right));
                        let expected = match (left.1.kind(), right.1.kind()) {
                            (TermKind::Injection { .. }, TermKind::Application { .. }) => {
                                !rigid(right)
                            }
                            (TermKind::Application { .. }, TermKind::Injection { .. }) => {
                                !rigid(left)
                            }
                            _ => !(rigid(left) && rigid(right)),
                        };
                        let mut unifier = SyntacticUnifier {
                            sorts: definition.sort_graph(),
                            subject_values: InheritedFromArguments(arguments),
                            bindings: HashMap::new(),
                            pending: Vec::new(),
                        };
                        assert_eq!(
                            unifier.unify_one(left, right),
                            expected,
                            "{left:?} against {right:?}"
                        );
                        checked += 1;
                    }
                }
            }
        }
        // Nine roots on each side, less the two same-kind pairs and the six same-name pairs.
        assert_eq!(checked, 4 * (9 * 9 - 2 - 6));
    }
}
