//! Portable SMT-LIB translation shared by native Z3 and solver-free builds.
//! Definition-local eligibility admits pure functional contexts as query-local UFs.
//! Operand eligibility visits each distinct term DAG node once per query; lexical let bindings
//! keep shared composite operands from expanding exponentially in the script.
//! A reachability search over generated constants and function names selects the conjuncts a
//! validity check sends (`closure_over`); this module has no counter of its own.

#![deny(clippy::wildcard_enum_match_arm)]

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    sync::Arc,
};

use k_rust_kore::names::BuiltinSort;
use num_bigint::BigInt;
use num_traits::{One, Zero};
use rustc_hash::FxHashMap;

use crate::{
    definition::BackendDefinition,
    matching::SortGraph,
    model::ModelQuery,
    rewrite::substitute_predicates,
    rule::{Predicate, RewriteRule, RuleRhs, Theory},
    stop::{PreludeSignal, Stoppable},
    substitution::Substitution,
    term::{HeadRole, Name, Sort, SortNode, Term, TermKind, Variable},
};

#[cfg(feature = "z3")]
mod aliases;
#[cfg(feature = "z3")]
mod congruence;
#[cfg(feature = "z3")]
mod query;
#[cfg(feature = "z3")]
mod z3;

mod functional;
mod literal;
mod observation;
#[cfg(any(feature = "z3", test))]
mod word;

#[cfg(any(feature = "z3", test))]
mod summary;

#[cfg(feature = "z3")]
use query::TranslatedQuery;

#[cfg(feature = "z3")]
pub use z3::{Z3Options, Z3Solver, z3_version};

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SmtType {
    Lib(String),
    Hook(SExpr),
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

impl SExpr {
    pub fn atom(value: impl Into<String>) -> Self {
        Self::Atom(value.into())
    }

    pub fn parse(source: &str) -> Result<Self, SExprError> {
        let mut parser = SExprParser::new(source);
        let expression = parser.expression()?;
        parser.skip_whitespace();
        if parser.peek().is_some() {
            return Err(SExprError::TrailingInput(parser.offset));
        }
        Ok(expression)
    }

    fn application(operator: impl Into<String>, arguments: Vec<Self>) -> Self {
        let mut items = Vec::with_capacity(arguments.len() + 1);
        items.push(Self::atom(operator));
        items.extend(arguments);
        Self::List(items)
    }
}

impl fmt::Display for SExpr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Atom(atom) => formatter.write_str(atom),
            Self::List(items) => {
                formatter.write_str("(")?;
                for (index, item) in items.iter().enumerate() {
                    if index != 0 {
                        formatter.write_str(" ")?;
                    }
                    write!(formatter, "{item}")?;
                }
                formatter.write_str(")")
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SExprError {
    UnexpectedEnd,
    UnexpectedClose(usize),
    UnterminatedList(usize),
    EmptyAtom(usize),
    TrailingInput(usize),
}

/// Offsets are zero-based byte offsets into the parsed text.
impl fmt::Display for SExprError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedEnd => {
                formatter.write_str("the text ends where an expression is expected")
            }
            Self::UnexpectedClose(offset) => {
                write!(formatter, "the ')' at byte offset {offset} closes no list")
            }
            Self::UnterminatedList(offset) => write!(
                formatter,
                "the list opened at byte offset {offset} is not closed"
            ),
            Self::EmptyAtom(offset) => write!(
                formatter,
                "the character at byte offset {offset} cannot begin an expression"
            ),
            Self::TrailingInput(offset) => write!(
                formatter,
                "text follows the expression at byte offset {offset}"
            ),
        }
    }
}

struct SExprParser<'a> {
    source: &'a str,
    offset: usize,
}

impl<'a> SExprParser<'a> {
    fn new(source: &'a str) -> Self {
        Self { source, offset: 0 }
    }

    fn expression(&mut self) -> Result<SExpr, SExprError> {
        self.skip_whitespace();
        match self.peek() {
            None => Err(SExprError::UnexpectedEnd),
            Some('(') => self.list(),
            Some(')') => Err(SExprError::UnexpectedClose(self.offset)),
            Some(_) => self.atom(),
        }
    }

    fn list(&mut self) -> Result<SExpr, SExprError> {
        let start = self.offset;
        self.bump();
        let mut items = Vec::new();
        loop {
            self.skip_whitespace();
            match self.peek() {
                Some(')') => {
                    self.bump();
                    return Ok(SExpr::List(items));
                }
                None => return Err(SExprError::UnterminatedList(start)),
                Some(_) => items.push(self.expression()?),
            }
        }
    }

    fn atom(&mut self) -> Result<SExpr, SExprError> {
        let start = self.offset;
        while self.peek().is_some_and(|character| {
            !character.is_whitespace() && !matches!(character, '(' | ')' | ';')
        }) {
            self.bump();
        }
        if self.offset == start {
            return Err(SExprError::EmptyAtom(start));
        }
        Ok(SExpr::atom(&self.source[start..self.offset]))
    }

    fn skip_whitespace(&mut self) {
        while self.peek().is_some_and(char::is_whitespace) {
            self.bump();
        }
    }

    fn peek(&self) -> Option<char> {
        self.source[self.offset..].chars().next()
    }

    fn bump(&mut self) {
        if let Some(character) = self.peek() {
            self.offset += character.len_utf8();
        }
    }
}

/// Whether an SMT-LIB translation denotes exactly the predicates it was made from.
///
/// Every abstraction of the translation over-approximates: eligible pure functional heads
/// and compatible injections become query-local uninterpreted functions retaining congruence;
/// partial domains retain separate source conditions and Boolean head functions;
/// other terms or predicates without an SMT translation become unrelated fresh constants.
/// Neither reading adds constructor injectivity. A free or quantified variable of a sort other
/// than `Int` or `Bool` ranges over an uninterpreted sort that need not have the K sort's values,
/// and an `smtlib` symbol retains congruence. Abstraction alone therefore lets every K
/// valuation that satisfies the predicates induce a model of the translation. A model is a K
/// valuation of the predicates only when the translation is `Exact`.
///
/// A partial function translated as a total SMT operation has a value where K has none, so the
/// translation states each atom with the domains of its operands (`atom_with_domains`): an atom
/// over an undefined term denotes in SMT what it denotes in K, whatever the form of the
/// predicates, and `Unsat` refutes them (docs/compatibility.md, "Solver decisions over partial
/// operations"). The partial function itself costs no exactness (GAP K29): every model of a
/// translation whose domain reads are closed formulas over hooked operations gives each atom
/// its K meaning at the model's values of the free variables, since the `smt-hook` is exact
/// where the term is defined and the atom reads it nowhere else; so restricted to those
/// variables, the model is a K valuation of the predicates. A domain the definition does not
/// decide is a domain function or an opaque atom, which a model may set true where the term is
/// undefined, so each such read is `Approximate` (`functional::translate_domain`), as are an
/// atom read without its operands' domains (`atom_readings`), an observation's value, a
/// summary whose body is, and a power with a symbolic exponent, whose value outside the cases
/// that fix it is the uninterpreted `KRUST-POWER`.
/// SMT hook translations, SMT lemma axioms and the user prelude are trusted, except that a power
/// with a symbolic exponent is read only where an integer is its value, and there by its value's
/// cases (`guard_powers`), and that a hook is
/// read at all only where its operation is a term at the application's sorts
/// (`hook_is_well_sorted`): elsewhere the application is abstracted. Every SMT term of an
/// uninterpreted sort therefore contains a declared constant, a bound variable or an `smtlib`
/// function of that sort, each of which records `Approximate`, so no translation over a sort the
/// solver does not interpret is `Exact`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Exactness {
    Approximate,
    Exact,
}

impl Exactness {
    /// The exactness of a translation made of two parts: exact only when both parts are.
    pub const fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::Exact, Self::Exact) => Self::Exact,
            (Self::Approximate, _) | (_, Self::Approximate) => Self::Approximate,
        }
    }
}

/// Immutable definition-local eligibility. Query names and expressions never live here.
#[derive(Clone, Debug, Eq, PartialEq)]
struct CongruencePolicy {
    heads: BTreeSet<Name>,
    effects: BTreeSet<String>,
    sorts: SortGraph,
}

impl CongruencePolicy {
    fn from_definition(definition: &BackendDefinition) -> Option<Self> {
        let effects = definition.console_effect_symbols()?;
        let heads = definition
            .symbols()
            .values()
            .filter(|symbol| {
                matches!(
                    symbol.attributes.head_role(),
                    HeadRole::Function { declared: true, .. } | HeadRole::FreeConstructor
                ) && !symbol.attributes.binder
                    && !symbol.attributes.macro_or_alias
                    && !effects.contains(symbol.name.as_ref())
            })
            .map(|symbol| symbol.name.clone())
            .collect();
        Some(Self {
            heads,
            effects,
            sorts: definition.sort_graph().clone(),
        })
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum CongruenceHead {
    Application {
        name: Name,
        sorts: Vec<Sort>,
        arguments: Vec<Sort>,
        result: Sort,
    },
    Injection {
        source: Sort,
        target: Sort,
    },
}

impl CongruenceHead {
    fn rank(&self) -> (Vec<Sort>, Sort) {
        match self {
            Self::Application {
                arguments, result, ..
            } => (arguments.clone(), *result),
            Self::Injection { source, target } => (vec![*source], *target),
        }
    }
}

/// The value `let`s of one lexical scope (`LetScope`). Parents refer to let-bound values; the
/// value lets of a scope are bound outside its domain lets, which may read them.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct SharedTerms {
    values: FxHashMap<Term, SExpr>,
    bindings: Vec<(String, SExpr)>,
}

impl SharedTerms {
    fn bind(&self, body: SExpr) -> SExpr {
        bind_shared(&self.bindings, body)
    }
}

/// One lexical scope of shared `let`s: a root predicate's or term's (`variable` is `None`), or
/// a quantifier's body, which binds `variable`. The scopes open at a point of the translation
/// form a stack, outermost first, and the expression being built lies inside all of them.
///
/// A `let` is visible in its scope, and an SMT term that mentions no variable a quantifier
/// binds denotes the same inside the quantifier and outside it. So the domain or value of a
/// node is bound in the outermost scope where both its meaning and its text are available: no
/// scope above it binds a variable of the node (`TranslationState::term_level`), and its text
/// names no `let` or bound variable of a scope above it (`TranslationState::text_level`). The
/// node is then named once for every binder below that scope that reads it, rather than once
/// per binder. A scope's bindings are emitted when it closes, values outside domains, and only
/// those its body needs (`bind_shared`).
#[derive(Clone, Debug, Eq, PartialEq)]
struct LetScope {
    variable: Option<Variable>,
    domains: Option<functional::SharedDomains>,
    terms: Option<SharedTerms>,
}

impl LetScope {
    fn bind(&self, mut body: SExpr) -> SExpr {
        if let Some(domains) = &self.domains {
            body = domains.bind(body);
        }
        if let Some(terms) = &self.terms {
            body = terms.bind(body);
        }
        body
    }

    /// The SMT names this scope introduces: its bound variable's and its lets'.
    fn names(&self) -> impl Iterator<Item = &String> {
        self.domains
            .iter()
            .flat_map(|domains| domains.bindings.iter().map(|(name, _)| name))
            .chain(
                self.terms
                    .iter()
                    .flat_map(|terms| terms.bindings.iter().map(|(name, _)| name)),
            )
    }
}

/// Close the transitive dependencies of a lexical result, rather than copying unrelated
/// earlier observations into every source fact. Bindings are topologically ordered and
/// their names come from this query's unique SMT namespace.
fn bind_shared(bindings: &[(String, SExpr)], mut body: SExpr) -> SExpr {
    if bindings.is_empty() {
        return body;
    }
    debug_assert!(bindings.iter().all(|(name, _)| name.starts_with("SMT-")));
    let mut needed = smt_variables(&body);
    let mut kept = Vec::new();
    for (name, value) in bindings.iter().rev() {
        if needed.remove(name.as_str()) {
            needed.extend(smt_variables(value));
            kept.push((name, value));
        }
    }
    drop(needed);
    for (name, value) in kept {
        body = SExpr::List(vec![
            SExpr::atom("let"),
            SExpr::List(vec![SExpr::List(vec![
                SExpr::atom(name.clone()),
                value.clone(),
            ])]),
            body,
        ]);
    }
    body
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TranslationState {
    pub mappings: BTreeMap<Term, String>,
    congruence: Option<Arc<CongruencePolicy>>,
    opaque_functions: BTreeMap<CongruenceHead, String>,
    domain_functions: BTreeMap<CongruenceHead, String>,
    /// The domain functions the query applies at a single point, declared as constants.
    single_point_domains: BTreeSet<String>,
    domains: BTreeMap<Term, Arc<[Predicate]>>,
    /// Facts of the conditional ceil equations at a partial application whose domain is its
    /// head's domain function (`functional::domain_lemmas`), each stated once per binder scope.
    domain_lemmas: BTreeMap<Term, Arc<[Predicate]>>,
    domain_lemma_seen: BTreeSet<(Term, Vec<String>)>,
    observations: BTreeMap<Term, Arc<crate::observation::reading::Reading>>,
    observation_demands: BTreeMap<Term, Vec<Term>>,
    observation_facts: BTreeMap<Term, Vec<Predicate>>,
    observation_fact_seen: BTreeSet<(Term, Vec<String>)>,
    observation_reading_seen: BTreeSet<(Term, Vec<String>)>,
    domain_link_seen: BTreeSet<(Term, Vec<String>)>,
    active_observations: BTreeSet<Term>,
    list_congruence: BTreeMap<Sort, Arc<crate::term::ListDefinition>>,
    map_congruence: BTreeMap<Sort, Arc<crate::term::MapDefinition>>,
    summary_congruence: BTreeSet<CongruenceHead>,
    #[cfg(any(feature = "z3", test))]
    active_summary_links: BTreeSet<Term>,
    #[cfg(any(feature = "z3", test))]
    summary_cases: BTreeMap<CongruenceHead, Vec<summary::Key>>,
    #[cfg(any(feature = "z3", test))]
    active_summary_cases: BTreeSet<CongruenceHead>,
    #[cfg(any(feature = "z3", test))]
    summary_case_seen: BTreeSet<(Term, Vec<String>)>,
    #[cfg(any(feature = "z3", test))]
    summary_case_budget: usize,
    domain_facts: Vec<SExpr>,
    /// The open `let` scopes, outermost first (`LetScope`).
    scopes: Vec<LetScope>,
    /// The scope index of each `let` name and bound variable name of an open scope, which a
    /// text referring to it must lie inside (`text_level`).
    name_levels: FxHashMap<String, usize>,
    eligible_operands: FxHashMap<Term, bool>,
    word_predicates: BTreeMap<Predicate, SExpr>,
    word_demands: BTreeSet<Predicate>,
    #[cfg(any(feature = "z3", test))]
    summaries: BTreeMap<summary::Key, summary::Reading>,
    derived_definitions: Vec<String>,
    predicate_mappings: Vec<(Predicate, String)>,
    /// The names of `predicate_mappings`, for a lookup that does not scan them.
    predicate_mapping_names: FxHashMap<Predicate, String>,
    /// Translate an atom as its reading alone, without its operands' domains: set by a reading
    /// that is related to another under those domains (the word plans' scalar fallback,
    /// `word::prepare`), never for a predicate the query asserts.
    atom_readings: bool,
    /// Domain readings that fell back to an opaque domain (a head's domain function or an
    /// opaque `\ceil` atom), counted to report the atoms whose operands read one
    /// (`Counter::SmtOpaqueAtomDomains`).
    opaque_domain_reads: usize,
    /// Terms whose `\ceil` is a conjunct of a conjunction enclosing the predicate being
    /// translated (`translate_predicates`, `translate_query_in_state`), or the children of the
    /// domain whose own condition is being translated (`translate_domain_node`), whose domains
    /// are conjoined beside it. Within a conjunction `φ /\ \ceil(t)` is `φ[D(t) := true] /\
    /// \ceil(t)`, so an atom over such a term states no copy of its domain
    /// (`operand_domain`). Set aside wherever a translation becomes a fact of its own
    /// (`record_source_fact` from an observation or a domain), and filtered under a binder.
    stated_defined: Vec<Term>,
    /// The facts tying a decided domain to its head's domain function, closed, with that
    /// function's name (`translate_domain_node`). One is asserted only when the query also reads
    /// the function as an undecided domain (`undecided_domain_heads`), the only reading it
    /// relates the decided instance to: alone, it constrains a function nothing else reads.
    pending_domain_links: Vec<(String, SExpr)>,
    /// Facts of the integer power at the powers whose exponent is not a numeral
    /// (`record_power`), asserted with the known predicates.
    power_facts: Vec<SExpr>,
    /// The base and exponent of each power `power_facts` states facts at, closed.
    powers: Vec<(SExpr, SExpr)>,
    undecided_domain_heads: BTreeSet<String>,
    /// Terms a plan admission found free of term-level `\and`s (`functional::admit_conditions`).
    conjunction_free: rustc_hash::FxHashSet<Term>,
    dependent_mappings: BTreeMap<(Predicate, Vec<Sort>), String>,
    bound_variables: Vec<(Variable, String)>,
    counter: usize,
    /// The exactness of everything translated so far; lowered by each site that approximates.
    exactness: Exactness,
    /// Whether the translation has written text it did not author (`Self::write_foreign_text`).
    foreign_text: bool,
}

impl Default for TranslationState {
    fn default() -> Self {
        Self::new()
    }
}

impl TranslationState {
    pub fn new() -> Self {
        Self {
            mappings: BTreeMap::new(),
            congruence: None,
            opaque_functions: BTreeMap::new(),
            domain_functions: BTreeMap::new(),
            single_point_domains: BTreeSet::new(),
            domains: BTreeMap::new(),
            domain_lemmas: BTreeMap::new(),
            domain_lemma_seen: BTreeSet::new(),
            observations: BTreeMap::new(),
            observation_demands: BTreeMap::new(),
            observation_facts: BTreeMap::new(),
            observation_fact_seen: BTreeSet::new(),
            observation_reading_seen: BTreeSet::new(),
            domain_link_seen: BTreeSet::new(),
            active_observations: BTreeSet::new(),
            list_congruence: BTreeMap::new(),
            map_congruence: BTreeMap::new(),
            summary_congruence: BTreeSet::new(),
            #[cfg(any(feature = "z3", test))]
            active_summary_links: BTreeSet::new(),
            #[cfg(any(feature = "z3", test))]
            summary_cases: BTreeMap::new(),
            #[cfg(any(feature = "z3", test))]
            active_summary_cases: BTreeSet::new(),
            #[cfg(any(feature = "z3", test))]
            summary_case_seen: BTreeSet::new(),
            #[cfg(any(feature = "z3", test))]
            summary_case_budget: 256,
            domain_facts: Vec::new(),
            scopes: Vec::new(),
            name_levels: FxHashMap::default(),
            eligible_operands: FxHashMap::default(),
            word_predicates: BTreeMap::new(),
            word_demands: BTreeSet::new(),
            #[cfg(any(feature = "z3", test))]
            summaries: BTreeMap::new(),
            derived_definitions: Vec::new(),
            predicate_mappings: Vec::new(),
            predicate_mapping_names: FxHashMap::default(),
            atom_readings: false,
            opaque_domain_reads: 0,
            stated_defined: Vec::new(),
            pending_domain_links: Vec::new(),
            power_facts: Vec::new(),
            powers: Vec::new(),
            undecided_domain_heads: BTreeSet::new(),
            conjunction_free: rustc_hash::FxHashSet::default(),
            dependent_mappings: BTreeMap::new(),
            bound_variables: Vec::new(),
            counter: 1,
            exactness: Exactness::Exact,
            foreign_text: false,
        }
    }

    /// The exactness of everything this state has translated and declared so far.
    pub fn exactness(&self) -> Exactness {
        self.exactness
    }

    fn approximate(&mut self, exactness: Exactness) {
        self.exactness = self.exactness.and(exactness);
    }

    /// Close a source consequence where it was derived. Value bindings precede domain
    /// bindings: query value totalizations do not depend on the query's domain lets, while
    /// domain conditions may read shared values. Both scopes remain inside their binders.
    fn record_source_fact(&mut self, fact: SExpr) -> Result<(), TranslationError> {
        let fact = self.close_source_fact(fact)?;
        self.domain_facts.push(fact);
        Ok(())
    }

    /// Define the function that reads the power `base ^ exponent` where its base is an integer
    /// literal ([`power_of_literal_definition`]), and state what the integer power satisfies at
    /// the power's value `V` ([`power_value`]) and at each pair of it and an earlier power of the
    /// same literal base: facts asserted with the known predicates.
    ///
    /// `V` is the integer power `b^e` at every `e >= 0` in every model of the definition, since
    /// each case of its reading is that power and `KRUST-POWER` is interpreted as the power there
    /// ([`POWER_FUNCTION`]), whatever integers the operands denote (an operand that is undefined
    /// in K denotes some integer in SMT, and each fact holds there too), so asserting a fact true
    /// of the power keeps the reading of every predicate. The facts are what Z3 can use where no
    /// case gives the value, in place of evaluating the power: its growth (`b^e >= b` and
    /// `b^e >= e + 1` for `b >= 2` and `e >= 1`, by `b^e = b * b^(e-1)` and `2^e >= e + 1`; for
    /// `b <= -2` the same of `|b|^e` with the sign of the parity); for an integer literal
    /// `b >= 2`, `b^e > b^W` past the last exponent `W` of [`power_window`]
    /// (`b^e = b^(e-W) * b^W >= 2 * b^W`); and, for two powers of one integer literal `b`, their
    /// quotient `b^(e1+k) = b^k * b^e1` for `e1 >= 0` (the power of a sum), where the exponents
    /// differ by an integer `k >= 0` whatever their operands denote ([`exponent_difference`]) and
    /// `b^k` is a numeral of the window, as `b^(8N+8) = 256 * b^(8N)`, and, for `b >= 2`, their
    /// order `b * b^e1 <= b^e2` for `0 <= e1 < e2` (`b^e2 = b^(e2-e1) * b^e1` with
    /// `b^(e2-e1) >= b` and `b^e1 >= 1`). The quotient is not stated at a difference that is
    /// not such an integer: its factor would be the power at the difference, a fresh reading
    /// through the window's cases for each pair, which made queries over a few powers of 2 with
    /// unrelated exponents too slow to decide (GAP K32 review). Each is a ground instance
    /// at powers the query states, the instance an instantiation pattern on those terms would
    /// give, never a quantified axiom: a quantified power axiom in the prelude leaves Z3 unable to
    /// show a model of a query of the definition, one without a power included.
    ///
    /// A power whose operands mention a variable a quantifier of the query binds gets no fact,
    /// since a fact about it would be a quantified one; its value's cases still read it. Facts
    /// are stated once per closed base and exponent, and pairs only among the first
    /// [`PAIRED_POWERS`] powers, so a query has one fact per power and at most
    /// `PAIRED_POWERS * (PAIRED_POWERS - 1) / 2` pair facts; each names the operands' closed text
    /// once, in a `let`.
    fn record_power(&mut self, base: SExpr, exponent: SExpr) {
        let literal = integer_literal(&base, &[]);
        if let Some(literal) = &literal
            && literal.magnitude() > &num_bigint::BigUint::one()
        {
            let definition = power_of_literal_definition(literal);
            if !self.derived_definitions.contains(&definition) {
                self.derived_definitions.push(definition);
            }
        }
        let close = |state: &Self, expression: SExpr| state.close_scopes(expression);
        let base = close(self, base);
        let exponent = close(self, exponent);
        let mentioned = smt_variables(&base)
            .into_iter()
            .chain(smt_variables(&exponent))
            .collect::<BTreeSet<_>>();
        if self
            .bound_variables
            .iter()
            .any(|(_, name)| mentioned.contains(name.as_str()))
            || self
                .powers
                .iter()
                .any(|(b, e)| *b == base && *e == exponent)
        {
            return;
        }
        let atom = |name: &str| SExpr::atom(name.to_owned());
        let app = |operator: &str, arguments: Vec<SExpr>| SExpr::application(operator, arguments);
        let implies = |condition: SExpr, conclusion: SExpr| app("=>", vec![condition, conclusion]);
        let let_in = |bindings: Vec<(String, SExpr)>, body: SExpr| {
            SExpr::List(vec![
                atom("let"),
                SExpr::List(
                    bindings
                        .into_iter()
                        .map(|(name, value)| SExpr::List(vec![SExpr::atom(name), value]))
                        .collect(),
                ),
                body,
            ])
        };
        let (b, e, v) = (self.fresh_name(), self.fresh_name(), self.fresh_name());
        let (bb, ee, vv) = (atom(&b), atom(&e), atom(&v));
        let even = app(
            "=",
            vec![app("mod", vec![ee.clone(), atom("2")]), atom("0")],
        );
        let successor = app("+", vec![ee.clone(), atom("1")]);
        let at_least_one = app(">=", vec![ee.clone(), atom("1")]);
        let mut facts = vec![
            implies(
                app(
                    "and",
                    vec![app(">=", vec![bb.clone(), atom("2")]), at_least_one.clone()],
                ),
                app(
                    "and",
                    vec![
                        app(">=", vec![vv.clone(), bb.clone()]),
                        app(">=", vec![vv.clone(), successor.clone()]),
                    ],
                ),
            ),
            implies(
                app(
                    "and",
                    vec![
                        app("<=", vec![bb.clone(), app("-", vec![atom("2")])]),
                        at_least_one,
                    ],
                ),
                app(
                    "ite",
                    vec![
                        even,
                        app(
                            "and",
                            vec![
                                app(">=", vec![vv.clone(), app("-", vec![bb.clone()])]),
                                app(">=", vec![vv.clone(), successor.clone()]),
                            ],
                        ),
                        app(
                            "and",
                            vec![
                                app("<=", vec![vv.clone(), bb.clone()]),
                                app("<=", vec![vv.clone(), app("-", vec![successor])]),
                            ],
                        ),
                    ],
                ),
            ),
        ];
        let growing = literal.as_ref().filter(|literal| **literal > BigInt::one());
        if let Some(literal) = growing {
            let window = power_window(literal);
            let last = window.len() - 1;
            facts.push(implies(
                app(">", vec![ee.clone(), atom(&last.to_string())]),
                app(">", vec![vv.clone(), integer_sexpr(&window[last])]),
            ));
        }
        self.power_facts.push(let_in(
            vec![(b, base.clone()), (e, exponent.clone())],
            let_in(
                vec![(
                    v,
                    power_value(&literal.as_ref().map_or(bb, integer_sexpr), &ee, &[]),
                )],
                app("and", facts),
            ),
        ));
        if let Some(literal) = &literal
            && self.powers.len() < PAIRED_POWERS
        {
            let earlier = self
                .powers
                .iter()
                .filter(|(other, _)| *other == base)
                .map(|(_, other)| other.clone())
                .collect::<Vec<_>>();
            let numeral = integer_sexpr(literal);
            for other in earlier {
                let (first, second) = (self.fresh_name(), self.fresh_name());
                let (v1, v2) = (self.fresh_name(), self.fresh_name());
                let (e1, e2, p1, p2) = (atom(&first), atom(&second), atom(&v1), atom(&v2));
                let mut pair = Vec::new();
                // The quotient, where the exponents differ by an integer `k` whatever their
                // operands' values, and `b^k` is a numeral of the window: `b^(e1 + k)` is
                // `b^k * b^e1` at `e1 >= 0`, for every base.
                let difference = exponent_difference(&other, &exponent);
                let ((low, low_value, high, high_value), quotient) = match &difference {
                    Some(difference) if difference.sign() == num_bigint::Sign::Minus => {
                        ((&e2, &p2, &e1, &p1), literal_power(literal, &-difference))
                    }
                    Some(difference) => ((&e1, &p1, &e2, &p2), literal_power(literal, difference)),
                    None => ((&e1, &p1, &e2, &p2), None),
                };
                if let Some(quotient) = quotient {
                    pair.push(implies(
                        app(">=", vec![low.clone(), atom("0")]),
                        app(
                            "=",
                            vec![
                                high_value.clone(),
                                app("*", vec![integer_sexpr(&quotient), low_value.clone()]),
                            ],
                        ),
                    ));
                }
                // The order, for `b >= 2`: `b * b^e1 <= b^e2` at `0 <= e1 < e2`, since
                // `b^e2 = b^(e2-e1) * b^e1` with `b^(e2-e1) >= b` and `b^e1 >= 1`. Where the
                // difference is a known integer it orders the pair one way only.
                if growing.is_some() {
                    let orders = match &difference {
                        Some(difference) if difference.is_zero() => vec![],
                        Some(_) => vec![(low, low_value, high, high_value)],
                        None => vec![(&e1, &p1, &e2, &p2), (&e2, &p2, &e1, &p1)],
                    };
                    for (low, low_value, high, high_value) in orders {
                        pair.push(implies(
                            app(
                                "and",
                                vec![
                                    app(">=", vec![low.clone(), atom("0")]),
                                    app("<", vec![low.clone(), high.clone()]),
                                ],
                            ),
                            app(
                                "<=",
                                vec![
                                    app("*", vec![numeral.clone(), low_value.clone()]),
                                    high_value.clone(),
                                ],
                            ),
                        ));
                    }
                }
                if pair.is_empty() {
                    continue;
                }
                self.power_facts.push(let_in(
                    vec![(first, other), (second, exponent.clone())],
                    let_in(
                        vec![
                            (v1, power_value(&numeral, &e1, &[])),
                            (v2, power_value(&numeral, &e2, &[])),
                        ],
                        app("and", pair),
                    ),
                ));
            }
        }
        self.powers.push((base, exponent));
    }

    /// `fact` closed where it was derived, as `record_source_fact` asserts it.
    fn close_source_fact(&mut self, fact: SExpr) -> Result<SExpr, TranslationError> {
        let mut fact = self.close_scopes(fact);
        let mentioned = smt_variables(&fact)
            .into_iter()
            .map(str::to_owned)
            .collect::<BTreeSet<_>>();
        for (variable, name) in self.bound_variables.clone().into_iter().rev() {
            if !mentioned.contains(&name) {
                continue;
            }
            let sort = self.smt_sort(&variable.sort)?;
            fact = SExpr::List(vec![
                SExpr::atom("forall"),
                SExpr::List(vec![SExpr::List(vec![
                    SExpr::atom(name),
                    SExpr::atom(sort),
                ])]),
                fact,
            ]);
        }
        Ok(fact)
    }

    /// `expression`, translated at this point, inside the bindings of every open scope it needs,
    /// innermost first, so that it can be asserted on its own.
    fn close_scopes(&self, expression: SExpr) -> SExpr {
        self.scopes
            .iter()
            .rev()
            .fold(expression, |expression, scope| scope.bind(expression))
    }

    /// Open a scope, whose quantifier binds `variable` (named `name`) unless it is a root.
    fn open_scope(&mut self, variable: Option<(Variable, String)>, domains: bool, terms: bool) {
        let level = self.scopes.len();
        if let Some((_, name)) = &variable {
            self.name_levels.insert(name.clone(), level);
        }
        self.scopes.push(LetScope {
            variable: variable.map(|(variable, _)| variable),
            domains: domains.then(functional::SharedDomains::default),
            terms: terms.then(SharedTerms::default),
        });
    }

    /// Close the innermost scope; its names are no longer visible. The scope is returned for
    /// its bindings.
    fn close_scope(&mut self, name: Option<&str>) -> LetScope {
        let scope = self.scopes.pop().expect("an open let scope");
        for binding in scope.names() {
            self.name_levels.remove(binding);
        }
        if let Some(name) = name {
            self.name_levels.remove(name);
        }
        scope
    }

    /// The innermost open scope whose quantifier binds a variable of `term`, or 0: `term`
    /// denotes the same in that scope and in every scope inside it, and only there (a scope
    /// further out does not bind that variable, or binds another variable of the same name).
    fn term_level(&self, term: &Term) -> usize {
        if self.bound_variables.is_empty() {
            return 0;
        }
        let variables = &term.attributes().variables;
        self.scopes
            .iter()
            .rposition(|scope| {
                scope
                    .variable
                    .as_ref()
                    .is_some_and(|variable| variables.contains(variable))
            })
            .unwrap_or(0)
    }

    /// The innermost open scope that introduces a name `expression` mentions (a `let` or a
    /// bound variable), or 0: `expression` can be bound in that scope or any scope inside it.
    fn text_level(&self, expression: &SExpr) -> usize {
        fn walk(expression: &SExpr, levels: &FxHashMap<String, usize>, level: &mut usize) {
            match expression {
                SExpr::Atom(atom) => {
                    if atom.starts_with("SMT-")
                        && let Some(&found) = levels.get(atom.as_str())
                    {
                        *level = (*level).max(found);
                    }
                }
                SExpr::List(items) => {
                    for item in items {
                        walk(item, levels, level);
                    }
                }
            }
        }
        let mut level = 0;
        if !self.name_levels.is_empty() {
            walk(expression, &self.name_levels, &mut level);
        }
        level
    }

    /// The outermost open scope at or inside `level` that holds domain lets.
    fn domain_scope_at(&self, level: usize) -> Option<usize> {
        (level..self.scopes.len()).find(|&index| self.scopes[index].domains.is_some())
    }

    /// The outermost open scope at or inside `level` that holds value lets.
    fn term_scope_at(&self, level: usize) -> Option<usize> {
        (level..self.scopes.len()).find(|&index| self.scopes[index].terms.is_some())
    }

    fn has_domain_scope(&self) -> bool {
        self.scopes.iter().any(|scope| scope.domains.is_some())
    }

    fn has_term_scope(&self) -> bool {
        self.scopes.iter().any(|scope| scope.terms.is_some())
    }

    /// Bind `value` to a fresh name in the outermost value scope at or inside `level` and the
    /// scopes its text needs, memoized there for `term` when given; `value` itself when no such
    /// scope is open.
    fn bind_value(&mut self, level: usize, term: Option<&Term>, value: SExpr) -> SExpr {
        let Some(level) = self.term_scope_at(level.max(self.text_level(&value))) else {
            return value;
        };
        let name = self.fresh_name();
        let reference = SExpr::atom(name.clone());
        self.name_levels.insert(name.clone(), level);
        let scope = self.scopes[level].terms.as_mut().expect("a value scope");
        scope.bindings.push((name, value));
        if let Some(term) = term {
            scope.values.insert(term.clone(), reference.clone());
        }
        reference
    }

    /// Bind `value` to a fresh name in the outermost domain scope at or inside `level` and the
    /// scopes its text needs, as [`Self::bind_value`]; an atom is memoized as itself.
    fn bind_domain(&mut self, level: usize, term: Option<&Term>, value: SExpr) -> SExpr {
        let level = self
            .domain_scope_at(level.max(self.text_level(&value)))
            .expect("a domain scope");
        let reference = if matches!(value, SExpr::Atom(_)) {
            value
        } else {
            let name = self.fresh_name();
            self.name_levels.insert(name.clone(), level);
            self.scopes[level]
                .domains
                .as_mut()
                .expect("a domain scope")
                .bindings
                .push((name.clone(), value));
            SExpr::atom(name)
        };
        if let Some(term) = term {
            self.scopes[level]
                .domains
                .as_mut()
                .expect("a domain scope")
                .values
                .insert(term.clone(), reference.clone());
        }
        reference
    }

    /// Only visible binders used by a source consequence distinguish its instantiation.
    /// Unrelated existential witnesses do not create another copy of that same fact.
    fn source_scope(&self, variables: &BTreeSet<Variable>) -> Vec<String> {
        let mut visible = BTreeSet::new();
        let mut scope = Vec::new();
        for (variable, name) in self.bound_variables.iter().rev() {
            if variables.contains(variable) && visible.insert(variable) {
                scope.push(name.clone());
            }
        }
        scope
    }

    /// Record that the translation copies text into the script that it did not write itself:
    /// an `smt-hook` operator or template, an `smtlib` function name, or a domain value's text
    /// that is not an SMT-LIB literal of its sort. Whether the solver reads such text depends
    /// on what its author wrote, so a script containing it that the solver rejects is not
    /// shown to be a defect of the translation (`SmtPrelude::blames_the_translation`).
    fn write_foreign_text(&mut self) {
        self.foreign_text = true;
    }

    /// Share operands in the value scope of their own variables (`LetScope`), preventing a small
    /// term DAG from expanding into an exponential script. Observation predicates own their
    /// value scope so that domain lets cannot outlive the values they read.
    pub fn translate_term(&mut self, term: &Term) -> Result<SExpr, TranslationError> {
        if self.congruence.is_none()
            || (!self.has_term_scope() && self.congruence_head(term).is_none())
        {
            return self.translate_term_node(term);
        }
        let root = !self.has_term_scope();
        if root {
            self.open_scope(None, false, true);
        }
        // A value memoized in a scope at or inside the node's own level denotes the node here.
        let level = self.term_level(term);
        let cached = (level..self.scopes.len()).rev().find_map(|index| {
            self.scopes[index]
                .terms
                .as_ref()
                .and_then(|scope| scope.values.get(term))
                .cloned()
        });
        let result = match cached {
            Some(value) => Ok(value),
            None => self.translate_term_node(term).map(|value| {
                if !root && matches!(value, SExpr::List(_)) {
                    self.bind_value(level, Some(term), value)
                } else {
                    value
                }
            }),
        };
        if !root {
            return result;
        }
        let scope = self.close_scope(None);
        result.map(|body| scope.bind(body))
    }

    fn translate_term_node(&mut self, term: &Term) -> Result<SExpr, TranslationError> {
        let reading = self.observations.get(term).cloned();
        let demands = self
            .observation_demands
            .get(term)
            .cloned()
            .unwrap_or_default();
        let mut facts = self
            .observation_facts
            .get(term)
            .cloned()
            .unwrap_or_default();
        if !facts.is_empty() {
            // These are unconditional source consequences closed by record_source_fact,
            // so another lexical value scope needs no second copy. Binders remain distinct.
            let mut variables = term.attributes().variables.to_btree_set();
            for fact in &facts {
                variables.extend(fact.free_variables());
            }
            let scope = self.source_scope(&variables);
            if !self.observation_fact_seen.insert((term.clone(), scope)) {
                facts.clear();
            }
        }
        if reading.is_some() || !demands.is_empty() || !facts.is_empty() {
            if !self.active_observations.insert(term.clone()) {
                return self.translate_term_node_plain(term);
            }
            // The facts below are asserted, so their atoms carry their domains whatever reading
            // the enclosing predicate takes (`translate_predicate_reading`).
            let outside = std::mem::replace(&mut self.atom_readings, false);
            let outside_defined = std::mem::take(&mut self.stated_defined);
            let result = (|| {
                for demand in demands {
                    self.translate_term(&demand)?;
                }
                let value = match reading {
                    Some(reading) => self.translate_observation(term, &reading),
                    None => self.translate_term_node_plain(term),
                }?;
                for fact in facts {
                    let fact = self.translate_predicate(&fact)?;
                    self.record_source_fact(fact)?;
                }
                Ok(value)
            })();
            self.active_observations.remove(term);
            self.atom_readings = outside;
            self.stated_defined = outside_defined;
            return result;
        }
        self.translate_term_node_plain(term)
    }

    fn translate_term_node_plain(&mut self, term: &Term) -> Result<SExpr, TranslationError> {
        #[cfg(any(feature = "z3", test))]
        if let Some(reading) = summary::reading(&self.summaries, term).cloned()
            && self.eligible_operand(term)
        {
            let TermKind::Application { arguments, .. } = term.kind() else {
                unreachable!()
            };
            let arguments = arguments
                .iter()
                .zip(&reading.summary.key.static_arguments)
                .filter(|(_, static_argument)| static_argument.is_none())
                .map(|(argument, _)| self.translate_term(argument))
                .collect::<Result<Vec<_>, _>>()?;
            self.approximate(reading.exactness);
            let value = if arguments.is_empty() {
                SExpr::atom(reading.name)
            } else {
                SExpr::application(reading.name, arguments)
            };
            if self
                .functional_head(term)
                .is_some_and(|head| self.summary_congruence.contains(&head))
            {
                self.link_summary_to_function(term, value.clone())?;
            }
            return Ok(value);
        }
        match term.kind() {
            // A term-level `\and` denotes the intersection of its operands' values, `\bottom` where
            // they differ, not their Boolean conjunction: `true /\ false` is `\bottom`, not
            // `false`. A Boolean one is therefore an unrelated constant, as any term without a
            // translation. Every atom over it is read under its domain (`atom_with_domains`), an
            // opaque `\ceil` here, so the constant is read only where the intersection is defined,
            // where a model of the definition gives it the intersection's value: faithful in every
            // polarity, `\not(c = true) /\ \not(c = false)` holding where the domain does not.
            // A request or condition with such an atom states that domain beside it, the equality
            // of the operands (`definedness::and_side`, GAP K30).
            TermKind::And(left, right)
                if left.sort().is_builtin(BuiltinSort::Bool)
                    && right.sort().is_builtin(BuiltinSort::Bool) =>
            {
                Ok(self.abstract_term(term, Exactness::Approximate))
            }
            TermKind::And(..) => Err(TranslationError::NonBooleanAnd(term.clone())),
            TermKind::Application {
                symbol, arguments, ..
            } if let Some(operation) = literal::read(symbol, &term.sort(), arguments) => {
                operation.translate(self)
            }
            TermKind::Application {
                symbol, arguments, ..
            } => match &symbol.attributes.smt {
                None => {
                    if let Some(head) = self.congruence_head(term) {
                        self.translate_congruent(head, arguments)
                    } else {
                        Ok(self.abstract_term(term, Exactness::Approximate))
                    }
                }
                // A hook whose operation is not a term at the application's sorts (every
                // `FLOAT` and `MINT` hook, an `INT` hook over a renamed `Int` sort) is no
                // reading of it; the application is then an opaque value of its sort, as one
                // without an `smt` attribute. That over-approximates: every K valuation extends
                // to a model by giving the constant the application's value.
                Some(SmtType::Hook(hook))
                    if !hook_is_well_sorted(hook, &term.sort(), arguments) =>
                {
                    Ok(self.abstract_term(term, Exactness::Approximate))
                }
                Some(SmtType::Lib(name)) => {
                    self.write_foreign_text();
                    self.translate_application(name, arguments, Exactness::Approximate)
                }
                // A hook is trusted to be exact where its symbol is defined, and a partial
                // symbol's value is read only under its domain (`atom_with_domains`), so the
                // application is exact; a domain read that is not a closed formula over hooked
                // operations approximates where it is read (`functional::translate_domain`).
                Some(SmtType::Hook(SExpr::Atom(name))) if name != POWER => {
                    self.write_foreign_text();
                    self.translate_application(name, arguments, Exactness::Exact)
                }
                Some(SmtType::Hook(expression)) => {
                    self.write_foreign_text();
                    let template = match expression {
                        SExpr::Atom(name) => SExpr::application(
                            name.clone(),
                            (1..=arguments.len())
                                .map(|index| SExpr::atom(format!("#{index}")))
                                .collect(),
                        ),
                        SExpr::List(_) => expression.clone(),
                    };
                    let arguments = arguments
                        .iter()
                        .map(|argument| self.translate_term(argument))
                        .collect::<Result<Vec<_>, _>>()?;
                    let (template, powers) = guard_powers(&template, &arguments);
                    if !powers.is_empty() {
                        // The power's value where no case of the operands fixes it is
                        // `KRUST-POWER`, an uninterpreted function the query's facts constrain
                        // only by bounds and ratios, not at a point: a model may give
                        // `2 ^Int E` at `E = 100` a value other than `2^100`, which is no K
                        // valuation, whatever the power's domain says. (Its value outside the
                        // integers is read only where the power is undefined, never under its
                        // domain.)
                        self.approximate(Exactness::Approximate);
                    }
                    for (base, exponent) in powers {
                        let base = fill_placeholders(&base, arguments.clone())?;
                        let exponent = fill_placeholders(&exponent, arguments.clone())?;
                        self.record_power(base, exponent);
                    }
                    fill_placeholders(&template, arguments)
                }
            },
            TermKind::DomainValue { sort, value }
                if sort.is_builtin(BuiltinSort::Bool) || sort.is_builtin(BuiltinSort::Int) =>
            {
                let value = value.as_utf8().map_err(|_| {
                    TranslationError::UnsupportedPredicate("non-UTF-8 Bool or Int SMT literal")
                })?;
                if !is_smt_literal(sort, value) {
                    self.write_foreign_text();
                }
                Ok(SExpr::atom(value))
            }
            TermKind::Variable(variable) => {
                match self
                    .bound_variables
                    .iter()
                    .rev()
                    .find(|(bound, _)| bound == variable)
                {
                    Some((_, name)) => Ok(SExpr::atom(name.clone())),
                    // A free variable stands for itself; the sort of its constant is recorded
                    // where the constant is declared (`mapping_declarations`).
                    None => Ok(self.abstract_term(term, Exactness::Exact)),
                }
            }
            TermKind::Injection { term: child, .. } => {
                if let Some(head) = self.congruence_head(term) {
                    self.translate_congruent(head, std::slice::from_ref(child))
                } else {
                    Ok(self.abstract_term(term, Exactness::Approximate))
                }
            }
            TermKind::List {
                definition,
                heads,
                rest,
            } if self.list_congruence.get(&term.sort()) == Some(definition)
                && heads
                    .len()
                    .saturating_add(rest.as_ref().map_or(0, |(_, tails)| tails.len()))
                    <= 128
                && heads
                    .iter()
                    .all(|head| head.sort() == definition.element_sort)
                && rest.as_ref().is_none_or(|(base, tails)| {
                    base.sort() == term.sort()
                        && tails
                            .iter()
                            .all(|tail| tail.sort() == definition.element_sort)
                })
                && self.eligible_operand(term) =>
            {
                self.translate_list(definition, heads, rest)
            }
            TermKind::Map {
                definition,
                entries,
                rest,
            } if self.map_congruence.get(&term.sort()) == Some(definition)
                && entries.len() <= 128
                && entries.iter().all(|(key, value)| {
                    key.sort() == definition.key_sort && value.sort() == definition.value_sort
                })
                && rest.as_ref().is_none_or(|base| base.sort() == term.sort())
                && self.eligible_operand(term) =>
            {
                self.translate_map(definition, entries, rest)
            }
            TermKind::DomainValue { .. }
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. } => Ok(self.abstract_term(term, Exactness::Approximate)),
        }
    }

    /// A memoized DAG walk using the same local functionality predicate as matching, and
    /// the existing definition's transitive effect closure. No contextual facts are cached.
    fn eligible_operand(&mut self, term: &Term) -> bool {
        let Some(policy) = self.congruence.clone() else {
            return false;
        };
        let mut pending = vec![(term.clone(), false)];
        while let Some((term, visited)) = pending.pop() {
            if self.eligible_operands.contains_key(&term) {
                continue;
            }
            let local = crate::rewrite::functional_pattern_node(&term)
                && match term.kind() {
                    TermKind::Application { symbol, .. } => {
                        !symbol.attributes.binder
                            && !symbol.attributes.macro_or_alias
                            && !policy.effects.contains(symbol.name.as_ref())
                    }
                    TermKind::And(..)
                    | TermKind::DomainValue { .. }
                    | TermKind::Variable(_)
                    | TermKind::Injection { .. }
                    | TermKind::Map { .. }
                    | TermKind::List { .. }
                    | TermKind::Set { .. } => true,
                };
            if !local {
                self.eligible_operands.insert(term, false);
                continue;
            }
            let children = crate::deferred::children(&term);
            if visited || children.is_empty() {
                let eligible = children
                    .iter()
                    .all(|child| self.eligible_operands.get(*child) == Some(&true));
                self.eligible_operands.insert(term, eligible);
            } else {
                pending.push((term.clone(), true));
                pending.extend(children.into_iter().map(|child| (child.clone(), false)));
            }
        }
        self.eligible_operands.get(term) == Some(&true)
    }

    fn congruence_head(&mut self, term: &Term) -> Option<CongruenceHead> {
        // Preserve interpreted primitive readings, including nonnegative collection sizes.
        // Their domain may still retain functional congruence through `functional_head`.
        if let TermKind::Application { symbol, .. } = term.kind()
            && (symbol.attributes.smt.is_some()
                || collection_size_hook(symbol.attributes.hook.as_deref()))
        {
            return None;
        }
        self.functional_head(term)
    }

    fn functional_head(&mut self, term: &Term) -> Option<CongruenceHead> {
        let head = self.functional_head_rank(term)?;
        self.eligible_operand(term).then_some(head)
    }

    /// The local rank/policy checks, before the complete operand-purity walk.
    fn functional_head_rank(&self, term: &Term) -> Option<CongruenceHead> {
        let policy = self.congruence.clone()?;
        let head = match term.kind() {
            TermKind::Application {
                symbol,
                sort_arguments,
                arguments,
            } => {
                if !policy.heads.contains(&symbol.name)
                    || arguments.len() != symbol.argument_sorts.len()
                    || sort_arguments.len() != symbol.sort_variables.len()
                    || sort_arguments.iter().any(Sort::has_variable)
                {
                    return None;
                }
                let substitution = symbol
                    .sort_variables
                    .iter()
                    .cloned()
                    .zip(sort_arguments.iter().copied())
                    .collect();
                if symbol
                    .argument_sorts
                    .iter()
                    .zip(arguments)
                    .any(|(sort, arg)| {
                        crate::definition::substitute_sort(sort, &substitution) != arg.sort()
                    })
                {
                    return None;
                }
                CongruenceHead::Application {
                    name: symbol.name.clone(),
                    sorts: sort_arguments.to_vec(),
                    arguments: arguments.iter().map(Term::sort).collect(),
                    result: term.sort(),
                }
            }
            TermKind::Injection {
                source,
                target,
                term: child,
            } => {
                if child.sort() != *source || policy.sorts.check_subsort(source, target) != Ok(true)
                {
                    return None;
                }
                CongruenceHead::Injection {
                    source: *source,
                    target: *target,
                }
            }
            TermKind::And(..)
            | TermKind::DomainValue { .. }
            | TermKind::Variable(_)
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. } => return None,
        };
        let (arguments, result) = head.rank();
        if sort_denotation(&result).is_err()
            || arguments.iter().any(|sort| sort_denotation(sort).is_err())
        {
            return None;
        }
        Some(head)
    }

    fn translate_congruent(
        &mut self,
        head: CongruenceHead,
        arguments: &[Term],
    ) -> Result<SExpr, TranslationError> {
        self.approximate(Exactness::Approximate);
        #[cfg(any(feature = "z3", test))]
        self.demand_summary_cases(&head, arguments)?;
        let name = self.congruence_name(head);
        if arguments.is_empty() {
            return Ok(SExpr::atom(name));
        }
        let arguments = arguments
            .iter()
            .map(|arg| self.translate_term(arg))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(SExpr::application(name, arguments))
    }

    fn congruence_name(&mut self, head: CongruenceHead) -> String {
        match self.opaque_functions.get(&head) {
            Some(name) => name.clone(),
            None => {
                let name = self.fresh_name();
                self.opaque_functions.insert(head, name.clone());
                name
            }
        }
    }

    pub fn translate_predicate(
        &mut self,
        predicate: &Predicate,
    ) -> Result<SExpr, TranslationError> {
        let root = !self.has_domain_scope();
        // Source domain links may read exact value operands too. Keep one lexical
        // value scope for every definition-aware predicate so those links preserve
        // shared input DAGs and their domain lets can refer to the value bindings.
        let value_root = root && !self.has_term_scope() && self.congruence.is_some();
        if root {
            self.open_scope(None, true, value_root);
        }
        let result = self.translate_predicate_node(predicate);
        if root {
            let scope = self.close_scope(None);
            return result.map(|body| scope.bind(body));
        }
        result
    }

    /// A predicate's translation. Each atom is translated with the domains of its operands
    /// (`atom_with_domains`), so that it denotes what the atom denotes in K wherever its
    /// operands are undefined too; every other connective is its Boolean operation, which is
    /// then the predicate's own (docs/compatibility.md, "Solver decisions over partial
    /// operations").
    /// `predicate` with each atom read as its operands' relation alone (`atom_readings`), for a
    /// reading that is used only where those operands are defined: a value read under the
    /// domain of the term it stands for (an observation's case test, `observation_value`), or
    /// the scalar reading that a word plan's fact relates to its word value under the operands'
    /// domains (`word::prepare`). Such a reading is a value, and value bindings precede domain
    /// bindings (`record_source_fact`), so it must not read a domain.
    pub(super) fn translate_predicate_reading(
        &mut self,
        predicate: &Predicate,
    ) -> Result<SExpr, TranslationError> {
        let outside = std::mem::replace(&mut self.atom_readings, true);
        let result = self.translate_predicate(predicate);
        self.atom_readings = outside;
        result
    }

    fn translate_predicate_node(
        &mut self,
        predicate: &Predicate,
    ) -> Result<SExpr, TranslationError> {
        let word = if self.bound_variables.is_empty() {
            self.word_predicates.get(predicate).cloned()
        } else {
            None
        };
        if word.is_none()
            && let Predicate::Equals(left, right) = predicate
            && let (
                TermKind::Injection {
                    source: sa,
                    target: ta,
                    term: a,
                },
                TermKind::Injection {
                    source: sb,
                    target: tb,
                    term: b,
                },
            ) = (left.kind(), right.kind())
            && sa == sb
            && ta == tb
            && self.functional_head(left).is_some()
            && self.functional_head(right).is_some()
        {
            // Licensed injections are injective. This is source injection theory, not
            // injectivity of arbitrary constructor/function UFs. Preserve model protection
            // for the carrier that this equality no longer needs to translate. An injection
            // is defined exactly where its operand is, so the inner equality's domains are
            // the outer one's.
            self.approximate(Exactness::Approximate);
            return self.translate_predicate(&Predicate::Equals(a.clone(), b.clone()));
        }
        match predicate {
            Predicate::Term(term) => {
                let reading = match word {
                    Some(value) => value,
                    None => self.translate_term(term)?,
                };
                self.atom_with_domains(&[term], reading)
            }
            Predicate::Equals(left, right) => {
                let reading = match word {
                    Some(value) => value,
                    None => SExpr::application(
                        "=",
                        vec![self.translate_term(left)?, self.translate_term(right)?],
                    ),
                };
                self.atom_with_domains(&[left, right], reading)
            }
            Predicate::True
            | Predicate::False
            | Predicate::Ceil(_)
            | Predicate::Floor(_)
            | Predicate::In(..)
            | Predicate::Not(_)
            | Predicate::And(_)
            | Predicate::Or(_)
            | Predicate::Implies(..)
            | Predicate::Iff(..)
            | Predicate::Exists(..)
            | Predicate::Forall(..)
            | Predicate::Absent(_)
            | Predicate::Defined(_) => self.translate_connective(predicate),
        }
    }

    /// The atom whose operands are `operands` (one Boolean term, or the two sides of an
    /// equality) and whose reading of their values is `reading`, with the operands' domains.
    ///
    /// A term denotes one element where it is defined and `\bottom` elsewhere; `D(t)`, the
    /// domain reading of `\ceil(t)` (`translate_domain`), is the SMT statement of where it is
    /// defined, and `\top` (left out) for a `ceil_free` term. Where the operands are defined
    /// the reading is their K values' relation (the `smt-hook`s are exact there), so:
    /// - a Boolean term `b` means `\equals(b, true)`, false where `b` is `\bottom`:
    ///   `D(b) /\ b`;
    /// - an equality with one side `c` defined means that the other side `a` is defined and is
    ///   `c`'s element: `D(a) /\ a = c`;
    /// - an equality of two possibly undefined sides holds where both denote the same element
    ///   or both denote none, since `\bottom = \bottom` is `\top`:
    ///   `(D(a) /\ D(b) /\ a = b) \/ (\not D(a) /\ \not D(b))`.
    ///
    /// Each is equivalent to the atom in K under the trusted readings, so the translation of a
    /// predicate, under any negation or disjunction, is too, and a solver answer about it is a
    /// K answer whatever form the simplifier left it in.
    fn atom_with_domains(
        &mut self,
        operands: &[&Term],
        reading: SExpr,
    ) -> Result<SExpr, TranslationError> {
        if self.atom_readings {
            // The reading alone states the operands' relation where they are undefined too,
            // where an `smt-hook` gives a value K does not. Its users read it only under those
            // operands' domains, but the reading itself does not show it, so a query that holds
            // one over an operand that owes a domain is approximate (GAP K29).
            if operands
                .iter()
                .any(|operand| !operand.attributes().ceil_free())
            {
                self.approximate(Exactness::Approximate);
            }
            return Ok(reading);
        }
        let mut domains = Vec::with_capacity(operands.len());
        for operand in operands {
            domains.push(self.operand_domain(operand)?);
        }
        Ok(match domains.as_slice() {
            [None] | [None, None] | [] => reading,
            [Some(domain)] | [Some(domain), None] | [None, Some(domain)] => {
                SExpr::application("and", vec![domain.clone(), reading])
            }
            [Some(left), Some(right)] => SExpr::application(
                "or",
                vec![
                    SExpr::application("and", vec![left.clone(), right.clone(), reading]),
                    SExpr::application(
                        "and",
                        vec![
                            SExpr::application("not", vec![left.clone()]),
                            SExpr::application("not", vec![right.clone()]),
                        ],
                    ),
                ],
            ),
            _ => unreachable!("an atom has one or two operands"),
        })
    }

    /// The domain of an atom's operand, `None` where it is `\top`: a `ceil_free` term owes no
    /// obligation under any definition, so its domain is not read at all, and one whose `\ceil`
    /// is a conjunct beside the atom is read as defined there (`stated_defined`).
    ///
    /// ```toml algorithm-site
    /// id = "backend.smt.check"
    /// role = "part"
    /// sites = ["TranslationState::operand_domain", "TranslationState::atom_with_domains"]
    /// ```
    fn operand_domain(&mut self, term: &Term) -> Result<Option<SExpr>, TranslationError> {
        if term.attributes().ceil_free() || self.stated_defined.contains(term) {
            return Ok(None);
        }
        let opaque = self.opaque_domain_reads;
        let domain = self.translate_domain(term)?;
        if self.opaque_domain_reads > opaque {
            k_rust_kore::measure::bump(k_rust_kore::measure::Counter::SmtOpaqueAtomDomains);
        }
        Ok((domain != SExpr::atom("true")).then_some(domain))
    }

    fn translate_connective(&mut self, predicate: &Predicate) -> Result<SExpr, TranslationError> {
        match predicate {
            Predicate::True => Ok(SExpr::atom("true")),
            Predicate::False => Ok(SExpr::atom("false")),
            Predicate::Term(_) | Predicate::Equals(..) => {
                unreachable!("atoms are translated by translate_predicate_node")
            }
            Predicate::Not(inner) => Ok(SExpr::application(
                "not",
                vec![self.translate_predicate(inner)?],
            )),
            Predicate::And(inner) => self.translate_predicates("and", inner),
            Predicate::Or(inner) => self.translate_predicates("or", inner),
            Predicate::Implies(left, right) if !matches!(**right, Predicate::Implies(..)) => {
                Ok(SExpr::application(
                    "=>",
                    vec![
                        self.translate_predicate(left)?,
                        self.translate_predicate(right)?,
                    ],
                ))
            }
            Predicate::Implies(..) => self.translate_implication_spine(predicate),
            Predicate::Iff(left, right) => Ok(SExpr::application(
                "=",
                vec![
                    self.translate_predicate(left)?,
                    self.translate_predicate(right)?,
                ],
            )),
            Predicate::Ceil(term) | Predicate::Defined(term)
                if term.attributes().constructor_like =>
            {
                Ok(SExpr::atom("true"))
            }
            // A domain reading does not evaluate the term. Preparation admits only pure
            // functional operands, so effects and unsupported deferred atoms stay opaque.
            Predicate::Ceil(term) | Predicate::Defined(term) => self.translate_domain(term),
            // An absence is opaque to the solver: one Boolean per key and rest.
            predicate @ (Predicate::Floor(_) | Predicate::In(..) | Predicate::Absent(_)) => {
                Ok(self.abstract_predicate(predicate))
            }
            Predicate::Exists(variable, inner) => {
                self.translate_quantifier("exists", variable, inner)
            }
            Predicate::Forall(variable, inner) => {
                self.translate_quantifier("forall", variable, inner)
            }
        }
    }

    /// Translates a right-nested implication spine `l1 => (l2 => ... => (ln => r))`, n >= 2, as
    /// the one disjunction `(or (not l1) ... (not ln) r)`.
    ///
    /// `a => b` is `¬a ∨ b`, so the spine is `¬l1 ∨ (¬l2 ∨ (... ∨ (¬ln ∨ r)))`, and `∨` is
    /// associative: `a ⇒ (b ⇒ c) ≡ ¬a ∨ ¬b ∨ c`. The flat formula is the same Boolean function
    /// of the same atoms, so an assertion containing it has exactly the models it had. The
    /// operands are translated in the order the nested translation visits them (l1, ..., ln,
    /// then r), so the abstraction constants get the same names and declarations, the first
    /// untranslatable operand is the same, and so is the exactness of the query.
    ///
    /// A single implication keeps its `=>` text. The nested text of a longer spine made the
    /// solver's construction of the assertion quadratic in n; the flat text is linear, and the
    /// loop below walks the spine without native recursion.
    fn translate_implication_spine(
        &mut self,
        spine: &Predicate,
    ) -> Result<SExpr, TranslationError> {
        let mut disjuncts = Vec::new();
        let mut rest = spine;
        while let Predicate::Implies(premise, conclusion) = rest {
            disjuncts.push(SExpr::application(
                "not",
                vec![self.translate_predicate(premise)?],
            ));
            rest = conclusion;
        }
        disjuncts.push(self.translate_predicate(rest)?);
        Ok(SExpr::application("or", disjuncts))
    }

    fn translate_quantifier(
        &mut self,
        quantifier: &str,
        variable: &Variable,
        body: &Predicate,
    ) -> Result<SExpr, TranslationError> {
        let sort = self.smt_sort(&variable.sort)?;
        let variable_name = self.fresh_name();
        self.bound_variables
            .push((variable.clone(), variable_name.clone()));
        // The body's scope: lets of the nodes that mention the variable stay inside the
        // quantifier, the others go to the scope of their own variables outside it (`LetScope`).
        let congruence = self.congruence.is_some();
        self.open_scope(
            Some((variable.clone(), variable_name.clone())),
            true,
            congruence,
        );
        // A term stated defined outside that mentions the variable is about the variable of
        // that name outside, not the one this binds.
        let outside_stated = self.stated_defined.clone();
        self.stated_defined
            .retain(|term| !term.attributes().variables.contains(variable));
        let body = self.translate_predicate(body);
        self.stated_defined = outside_stated;
        let scope = self.close_scope(Some(&variable_name));
        let body = body.map(|body| scope.bind(body));
        self.bound_variables.pop();
        Ok(SExpr::List(vec![
            SExpr::atom(quantifier),
            SExpr::List(vec![SExpr::List(vec![
                SExpr::atom(variable_name),
                SExpr::atom(sort),
            ])]),
            body?,
        ]))
    }

    fn translate_predicates(
        &mut self,
        operator: &str,
        predicates: &[Predicate],
    ) -> Result<SExpr, TranslationError> {
        let stated = self.stated_defined.len();
        if operator == "and" {
            stated_definedness(predicates, &mut self.stated_defined);
        }
        let result = predicates
            .iter()
            .map(|predicate| self.translate_predicate(predicate))
            .collect::<Result<Vec<_>, _>>();
        self.stated_defined.truncate(stated);
        Ok(SExpr::application(operator, result?))
    }

    /// Applies the SMT operation `name` to the translated arguments. `exactness` states whether
    /// the operation denotes the symbol exactly (`symbol_exactness`).
    fn translate_application(
        &mut self,
        name: &str,
        arguments: &[Term],
        exactness: Exactness,
    ) -> Result<SExpr, TranslationError> {
        self.approximate(exactness);
        if arguments.is_empty() {
            return Ok(SExpr::atom(name));
        }
        Ok(SExpr::application(
            name,
            arguments
                .iter()
                .map(|argument| self.translate_term(argument))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }

    /// The constant (or, under a binder it mentions, the function of the bound variables) that
    /// stands for `term`. `exactness` is `Exact` only for a free variable, which the constant
    /// denotes exactly up to its sort; every other abstracted term is `Approximate`, because the
    /// constant forgets its structure.
    fn abstract_term(&mut self, term: &Term, exactness: Exactness) -> SExpr {
        self.approximate(exactness);
        if !self.bound_variables.is_empty()
            && let Some(expression) = self.abstract_dependent(&Predicate::Term(term.clone()))
        {
            return expression;
        }
        if let Some(name) = self.mappings.get(term) {
            return SExpr::atom(name);
        }
        let name = self.fresh_name();
        self.mappings.insert(term.clone(), name.clone());
        SExpr::atom(name)
    }

    /// A Boolean constant that stands for a predicate without an SMT translation; it forgets
    /// what the predicate says, so the translation is `Approximate`.
    fn abstract_predicate(&mut self, predicate: &Predicate) -> SExpr {
        self.approximate(Exactness::Approximate);
        if !self.bound_variables.is_empty()
            && let Some(expression) = self.abstract_dependent(predicate)
        {
            return expression;
        }
        if let Some(name) = self.predicate_mapping_names.get(predicate) {
            return SExpr::atom(name);
        }
        let name = self.fresh_name();
        self.predicate_mappings
            .push((predicate.clone(), name.clone()));
        self.predicate_mapping_names
            .insert(predicate.clone(), name.clone());
        SExpr::atom(name)
    }

    fn fresh_name(&mut self) -> String {
        let name = format!("SMT-{}", self.counter);
        self.counter += 1;
        name
    }

    /// An opaque atom under a quantifier must be a function of the bound variables it
    /// mentions, since its value can differ for each value they take. A constant
    /// would erase that dependence and could make a satisfiable formula unsatisfiable.
    /// Cache its template modulo bound-variable spelling, retaining free variables.
    fn abstract_dependent(&mut self, predicate: &Predicate) -> Option<SExpr> {
        let variables = predicate.free_variables();
        let mut seen = BTreeSet::new();
        let mut dependencies = self
            .bound_variables
            .iter()
            .rev()
            .filter(|(variable, _)| variables.contains(variable) && seen.insert(variable.clone()))
            .cloned()
            .collect::<Vec<_>>();
        dependencies.reverse();
        if dependencies.is_empty() {
            return None;
        }
        // An uninterpreted function of the bound variables retains only congruence.
        self.approximate(Exactness::Approximate);
        let free = variables.difference(&seen).collect::<Vec<_>>();
        let mut substitution = Substitution::new();
        let mut sorts = Vec::new();
        let mut arguments = Vec::new();
        for (index, (variable, name)) in dependencies.into_iter().enumerate() {
            let mut placeholder = format!("#SMT-bound-{index}");
            while free
                .iter()
                .any(|variable| variable.name.as_ref() == placeholder)
            {
                placeholder.push('_');
            }
            substitution.insert(
                variable.clone(),
                Term::variable(variable.with_name(placeholder)),
            );
            sorts.push(variable.sort);
            arguments.push(SExpr::atom(name));
        }
        // Only atomic predicates reach this method, so this substitution crosses no binder.
        #[expect(
            clippy::disallowed_methods,
            reason = "a renaming to placeholder variables; a variable denotes an element"
        )]
        let template = substitute_predicates(std::slice::from_ref(predicate), &substitution)
            .pop()
            .unwrap();
        let key = (template, sorts);
        let name = if let Some(name) = self.dependent_mappings.get(&key) {
            name.clone()
        } else {
            let name = self.fresh_name();
            self.dependent_mappings.insert(key, name.clone());
            name
        };
        Some(SExpr::application(name, arguments))
    }

    /// The SMT-LIB sort that stands for `sort` in a query. `Int` and `Bool` denote the K sort's
    /// values; every other sort is declared as an uninterpreted sort, whose models need not have
    /// them, so naming it records `Approximate`. Every sort of a query is named here.
    fn smt_sort(&mut self, sort: &Sort) -> Result<String, TranslationError> {
        let sort = sort_denotation(sort)?;
        self.approximate(sort.exactness());
        Ok(sort.name())
    }

    /// The declarations of the constants and functions that stand for abstracted terms and
    /// predicates, each sort named through `smt_sort`.
    fn mapping_declarations(&mut self) -> Result<Vec<String>, TranslationError> {
        let constants = self
            .mappings
            .iter()
            .map(|(term, name)| (term.sort(), name.clone(), collection_size_term(term)))
            .collect::<Vec<_>>();
        let functions = self
            .dependent_mappings
            .iter()
            .map(|((predicate, arguments), name)| {
                #[expect(
                    clippy::wildcard_enum_match_arm,
                    reason = "Predicate is syntax; only the listed variants are special here"
                )]
                let result = match predicate {
                    Predicate::Term(term) => Some(term.sort()),
                    _ => None,
                };
                (result, arguments.clone(), name.clone())
            })
            .collect::<Vec<_>>();
        let mut declarations = Vec::new();
        for (sort, name, collection_size) in constants {
            declarations.push(format!("(declare-const {name} {})", self.smt_sort(&sort)?));
            if collection_size {
                declarations.push(format!("(assert (>= {name} 0))"));
            }
        }
        for (_, name) in &self.predicate_mappings {
            declarations.push(format!("(declare-const {name} Bool)"));
        }
        for (result, arguments, name) in functions {
            let result = match result {
                Some(sort) => self.smt_sort(&sort)?,
                None => "Bool".into(),
            };
            let arguments = arguments
                .iter()
                .map(|sort| self.smt_sort(sort))
                .collect::<Result<Vec<_>, _>>()?;
            declarations.push(format!(
                "(declare-fun {name} ({}) {result})",
                arguments.join(" ")
            ));
        }
        for (head, name) in self.opaque_functions.clone() {
            let (arguments, result) = head.rank();
            let arguments = arguments
                .iter()
                .map(|sort| self.smt_sort(sort))
                .collect::<Result<Vec<_>, _>>()?;
            let result = self.smt_sort(&result)?;
            declarations.push(format!(
                "(declare-fun {name} ({}) {result})",
                arguments.join(" ")
            ));
        }
        for (head, name) in self.domain_functions.clone() {
            let (arguments, _) = head.rank();
            let arguments = if self.single_point_domains.contains(&name) {
                Vec::new()
            } else {
                arguments
                    .iter()
                    .map(|sort| self.smt_sort(sort))
                    .collect::<Result<Vec<_>, _>>()?
            };
            declarations.push(format!(
                "(declare-fun {name} ({}) Bool)",
                arguments.join(" ")
            ));
        }
        Ok(declarations)
    }
}

/// The SMT-LIB power operation as an `smt-hook` names it.
const POWER: &str = "^";

/// The uninterpreted function that stands for a power where no integer is its value
/// (`guard_powers`), declared in the prelude of a definition whose `smt-hook`s use [`POWER`],
/// with [`POWER_FUNCTION`] and [`POWER_VALUE`].
const POWER_OUTSIDE_THE_INTEGERS: &str = "|KRUST-POWER-OUTSIDE-THE-INTEGERS|";

/// The powers of one query whose pairs `TranslationState::record_power` states facts at.
const PAIRED_POWERS: usize = 32;

/// The uninterpreted function that stands for a power with a symbolic exponent where an integer
/// is its value and no case of [`power_value`] gives it (`guard_powers`), declared beside
/// [`POWER_OUTSIDE_THE_INTEGERS`]. A model of the definition interprets it as the integer power
/// `b^e` at every `e >= 0` (and anyhow elsewhere), the one interpretation every fact of
/// `power_facts` is true of.
const POWER_FUNCTION: &str = "|KRUST-POWER|";

/// `expression` with every binary power `(^ a b)` whose exponent is not a numeral read as
/// `(ite (or (>= b 0) (= a 1) (= a (- 1))) V (KRUST-POWER-OUTSIDE-THE-INTEGERS a b))`, where `V`
/// is [`power_value`], with the base and exponent (template operands) of each such power.
///
/// An `smt-hook` is trusted to state its hook's operation wherever the hook has a value; where
/// the hook has none, the solver must not decide anything that depends on a value. SMT-LIB's own
/// partial operations leave such a value unconstrained (`div` and `mod` by zero), so a validity
/// answer holds for whatever it is. Z3's `^` on two integers does not: it is the real power,
/// which has a value (`(^ 2 (- 1))` is `1/2`, and `mod` reads its integer part, 0) exactly where
/// no integer is the power and `^Int` is undefined. The guard is the set where an integer power
/// exists, a nonnegative exponent or a base of magnitude 1; outside it the power is an
/// uninterpreted function of its operands, as a division by zero is.
///
/// Inside the guard the power is not Z3's `^` either: Z3's nonlinear arithmetic evaluates a
/// power with a symbolic exponent at the values its candidate models give the operands, a
/// bignum computation that neither its timeout nor its resource limit stops, at values it picks
/// itself however small the query's constants are. [`power_value`] gives the power's value
/// where a case of the operands fixes it and an uninterpreted function ([`POWER_FUNCTION`])
/// elsewhere, and `TranslationState::record_power` states what the integer power satisfies
/// there, so Z3 has no power to evaluate. `V` and both uninterpreted functions are Int-valued,
/// so both branches and every context have one sort. The guard names each operand several
/// times; `fill_placeholders` states each argument once.
///
/// A power whose exponent is a numeral, written in the template or as the argument a
/// placeholder names (`arguments` are the translated arguments), has an integer value for every
/// base. A positive numeral leaves it as it is: its guard is constantly true, and Z3 reads it as
/// the product of that many bases, 0 included. The numeral 0 makes it the constant `1.0` (of the
/// sort of Z3's `^`): `X ^Int 0` is 1 for every integer `X`, `0 ^Int 0` included, while Z3 leaves
/// `(^ 0 0)` uninterpreted, so the power itself would not be an exact reading there. The
/// exponent 0 is 1 whatever the exponent's form: a symbolic exponent equal to 0 has a case of
/// [`power_value`] whose value is 1 for every base (GAP K16).
fn guard_powers(expression: &SExpr, arguments: &[SExpr]) -> (SExpr, Vec<(SExpr, SExpr)>) {
    let mut powers = Vec::new();
    let guarded = guard_powers_into(expression, arguments, &mut powers);
    (guarded, powers)
}

fn guard_powers_into(
    expression: &SExpr,
    arguments: &[SExpr],
    powers: &mut Vec<(SExpr, SExpr)>,
) -> SExpr {
    match expression {
        SExpr::Atom(_) => expression.clone(),
        SExpr::List(items) => {
            // A power whose base or exponent holds a power is guarded with its operands, so
            // the inner one's guard is part of the outer one's operand and is recorded first.
            let mut inner = Vec::new();
            let items = items
                .iter()
                .map(|item| guard_powers_into(item, arguments, &mut inner))
                .collect::<Vec<_>>();
            match items.as_slice() {
                [SExpr::Atom(operator), _, exponent]
                    if operator == POWER
                        && numeral(exponent, arguments)
                            .is_some_and(|value| value.bytes().all(|digit| digit == b'0')) =>
                {
                    // The base is dropped, and with it any power it held.
                    SExpr::atom("1.0")
                }
                [SExpr::Atom(operator), base, exponent]
                    if operator == POWER && numeral(exponent, arguments).is_none() =>
                {
                    powers.append(&mut inner);
                    powers.push((base.clone(), exponent.clone()));
                    let condition = SExpr::application(
                        "or",
                        vec![
                            SExpr::application(">=", vec![exponent.clone(), SExpr::atom("0")]),
                            SExpr::application("=", vec![base.clone(), SExpr::atom("1")]),
                            SExpr::application("=", vec![base.clone(), negative_one()]),
                        ],
                    );
                    let outside = SExpr::application(
                        POWER_OUTSIDE_THE_INTEGERS,
                        vec![base.clone(), exponent.clone()],
                    );
                    SExpr::application(
                        "ite",
                        vec![condition, power_value(base, exponent, arguments), outside],
                    )
                }
                _ => {
                    powers.append(&mut inner);
                    SExpr::List(items)
                }
            }
        }
    }
}

fn negative_one() -> SExpr {
    SExpr::application("-", vec![SExpr::atom("1")])
}

/// The integer power `b^e` where an integer is its value (`e >= 0`, or `b` is 1 or -1), read
/// without Z3's power: by its value's cases where they fix it, and `KRUST-POWER(b, e)`
/// ([`POWER_FUNCTION`]) where none does. Each case is linear in `e`, whose value is only
/// compared with numerals.
///
/// A base that is not an integer literal is read by [`POWER_VALUE`], the prelude's function of
/// [`power_cases`]. An integer literal base `b` is read by `KRUST-POWER-OF-b`
/// ([`power_of_literal`]), whose cases give the numeral `b^k` for each `k` of [`power_window`],
/// so that a power whose exponent the query fixes in that window has its value, as Z3's own power
/// gave it there; the bases 1, -1 and 0 are read by their value for every exponent the guard
/// admits: 1, 1 or -1 by the parity (`1 / (-1)^n = (-1)^n` for a negative one), and 1 at
/// `e = 0` and 0 at every other `e`, which is `e >= 1` there.
fn power_value(base: &SExpr, exponent: &SExpr, arguments: &[SExpr]) -> SExpr {
    let Some(literal) = integer_literal(base, arguments) else {
        return SExpr::application(POWER_VALUE, vec![base.clone(), exponent.clone()]);
    };
    let ite =
        |condition, then, otherwise| SExpr::application("ite", vec![condition, then, otherwise]);
    let equals = |operand: &SExpr, value: &str| {
        SExpr::application("=", vec![operand.clone(), SExpr::atom(value)])
    };
    if literal.is_one() {
        SExpr::atom("1")
    } else if literal == -BigInt::one() {
        let parity = SExpr::application("mod", vec![exponent.clone(), SExpr::atom("2")]);
        ite(equals(&parity, "0"), SExpr::atom("1"), negative_one())
    } else if literal.is_zero() {
        ite(equals(exponent, "0"), SExpr::atom("1"), SExpr::atom("0"))
    } else {
        SExpr::application(power_of_literal(&literal), vec![exponent.clone()])
    }
}

/// The function of the prelude that reads a power whose base is not an integer literal
/// ([`power_cases`]).
const POWER_VALUE: &str = "|KRUST-POWER-VALUE|";

/// The cases of the integer power `b^e` of the operands `b` and `e`, where `e >= 0` or `b` is 1
/// or -1, each its value at every integer it covers, in order:
/// `e = 0`: 1, for every base, 0 included (`X ^Int 0` is 1);
/// `b = 1`: 1, for every exponent, a negative one included (`1 / 1^n`);
/// `b = -1`: 1 for an even exponent and -1 for an odd one, a negative one included
/// (`1 / (-1)^n = (-1)^n`), and SMT-LIB's `mod` by 2 is 0 or 1 by the parity of any integer;
/// `e = 1`: `b`;
/// `b = 0`: 0, since here `e >= 0` (with `b` not 1 or -1) and `e` is not 0, so `e >= 1`;
/// `e = k` for `k` up to [`UNROLLED_EXPONENT`]: the product of `k` bases, a polynomial of fixed
/// degree, whose value at any operands Z3 computes in time polynomial in their size;
/// otherwise `KRUST-POWER(b, e)`.
fn power_cases(base: &SExpr, exponent: &SExpr) -> SExpr {
    let equals =
        |operand: &SExpr, value: SExpr| SExpr::application("=", vec![operand.clone(), value]);
    let ite =
        |condition, then, otherwise| SExpr::application("ite", vec![condition, then, otherwise]);
    let one = || SExpr::atom("1");
    let parity = ite(
        equals(
            &SExpr::application("mod", vec![exponent.clone(), SExpr::atom("2")]),
            SExpr::atom("0"),
        ),
        one(),
        negative_one(),
    );
    let product = |k: usize| {
        (1..k).fold(base.clone(), |product, _| {
            SExpr::application("*", vec![base.clone(), product])
        })
    };
    let unrolled = (2..=UNROLLED_EXPONENT).rev().fold(
        SExpr::application(POWER_FUNCTION, vec![base.clone(), exponent.clone()]),
        |otherwise, k| {
            ite(
                equals(exponent, SExpr::atom(k.to_string())),
                product(k),
                otherwise,
            )
        },
    );
    ite(
        equals(exponent, SExpr::atom("0")),
        one(),
        ite(
            equals(base, one()),
            one(),
            ite(
                equals(base, negative_one()),
                parity,
                ite(
                    equals(exponent, one()),
                    base.clone(),
                    ite(equals(base, SExpr::atom("0")), SExpr::atom("0"), unrolled),
                ),
            ),
        ),
    )
}

/// The prelude's definition of [`POWER_VALUE`].
fn power_value_definition() -> String {
    let (base, exponent) = (SExpr::atom("KRUST-BASE"), SExpr::atom("KRUST-EXPONENT"));
    format!(
        "(define-fun {POWER_VALUE} ((KRUST-BASE Int) (KRUST-EXPONENT Int)) Int {})",
        power_cases(&base, &exponent)
    )
}

/// The name of the function that reads the powers of the integer literal `base` (`|base| >= 2`),
/// which a query that applies it defines ([`power_of_literal_definition`]).
fn power_of_literal(base: &BigInt) -> String {
    format!("|KRUST-POWER-OF-{base}|")
}

/// The definition of [`power_of_literal`]: the numeral `b^k` at each exponent `k` of
/// [`power_window`], and `KRUST-POWER(b, e)` at every other.
fn power_of_literal_definition(base: &BigInt) -> String {
    let exponent = SExpr::atom("KRUST-EXPONENT");
    let body = power_window(base).into_iter().enumerate().rev().fold(
        SExpr::application(POWER_FUNCTION, vec![integer_sexpr(base), exponent.clone()]),
        |otherwise, (k, value)| {
            SExpr::application(
                "ite",
                vec![
                    SExpr::application("=", vec![exponent.clone(), SExpr::atom(k.to_string())]),
                    integer_sexpr(&value),
                    otherwise,
                ],
            )
        },
    );
    format!(
        "(define-fun {} ((KRUST-EXPONENT Int)) Int {body})",
        power_of_literal(base)
    )
}

/// The largest exponent at which [`power_cases`] reads a power as a product of bases.
const UNROLLED_EXPONENT: usize = 4;

/// The powers `b^0, b^1, ..., b^W` of an integer literal `b` with `|b| >= 2` that
/// [`power_of_literal_definition`] states as numerals: `W` is the largest exponent of at most 256 whose power
/// has at most 512 bits, so a 256-bit word's powers of 2 (KEVM's `2 ^Int (8 *Int N)` for `N` up
/// to 32) are all in it, and the window's numerals take a few kilobytes of text.
fn power_window(base: &BigInt) -> Vec<BigInt> {
    let mut powers = vec![BigInt::one()];
    let mut power = BigInt::one();
    while powers.len() <= 256 {
        power *= base;
        if power.bits() > 512 {
            break;
        }
        powers.push(power.clone());
    }
    powers
}

/// `second - first` where it is one integer whatever the values of the operands of the two
/// closed exponents: both read as linear sums ([`linear_integer`]) whose difference has no
/// term but its constant. `None` where the difference is not such an integer or is not seen to be.
fn exponent_difference(first: &SExpr, second: &SExpr) -> Option<BigInt> {
    let scope = BTreeMap::new();
    let mut difference = linear_integer(second, &scope)?;
    let first = linear_integer(first, &scope)?;
    difference.constant -= first.constant;
    for (term, coefficient) in first.terms {
        *difference.terms.entry(term).or_default() -= coefficient;
    }
    difference
        .terms
        .values()
        .all(Zero::is_zero)
        .then_some(difference.constant)
}

/// An integer expression as `constant + sum of coefficient * term`, each term an atom or an
/// application that is not linear, keyed by its text.
#[derive(Clone, Debug, Default)]
struct LinearInteger {
    constant: BigInt,
    terms: BTreeMap<SExpr, BigInt>,
}

impl LinearInteger {
    fn scaled(mut self, factor: &BigInt) -> Self {
        self.constant *= factor;
        for coefficient in self.terms.values_mut() {
            *coefficient *= factor;
        }
        self
    }

    fn add(mut self, other: Self) -> Self {
        self.constant += other.constant;
        for (term, coefficient) in other.terms {
            *self.terms.entry(term).or_default() += coefficient;
        }
        self
    }
}

/// The linear sum an SMT-LIB integer expression denotes, reading numerals, `+`, `-` (unary and
/// binary or more), `*` with at most one factor that is not a constant, and `let` (by
/// substitution, its bindings read in the outer scope); any other application, or an atom no
/// `let` binds, is a term. `scope` holds the `let`-bound names in reach. `None` where a term
/// would mention a name of `scope`, whose text alone does not say what it denotes.
fn linear_integer(
    expression: &SExpr,
    scope: &BTreeMap<String, Option<LinearInteger>>,
) -> Option<LinearInteger> {
    let term = |expression: &SExpr| {
        let mut terms = BTreeMap::new();
        terms.insert(expression.clone(), BigInt::one());
        LinearInteger {
            constant: BigInt::zero(),
            terms,
        }
    };
    match expression {
        SExpr::Atom(atom) => {
            if let Some(bound) = scope.get(atom) {
                return bound.clone();
            }
            if !atom.is_empty() && atom.bytes().all(|byte| byte.is_ascii_digit()) {
                return Some(LinearInteger {
                    constant: atom.parse().ok()?,
                    terms: BTreeMap::new(),
                });
            }
            Some(term(expression))
        }
        SExpr::List(items) => match items.as_slice() {
            [SExpr::Atom(head), SExpr::List(bindings), body] if head == "let" => {
                let mut inner = scope.clone();
                for binding in bindings {
                    let SExpr::List(binding) = binding else {
                        return None;
                    };
                    let [SExpr::Atom(name), value] = binding.as_slice() else {
                        return None;
                    };
                    inner.insert(name.clone(), linear_integer(value, scope));
                }
                linear_integer(body, &inner)
            }
            [SExpr::Atom(head), operands @ ..] if head == "+" && !operands.is_empty() => operands
                .iter()
                .try_fold(LinearInteger::default(), |sum, operand| {
                    Some(sum.add(linear_integer(operand, scope)?))
                }),
            [SExpr::Atom(head), operand] if head == "-" => {
                Some(linear_integer(operand, scope)?.scaled(&-BigInt::one()))
            }
            [SExpr::Atom(head), first, rest @ ..] if head == "-" => {
                rest.iter()
                    .try_fold(linear_integer(first, scope)?, |difference, operand| {
                        Some(
                            difference.add(linear_integer(operand, scope)?.scaled(&-BigInt::one())),
                        )
                    })
            }
            [SExpr::Atom(head), operands @ ..] if head == "*" && !operands.is_empty() => {
                let factors = operands
                    .iter()
                    .map(|operand| linear_integer(operand, scope))
                    .collect::<Option<Vec<_>>>()?;
                let (constants, linear): (Vec<_>, Vec<_>) = factors
                    .into_iter()
                    .partition(|factor| factor.terms.values().all(Zero::is_zero));
                let factor = constants
                    .iter()
                    .fold(BigInt::one(), |product, factor| product * &factor.constant);
                match linear.as_slice() {
                    [] => Some(LinearInteger {
                        constant: factor,
                        terms: BTreeMap::new(),
                    }),
                    [single] => Some(single.clone().scaled(&factor)),
                    _ => opaque(expression, scope).then(|| term(expression)),
                }
            }
            _ => opaque(expression, scope).then(|| term(expression)),
        },
    }
}

/// Whether `expression`'s text names what it denotes in `scope`: it mentions no name `scope`
/// binds.
fn opaque(expression: &SExpr, scope: &BTreeMap<String, Option<LinearInteger>>) -> bool {
    match expression {
        SExpr::Atom(atom) => !scope.contains_key(atom),
        SExpr::List(items) => items.iter().all(|item| opaque(item, scope)),
    }
}

/// `base^k` for an integer `k >= 0`, where it is a numeral of [`power_window`] (or `base` is 0,
/// 1 or -1, whose powers are those three): the factor a pair fact of
/// `TranslationState::record_power` states.
fn literal_power(base: &BigInt, k: &BigInt) -> Option<BigInt> {
    let k = usize::try_from(k).ok()?;
    if base.magnitude() > &num_bigint::BigUint::one() {
        power_window(base).into_iter().nth(k)
    } else if base.is_zero() {
        Some(if k == 0 {
            BigInt::one()
        } else {
            BigInt::zero()
        })
    } else {
        // 1 or -1: the power is the base at an odd exponent and 1 at an even one.
        Some(if k % 2 == 0 {
            BigInt::one()
        } else {
            base.clone()
        })
    }
}

/// The integer a template operand states as a literal, by itself or as the argument it names:
/// an atom of digits with an optional leading `-`, or `(- n)`.
fn integer_literal(operand: &SExpr, arguments: &[SExpr]) -> Option<BigInt> {
    let operand = match operand {
        SExpr::Atom(atom) => match placeholder(atom) {
            Some(index) => index
                .checked_sub(1)
                .and_then(|index| arguments.get(index))?,
            None => operand,
        },
        SExpr::List(_) => operand,
    };
    let digits = |text: &str| {
        (!text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit()))
            .then(|| text.parse::<BigInt>().ok())
            .flatten()
    };
    match operand {
        SExpr::Atom(atom) => match atom.strip_prefix('-') {
            Some(rest) => digits(rest).map(|value| -value),
            None => digits(atom),
        },
        SExpr::List(items) => match items.as_slice() {
            [SExpr::Atom(minus), SExpr::Atom(value)] if minus == "-" => {
                digits(value).map(|value| -value)
            }
            _ => None,
        },
    }
}

/// An integer as an SMT-LIB term: a numeral, or `(- n)` below zero.
fn integer_sexpr(value: &BigInt) -> SExpr {
    if value.sign() == num_bigint::Sign::Minus {
        SExpr::application("-", vec![SExpr::atom((-value).to_string())])
    } else {
        SExpr::atom(value.to_string())
    }
}

/// The template operand `operand` when it is a numeral, a nonnegative integer literal, by itself
/// or as the argument it names.
fn numeral<'a>(operand: &'a SExpr, arguments: &'a [SExpr]) -> Option<&'a str> {
    let SExpr::Atom(atom) = operand else {
        return None;
    };
    let value = match placeholder(atom) {
        Some(index) => match index.checked_sub(1).and_then(|index| arguments.get(index)) {
            Some(SExpr::Atom(argument)) => argument,
            Some(SExpr::List(_)) | None => return None,
        },
        None => atom,
    };
    (!value.is_empty() && value.bytes().all(|byte| byte.is_ascii_digit())).then_some(value.as_str())
}

/// Whether `expression` applies [`POWER`], so that its translation uses
/// [`POWER_OUTSIDE_THE_INTEGERS`].
fn applies_power(expression: &SExpr) -> bool {
    match expression {
        SExpr::Atom(name) => name == POWER,
        SExpr::List(items) => items.iter().any(applies_power),
    }
}

/// Push the terms whose definedness a conjunct of `conjunction` (through nested conjunctions)
/// states as a `\ceil` or deferred atom.
fn stated_definedness(conjunction: &[Predicate], stated: &mut Vec<Term>) {
    for predicate in conjunction {
        match predicate {
            Predicate::Ceil(term) | Predicate::Defined(term) => {
                if !term.attributes().ceil_free() {
                    stated.push(term.clone());
                }
            }
            Predicate::And(conjuncts) => stated_definedness(conjuncts, stated),
            Predicate::True
            | Predicate::False
            | Predicate::Term(_)
            | Predicate::Equals(..)
            | Predicate::Floor(_)
            | Predicate::In(..)
            | Predicate::Not(_)
            | Predicate::Or(_)
            | Predicate::Implies(..)
            | Predicate::Iff(..)
            | Predicate::Exists(..)
            | Predicate::Forall(..)
            | Predicate::Absent(_) => {}
        }
    }
}

/// A query's translation, with its mappings declared, and the parts `SmtPrelude::query`
/// assembles into a script: the mapping declarations, the substitution's equations, the known
/// assertions and the checked conjunction.
type QueryTranslation = (TranslationState, Vec<String>, Vec<SExpr>, Vec<SExpr>, SExpr);

/// Translates a query and declares its mappings: the one translation `SmtPrelude::query` poses
/// and `translation_exactness` reads.
fn translate_query(
    known: &[Predicate],
    substitution: &Substitution,
    checked: &[Predicate],
) -> Result<QueryTranslation, TranslationError> {
    translate_query_with_policy(known, substitution, checked, None)
}

fn translate_query_with_policy(
    known: &[Predicate],
    substitution: &Substitution,
    checked: &[Predicate],
    congruence: Option<Arc<CongruencePolicy>>,
) -> Result<QueryTranslation, TranslationError> {
    let mut translation = TranslationState::new();
    translation.congruence = congruence;
    translate_query_in_state(known, substitution, checked, translation)
}

fn translate_query_in_state(
    known: &[Predicate],
    substitution: &Substitution,
    checked: &[Predicate],
    mut translation: TranslationState,
) -> Result<QueryTranslation, TranslationError> {
    // The known predicates are asserted in every query posed, and the checked ones are a
    // conjunction: a `\ceil(t)` among the first is a conjunct of each assertion, one among
    // the second of the checked conjunction (`TranslationState::stated_defined`).
    stated_definedness(known, &mut translation.stated_defined);
    // A binding `X = t` of an element variable, which is defined: the equality with `t`'s domain
    // (`atom_with_domains`), where the pattern's instances are.
    let substitution = substitution
        .iter()
        .map(|(variable, term)| {
            translation.translate_predicate(&Predicate::Equals(
                Term::variable(variable.clone()),
                term.clone(),
            ))
        })
        .collect::<Result<Vec<_>, TranslationError>>()?;
    let mut known = known
        .iter()
        .map(|predicate| translation.translate_predicate(predicate))
        .collect::<Result<Vec<_>, _>>()?;
    let checked = translation.translate_predicates("and", checked)?;
    translation.stated_defined.clear();
    for (head, fact) in std::mem::take(&mut translation.pending_domain_links) {
        if translation.undecided_domain_heads.contains(&head) {
            translation.domain_facts.push(fact);
        }
    }
    let mut checked = checked;
    known.extend(translation.domain_facts.clone());
    known.extend(translation.power_facts.clone());
    let mut substitution = substitution;
    translation.close_single_point_domains(
        substitution
            .iter_mut()
            .chain(known.iter_mut())
            .chain(std::iter::once(&mut checked))
            .collect(),
    );
    let mut declarations = translation.mapping_declarations()?;
    declarations.extend(translation.derived_definitions.clone());
    Ok((translation, declarations, substitution, known, checked))
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum TranslationError {
    NonBooleanAnd(Term),
    PlaceholderOutOfBounds {
        placeholder: usize,
        arguments: usize,
    },
    UnsupportedPredicate(&'static str),
    ParametricSort(Sort),
    SmtLemmaSurplusMappings {
        rule_id: String,
        terms: Vec<Term>,
    },
    /// Not produced since GAP K18, which reads a lemma's `requires` with its operands' domains
    /// and leaves out a lemma whose domains no closed formula states (`dropped_smt_lemmas`);
    /// kept for the wire format.
    SmtLemmaSurplusPredicates {
        rule_id: String,
        predicates: Vec<Predicate>,
    },
    MissingSmtLemmaVariable {
        rule_id: String,
        variable: Variable,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SmtPrelude {
    declarations: Vec<String>,
    /// The functions the definition's `smtlib` attributes name, which the prelude declares
    /// under names their authors chose (as SMT-LIB symbols, `symbol_name`).
    smtlib_names: BTreeSet<String>,
    /// Whether the prelude ends with a user prelude, a script k-rust did not write.
    user_script: bool,
    /// The `UNIQUE_ID`s of the `smt-lemma`s the prelude leaves out because a closed formula
    /// cannot state the domain of an operand of their `requires` ([`dropped_smt_lemmas`]), or
    /// because their text applies a function a query defines for itself, the reading of a power of
    /// an integer literal base with a symbolic exponent (`KRUST-POWER-OF-b`) among them
    /// (`translate_smt_lemma`); each once (the equations internalized from one axiom share it).
    dropped_lemmas: Vec<String>,
    congruence: Option<Arc<CongruencePolicy>>,
    #[cfg(any(feature = "z3", test))]
    source: Option<summary::Source>,
}

impl SmtPrelude {
    pub fn from_definition(definition: &BackendDefinition) -> Result<Self, TranslationError> {
        let mut declarations = definition
            .sorts()
            .iter()
            .filter(|(name, _)| {
                name.as_ref() != BuiltinSort::Int.kore_name()
                    && name.as_ref() != BuiltinSort::Bool.kore_name()
            })
            .map(|(name, info)| format!("(declare-sort {} {})", quote(name), info.parameters.len()))
            .collect::<Vec<_>>();
        if definition.symbols().values().any(|symbol| {
            matches!(&symbol.attributes.smt, Some(SmtType::Hook(expression)) if applies_power(expression))
        }) {
            declarations.push(format!(
                "(declare-fun {POWER_OUTSIDE_THE_INTEGERS} (Int Int) Int)"
            ));
            declarations.push(format!("(declare-fun {POWER_FUNCTION} (Int Int) Int)"));
            declarations.push(power_value_definition());
        }
        // K symbols that name the same `smtlib` function with the same SMT signature stand for
        // one function, which is declared once: SMT-LIB rejects a second declaration of it, and
        // a rejected prelude states nothing.
        let mut declared = BTreeSet::new();
        let mut smtlib_names = BTreeSet::new();
        for symbol in definition.symbols().values() {
            let Some(SmtType::Lib(name)) = &symbol.attributes.smt else {
                continue;
            };
            smtlib_names.insert(symbol_name(name).to_owned());
            let arguments = symbol
                .argument_sorts
                .iter()
                .map(prelude_smt_sort)
                .collect::<Result<Vec<_>, _>>()?;
            let declaration = format!(
                "(declare-fun {name} ({}) {})",
                arguments.join(" "),
                prelude_smt_sort(&symbol.result_sort)?
            );
            if !declared.insert(declaration.clone()) {
                continue;
            }
            declarations.push(declaration);
            if collection_size_hook(symbol.attributes.hook.as_deref())
                && symbol.argument_sorts.len() == 1
                && symbol.result_sort.is_builtin(BuiltinSort::Int)
            {
                declarations.push(format!(
                    "(assert (forall ((KRUST-COLLECTION {})) (>= ({name} KRUST-COLLECTION) 0)))",
                    arguments[0]
                ));
            }
        }
        let congruence = CongruencePolicy::from_definition(definition).map(Arc::new);
        let (assertions, dropped) = lemma_assertions(definition, congruence.clone())?;
        declarations.extend(assertions);
        // One per lemma as written: the equations internalized from one axiom share its unique
        // id, and are one lemma to its author, as in the load warning.
        let mut dropped_lemmas = Vec::<String>::new();
        for lemma in dropped {
            if !dropped_lemmas.contains(&lemma.rule.attributes.unique_id) {
                dropped_lemmas.push(lemma.rule.attributes.unique_id.clone());
            }
        }
        k_rust_kore::measure::add(
            k_rust_kore::measure::Counter::SmtLemmasLeftOut,
            dropped_lemmas.len() as u64,
        );
        Ok(Self {
            declarations,
            smtlib_names,
            user_script: false,
            dropped_lemmas,
            congruence,
            #[cfg(any(feature = "z3", test))]
            source: Some(summary::Source::new(definition)),
        })
    }

    pub fn from_definition_with_prelude(
        definition: &BackendDefinition,
        prelude: &str,
    ) -> Result<Self, TranslationError> {
        let mut generated = Self::from_definition(definition)?;
        if !prelude.trim().is_empty() {
            generated.declarations.push(prelude.to_owned());
            generated.user_script = true;
        }
        Ok(generated)
    }

    pub fn declarations(&self) -> &[String] {
        &self.declarations
    }

    /// The `UNIQUE_ID`s of the definition's `smt-lemma`s the prelude leaves out: those whose
    /// `requires` reads an operand whose domain no closed formula states ([`dropped_smt_lemmas`]),
    /// and those whose text applies a function a query defines for itself, as the reading of a
    /// power of an integer literal base with a symbolic exponent does (`KRUST-POWER-OF-b`, GAP
    /// K32) (`translate_smt_lemma`). Leaving out an axiom only weakens what the solver knows.
    pub fn dropped_lemmas(&self) -> &[String] {
        &self.dropped_lemmas
    }

    #[cfg(feature = "z3")]
    fn query(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
        filter_for_checked: bool,
    ) -> Stoppable<Result<TranslatedQuery, TranslationError>> {
        k_rust_kore::measure::bump(k_rust_kore::measure::Counter::SmtPreparedQueries);
        let mut translation = TranslationState::new();
        translation.congruence = self.congruence.clone();
        if let Some(source) = &self.source {
            let observations = observation::prepare(
                source.definition(),
                &mut translation,
                known,
                substitution,
                checked,
            )?;
            let preparation = known
                .iter()
                .chain(&observations)
                .cloned()
                .collect::<Vec<_>>();
            functional::prepare(
                source.definition(),
                &mut translation,
                &preparation,
                substitution,
                checked,
            )?;
            if let Err(error) = summary::prepare(
                source,
                &mut translation,
                &preparation,
                substitution,
                checked,
            )? {
                return Ok(Err(error));
            }
            observation::finish_summary_readings(&mut translation, &observations)?;
        }
        if let Err(error) = word::prepare(&mut translation, known, checked)? {
            return Ok(Err(error));
        }
        Ok((|| {
            let (mut translation, declarations, substitution, known, checked) =
                translate_query_in_state(known, substitution, checked, translation)?;
            let (substitution, known) = if filter_for_checked {
                let interesting = smt_variables(&checked);
                let (substitution, substitution_exactness) =
                    closure_over(&interesting, substitution);
                let (known, known_exactness) = closure_over(&interesting, known);
                translation.approximate(substitution_exactness.and(known_exactness));
                (substitution, known)
            } else {
                (substitution, known)
            };
            let mut base = self.declarations.clone();
            base.extend(declarations);
            base.extend(
                substitution
                    .into_iter()
                    .chain(known)
                    .map(|expression| format!("(assert {expression})")),
            );
            Ok(TranslatedQuery::new(base.join("\n"), checked, translation))
        })())
    }

    /// Whether the solver's rejection of `script`, which poses `query` under this prelude, is a
    /// defect of k-rust's translation: a script k-rust wrote by itself that is not well-formed
    /// SMT-LIB. The caller has checked that the prelude alone loads.
    ///
    /// A rejection is a defect of the text that makes the script ill-formed, and only k-rust's
    /// own text is k-rust's defect. The script is the prelude followed by the text the
    /// translation writes for the query. That text is all k-rust's (its fresh `SMT-` names, the
    /// names of the definition's sorts, which the prelude declares, the core and integer
    /// operations it writes, and literals) unless the translation copied foreign text into it
    /// (`TranslationState::write_foreign_text`): an `smt-hook` whose operator is unknown or
    /// whose rank does not fit, or an `smtlib` name declared twice at overlapping signatures,
    /// is ill-formed through its author's text. The loaded prelude reaches into the query's text
    /// only through what it declares: k-rust declares the definition's sorts and its own names,
    /// a user prelude may declare anything and change how the rest of the script is read (a
    /// `set-logic`, a `reset`), and a declared `smtlib` function changes the reading of every
    /// occurrence of its name, so a query whose text writes that name (a fresh `SMT-1`, or an
    /// operation such as `and` that an `smtlib` attribute overloads) may be rejected for the
    /// clash. Every other rejection of the script can only be of k-rust's text.
    ///
    /// The query's text is split into tokens at whitespace and parentheses; text k-rust wrote
    /// by itself has no quoted symbol containing either, so the tokens are its atoms.
    #[cfg(feature = "z3")]
    fn blames_the_translation(&self, query: &TranslatedQuery, script: &str) -> bool {
        if query.foreign_text() || self.user_script {
            return false;
        }
        let prelude = self.declarations.join("\n");
        let Some(text) = script.strip_prefix(prelude.as_str()) else {
            // Every script starts with its prelude; one that does not is no script this
            // reasoning covers.
            return false;
        };
        !text
            .split(|character: char| character.is_whitespace() || matches!(character, '(' | ')'))
            .any(|token| self.smtlib_names.contains(symbol_name(token)))
    }
}

/// The exactness of the translation of `predicates`, read from the same translation and
/// declarations `SmtPrelude::query` poses; `Approximate` when they do not translate.
///
/// A `Sat` answer for `predicates` shows a K valuation of them only when this is `Exact`
/// (see [`Exactness`]).
///
/// An `Unsat`, `Valid` or `Refuted` answer of `SmtSolver::is_sat` and
/// `SmtSolver::check_predicates` is a K answer whatever form the predicates have: each atom is
/// translated with its operands' domains (see [`Exactness`]), so the totalized operation is read
/// only where its application is defined. The definedness-explicit forms the callers state
/// before simplifying (`definedness::condition_definedness` and
/// `definedness::faithful_conditions` on every `requires` and `ensures`, the admission of a
/// request's predicates, `definition::Admitted` and `definedness::request_definedness`, and the
/// internalization of a claim's constraints, `claim::with_explicit_definedness`) serve the
/// simplifier, which may rewrite a term so that a partial subterm no longer shows; the solver
/// does not rely on them (docs/compatibility.md, "Solver decisions over partial operations").
/// An atom over a term-level conjunction has its definedness stated too, the equality of the
/// conjunction's sides (GAP K30).
#[must_use]
pub fn translation_exactness(predicates: &[Predicate]) -> Exactness {
    translate_query(predicates, &Substitution::new(), &[])
        .map_or(Exactness::Approximate, |(translation, ..)| {
            translation.exactness()
        })
}

fn collection_size_hook(hook: Option<&str>) -> bool {
    matches!(hook, Some("LIST.size" | "MAP.size" | "SET.size"))
}

fn collection_size_term(term: &Term) -> bool {
    matches!(
        term.kind(),
        TermKind::Application { symbol, .. }
            if collection_size_hook(symbol.attributes.hook.as_deref())
                && term.sort().is_builtin(BuiltinSort::Int)
    )
}

/// The generated SMT identifiers (constants, functions and local bindings) mentioned in one walk.
fn smt_variables(expression: &SExpr) -> BTreeSet<&str> {
    fn collect<'a>(expression: &'a SExpr, names: &mut BTreeSet<&'a str>) {
        match expression {
            SExpr::Atom(atom) if atom.starts_with("SMT-") => {
                names.insert(atom);
            }
            SExpr::Atom(_) => {}
            SExpr::List(items) => {
                for item in items {
                    collect(item, names);
                }
            }
        }
    }
    let mut names = BTreeSet::new();
    collect(expression, &mut names);
    names
}

/// The expressions that share a generated SMT identifier with `interesting`, transitively, each once and in
/// `SExpr` order. Dropping a conjunct weakens the query, so its `Sat` need not hold for the whole
/// conjunction: the selection is `Exact` only when nothing was dropped.
///
/// The selection is the set of expressions reachable from `interesting` in the graph that links
/// each distinct expression to the identifiers it mentions. Each expression's identifiers are read
/// once and indexed, and a breadth-first search follows each identifier once, however
/// long the chains of shared identifiers are. Function names retain ground and quantified facts
/// about the same generated head even when no free constant connects them.
#[cfg(feature = "z3")]
fn closure_over(interesting: &BTreeSet<&str>, expressions: Vec<SExpr>) -> (Vec<SExpr>, Exactness) {
    let distinct = expressions
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let selected = {
        let names = distinct.iter().map(smt_variables).collect::<Vec<_>>();
        let mut mentioning = BTreeMap::<&str, Vec<usize>>::new();
        for (index, expression_names) in names.iter().enumerate() {
            for &name in expression_names {
                mentioning.entry(name).or_default().push(index);
            }
        }
        let mut selected = vec![false; distinct.len()];
        let mut followed = BTreeSet::new();
        let mut pending = interesting
            .iter()
            .copied()
            .collect::<std::collections::VecDeque<&str>>();
        while let Some(name) = pending.pop_front() {
            if !followed.insert(name) {
                continue;
            }
            for &index in mentioning.get(name).into_iter().flatten() {
                if !selected[index] {
                    selected[index] = true;
                    pending.extend(names[index].iter().copied());
                }
            }
        }
        selected
    };
    let exactness = if selected.iter().all(|&chosen| chosen) {
        Exactness::Exact
    } else {
        Exactness::Approximate
    };
    let chosen = distinct
        .into_iter()
        .zip(selected)
        .filter_map(|(expression, chosen)| chosen.then_some(expression))
        .collect();
    (chosen, exactness)
}

fn smt_lemmas(definition: &BackendDefinition) -> Vec<&RewriteRule> {
    fn theory_rules(theory: &Theory) -> impl Iterator<Item = &RewriteRule> {
        theory
            .values()
            .flat_map(|priorities| priorities.values())
            .flatten()
            .map(AsRef::as_ref)
    }
    // A lemma holding a literal whose element the definition leaves open states a fact of one
    // model, and the solver answers every route: it is not given to the solver
    // (`crate::literal`).
    theory_rules(definition.function_theory())
        .chain(theory_rules(definition.simplification_theory()))
        .filter(|rule| {
            rule.attributes.smt_lemma && rule.computed_attributes.open_literals.is_empty()
        })
        .collect()
}

/// Why the prelude leaves out an `smt-lemma`: what the domain of an operand of its `requires`
/// needs that no closed formula over the lemma's variables states, since it is a name or a fact of
/// one query's translation (`translate_smt_lemma`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeftOutReason {
    /// The domain stays the head's domain function: a partial function whose domain no
    /// unconditional ceil equation states.
    DomainFunction,
    /// The domain is an opaque `\ceil` (no ceil equation states it), or the `requires` holds
    /// another atom the translation can only abstract.
    OpaqueAtom,
    /// The domain holds a fact stated beside it, or a link of a decided domain to its head's
    /// domain function.
    DomainFact,
    /// The domain holds a definition the translation derives for one query.
    DerivedDefinition,
    /// The condition of the domain's plan holds a term with no SMT reading, which the translation
    /// can only abstract.
    AbstractedTerm,
}

impl fmt::Display for LeftOutReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::DomainFunction => {
                "it is its head's domain function, which no unconditional ceil equation states"
            }
            Self::OpaqueAtom => {
                "no ceil equation states it, so it is an opaque `#Ceil` the solver can only abstract"
            }
            Self::DomainFact => "it needs a fact about a domain function stated beside it",
            Self::DerivedDefinition => "it needs a definition derived for one query",
            Self::AbstractedTerm => "its ceil condition holds a term with no SMT reading",
        })
    }
}

/// An `smt-lemma` the prelude leaves out ([`dropped_smt_lemmas`]).
#[derive(Clone, Debug)]
pub struct DroppedLemma<'a> {
    /// The lemma.
    pub rule: &'a RewriteRule,
    /// The innermost operand of the lemma's `requires` whose domain alone the prelude cannot
    /// state; none where no single operand's domain is the cause (a predicate of the
    /// `requires` that the translation only abstracts).
    pub operand: Option<Term>,
    /// What that domain, or the `requires`, needs.
    pub reason: LeftOutReason,
}

/// The `smt-lemma`s of `definition` that the solver's prelude leaves out, with why: those whose
/// `requires` reads an operand whose domain no closed formula states (`translate_smt_lemma`).
/// It is the computation [`SmtPrelude::from_definition`] states its lemmas by, so a report of
/// these and the prelude agree; and, run detached from any request, a function of the definition
/// alone. Empty where the prelude cannot state its lemmas at all (a lemma the translation
/// refuses), which every solver operation then reports.
#[cfg(feature = "z3")]
pub fn dropped_smt_lemmas(definition: &BackendDefinition) -> Vec<DroppedLemma<'_>> {
    if smt_lemmas(definition).is_empty() {
        return Vec::new();
    }
    // The report repeats the prelude's computation for a reader, beside the prelude's own,
    // which counts it: the repetition counts nothing, so the counters a run reads
    // (`smt.opaque_atom_domains` among them) measure the same work with or without the report.
    k_rust_kore::measure::without_counting(|| {
        let congruence = CongruencePolicy::from_definition(definition).map(Arc::new);
        lemma_assertions(definition, congruence)
            .map(|(_, dropped)| dropped)
            .unwrap_or_default()
    })
}

/// The assertions of `definition`'s `smt-lemma`s the prelude states, and the lemmas it leaves
/// out.
///
/// The translation runs detached from the calling thread's request (`stop::detached`): a
/// solver is built lazily, at the first operation that needs it, which may run inside a request
/// whose cancellation or deadline would otherwise leave a lemma's domains unprepared, and so
/// leave the lemma out of a prelude the session keeps. The preparation is bounded on its own
/// (`functional::prepare`'s budget and depth guard), so it ends without a deadline, and which
/// lemmas the prelude states is a function of the definition, as the load-time check's verdicts
/// are.
fn lemma_assertions(
    definition: &BackendDefinition,
    congruence: Option<Arc<CongruencePolicy>>,
) -> Result<(Vec<String>, Vec<DroppedLemma<'_>>), TranslationError> {
    crate::stop::detached(|| {
        let mut assertions = Vec::new();
        let mut dropped = Vec::new();
        for rule in smt_lemmas(definition) {
            match translate_smt_lemma(definition, congruence.clone(), rule)? {
                LemmaTranslation::Stated(lemma) => assertions.push(format!("(assert {lemma})")),
                LemmaTranslation::LeftOut { operand, reason } => dropped.push(DroppedLemma {
                    rule,
                    operand,
                    reason,
                }),
            }
        }
        Ok((assertions, dropped))
    })
}

/// How the prelude reads one `smt-lemma` (`translate_smt_lemma`).
enum LemmaTranslation {
    /// The closed formula that states it.
    Stated(SExpr),
    /// Left out, as [`DroppedLemma`] says.
    LeftOut {
        operand: Option<Term>,
        reason: LeftOutReason,
    },
}

/// Prepare the domain plans of the operands of `predicates` in `translation`, as a query does,
/// those of the definition's functional heads. The policy is set only for preparing them: the
/// lemma's own terms are translated as before, with no congruence function of a query's
/// translation.
fn prepare_lemma_domains(
    definition: &BackendDefinition,
    translation: &mut TranslationState,
    congruence: Option<Arc<CongruencePolicy>>,
    predicates: &[Predicate],
) {
    #[cfg(any(feature = "z3", test))]
    {
        translation.congruence = congruence;
        // Run detached (`lemma_assertions`), the preparation meets no request, deadline or poll
        // budget, so no poll raises; were one raised, the domains would stay unprepared and the
        // lemma be left out, which only weakens what the solver knows.
        if let Err(stop) = functional::prepare(
            definition,
            translation,
            &[],
            &Substitution::new(),
            predicates,
        ) {
            stop.forgo_refinement();
        }
        translation.congruence = None;
    }
    #[cfg(not(any(feature = "z3", test)))]
    let _ = (definition, translation, congruence, predicates);
}

/// What a lemma's translation holds that no closed formula over its variables can state, if
/// anything: a name or a fact of one query's translation (a domain function, an abstracted atom,
/// a fact or link beside a domain, a derived definition), or a term the translation abstracts
/// that is not in the lemma's text `written`. Read after the left-hand side's variables are
/// bound.
fn left_out_reason(
    translation: &TranslationState,
    written: &rustc_hash::FxHashSet<Term>,
) -> Option<LeftOutReason> {
    if !translation.domain_functions.is_empty() {
        Some(LeftOutReason::DomainFunction)
    } else if !translation.predicate_mappings.is_empty()
        || !translation.dependent_mappings.is_empty()
    {
        Some(LeftOutReason::OpaqueAtom)
    } else if translation
        .mappings
        .keys()
        .any(|term| !written.contains(term))
    {
        Some(LeftOutReason::AbstractedTerm)
    } else if !translation.domain_facts.is_empty() || !translation.pending_domain_links.is_empty() {
        Some(LeftOutReason::DomainFact)
    } else if !translation.derived_definitions.is_empty() {
        Some(LeftOutReason::DerivedDefinition)
    } else {
        None
    }
}

/// The innermost operand of `rule`'s `requires` whose domain alone a closed formula cannot
/// state, with what it needs (`left_out_reason`): the domain of each non-`ceil_free` subterm,
/// children before parents, is translated as `\ceil` of it alone, as an atom's operand domain is.
/// Run only for a lemma the prelude leaves out, to name the cause in its report.
fn left_out_operand(
    definition: &BackendDefinition,
    congruence: &Option<Arc<CongruencePolicy>>,
    rule: &RewriteRule,
    written: &rustc_hash::FxHashSet<Term>,
) -> Option<(Term, LeftOutReason)> {
    let mut order = Vec::new();
    let mut seen = rustc_hash::FxHashSet::default();
    let mut pending = Vec::new();
    for predicate in rule.requires.iter() {
        predicate.visit_terms(&mut |term| pending.push((term.clone(), false)));
    }
    while let Some((term, expanded)) = pending.pop() {
        if expanded {
            order.push(term);
        } else if seen.insert(term.clone()) {
            let children = crate::deferred::children(&term)
                .into_iter()
                .cloned()
                .collect::<Vec<_>>();
            pending.push((term, true));
            pending.extend(children.into_iter().map(|child| (child, false)));
        }
    }
    order.into_iter().find_map(|term| {
        if term.attributes().ceil_free() || term.attributes().constructor_like {
            return None;
        }
        let ceil = Predicate::Ceil(term.clone());
        let mut translation = TranslationState::new();
        prepare_lemma_domains(
            definition,
            &mut translation,
            congruence.clone(),
            std::slice::from_ref(&ceil),
        );
        translation.translate_predicate(&ceil).ok()?;
        left_out_reason(&translation, written).map(|reason| (term, reason))
    })
}

/// How the prelude states the `smt-lemma` `rule`, `l = r requires R`: as the closed formula
/// `∀ vars(l). T(R) => l = r`, or left out when no closed formula states it.
///
/// `T(R)` reads each atom of `R` with its operands' domains, as a query does
/// (`atom_with_domains`): in K an atom over an undefined term does not hold, so the lemma holds
/// only where they are defined. The domains are prepared from the definition
/// (`functional::prepare`), so a domain a ceil equation states, or that is `\top`, is a formula
/// over the bound variables. A domain that stays the head's domain function, an opaque
/// `\ceil` atom or a fact beside the domain is a name of one query's translation, which a
/// prelude cannot mention, as is a term of such a domain's condition that the translation can
/// only abstract (a function with no SMT reading), and so is a function the translation defines
/// for one query (a derived definition, as `KRUST-POWER-OF-b` reads a power of an integer
/// literal base with a symbolic exponent); such a lemma is left out ([`dropped_smt_lemmas`]),
/// which only weakens what the solver knows. A term of the
/// lemma's own text with no SMT reading is the author's, and stays an error
/// (`TranslationError::SmtLemmaSurplusMappings`). Stating `R` without the domains would assert `l = r` where
/// `R`'s total reading holds but `R` is `\bottom`.
fn translate_smt_lemma(
    definition: &BackendDefinition,
    congruence: Option<Arc<CongruencePolicy>>,
    rule: &RewriteRule,
) -> Result<LemmaTranslation, TranslationError> {
    let RuleRhs::Term(rhs) = &rule.rhs else {
        return Err(TranslationError::UnsupportedPredicate("ceil SMT lemma"));
    };
    let mut translation = TranslationState::new();
    // The domain plans of `requires`' operands are those of the definition's functional heads,
    // as in a query.
    let requires = rule.requires.iter().cloned().collect::<Vec<_>>();
    prepare_lemma_domains(definition, &mut translation, congruence.clone(), &requires);
    let equality = SExpr::application(
        "=",
        vec![
            translation.translate_term(&rule.lhs)?,
            translation.translate_term(rhs)?,
        ],
    );
    let body = if rule.requires.is_empty() {
        equality
    } else {
        let requires = rule
            .requires
            .iter()
            .map(|predicate| translation.translate_predicate(predicate))
            .collect::<Result<Vec<_>, _>>()?;
        SExpr::application("=>", vec![SExpr::application("and", requires), equality])
    };
    let mut binders = Vec::new();
    for variable in &rule.lhs.attributes().variables {
        let term = Term::variable(variable.clone());
        let Some(name) = translation.mappings.remove(&term) else {
            return Err(TranslationError::MissingSmtLemmaVariable {
                rule_id: rule.attributes.unique_id.clone(),
                variable: variable.clone(),
            });
        };
        binders.push(SExpr::List(vec![
            SExpr::atom(name),
            SExpr::atom(prelude_smt_sort(&variable.sort)?),
        ]));
    }
    // A surplus term of the lemma's own text is the author's, a lemma the prelude cannot state:
    // an error, as before domains were read. Any other came from an operand's domain plan (a
    // ceil equation's condition over a function the translation abstracts), a name of this
    // translation like a domain function: the lemma is left out.
    let written = lemma_subterms(rule, rhs);
    if !translation.mappings.is_empty()
        && translation
            .mappings
            .keys()
            .all(|term| written.contains(term))
    {
        return Err(TranslationError::SmtLemmaSurplusMappings {
            rule_id: rule.attributes.unique_id.clone(),
            terms: translation.mappings.into_keys().collect(),
        });
    }
    if let Some(reason) = left_out_reason(&translation, &written) {
        // Naming the operand is for the report, not the solver: it counts nothing, so the
        // prelude's build counts only its one translation of each lemma.
        let named = k_rust_kore::measure::without_counting(|| {
            left_out_operand(definition, &congruence, rule, &written)
        });
        let (operand, reason) = match named {
            Some((operand, reason)) => (Some(operand), reason),
            None => (None, reason),
        };
        return Ok(LemmaTranslation::LeftOut { operand, reason });
    }
    Ok(LemmaTranslation::Stated(if binders.is_empty() {
        body
    } else {
        SExpr::List(vec![SExpr::atom("forall"), SExpr::List(binders), body])
    }))
}

/// Every subterm of the `smt-lemma` `rule` as written: of its left-hand side, its right-hand
/// side `rhs` and the terms of its `requires`.
fn lemma_subterms(rule: &RewriteRule, rhs: &Term) -> rustc_hash::FxHashSet<Term> {
    let mut pending = vec![rule.lhs.clone(), rhs.clone()];
    for predicate in rule.requires.iter() {
        predicate.visit_terms(&mut |term| pending.push(term.clone()));
    }
    let mut seen = rustc_hash::FxHashSet::default();
    while let Some(term) = pending.pop() {
        if seen.insert(term.clone()) {
            pending.extend(crate::deferred::children(&term).into_iter().cloned());
        }
    }
    seen
}

/// The SMT-LIB sort that stands for a K sort in a translation (`sort_denotation`).
///
/// Only `Int` and `Bool` are interpreted: they denote the K sort's values, and the SMT-LIB
/// theory operations over them are the ones an `smt-hook` names. Every other sort is an
/// uninterpreted sort, declared by the prelude, whose models need not have the K sort's values
/// and over which no theory operation is defined. Interpreting a further sort (a floating-point
/// or bit-vector sort) is a new variant here, and `hook_is_well_sorted` then decides which hooks
/// it admits.
#[derive(Clone, Debug, Eq, PartialEq)]
enum SmtSort {
    Int,
    Bool,
    /// The SMT-LIB sort expression that names the declared uninterpreted sort.
    Uninterpreted(String),
}

impl SmtSort {
    fn name(&self) -> String {
        match self {
            Self::Int => "Int".into(),
            Self::Bool => "Bool".into(),
            Self::Uninterpreted(name) => name.clone(),
        }
    }

    /// Whether the sort denotes the K sort's values: only an interpreted sort does.
    const fn exactness(&self) -> Exactness {
        match self {
            Self::Int | Self::Bool => Exactness::Exact,
            Self::Uninterpreted(_) => Exactness::Approximate,
        }
    }
}

/// The SMT-LIB sort that stands for `sort`: `Int` and `Bool` denote the K sorts named `SortInt`
/// and `SortBool`; every other sort is declared as an uninterpreted sort
/// (`SmtPrelude::from_definition`).
fn sort_denotation(sort: &Sort) -> Result<SmtSort, TranslationError> {
    match sort.node() {
        SortNode::Variable(_) => Err(TranslationError::ParametricSort(*sort)),
        _ if sort.is_builtin(BuiltinSort::Int) => Ok(SmtSort::Int),
        _ if sort.is_builtin(BuiltinSort::Bool) => Ok(SmtSort::Bool),
        SortNode::Application { name, arguments } if arguments.is_empty() => {
            Ok(SmtSort::Uninterpreted(quote(name)))
        }
        SortNode::Application { name, arguments } => Ok(SmtSort::Uninterpreted(format!(
            "({} {})",
            quote(name),
            arguments
                .iter()
                .map(prelude_smt_sort)
                .collect::<Result<Vec<_>, _>>()?
                .join(" ")
        ))),
    }
}

/// Whether the application of the `smt-hook` `hook` to `arguments`, of sort `result`, is a term
/// of the SMT-LIB signature the translation declares, so that the hook's operation may stand for
/// the application.
///
/// An SMT-LIB function applied to arguments outside its rank is not a term of any signature: it
/// denotes nothing, and a script containing it has no models to compare with K valuations. The
/// theory operations a hook names (`+`, `<`, `fp.add`, `bvult`, `int2bv`, ...) are defined over
/// interpreted sorts only, and the translation interprets only `Int` and `Bool` (`SmtSort`), so a
/// hook is applied only where its result and every argument have an interpreted sort. Over any
/// other sort (`Float`, `MInt{W}`, a sort hooked `INT.Int` under another name) its operands are
/// constants of an uninterpreted sort that no theory operation accepts, whatever the hook says.
///
/// The core operators `=` and `distinct` are defined at every sort, of their arguments taken
/// together, and `ite` at every sort of its branches under a `Bool` condition; each is admitted
/// over any sort when its operands have one sort, as their rank requires.
///
/// A sort that has no SMT-LIB sort (a sort variable) admits no hook either.
///
/// The decision reads the sorts only. A hook over `Int` and `Bool` is trusted to name an
/// operation of that rank, as the `Exactness` contract states; where its text is not one (an
/// unknown operator, a wrong arity), the solver rejects the query's script, which is a query
/// failure (`SmtError::MalformedScript`), never an answer.
fn hook_is_well_sorted(hook: &SExpr, result: &Sort, arguments: &[Term]) -> bool {
    let Ok(result) = sort_denotation(result) else {
        return false;
    };
    let Ok(operands) = arguments
        .iter()
        .map(|argument| sort_denotation(&argument.sort()))
        .collect::<Result<Vec<_>, _>>()
    else {
        return false;
    };
    let interpreted = |sort: &SmtSort| match sort {
        SmtSort::Int | SmtSort::Bool => true,
        SmtSort::Uninterpreted(_) => false,
    };
    match hook {
        SExpr::Atom(operator) if operator == "=" || operator == "distinct" => {
            result == SmtSort::Bool
                && operands.len() >= 2
                && operands.iter().all(|operand| *operand == operands[0])
        }
        SExpr::Atom(operator) if operator == "ite" => matches!(
            operands.as_slice(),
            [SmtSort::Bool, then, otherwise] if *then == result && *otherwise == result
        ),
        SExpr::Atom(_) | SExpr::List(_) => interpreted(&result) && operands.iter().all(interpreted),
    }
}

/// The SMT-LIB sort that stands for `sort` in the prelude, which declares the trusted
/// signatures of `smtlib` symbols and the SMT lemmas, not a query, and so records nothing.
fn prelude_smt_sort(sort: &Sort) -> Result<String, TranslationError> {
    sort_denotation(sort).map(|sort| sort.name())
}

fn quote(name: &str) -> String {
    format!("|{name}|")
}

/// The SMT-LIB symbol `name` denotes: `|s|` and `s` are one symbol.
fn symbol_name(name: &str) -> &str {
    name.strip_prefix('|')
        .and_then(|name| name.strip_suffix('|'))
        .unwrap_or(name)
}

/// Whether `value`, the text of a domain value of the `Bool` or `Int` sort `sort`, is an SMT-LIB
/// literal of that sort as the solver reads it: `true` or `false`, or a decimal numeral with an
/// optional minus sign. The translation writes such a literal as itself; any other text it copies
/// is not its own (`TranslationState::write_foreign_text`).
fn is_smt_literal(sort: &Sort, value: &str) -> bool {
    if sort.is_builtin(BuiltinSort::Bool) {
        return matches!(value, "true" | "false");
    }
    let digits = value.strip_prefix('-').unwrap_or(value);
    !digits.is_empty() && digits.bytes().all(|digit| digit.is_ascii_digit())
}

#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Satisfiability {
    /// The translation has a model. It is a K valuation of the predicates only when the
    /// translation is exact (`translation_exactness`).
    Sat,
    /// No K valuation satisfies the predicates, when they are definedness-faithful
    /// (docs/compatibility.md, "Solver decisions over partial operations"); otherwise only the
    /// translation has no model. Every predicate the backend poses is, except over a definition
    /// whose rule or equation condition equates two possibly undefined terms or whose axioms hold
    /// an `\equals` that reads a term as a predicate or a condition over a Boolean term-level
    /// `\and` (that section's gaps).
    Unsat,
    /// The solver ran within its own per-query bounds (its timeout, resource limit and retries)
    /// and did not decide the query; the payload is its reason. Never a stop: a query that stopped (a
    /// cancelled request, a passed step deadline, a failed prelude) returns the stop on the outer
    /// layer of [`SmtSolver::is_sat`] instead.
    Unknown(String),
}

/// The answer of `SmtSolver::check_predicates(known, substitution, checked)`.
#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Validity {
    /// `known ∧ ¬checked` is unsatisfiable: every instance of `known` satisfies `checked`.
    Valid,
    /// `known ∧ checked` is unsatisfiable: no instance of `known` satisfies `checked`.
    /// `known` is not shown empty; it may be empty when its own satisfiability came from an
    /// approximate translation. This is a refutation, not a counterexample.
    Refuted,
    /// `known` is unsatisfiable.
    InconsistentGroundTruth,
    /// Neither `checked` nor its negation is refuted under `known`: both have SMT models.
    /// With an approximate translation neither model need be a K valuation, so this answer
    /// shows no instance on either side.
    Contingent,
    /// The solver ran within its own per-query bounds and decided neither side; the payload is
    /// its reason. Never a stop, which [`SmtSolver::check_predicates`] returns on its outer layer.
    Unknown(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ModelResult {
    Sat(Substitution),
    Unsat,
    /// No model was obtained: the solver ran within its own per-query bounds and did not decide
    /// the query, or its model was of an approximate translation and so no K valuation (the
    /// payload says which). Never a stop, which [`SmtSolver::get_model`] returns on its outer
    /// layer.
    Unknown(String),
}

/// A failure of one solver query: a fact about the query and the backend's capabilities. A stop
/// is not a failure (design CBC-04): a failed solver prelude, in particular, is
/// `stop::StopCause::SolverPrelude`, because it belongs to every operation using the solver.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum SmtError {
    Translation(TranslationError),
    Unavailable,
    /// The solver ran within its own per-query bounds and returned unknown where the query's
    /// consumer needed an answer. Never a stop.
    Unknown(String),
    InconsistentGroundTruth,
    /// The solver rejected the query's script (a parse or sort error, an undeclared or a
    /// redeclared symbol), so it answered nothing about it; `message` is the solver's message.
    /// The prelude is known to load when this is returned, so the query's own text is at fault:
    /// text the definition supplies (an `smt-hook`, an `smtlib` name clashing with a name the
    /// query writes), the user prelude, or k-rust's translation. `translation_blamed` holds when
    /// only the last can be (`SmtPrelude::blames_the_translation`): the script holds no text
    /// k-rust did not write itself, so the rejection is a defect of k-rust. A debug build panics
    /// on such a rejection instead of returning it. Never a stop.
    MalformedScript {
        message: String,
        translation_blamed: bool,
    },
    MissingModel,
    MissingModelValue(Variable),
    InvalidModelValue {
        variable: Variable,
        value: String,
    },
}

impl From<TranslationError> for SmtError {
    fn from(error: TranslationError) -> Self {
        Self::Translation(error)
    }
}

/// A decision procedure for predicates under the definition's `smt-lemma` axioms and prelude.
///
/// Each query answers in two layers: the outer `Err` is a [`Stop`](crate::stop::Stop), the
/// query ended before answering because a resource of its owner ran out or failed (the request
/// was cancelled, the step deadline passed, the solver's prelude failed); the inner `Result` is
/// the answer or the query's own failure. A consumer that falls back on a failure writes its
/// fallback against the inner layer, after `?`, so the fallback cannot see a stop. The
/// single-layer shape no longer compiles:
///
/// ```compile_fail,E0308
/// use k_rust_backend::{
///     smt::{NoSolver, Satisfiability, SmtSolver},
///     stop::Stoppable,
///     substitution::Substitution,
/// };
///
/// fn refuted() -> Stoppable<bool> {
///     Ok(matches!(NoSolver.is_sat(&[], &Substitution::new()), Ok(Satisfiability::Unsat)))
/// }
/// ```
///
/// The same decision with the stop propagated first:
///
/// ```
/// use k_rust_backend::{
///     smt::{NoSolver, Satisfiability, SmtSolver},
///     stop::{Stop, Stoppable},
///     substitution::Substitution,
/// };
///
/// fn refuted() -> Stoppable<bool> {
///     Ok(matches!(NoSolver.is_sat(&[], &Substitution::new())?, Ok(Satisfiability::Unsat)))
/// }
/// assert_eq!(refuted().map_err(Stop::into_cause), Ok(false));
/// ```
///
/// An implementation that does work a stop should interrupt polls `stop::check()?` before it.
pub trait SmtSolver {
    fn is_sat(
        &self,
        predicates: &[Predicate],
        substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>>;

    fn check_predicates(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>>;

    /// A model of `query`'s residual: a `Sat` substitution must satisfy its predicates and its
    /// substitution in K. An approximate SMT model is reported as `Unknown` instead.
    ///
    /// Only [`model_of`](crate::model::model_of) builds a [`ModelQuery`], after the definition
    /// has decided what it can of the predicate, so this is never asked about a predicate whose
    /// answer depends on equations or constructor freeness the solver does not see.
    fn get_model(&self, _query: &ModelQuery<'_>) -> Stoppable<Result<ModelResult, SmtError>> {
        Ok(Err(SmtError::Unavailable))
    }

    /// The prelude-failure signal an operation using this solver installs
    /// (`stop::operation`); `None` for a solver without a prelude that can fail.
    fn prelude_signal(&self) -> Option<&PreludeSignal> {
        None
    }

    /// Whether an undecided answer of this solver is, as a decided one is, a function of the
    /// query and the build: true only where every bound on an attempt counts the solver's own
    /// work, not time (`z3::Z3Options::resource_limit`). By default an `Unknown` may be a
    /// timeout, which depends on the machine's speed and load. A solver that forwards its
    /// queries to another forwards this too.
    fn undecided_answers_reproducible(&self) -> bool {
        false
    }

    /// The identity of the solver whose answers this one gives: by default its own address. A
    /// solver that forwards every query to another and returns its answers unchanged gives that
    /// one's identity, so that work the backend keys by its solver (`simplify`'s reuse of an
    /// `Unspecified` evaluation or of an equation-condition verdict) is shared across the
    /// forwarding.
    fn identity(&self) -> usize {
        std::ptr::from_ref(self).cast::<()>().addr()
    }
}

/// The solver of a build without one: every query that needs a solver fails with `Unavailable`,
/// immediately, so there is no work for a stop to interrupt.
#[derive(Clone, Copy, Debug, Default)]
pub struct NoSolver;

impl SmtSolver for NoSolver {
    fn is_sat(
        &self,
        _predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        Ok(Err(SmtError::Unavailable))
    }

    fn check_predicates(
        &self,
        _known: &[Predicate],
        _substitution: &Substitution,
        checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        Ok(if checked.is_empty() {
            Ok(Validity::Valid)
        } else {
            Err(SmtError::Unavailable)
        })
    }
}

/// The reason of a [`ModelResult::Unknown`] that reports an approximate translation: the model
/// the solver found is no K valuation. It is a fact about the query, not an undecided answer.
pub(crate) const APPROXIMATE_MODEL_REASON: &str =
    "the query abstracts symbols or sorts; a solver model is not a model of the predicate";

/// A solver that forwards every query to `inner` and counts the undecided answers it delivers:
/// an `Unknown` from [`SmtSolver::is_sat`] or [`SmtSolver::check_predicates`], and an `Unknown`
/// from [`SmtSolver::get_model`] other than the approximate-model one
/// ([`APPROXIMATE_MODEL_REASON`]).
///
/// An undecided answer depends on the solver's bounds (its timeout, its resource limit, its
/// incompleteness), so a consumer that reads it as an over-approximation may compute another
/// result than a run in which the same query was decided. A decided answer (`Sat`, `Unsat`, a
/// validity verdict, a model) is a function of the query and the build, whatever produced it (the
/// solver, a retry, another subquery of a validity check, or a cache that holds only decided
/// answers), and so is a failure (`Err`: no solver in this build, a query that does not
/// translate); neither is counted, and nor is a stop. The count is taken once per answer as the
/// consumer receives it, after the inner solver's retries.
///
/// Each count is also added to this thread's [`undecided_on_thread`], which a caller reads
/// before and after work that queries through such a solver to learn whether that work received
/// an undecided answer (`simplify::ConditionMemo`).
pub(crate) struct UndecidedCounting<'a> {
    inner: &'a dyn SmtSolver,
    undecided: std::sync::atomic::AtomicUsize,
}

impl<'a> UndecidedCounting<'a> {
    pub(crate) fn new(inner: &'a dyn SmtSolver) -> Self {
        Self {
            inner,
            undecided: std::sync::atomic::AtomicUsize::new(0),
        }
    }

    /// The undecided answers delivered so far.
    pub(crate) fn undecided(&self) -> usize {
        self.undecided.load(std::sync::atomic::Ordering::Relaxed)
    }

    fn count(&self, undecided: bool) {
        if undecided {
            self.undecided
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            UNDECIDED_ON_THREAD.set(UNDECIDED_ON_THREAD.get() + 1);
        }
    }
}

thread_local! {
    static UNDECIDED_ON_THREAD: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The undecided answers every [`UndecidedCounting`] delivered on this thread so far, one per
/// layer an answer passed through: a monotone count, read as a difference around some work.
pub(crate) fn undecided_on_thread() -> usize {
    UNDECIDED_ON_THREAD.get()
}

impl SmtSolver for UndecidedCounting<'_> {
    fn is_sat(
        &self,
        predicates: &[Predicate],
        substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        let answer = self.inner.is_sat(predicates, substitution);
        self.count(matches!(answer, Ok(Ok(Satisfiability::Unknown(_)))));
        answer
    }

    fn check_predicates(
        &self,
        known: &[Predicate],
        substitution: &Substitution,
        checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        let answer = self.inner.check_predicates(known, substitution, checked);
        self.count(matches!(answer, Ok(Ok(Validity::Unknown(_)))));
        answer
    }

    fn get_model(&self, query: &ModelQuery<'_>) -> Stoppable<Result<ModelResult, SmtError>> {
        let answer = self.inner.get_model(query);
        self.count(matches!(
            &answer,
            Ok(Ok(ModelResult::Unknown(reason))) if reason != APPROXIMATE_MODEL_REASON
        ));
        answer
    }

    fn prelude_signal(&self) -> Option<&PreludeSignal> {
        self.inner.prelude_signal()
    }

    fn undecided_answers_reproducible(&self) -> bool {
        self.inner.undecided_answers_reproducible()
    }

    fn identity(&self) -> usize {
        self.inner.identity()
    }
}

/// The argument index that a template atom `#i` names, when it is a placeholder.
fn placeholder(atom: &str) -> Option<usize> {
    atom.strip_prefix('#')
        .and_then(|index| index.parse::<usize>().ok())
}

/// The prefix of the name that states an argument named more than once in an `smt-hook`
/// template (`fill_placeholders`).
const HOOK_ARGUMENT: &str = "KRUST-HOOK-ARGUMENT-";

/// The `smt-hook` template `expression` applied to the translations of its `arguments`.
///
/// A template is a function of its arguments, and one that names an argument several times
/// names one value several times (`/Int` names each argument five times, the power guard of
/// `guard_powers` its base four times). Written as a copy at every occurrence, a nesting of such
/// hooks would be exponentially long in its depth; so an argument named more than once whose
/// translation is not an atom is stated once, in a `let` around the template, and named by its
/// binding. `let` denotes substitution, so the formula is the one the copies write. No binding
/// captures a name: an argument's translation is closed (it binds every `let` name it uses), and
/// the template names only its own bindings.
///
/// The translations are taken by value and each is moved to the one place that states it, its
/// single occurrence or its binding; only an atom named several times is copied. A nesting of
/// hooks then builds each level from its own template and its arguments' translations, and
/// copies none of the levels below it.
fn fill_placeholders(expression: &SExpr, arguments: Vec<SExpr>) -> Result<SExpr, TranslationError> {
    /// How the template states one argument.
    enum Slot {
        /// The translation itself, with the occurrences that still name it: an atom, or a list
        /// named at most once. The last occurrence takes it.
        Stated {
            value: Option<SExpr>,
            remaining: usize,
        },
        /// A list named more than once: the name of its `let` binding.
        Bound(SExpr),
    }
    fn count(expression: &SExpr, uses: &mut [usize]) {
        match expression {
            SExpr::Atom(atom) => {
                if let Some(slot) = placeholder(atom)
                    .and_then(|index| index.checked_sub(1))
                    .and_then(|index| uses.get_mut(index))
                {
                    *slot += 1;
                }
            }
            SExpr::List(items) => items.iter().for_each(|item| count(item, uses)),
        }
    }
    fn substitute(expression: &SExpr, slots: &mut [Slot]) -> Result<SExpr, TranslationError> {
        match expression {
            SExpr::Atom(atom) => {
                let Some(index) = placeholder(atom) else {
                    return Ok(expression.clone());
                };
                if index == 0 || index > slots.len() {
                    return Err(TranslationError::PlaceholderOutOfBounds {
                        placeholder: index,
                        arguments: slots.len(),
                    });
                }
                Ok(match &mut slots[index - 1] {
                    Slot::Bound(name) => name.clone(),
                    Slot::Stated { value, remaining } => {
                        *remaining -= 1;
                        if *remaining == 0 {
                            value.take()
                        } else {
                            value.clone()
                        }
                        .expect("an argument is taken by its last occurrence only")
                    }
                })
            }
            SExpr::List(items) => Ok(SExpr::List(
                items
                    .iter()
                    .map(|item| substitute(item, slots))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
        }
    }

    let mut uses = vec![0; arguments.len()];
    count(expression, &mut uses);
    let mut bindings = Vec::new();
    let mut slots = arguments
        .into_iter()
        .zip(uses)
        .enumerate()
        .map(|(index, (argument, uses))| {
            if uses > 1 && matches!(argument, SExpr::List(_)) {
                let name = SExpr::atom(format!("{HOOK_ARGUMENT}{}", index + 1));
                bindings.push(SExpr::List(vec![name.clone(), argument]));
                Slot::Bound(name)
            } else {
                Slot::Stated {
                    value: Some(argument),
                    remaining: uses,
                }
            }
        })
        .collect::<Vec<_>>();
    let body = substitute(expression, &mut slots)?;
    Ok(if bindings.is_empty() {
        body
    } else {
        SExpr::application("let", vec![SExpr::List(bindings), body])
    })
}

#[cfg(test)]
#[allow(clippy::wildcard_enum_match_arm)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::term::{FunctionType, Symbol, SymbolAttributes, SymbolType, Variable};

    /// A solver that answers every query with the next scripted answer of its kind.
    struct Scripted {
        satisfiability: std::cell::RefCell<Vec<Option<Result<Satisfiability, SmtError>>>>,
        validity: std::cell::RefCell<Vec<Option<Result<Validity, SmtError>>>>,
        signal: PreludeSignal,
    }

    impl SmtSolver for Scripted {
        /// `None` scripts a stop.
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            match self.satisfiability.borrow_mut().remove(0) {
                Some(answer) => Ok(answer),
                None => Err(crate::stop::Stop::solver_prelude(
                    crate::stop::PreludeFailure::Inconsistent,
                )),
            }
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &Substitution,
            _checked: &[Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            match self.validity.borrow_mut().remove(0) {
                Some(answer) => Ok(answer),
                None => Err(crate::stop::Stop::solver_prelude(
                    crate::stop::PreludeFailure::Inconsistent,
                )),
            }
        }

        fn prelude_signal(&self) -> Option<&PreludeSignal> {
            Some(&self.signal)
        }
    }

    /// The adapter counts one per undecided answer it delivers (`Unknown` from `is_sat` and
    /// `check_predicates`), and nothing for a decided answer, a failure or a stop; it delivers
    /// every answer unchanged and forwards the inner solver's prelude signal.
    #[test]
    fn the_undecided_counting_adapter_counts_each_unknown_answer_once() {
        let unknown = || "timeout".to_owned();
        let satisfiability = vec![
            Some(Ok(Satisfiability::Unknown(unknown()))),
            Some(Ok(Satisfiability::Sat)),
            Some(Ok(Satisfiability::Unsat)),
            Some(Err(SmtError::Unavailable)),
            Some(Err(SmtError::Unknown(unknown()))),
            Some(Ok(Satisfiability::Unknown(unknown()))),
            None,
        ];
        let validity = vec![
            Some(Ok(Validity::Valid)),
            Some(Ok(Validity::Refuted)),
            Some(Ok(Validity::Contingent)),
            Some(Ok(Validity::InconsistentGroundTruth)),
            Some(Ok(Validity::Unknown(unknown()))),
            Some(Err(SmtError::Unavailable)),
            None,
        ];
        let solver = Scripted {
            satisfiability: std::cell::RefCell::new(satisfiability.clone()),
            validity: std::cell::RefCell::new(validity.clone()),
            signal: PreludeSignal::default(),
        };
        let counting = UndecidedCounting::new(&solver);
        assert!(std::ptr::eq(
            counting.prelude_signal().unwrap(),
            &raw const solver.signal
        ));
        for expected in satisfiability {
            let answer = counting.is_sat(&[], &Substitution::new());
            match expected {
                Some(expected) => assert_eq!(answer.unwrap(), expected),
                None => {
                    let _cause = answer.unwrap_err().into_cause();
                }
            }
        }
        assert_eq!(counting.undecided(), 2);
        for expected in validity {
            let answer = counting.check_predicates(&[], &Substitution::new(), &[]);
            match expected {
                Some(expected) => assert_eq!(answer.unwrap(), expected),
                None => {
                    let _cause = answer.unwrap_err().into_cause();
                }
            }
        }
        assert_eq!(counting.undecided(), 3);
    }

    fn symbol(name: &str, smt: Option<SmtType>, arguments: Vec<Sort>, result: Sort) -> Arc<Symbol> {
        Arc::new(Symbol {
            name: name.into(),
            sort_variables: Vec::new(),
            argument_sorts: arguments,
            result_sort: result,
            attributes: {
                let mut attributes = SymbolAttributes::constructor().with_declared_function(true);
                attributes.symbol_type = SymbolType::Function(FunctionType::Total);
                attributes.smt = smt;
                attributes
            },
        })
    }

    fn integer(value: &str) -> Term {
        Term::raw_domain_value(Sort::simple("SortInt"), value)
    }

    #[test]
    fn parses_and_renders_nested_s_expressions() {
        let source = "(ite (< #1 0) (- 0 #1) #1)";
        assert_eq!(SExpr::parse(source).unwrap().to_string(), source);
        assert!(matches!(
            SExpr::parse("(+ #1 #2) trailing"),
            Err(SExprError::TrailingInput(_))
        ));
    }

    /// A malformed `smt-hook` is reported by where its text goes wrong, in words.
    #[test]
    fn s_expression_errors_state_where_the_text_goes_wrong() {
        let message = |source: &str| SExpr::parse(source).unwrap_err().to_string();
        assert_eq!(
            message("  "),
            "the text ends where an expression is expected"
        );
        assert_eq!(message(")"), "the ')' at byte offset 0 closes no list");
        assert_eq!(
            message("(+ #1"),
            "the list opened at byte offset 0 is not closed"
        );
        assert_eq!(
            message("(+ ;)"),
            "the character at byte offset 3 cannot begin an expression"
        );
        assert_eq!(
            message("(+ #1 #2) trailing"),
            "text follows the expression at byte offset 10"
        );
    }

    #[test]
    fn expands_smt_hook_placeholders_recursively() {
        let int = Sort::simple("SortInt");
        let absolute = Term::application(
            symbol(
                "absolute",
                Some(SmtType::Hook(
                    SExpr::parse("(ite (< #1 0) (- 0 #1) #1)").unwrap(),
                )),
                vec![int],
                int,
            ),
            Vec::new(),
            vec![integer("-5")],
        );

        assert_eq!(
            TranslationState::new()
                .translate_term(&absolute)
                .unwrap()
                .to_string(),
            "(ite (< -5 0) (- 0 -5) -5)"
        );
    }

    /// Literal projections/shifts and finite masks retain the hook's signed integer meaning.
    /// Symbolic/negative amounts and unsupported masks keep the attribute's opaque reading.
    #[test]
    fn reads_bit_operations_by_literal_amounts_as_division_by_powers_of_two() {
        let int = Sort::simple("SortInt");
        let hooked = |name: &str, hook: &str, smt: Option<SmtType>, arity: usize| {
            let mut symbol = Arc::unwrap_or_clone(symbol(name, smt, vec![int; arity], int));
            symbol.attributes.hook = Some(hook.into());
            symbol.attributes.symbol_type = SymbolType::Function(FunctionType::Partial);
            Arc::new(symbol)
        };
        let bit_range = hooked("bitRange", "INT.bitRange", None, 3);
        let shr = hooked("shr", "INT.shr", Some(SmtType::Lib("shrInt".into())), 2);
        let shl = hooked("shl", "INT.shl", Some(SmtType::Lib("shlInt".into())), 2);
        let and = hooked("and", "INT.and", Some(SmtType::Lib("andInt".into())), 2);
        let or = hooked("or", "INT.or", Some(SmtType::Lib("orInt".into())), 2);
        let xor = hooked("xor", "INT.xor", Some(SmtType::Lib("xorInt".into())), 2);
        let x = Term::variable(Variable::new("X", int));
        let y = Term::variable(Variable::new("Y", int));
        let apply = |symbol: &Arc<Symbol>, arguments: Vec<Term>| {
            Term::application(symbol.clone(), Vec::new(), arguments)
        };
        for (application, expected, exactness) in [
            (
                apply(&bit_range, vec![x.clone(), integer("3"), integer("3")]),
                "(mod (div SMT-1 8) 8)",
                Exactness::Exact,
            ),
            (
                apply(&bit_range, vec![x.clone(), integer("0"), integer("3")]),
                "(mod SMT-1 8)",
                Exactness::Exact,
            ),
            (
                apply(&bit_range, vec![x.clone(), integer("2"), integer("0")]),
                "(mod (div SMT-1 4) 1)",
                Exactness::Exact,
            ),
            (
                apply(&shr, vec![x.clone(), integer("6")]),
                "(div SMT-1 64)",
                Exactness::Exact,
            ),
            (
                apply(&and, vec![x.clone(), integer("7")]),
                "(mod SMT-1 8)",
                Exactness::Exact,
            ),
            (
                apply(&and, vec![integer("15"), x.clone()]),
                "(mod SMT-1 16)",
                Exactness::Exact,
            ),
            (
                apply(&and, vec![x.clone(), integer("0")]),
                "0",
                Exactness::Exact,
            ),
            (
                apply(&and, vec![x.clone(), integer("6")]),
                "(* 2 (mod (div SMT-1 2) 4))",
                Exactness::Exact,
            ),
            (
                apply(&and, vec![x.clone(), integer("128")]),
                "(* 128 (mod (div SMT-1 128) 2))",
                Exactness::Exact,
            ),
            (
                apply(&and, vec![x.clone(), integer("165")]),
                "(+ (mod SMT-1 2) (* 4 (mod (div SMT-1 4) 2)) (* 32 (mod (div SMT-1 32) 2)) (* 128 (mod (div SMT-1 128) 2)))",
                Exactness::Exact,
            ),
            (
                apply(&shl, vec![x.clone(), integer("4")]),
                "(* SMT-1 16)",
                Exactness::Exact,
            ),
            (
                apply(&or, vec![x.clone(), integer("255")]),
                "(- (+ SMT-1 255) (mod SMT-1 256))",
                Exactness::Exact,
            ),
            (
                apply(&xor, vec![integer("255"), x.clone()]),
                "(- (+ SMT-1 255) (* 2 (mod SMT-1 256)))",
                Exactness::Exact,
            ),
            (
                apply(&and, vec![x.clone(), integer("-1")]),
                "(andInt SMT-1 -1)",
                Exactness::Approximate,
            ),
            (
                apply(&shr, vec![x.clone(), y.clone()]),
                "(shrInt SMT-1 SMT-2)",
                Exactness::Approximate,
            ),
            (
                apply(&shr, vec![x.clone(), integer("-1")]),
                "(shrInt SMT-1 -1)",
                Exactness::Approximate,
            ),
            (
                apply(&bit_range, vec![x.clone(), y, integer("3")]),
                "SMT-1",
                Exactness::Approximate,
            ),
        ] {
            let mut translation = TranslationState::new();
            let translated = translation.translate_term(&application).unwrap();
            assert_eq!(translated.to_string(), expected, "{application:?}");
            assert_eq!(translation.exactness(), exactness, "{application:?}");
        }

        // The readings against the hooks' values.
        let value = |hook: &str, arguments: &[i64]| {
            let arguments = arguments
                .iter()
                .map(|value| integer(&value.to_string()))
                .collect::<Vec<_>>();
            match crate::builtin::evaluate_hook(hook, &arguments) {
                Ok(Ok(crate::builtin::BuiltinResult::Value(result))) => {
                    crate::builtin::read_int(&result).unwrap()
                }
                other => panic!("{hook}{arguments:?}: {other:?}"),
            }
        };
        let floor_div =
            |value: i64, power: u32| num_bigint::BigInt::from(value.div_euclid(1 << power));
        for operand in -300_i64..300 {
            for offset in 0..10 {
                for length in 0..10 {
                    let reading = (operand.div_euclid(1 << offset)).rem_euclid(1 << length);
                    assert_eq!(
                        value("INT.bitRange", &[operand, offset.into(), length.into()]),
                        reading.into()
                    );
                }
                assert_eq!(
                    value("INT.shr", &[operand, offset.into()]),
                    floor_div(operand, offset)
                );
                let mask = (1_i64 << offset) - 1;
                assert_eq!(
                    value("INT.and", &[operand, mask]),
                    operand.rem_euclid(1 << offset).into()
                );
            }
        }
    }

    /// Every power of an `smt-hook` whose exponent is not a numeral, written as the hook's
    /// operation or inside its expression, is read by its value's cases where an integer is its
    /// value, the rest an uninterpreted function (`power_value`), and as another uninterpreted
    /// function elsewhere, never as Z3's power; the uninterpreted parts make the translation
    /// approximate even for a total symbol. A power whose exponent is a numeral has an integer
    /// value for every base, and is read as itself.
    #[test]
    fn reads_a_power_as_itself_only_where_an_integer_is_its_value() {
        let int = Sort::simple("SortInt");
        let power = symbol(
            "power",
            Some(SmtType::Hook(SExpr::atom("^"))),
            vec![int, int],
            int,
        );
        let power_modulo = symbol(
            "powerModulo",
            Some(SmtType::Hook(SExpr::parse("(mod (^ #1 #2) #3)").unwrap())),
            vec![int, int, int],
            int,
        );
        let exponent = Term::variable(Variable::new("B", int));
        let guard = |base: &str, exponent: &str, value: &str| {
            format!(
                "(ite (or (>= {exponent} 0) (= {base} 1) (= {base} (- 1))) {value} \
                 (|KRUST-POWER-OUTSIDE-THE-INTEGERS| {base} {exponent}))"
            )
        };
        // A base that is not a literal is read by the prelude's function of its cases, with
        // products up to the exponent 4.
        let symbolic = |base: &str, exponent: &str| {
            guard(
                base,
                exponent,
                &format!("(|KRUST-POWER-VALUE| {base} {exponent})"),
            )
        };
        assert_eq!(
            power_value_definition(),
            "(define-fun |KRUST-POWER-VALUE| ((KRUST-BASE Int) (KRUST-EXPONENT Int)) Int \
             (ite (= KRUST-EXPONENT 0) 1 (ite (= KRUST-BASE 1) 1 (ite (= KRUST-BASE (- 1)) \
             (ite (= (mod KRUST-EXPONENT 2) 0) 1 (- 1)) (ite (= KRUST-EXPONENT 1) KRUST-BASE \
             (ite (= KRUST-BASE 0) 0 (ite (= KRUST-EXPONENT 2) (* KRUST-BASE KRUST-BASE) \
             (ite (= KRUST-EXPONENT 3) (* KRUST-BASE (* KRUST-BASE KRUST-BASE)) \
             (ite (= KRUST-EXPONENT 4) (* KRUST-BASE (* KRUST-BASE (* KRUST-BASE KRUST-BASE))) \
             (|KRUST-POWER| KRUST-BASE KRUST-EXPONENT))))))))))"
        );
        // A literal base of magnitude at least 2 is read by the query's function of its powers
        // as numerals, up to the exponent 256.
        let literal = |base: i64, exponent: &str| {
            guard(
                &base.to_string(),
                exponent,
                &format!("(|KRUST-POWER-OF-{base}| {exponent})"),
            )
        };
        let mut table = "(|KRUST-POWER| 2 KRUST-EXPONENT)".to_owned();
        for k in (0..=256u32).rev() {
            table = format!(
                "(ite (= KRUST-EXPONENT {k}) {} {table})",
                BigInt::from(2).pow(k)
            );
        }
        assert_eq!(
            power_of_literal_definition(&BigInt::from(2)),
            format!("(define-fun |KRUST-POWER-OF-2| ((KRUST-EXPONENT Int)) Int {table})")
        );
        let x = Term::variable(Variable::new("X", Sort::simple("SortInt")));
        let mut translation = TranslationState::new();
        let translated = translation
            .translate_term(&Term::application(
                power.clone(),
                Vec::new(),
                vec![x.clone(), exponent.clone()],
            ))
            .unwrap();
        assert_eq!(translated.to_string(), symbolic("SMT-1", "SMT-2"));
        assert_eq!(translation.exactness(), Exactness::Approximate);
        // One fact of the power at its operands, which no quantifier binds.
        assert_eq!(translation.power_facts.len(), 1);
        assert!(translation.power_facts[0].to_string().starts_with(
            "(let ((SMT-3 SMT-1) (SMT-4 SMT-2)) (let ((SMT-5 (|KRUST-POWER-VALUE| SMT-3 SMT-4)))"
        ));
        assert!(translation.derived_definitions.is_empty());

        let mut translation = TranslationState::new();
        let translated = translation
            .translate_term(&Term::application(
                power.clone(),
                Vec::new(),
                vec![integer("2"), exponent.clone()],
            ))
            .unwrap();
        assert_eq!(translated.to_string(), literal(2, "SMT-1"));
        assert_eq!(
            translation.derived_definitions,
            [power_of_literal_definition(&BigInt::from(2))]
        );
        // The fact past the window: the power exceeds 2^256.
        assert!(translation.power_facts[0].to_string().contains(&format!(
            "(=> (> SMT-3 256) (> SMT-4 {}))",
            BigInt::from(2).pow(256)
        )));
        let translated = TranslationState::new()
            .translate_term(&Term::application(
                power_modulo,
                Vec::new(),
                vec![integer("-3"), exponent.clone(), integer("7")],
            ))
            .unwrap();
        assert_eq!(
            translated.to_string(),
            format!("(mod {} 7)", literal(-3, "SMT-1"))
        );
        // The bases 1, -1 and 0 have their values for every exponent the guard admits.
        for (base, value) in [
            ("1", "1".to_owned()),
            ("-1", "(ite (= (mod SMT-1 2) 0) 1 (- 1))".to_owned()),
            ("0", "(ite (= SMT-1 0) 1 0)".to_owned()),
        ] {
            let translated = TranslationState::new()
                .translate_term(&Term::application(
                    power.clone(),
                    Vec::new(),
                    vec![integer(base), exponent.clone()],
                ))
                .unwrap();
            assert_eq!(translated.to_string(), guard(base, "SMT-1", &value));
        }

        // A positive numeral exponent, as the argument or in the template, leaves the power as it
        // is: the guard holds, and Z3 reads it as a product. The exponent 0 is the constant 1, of
        // the sort of Z3's power, for every base: Z3 leaves `(^ 0 0)` uninterpreted, and K's
        // `0 ^Int 0` is 1. A negative literal is not a numeral.
        for (arguments, expected) in [
            (vec![x.clone(), integer("2")], "(^ SMT-1 2)"),
            (vec![x.clone(), integer("0")], "1.0"),
        ] {
            let mut translation = TranslationState::new();
            let translated = translation
                .translate_term(&Term::application(power.clone(), Vec::new(), arguments))
                .unwrap();
            assert_eq!(translated.to_string(), expected);
            assert_eq!(translation.exactness(), Exactness::Exact);
        }
        assert_eq!(
            TranslationState::new()
                .translate_term(&Term::application(
                    power.clone(),
                    Vec::new(),
                    vec![integer("2"), integer("-1")],
                ))
                .unwrap()
                .to_string(),
            literal(2, "-1")
        );
        let squared_modulo = symbol(
            "squaredModulo",
            Some(SmtType::Hook(SExpr::parse("(mod (^ #1 2) #2)").unwrap())),
            vec![int, int],
            int,
        );
        assert_eq!(
            TranslationState::new()
                .translate_term(&Term::application(
                    squared_modulo,
                    Vec::new(),
                    vec![x.clone(), integer("7")],
                ))
                .unwrap()
                .to_string(),
            "(mod (^ SMT-1 2) 7)"
        );
        let zeroth_modulo = symbol(
            "zerothModulo",
            Some(SmtType::Hook(SExpr::parse("(mod (^ #1 0) #2)").unwrap())),
            vec![int, int],
            int,
        );
        assert_eq!(
            TranslationState::new()
                .translate_term(&Term::application(
                    zeroth_modulo,
                    Vec::new(),
                    vec![x, integer("7")],
                ))
                .unwrap()
                .to_string(),
            "(mod 1.0 7)"
        );
        assert!(applies_power(&SExpr::atom("^")));
        assert!(applies_power(&SExpr::parse("(mod (^ #1 #2) #3)").unwrap()));
        assert!(!applies_power(&SExpr::parse("(mod #1 #2)").unwrap()));
    }

    /// GAP K32: the facts of a power read with `KRUST-POWER` are ground instances at the powers
    /// the query states. A power whose exponent a quantifier binds gets none, since its fact would
    /// be a quantified formula over the function; two powers of one literal base get the facts of
    /// their pair besides their own.
    #[test]
    fn states_power_facts_only_at_powers_no_quantifier_binds() {
        let int = Sort::simple("SortInt");
        let power = symbol(
            "power",
            Some(SmtType::Hook(SExpr::atom("^"))),
            vec![int, int],
            int,
        );
        let b = Variable::new("B", int);
        let c = Term::variable(Variable::new("C", int));
        let power_of = |exponent: Term| {
            Term::application(power.clone(), Vec::new(), vec![integer("2"), exponent])
        };
        let equation = |exponent: Term| Predicate::Equals(power_of(exponent), integer("4"));

        let mut translation = TranslationState::new();
        translation
            .translate_predicate(&Predicate::Exists(
                b.clone(),
                Arc::new(equation(Term::variable(b.clone()))),
            ))
            .unwrap();
        assert!(translation.power_facts.is_empty());

        let mut translation = TranslationState::new();
        translation
            .translate_predicate(&equation(Term::variable(b.clone())))
            .unwrap();
        translation
            .translate_predicate(&equation(c.clone()))
            .unwrap();
        translation.translate_predicate(&equation(c)).unwrap();
        // One fact for each distinct power, and one for their pair.
        assert_eq!(translation.power_facts.len(), 3);
        assert!(
            translation.power_facts[2]
                .to_string()
                .contains("(|KRUST-POWER-OF-2| SMT-")
        );
    }

    /// GAP K32 review: two powers' exponents differ by a constant only where their linear sums
    /// say so, through `let`s read by substitution; a term that is not linear is compared by its
    /// text only where that text names no `let`-bound name.
    #[test]
    fn reads_an_exponent_difference_only_where_it_is_a_constant() {
        let difference = |first: &str, second: &str| {
            exponent_difference(
                &SExpr::parse(first).unwrap(),
                &SExpr::parse(second).unwrap(),
            )
        };
        let constant = |value: i64| Some(BigInt::from(value));
        assert_eq!(difference("(* 8 B)", "(* 8 (+ B 1))"), constant(8));
        assert_eq!(difference("(* 8 (+ B 1))", "(* 8 B)"), constant(-8));
        assert_eq!(
            difference("(let ((X (* 8 B))) X)", "(let ((Y (+ B 1))) (* Y 8))"),
            constant(8)
        );
        assert_eq!(
            difference("(- 256 (* 8 B))", "(- 264 (* 8 B))"),
            constant(8)
        );
        assert_eq!(difference("(+ (div B 2) 3)", "(div B 2)"), constant(-3));
        assert_eq!(difference("(* B B)", "(+ (* B B) (- 1))"), constant(-1));
        assert_eq!(difference("B", "C"), None);
        assert_eq!(difference("(* 8 B)", "(* 4 B)"), None);
        // `(div X 2)` names a `let`-bound `X`: its text is not what it denotes.
        assert_eq!(
            difference("(let ((X B)) (div X 2))", "(let ((X C)) (div X 2))"),
            None
        );
    }

    /// An `smt-hook` template that names an argument several times states it once, in a `let`,
    /// so a nesting of such hooks translates to text linear in its depth, not exponential: a
    /// power names its base four times and its exponent three times through its guard, and
    /// `/Int`'s template in `domains.md` names each argument five times. An atom is written in
    /// place.
    #[test]
    fn states_each_hook_argument_once_however_hooks_nest() {
        const DEPTH: usize = 8;
        const LEVEL: usize = 600;
        let int = Sort::simple("SortInt");
        let binary = |name: &str, template: SExpr| {
            symbol(name, Some(SmtType::Hook(template)), vec![int, int], int)
        };
        let power = binary("power", SExpr::atom("^"));
        let division = binary(
            "division",
            SExpr::parse(
                "(ite (or (= 0 (mod #1 #2)) (>= #1 0)) (div #1 #2) \
                 (ite (> #2 0) (+ (div #1 #2) 1) (- (div #1 #2) 1)))",
            )
            .unwrap(),
        );
        let plus = binary("plus", SExpr::atom("+"));
        let x = Term::variable(Variable::new("X", int));
        let y = Term::variable(Variable::new("Y", int));

        for symbol in [&power, &division] {
            let mut nested = x.clone();
            for _ in 0..DEPTH {
                nested = Term::application(symbol.clone(), Vec::new(), vec![nested, y.clone()]);
            }
            let text = TranslationState::new()
                .translate_term(&nested)
                .unwrap()
                .to_string();
            assert!(
                text.len() <= DEPTH * LEVEL,
                "{} nested {:?}: {} characters",
                DEPTH,
                symbol.name,
                text.len()
            );
        }

        let base = Term::application(plus, Vec::new(), vec![x, integer("1")]);
        let translated = TranslationState::new()
            .translate_term(&Term::application(power, Vec::new(), vec![base, y]))
            .unwrap();
        let name = "KRUST-HOOK-ARGUMENT-1";
        assert_eq!(
            translated.to_string(),
            format!(
                "(let (({name} (+ SMT-1 1))) (ite (or (>= SMT-2 0) (= {name} 1) (= {name} (- 1))) \
                 (|KRUST-POWER-VALUE| {name} SMT-2) (|KRUST-POWER-OUTSIDE-THE-INTEGERS| {name} SMT-2)))"
            )
        );
    }

    #[test]
    fn abstracts_uninterpreted_terms_stably_and_preserves_their_sorts() {
        let variable = Term::variable(Variable::new("X", Sort::simple("SortInt")));
        let predicate = Predicate::Equals(variable.clone(), variable.clone());
        let mut translation = TranslationState::new();

        assert_eq!(
            translation
                .translate_predicate(&predicate)
                .unwrap()
                .to_string(),
            "(= SMT-1 SMT-1)"
        );
        assert_eq!(translation.mappings.get(&variable), Some(&"SMT-1".into()));
        assert_eq!(variable.sort(), Sort::simple("SortInt"));
    }

    /// A term-level `\and` is the intersection of its operands, `\bottom` where they differ, so a
    /// Boolean one is not their conjunction: `\equals(true /\ false, false)` is false in K, while
    /// `(= (and true false) false)` holds. It translates as an unrelated constant.
    #[test]
    fn a_boolean_term_conjunction_is_not_translated_as_a_conjunction() {
        let boolean = Sort::simple("SortBool");
        let operand = |name: &str| Term::variable(Variable::new(name, boolean));
        let predicate = Predicate::Equals(
            Term::and(operand("B1"), operand("B2")),
            Term::raw_domain_value(boolean, "false"),
        );
        let mut state = TranslationState::new();
        let translated = state.translate_predicate(&predicate).unwrap().to_string();
        // The constant is the conjunction's only mapped term: neither operand is translated, so
        // no SMT `and` of them is written. (Since GAP K15 the atom carries the conjunction's
        // domain, `(and D (= c false))`, an SMT `and` of the domain and the equality.)
        assert_eq!(state.mappings.len(), 1, "{translated}");
        assert!(
            !state.mappings.contains_key(&operand("B1"))
                && !state.mappings.contains_key(&operand("B2")),
            "{translated}"
        );
        assert_eq!(state.exactness(), Exactness::Approximate);
    }

    #[test]
    fn translates_quantified_predicates_with_typed_binders() {
        let variable = Variable::new("X", Sort::simple("SortInt"));
        let predicate = Predicate::Exists(
            variable.clone(),
            Arc::new(Predicate::Equals(Term::variable(variable), integer("1"))),
        );

        assert_eq!(
            TranslationState::new()
                .translate_predicate(&predicate)
                .unwrap()
                .to_string(),
            "(exists ((SMT-1 Int)) (= SMT-1 1))"
        );
    }

    /// A right-nested implication spine is one disjunction of the negated premises and the
    /// conclusion, its operands named in the order the nested form names them; a single
    /// implication, and an implication in a premise, keep their `=>`.
    #[test]
    fn translates_an_implication_spine_as_one_flat_disjunction() {
        let int = Sort::simple("SortInt");
        let atom =
            |name: &str| Predicate::Equals(Term::variable(Variable::new(name, int)), integer("0"));
        let implies =
            |left: Predicate, right: Predicate| Predicate::Implies(Arc::new(left), Arc::new(right));
        let translate = |predicate: &Predicate| {
            TranslationState::new()
                .translate_predicate(predicate)
                .unwrap()
                .to_string()
        };

        assert_eq!(
            translate(&implies(atom("A"), atom("B"))),
            "(=> (= SMT-1 0) (= SMT-2 0))"
        );
        assert_eq!(
            translate(&implies(
                atom("A"),
                implies(implies(atom("B"), atom("C")), implies(atom("D"), atom("A")))
            )),
            "(or (not (= SMT-1 0)) (not (=> (= SMT-2 0) (= SMT-3 0))) (not (= SMT-4 0)) (= SMT-1 0))"
        );
    }

    #[test]
    fn exactness_rejects_uninterpreted_smtlib_symbols_at_any_predicate_depth() {
        let int = Sort::simple("SortInt");
        let variable = Variable::new("X", int);
        let application = |smt| {
            Term::application(
                symbol("bitwise", smt, vec![int, int], int),
                Vec::new(),
                vec![Term::variable(variable.clone()), integer("1")],
            )
        };
        let equality = |term| Predicate::Equals(term, integer("2"));
        let uninterpreted = application(Some(SmtType::Lib("andInt".into())));
        let hooked = application(Some(SmtType::Hook(SExpr::atom("+"))));

        assert_eq!(
            translation_exactness(&[equality(uninterpreted.clone())]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[Predicate::Not(Arc::new(Predicate::Exists(
                variable,
                Arc::new(Predicate::Or(vec![equality(uninterpreted)].into())),
            )))]),
            Exactness::Approximate
        );
        assert_eq!(translation_exactness(&[equality(hooked)]), Exactness::Exact);
    }

    #[test]
    fn exactness_rejects_quantifiers_over_uninterpreted_sorts() {
        let nat = Variable::new("N", Sort::simple("SortNat"));
        let int = Variable::new("I", Sort::simple("SortInt"));
        let body = |variable: &Variable| {
            Predicate::Equals(
                Term::variable(variable.clone()),
                Term::variable(variable.clone()),
            )
        };

        assert_eq!(
            translation_exactness(&[Predicate::Forall(nat.clone(), Arc::new(body(&nat)))]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[Predicate::Exists(nat, Arc::new(Predicate::True))]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[Predicate::Exists(
                int.clone(),
                Arc::new(Predicate::Equals(Term::variable(int), integer("1"))),
            )]),
            Exactness::Exact
        );
    }

    #[test]
    fn exactness_rejects_free_variables_of_uninterpreted_sorts() {
        let nat = Term::variable(Variable::new("N", Sort::simple("SortNat")));
        let int = Term::variable(Variable::new("I", Sort::simple("SortInt")));
        let boolean = Term::variable(Variable::new("B", Sort::simple("SortBool")));

        assert_eq!(
            translation_exactness(&[Predicate::Equals(nat.clone(), nat)]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[
                Predicate::Equals(int, integer("1")),
                Predicate::Term(boolean),
            ]),
            Exactness::Exact
        );
    }

    /// A partial operation is approximate here because no definition states its domain, which
    /// is then an opaque atom; under a ceil equation it is exact (GAP K29,
    /// `a_query_whose_partial_symbols_have_closed_domains_is_exact` in smt/z3.rs).
    #[test]
    fn exactness_rejects_abstracted_terms_predicates_and_partial_operations() {
        let int = Sort::simple("SortInt");
        let variable = Term::variable(Variable::new("X", int));
        let equality = |term| Predicate::Equals(term, integer("2"));
        let opaque = Term::application(
            symbol("opaque", None, vec![int], int),
            Vec::new(),
            vec![variable.clone()],
        );
        let mut partial_symbol = symbol(
            "division",
            Some(SmtType::Hook(SExpr::atom("div"))),
            vec![int, int],
            int,
        );
        Arc::make_mut(&mut partial_symbol).attributes.symbol_type =
            SymbolType::Function(FunctionType::Partial);
        let partial = Term::application(
            partial_symbol,
            Vec::new(),
            vec![variable.clone(), integer("1")],
        );

        assert_eq!(
            translation_exactness(&[equality(opaque)]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[equality(partial)]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[Predicate::Ceil(variable.clone())]),
            Exactness::Approximate
        );
        assert_eq!(
            translation_exactness(&[equality(variable)]),
            Exactness::Exact
        );
    }

    #[test]
    fn abstracts_symbolic_definedness_as_a_stable_boolean() {
        let variable = Term::variable(Variable::new("X", Sort::simple("SortInt")));
        let predicate = Predicate::Ceil(variable);
        let mut translation = TranslationState::new();

        assert_eq!(
            translation
                .translate_predicate(&predicate)
                .unwrap()
                .to_string(),
            "SMT-1"
        );
        assert_eq!(
            translation
                .translate_predicate(&predicate)
                .unwrap()
                .to_string(),
            "SMT-1"
        );
        assert_eq!(translation.predicate_mappings.len(), 1);
    }

    #[test]
    fn abstracts_symbolic_membership_as_a_stable_boolean() {
        // `\in{S1,S2}(P1:S1, P2:S1)`: both operands have the operand sort.
        let element = Term::variable(Variable::new("X", Sort::simple("SortElement")));
        let pattern = Term::variable(Variable::new("P", Sort::simple("SortElement")));
        let membership = Predicate::In(element, pattern);
        let negated = Predicate::Not(Arc::new(membership.clone()));
        let mut translation = TranslationState::new();

        assert_eq!(
            translation
                .translate_predicate(&membership)
                .unwrap()
                .to_string(),
            "SMT-1"
        );
        assert_eq!(
            translation
                .translate_predicate(&negated)
                .unwrap()
                .to_string(),
            "(not SMT-1)"
        );
        assert_eq!(translation.predicate_mappings.len(), 1);
    }

    /// The absence of one key from one rest is one Boolean, wherever it was stated, and
    /// another key or rest is another Boolean.
    #[test]
    fn abstracts_an_absence_as_one_boolean_per_key_and_rest() {
        use std::sync::Arc;

        use crate::rule::{Absence, KeyedCollection};
        use crate::term::{CollectionSymbols, MapDefinition};

        let map = KeyedCollection::Map(Arc::new(MapDefinition {
            symbols: CollectionSymbols {
                unit: "mapUnit".into(),
                element: "mapItem".into(),
                concat: "mapConcat".into(),
            },
            key_sort: Sort::simple("SortKey"),
            value_sort: Sort::simple("SortValue"),
            map_sort: "SortMap".into(),
        }));
        let variable =
            |name: &str, sort: &str| Term::variable(Variable::new(name, Sort::simple(sort)));
        let absence = |key: &str, rest: &str| {
            Absence::predicate(
                map.clone(),
                variable(key, "SortKey"),
                variable(rest, "SortMap"),
            )
        };
        let mut translation = TranslationState::new();
        let mut translate = |predicate: Predicate| {
            translation
                .translate_predicate(&predicate)
                .unwrap()
                .to_string()
        };

        assert_eq!(translate(absence("K", "M")), "SMT-1");
        assert_eq!(translate(absence("K", "M")), "SMT-1");
        assert_eq!(translate(absence("J", "M")), "SMT-2");
        assert_eq!(translate(absence("K", "N")), "SMT-3");
    }

    #[test]
    fn rejects_out_of_range_placeholders() {
        assert_eq!(
            fill_placeholders(&SExpr::atom("#2"), vec![SExpr::atom("one")]),
            Err(TranslationError::PlaceholderOutOfBounds {
                placeholder: 2,
                arguments: 1,
            })
        );
    }

    /// The selection as a least fixed point computed by rounds: every round adds each remaining
    /// expression that mentions a constant of the selection so far, until a round adds none.
    #[cfg(feature = "z3")]
    fn closure_by_rounds(
        interesting: &BTreeSet<&str>,
        expressions: Vec<SExpr>,
    ) -> (Vec<SExpr>, Exactness) {
        let mut constants = interesting
            .iter()
            .map(|&name| name.to_owned())
            .collect::<BTreeSet<_>>();
        let mut remaining = expressions.into_iter().collect::<BTreeSet<_>>();
        let mut selected = BTreeSet::new();
        loop {
            let added = remaining
                .iter()
                .filter(|expression| {
                    smt_variables(expression)
                        .iter()
                        .any(|&name| constants.contains(name))
                })
                .cloned()
                .collect::<Vec<_>>();
            if added.is_empty() {
                let exactness = if remaining.is_empty() {
                    Exactness::Exact
                } else {
                    Exactness::Approximate
                };
                return (selected.into_iter().collect(), exactness);
            }
            for expression in added {
                remaining.remove(&expression);
                constants.extend(
                    smt_variables(&expression)
                        .iter()
                        .map(|&name| name.to_owned()),
                );
                selected.insert(expression);
            }
        }
    }

    /// Expressions over a few SMT constants and other atoms, nested a few levels.
    #[cfg(feature = "z3")]
    fn constant_expression() -> impl proptest::strategy::Strategy<Value = SExpr> {
        use proptest::{collection::vec, prelude::*};
        let atom = prop_oneof![
            (0..6_u8).prop_map(|index| SExpr::atom(format!("SMT-{index}"))),
            prop_oneof![Just("="), Just("and"), Just("x"), Just("0")].prop_map(SExpr::atom),
        ];
        atom.prop_recursive(3, 12, 3, |inner| vec(inner, 0..4).prop_map(SExpr::List))
    }

    #[cfg(feature = "z3")]
    proptest::proptest! {
        /// The breadth-first selection is the least set closed under sharing a constant with
        /// the check or with a selected expression, which the rounds compute directly.
        #[test]
        fn breadth_first_selection_is_the_closure_by_rounds(
            expressions in proptest::collection::vec(constant_expression(), 0..8),
            interesting in proptest::collection::btree_set(0..6_u8, 0..3),
        ) {
            let interesting = interesting
                .into_iter()
                .map(|index| format!("SMT-{index}"))
                .collect::<Vec<_>>();
            let interesting = interesting.iter().map(String::as_str).collect::<BTreeSet<_>>();
            proptest::prop_assert_eq!(
                closure_over(&interesting, expressions.clone()),
                closure_by_rounds(&interesting, expressions)
            );
        }
    }

    fn hooked(name: &str, hook: &str, arguments: Vec<Sort>, result: Sort) -> Arc<Symbol> {
        symbol(
            name,
            Some(SmtType::Hook(SExpr::parse(hook).unwrap())),
            arguments,
            result,
        )
    }

    /// The text `SmtPrelude::query` would pose for `predicates` as known facts, after the
    /// definition's prelude: the mapping declarations and the assertions. And its exactness.
    fn query_text(predicates: &[Predicate]) -> (String, Exactness) {
        let (translation, declarations, _, known, _) =
            translate_query(predicates, &Substitution::new(), &[]).unwrap();
        let text = declarations
            .into_iter()
            .chain(known.iter().map(ToString::to_string))
            .collect::<Vec<_>>()
            .join("\n");
        (text, translation.exactness())
    }

    fn float() -> Sort {
        Sort::simple("SortFloat")
    }

    fn mint() -> Sort {
        Sort::application("SortMInt", vec![Sort::simple("Sort8")])
    }

    fn boolean() -> Sort {
        Sort::simple("SortBool")
    }

    fn int() -> Sort {
        Sort::simple("SortInt")
    }

    fn variable(name: &str, sort: Sort) -> Term {
        Term::variable(Variable::new(name, sort))
    }

    /// The solver interprets only `Int` and `Bool`, so an `fp.*` or `bv*` operation applied to
    /// constants of the uninterpreted `Float` or `MInt` sort is no SMT-LIB term, and `fg.gt` is
    /// no SMT-LIB function at all. Each such application is an opaque value of its own sort, and
    /// the translation is `Approximate`: the script names none of these operators.
    #[test]
    fn float_and_mint_hook_applications_are_opaque_values_of_their_sort() {
        let f = || variable("F", float());
        let g = || variable("G", float());
        let a = || variable("A", mint());
        let b = || variable("B", mint());
        let applications = [
            (
                hooked("isNaN", "fp.isNaN", vec![float()], boolean()),
                vec![f()],
            ),
            (
                hooked("gtFloat", "fg.gt", vec![float(), float()], boolean()),
                vec![f(), g()],
            ),
            (
                hooked("negFloat", "fp.neg", vec![float()], float()),
                vec![f()],
            ),
            (
                hooked(
                    "mulFloat",
                    "(fp.mul roundNearestTiesToEven #1 #2)",
                    vec![float(), float()],
                    float(),
                ),
                vec![f(), g()],
            ),
            (
                hooked("addMInt", "bvadd", vec![mint(), mint()], mint()),
                vec![a(), b()],
            ),
            (
                hooked("ultMInt", "bvult", vec![mint(), mint()], boolean()),
                vec![a(), b()],
            ),
            (
                hooked(
                    "neFloat",
                    "(not (fp.eq #1 #2))",
                    vec![float(), float()],
                    boolean(),
                ),
                vec![f(), g()],
            ),
        ];
        for (symbol, arguments) in applications {
            let application = Term::application(symbol, Vec::new(), arguments);
            let mut translation = TranslationState::new();
            assert_eq!(
                translation.translate_term(&application).unwrap(),
                SExpr::atom("SMT-1"),
                "{application:?}"
            );
            assert_eq!(translation.exactness(), Exactness::Approximate);
            let predicate = if application.sort() == boolean() {
                Predicate::Term(application.clone())
            } else {
                Predicate::Equals(application.clone(), variable("H", application.sort()))
            };
            let (text, exactness) = query_text(&[predicate]);
            assert!(
                !["fp.", "fg.", "bv", "roundNearest"]
                    .iter()
                    .any(|operator| text.contains(operator)),
                "{text}"
            );
            assert_eq!(exactness, Exactness::Approximate, "{text}");
        }
    }

    /// `MInt2Unsigned(Int2MInt(X)) <Int 0` has `Int` leaves and total symbols, but its
    /// intermediate value is a machine integer, which the solver does not interpret: the
    /// `MInt2Unsigned` application is an `Int` constant, and the translation is `Approximate`,
    /// so a `Sat` for it shows no K valuation. Comparing two machine integers with `=` is a
    /// well-sorted equation of two constants of the uninterpreted sort.
    #[test]
    fn an_int_over_an_uninterpreted_intermediate_value_is_not_exact() {
        let int2mint = |argument| {
            Term::application(
                hooked("Int2MInt", "int2bv", vec![int()], mint()),
                Vec::new(),
                vec![argument],
            )
        };
        let unsigned = Term::application(
            hooked("MInt2Unsigned", "bv2int", vec![mint()], int()),
            Vec::new(),
            vec![int2mint(variable("X", int()))],
        );
        let negative = Predicate::Term(Term::application(
            hooked("ltInt", "<", vec![int(), int()], boolean()),
            Vec::new(),
            vec![unsigned, integer("0")],
        ));
        let (text, exactness) = query_text(std::slice::from_ref(&negative));
        assert_eq!(exactness, Exactness::Approximate);
        assert_eq!(translation_exactness(&[negative]), Exactness::Approximate);
        assert!(text.contains("(declare-const SMT-1 Int)"), "{text}");
        assert!(text.contains("(< SMT-1 0)"), "{text}");
        assert!(!text.contains("bv"), "{text}");

        let equal = Predicate::Term(Term::application(
            hooked("eqMInt", "=", vec![mint(), mint()], boolean()),
            Vec::new(),
            vec![
                int2mint(variable("X", int())),
                int2mint(variable("Y", int())),
            ],
        ));
        let (text, exactness) = query_text(&[equal]);
        assert_eq!(exactness, Exactness::Approximate);
        assert!(text.contains("(= SMT-1 SMT-2)"), "{text}");
        assert!(
            text.contains("(declare-const SMT-1 (|SortMInt| |Sort8|))"),
            "{text}"
        );
        assert!(!text.contains("bv"), "{text}");
    }

    /// `=`, `distinct` and `ite` are defined at every sort, so they are stated over operands of
    /// an uninterpreted sort, as long as the operands have one sort (and `ite` a `Bool`
    /// condition); an application outside their rank is an opaque value as any other.
    #[test]
    fn core_polymorphic_hooks_apply_over_operands_of_one_sort() {
        let f = || variable("F", float());
        let g = || variable("G", float());
        let condition = || variable("C", boolean());
        let translated = |symbol, arguments| {
            let application = Term::application(symbol, Vec::new(), arguments);
            TranslationState::new()
                .translate_term(&application)
                .unwrap()
                .to_string()
        };
        assert_eq!(
            translated(
                hooked("ite", "ite", vec![boolean(), float(), float()], float()),
                vec![condition(), f(), g()],
            ),
            "(ite SMT-1 SMT-2 SMT-3)"
        );
        assert_eq!(
            translated(
                hooked("eqFloatK", "=", vec![float(), float()], boolean()),
                vec![f(), g()],
            ),
            "(= SMT-1 SMT-2)"
        );
        assert_eq!(
            translated(
                hooked("neFloatK", "distinct", vec![float(), float()], boolean()),
                vec![f(), g()],
            ),
            "(distinct SMT-1 SMT-2)"
        );
        assert_eq!(
            translated(
                hooked("mixed", "=", vec![float(), int()], boolean()),
                vec![f(), variable("X", int())],
            ),
            "SMT-1"
        );
        assert_eq!(
            translated(
                hooked("iteOverFloat", "ite", vec![float(), int(), int()], int()),
                vec![f(), variable("X", int()), variable("Y", int())],
            ),
            "SMT-1"
        );
    }

    /// A sort hooked `INT.Int` under another name has integer values, but the solver reads a
    /// sort by its name, and declares `SortMyInt` as an uninterpreted sort, over which `+` and
    /// `>` are not defined. Its hooked operations are opaque values, never `+` over constants of
    /// `|SortMyInt|`.
    #[test]
    fn int_hooks_over_a_renamed_int_sort_are_opaque_values() {
        let my_int = Sort::simple("SortMyInt");
        let sum = Term::application(
            hooked("addMyInt", "+", vec![my_int, my_int], my_int),
            Vec::new(),
            vec![variable("M", my_int), variable("N", my_int)],
        );
        let greater = Predicate::Term(Term::application(
            hooked("gtMyInt", ">", vec![my_int, my_int], boolean()),
            Vec::new(),
            vec![sum, variable("M", my_int)],
        ));
        let mut translation = TranslationState::new();
        assert_eq!(
            translation.translate_predicate(&greater).unwrap(),
            SExpr::atom("SMT-1")
        );
        let (text, exactness) = query_text(&[greater]);
        assert_eq!(exactness, Exactness::Approximate);
        assert!(!text.contains("(+") && !text.contains("(>"), "{text}");
    }

    /// An `Int` hook over `Int` and `Bool` operands is still stated as its operation, exactly.
    #[test]
    fn int_hooks_over_int_operands_are_still_their_operation() {
        let sum = Term::application(
            hooked("addInt", "+", vec![int(), int()], int()),
            Vec::new(),
            vec![variable("X", int()), integer("1")],
        );
        let greater = Predicate::Term(Term::application(
            hooked("gtInt", ">", vec![int(), int()], boolean()),
            Vec::new(),
            vec![sum, variable("X", int())],
        ));
        let (text, exactness) = query_text(&[greater]);
        assert_eq!(exactness, Exactness::Exact);
        assert!(text.contains("(> (+ SMT-1 1) SMT-1)"), "{text}");
    }
}
