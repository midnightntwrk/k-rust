//! Data terms: ground terms whose meaning in a definition is fixed by its constructors and by
//! the normal forms of its equations alone, so that two different data terms denote different
//! values of the definition. A client comparing ends of two definitions (a differential test) compares only
//! terms that are data in both, each judged by its own definition.
//!
//! # The class
//!
//! A definition *has data* when its full critical-pair check
//! ([`CheckScope::All`](crate::confluence::CheckScope::All), which classifies every pair of
//! executable equations) reports nothing: every pair joins or is refuted, no
//! equation is one the evaluator does not apply to every subject it describes, and no
//! precondition row is violated (no equation rooted at a free constructor, an injection, a
//! collection or a bare variable; every overload equation of the canonical shape below; a unique
//! least common overload for any two members of a family). A definition whose check reports
//! something has no data: its findings ([`DataHeads::findings`]) say why. In a definition that
//! has data, a ground term is *data* when it is built only from
//!
//! - domain values, sort injections and free-constructor applications ([`HeadRole::FreeConstructor`]);
//! - map, list and set terms without an opaque rest, whose keys, values or elements are data and
//!   whose map keys and set elements are pairwise distinct;
//! - applications of a *data head* ([`DataHeads`]) that are instance-normal
//!   (`BackendDefinition::instance_normal`: no equation offered the application, from the
//!   definition's own equations, with its own subsort order, can apply to any instance of it),
//!   whose arguments are data.
//!
//! A data head `g` is a symbol that meets all of the following:
//!
//! - **H1, an equation head.** `g` is `anywhere` and not a declared function
//!   ([`HeadRole::EquationHead`]): on the KORE, `anywhere` with no `function` attribute, or with
//!   `function` beside `value-production`, which k-rust's compiler adds together to a non-function
//!   production that has `anywhere` rules (a source `[function]` production never gets
//!   `value-production`). An `assoc`, `comm` or `idem` symbol is uninterpreted and a macro is
//!   residual, so neither is an equation head. A declared partial function that no equation
//!   rewrites is `\bottom` in `M_NF` (compat, "Anywhere rules"), so a stuck application of one
//!   never denotes a value.
//! - **H2, its irreducible applications are elements.** `g` is declared total (its symbol type is
//!   not partial: `functional`, `total` or `constructor`), or it is a `value-production`, which
//!   states that an application no equation reduces is a value of its sort. Without either, an
//!   irreducible application is a normal form of `M_NF` whose `\ceil` nothing discharges, so it
//!   need not denote an element of another model, and it is not data. This drops the overload
//!   heads of hand-written KORE declared with neither (k-rust's compiler always declares one): a
//!   deliberate tightening, since every data term must exist (below).
//! - **H3, hygiene.** `g` has no hook; no `simplification` lemma and no ceil equation is offered at
//!   its index (a ceil lemma would state the existence of its applications, which the walk honours
//!   before `value-production`, so a head with one is never data whatever the lemma says); the
//!   load-time critical-pair check admits its index (`ValueClaims::admit`); and it roots at least
//!   one equation, every equation rooted at it is executable, and every one that carries an
//!   `overload` attribute is a *canonical* overload equation of `g`:
//!   `g(p1, ..., pn) = inj{R,T}(h(x1, ..., xn))` (or `h(x1, ..., xn)`) with each `pi` the
//!   variable `xi` or `inj{Si,Ti}(xi)`, the variables distinct, `h` its overload partner
//!   (`RuleAttributes::overload`), and no `requires` or `ensures`. A K-placed overload (an overload
//!   equation of another shape) is never data, whatever is assumed of its precondition row. A
//!   plain `anywhere` equation may have any shape: conditional, `owise` or prioritized (SIMPLE's
//!   `_[_]`, whose equations `V:Val[N1, N2, Vs] => V[N1][N2, Vs]` and
//!   `array(L, _)[N:Int] => lookup(L +Int N)` are plain).
//!
//! Why an instance-normal application of a data head over data is a normal form in every context:
//! an `anywhere` equation reads only the term it matches (a non-function head never receives the
//! configuration), and the instance-normality scan ignores `requires` and priorities, so an
//! instance that no equation of `g` (or rooted at a bare variable) can match is rewritten in no
//! context, wherever it is stored (an `a[4]` kept inside a stored function body) and whatever
//! later surrounds it. A transition rule rooted at `g` changes states, not values. An equation
//! rooted at another symbol `h` that mentions `g` below its root applies only at an `h` node,
//! which is a free constructor, an injection or a collection (then a precondition row, so no
//! data at all), a function (not data), or another data head (scanned at its own node); its
//! overlap with `g`'s equations is a pair of the full check. An `owise` equation counts as
//! applying wherever its left-hand side matches, so a head with `g(X) => ... [owise]` has no data
//! application; an equation whose left-hand side matches but whose `requires` is false still
//! withholds data. Both lose precision only.
//!
//! Data implies existence: with H2 and instance normality, `\ceil(g(t1, ..., tn))` is
//! `\ceil(t1) /\ ... /\ \ceil(tn)` (`definedness::ceil_term` owes nothing at a total head, and
//! discharges an irreducible `value-production` application,
//! `BackendDefinition::irreducible_application_is_defined`; H3 leaves no ceil equation to come
//! first), so a data term whose maps and sets have keys k-rust shows apart is
//! [`BackendDefinition::ground_defined`]. k-rust's apartness test does not separate two
//! applications of an equation head, even of one shape (`a[4]` and `a[5]`): two distinct data keys
//! holding one may be equal in another model, which interprets the head freely outside its
//! equations' instances. So a map or set keyed by two such keys is data and not `ground_defined`,
//! and the existence of data holds in `M+` (where distinct data keys are distinct normal forms),
//! which is the model the argument below reads.
//!
//! # What a data term denotes, and why two of them differ
//!
//! A term denotes a value of the initial model of the definition: two ground terms denote one
//! value exactly when every model of the definition equates them. Differing in *every* model is
//! not attainable for an overload application, since outside the instances of its equations a
//! model may interpret an equation head as it likes.
//!
//! The backend reads a definition in the model `M+` (`docs/compatibility.md`, "Anywhere rules";
//! `confluence.rs`): each sort is interpreted by the normal forms of innermost evaluation by the
//! executable equations and the full check's witness equations over the signature with one fresh
//! constant in each sort that is not surely inhabited, and each symbol by normalizing its
//! application, so every carrier is nonempty, as in every model. On the terms free of the
//! constants it is the normal-form model `M_NF` of evaluation. `M+` is a model of the definition
//! when that evaluation terminates and the critical pairs of the executable and witness equations
//! join. The argument assumes:
//!
//! - **A1 (termination).** Evaluation terminates, as every evaluation assumes.
//! - **A1+ (termination with witnesses).** Innermost evaluation by the executable equations and
//!   the full check's witness equations ([`ValueClaims::witnesses`](crate::confluence::ValueClaims::witnesses))
//!   terminates over the signature with one fresh constant in each sort that is not surely
//!   inhabited (the model `M+`, `confluence.rs`). A new premise, not checked: it is derived
//!   neither from A1, which is about ground terms of the signature, nor from termination on open
//!   terms (`k(inj{E,T}(X)) => k(f(X))` with the witness `f(X:E) => inj X` loops on `k(inj *)`).
//!   It implies A1, since no witness applies to a term free of the constants.
//! - **A2 (lemmas).** The axioms no check pairs, `simplification` lemmas and `[symbolic]`
//!   function equations, are theorems of the executable equations, as every use of them assumes
//!   (compat, "Anywhere rules"), and the declarations the check reads as true hold (the verdict
//!   contract of `CheckScope::All`). Its reach grows with the data heads: a predicate lemma that
//!   mentions a data head below its root (an `#Equals` between applications of `g`, say) is
//!   neither an equation the instance-normality scan reads nor one the check pairs, so only A2
//!   keeps it from identifying two data terms, as for overload heads before.
//!
//! A local check cannot replace the global one. An identification anywhere reaches other terms
//! through congruence: if two terms are equal, every equation that tells them apart equates its
//! results. Two equations `p(_:Id, _:Ids) => a` and `p(_:Exp, _:Exps) => bb`, overlapping only
//! modulo an overload axiom, equate `a` with `bb`, and a broken overload family's
//! `inj{Ids,Exps}(.Ids) = .Exps = inj{Vals,Exps}(.Vals)` reaches `a` and `bb` through
//! `pick(.Ids) => a` and `pick(.Vals) => bb`. KORE has no axiom keeping injections from different
//! source sorts apart, so such a theory stays consistent and equates terms that are syntactically
//! different and free of every symbol involved. Hence the whole definition must be shown
//! confluent.
//!
//! When the full check reports nothing, then under A1+ and A2 `M+` is a model of the executable
//! and witness equations, so of the definition (`M_NF` is the part of `M+` free of the
//! constants). Every data term is free of the constants and a normal form: no executable equation
//! is rooted at a free constructor, an injection or a collection (no precondition row), an
//! instance-normal application of a data head over normal forms is one (no equation applies at
//! its root in any context, "The class"), and no witness applies to a term free of the
//! constants. Distinct normal forms are distinct elements of `M+`, so two
//! different data terms are kept apart by a model, and they differ in the initial model.
//! (Syntactic difference is read on k-rust's internal normal form, below.)
//!
//! # Two definitions
//!
//! A differential test asks whether the mutant's end `tm` is none of the baseline's ends `tb`.
//! Each definition reads the ends with its own theory, and the two theories may differ on any
//! symbol: a constructor free in one may be an overload head of the other (a mutant that adds
//! `Bot ::= f(Bot) [overload(f)]` lowers the baseline's normal form `f_Nm(inj(b))` to
//! `inj(f_Bot(b))`), an `anywhere` rule may be added (`c(1) => d`, or `X:Id[N] => ...` beside
//! SIMPLE's `_[_]`), a subsort may be added below an argument sort of a data head's equation
//! (`Id < Val`, which lets SIMPLE's `_[_]` equations reach `a[4]`), parametric instances such as
//! `MInt{8}` included. So the comparison
//! is sound when every term compared is data in *both* definitions, each judged by
//! [`BackendDefinition::is_data`] with that definition's own [`DataHeads`] (its own full check,
//! equations and overload families, its own full subsort order through its matcher), so each of
//! the two definitions must have data. Then, by the argument
//! above under A1+ and A2 for each definition, two different such terms denote different values of
//! each definition's initial model, so `tm` differs from every `tb` whichever theory reads them.
//! Syntactic difference is read on k-rust's internal normal form, whose injections are taken
//! from the term's own sort (nested injections compose), which does not depend on the
//! definition. A term that does not internalize in a definition (a symbol it lacks) is not data
//! there.
//!
//! # Findings: genuine or undecided
//!
//! A finding of the full check ([`Finding`]) is *genuine* only when it comes with a
//! [`GroundInstance`] (`instance.rs`): a ground input with two different results. The instance
//! is built from normal forms (its maps and sets keyed by distinct ones), both equations apply
//! there by the evaluator's own rule (each matches its redex, its `requires` evaluates to true,
//! and no equation of its head with a higher priority applies, an undecided one counting as
//! applying), and the two reducts evaluate either to two different normal forms, read on
//! k-rust's internal normal form as everywhere in this module, or to a normal form and an
//! undefined value. A normal form there may hold an application of a declared total function
//! without a hook or an algebraic axiom that no equation or lemma at its index matches (also
//! the `symbolic`, `simplification` and `non-executable` ones); an undefined value holds,
//! under free constructors, injections and collection items only, such an application of a
//! declared partial function without a hook, which is `\bottom` in `M_NF`
//! ([`GroundInstance::stuck`]; `instance.rs`, "Stuck applications"). No term is both a normal
//! form and `\bottom`, so evaluation of that input is not uniquely determined: `M_NF` is not a
//! model of the definition, and k-rust's result for the input depends on the order in which it
//! tries the equations (the evaluator returns a stuck partial application as it stands, which
//! still differs from the other result). Two undefined values are no instance. This is not a
//! claim that no model satisfies the definition (no KORE axiom keeps, for instance, injections
//! from different source sorts apart, and a model may give a partial function a value where no
//! equation does). Every other finding is *undecided*: not shown to join, which may be a limit of
//! the checker (a condition its solver-free reader does not decide, a shape its unifier does not
//! solve) as well as a defect of the definition.
//!
//! # Assumed pairs
//!
//! A client may name findings the definition is to be read without
//! ([`BackendDefinition::data_heads_assuming`]): a pair as joining, an equation at an evaluated
//! hook as agreeing with the hook, another per-equation report as applying as written, an
//! overload precondition row (`OverloadShape`, `NoLeastCommonOverload`, `PinnedByInjectiveTotal`)
//! as met. The data judgement is then about that reading of the definition, not about the
//! definition as written: a premise the client states wherever the judgement is reported. Which
//! inputs reach the finding does not enter: the judgement reads the definition by `M_NF`, which a
//! genuine pair makes no model whatever the inputs.
//!
//! A decided finding ([`Finding::is_decided`]) cannot be assumed: an equation headed by a
//! constructor or an injection rewrites, and one indexed at a collection or a bare variable
//! equates with its right-hand side (as an axiom the evaluator never applies, or at every
//! subject), terms that [`BackendDefinition::is_data`] reads as free without consulting the load
//! verdict, so they are not distinct normal forms, and no premise that keeps the equation an
//! axiom makes them so; and an
//! equation whose right-hand side leaves a variable unbound by its left-hand side equates, read
//! as written, its left-hand side with every value of that variable's sort, which the evaluator
//! never applies, so there is no reading of it as written to assume.
//!
//! Every finding that can be assumed bears on data only through the load verdict
//! (`ValueClaims`), which still withholds what it taints. The data heads and the
//! instance-normal scan read that verdict, which withdraws the claims an assumed pair's or hook
//! equation's taint closure reaches; an overload head whose overload equations are not canonical
//! is never a data head, whatever is assumed of an overload row; and the heads a
//! pinned injective symbol pins keep their withheld claims. Free-constructor applications,
//! injections, domain values and collections do not depend on any assumable finding. So an
//! assumed finding can only make fewer terms data than the definition read as if it were
//! resolved. This reaches the plain `anywhere` heads as it reaches overload heads: a pair of one
//! head's own equations with different results at an overlap (`g(X) => a` beside `g(c) => b`)
//! assumed joined leaves `g` withdrawn by the load, so no application of it becomes data under
//! the premise.
//!
//! # Names
//!
//! Every finding has a name ([`names::finding_name`]), and a client assumes findings by name
//! ([`names::names_finding`]): the one renderer every client prints and reads, so a name one
//! client prints (k-rust-fuzz's `definition-findings`) is a name another reads (kink's
//! `[spec] assume_joined`).

mod instance;
pub mod names;

use std::collections::BTreeSet;

pub use instance::{GroundInstance, Stuck};

use crate::{
    confluence::{UnjoinedPair, Violation},
    definition::BackendDefinition,
    rule::{RuleRhs, TermIndex, applicable_groups},
    term::{FunctionType, HeadRole, Name, SymbolType, Term, TermKind},
};

/// The data heads of one definition and the findings of its full critical-pair check
/// (the [module documentation](self), "The class"), built by [`BackendDefinition::data_heads`]
/// and read only by [`BackendDefinition::is_data`] of the same definition.
#[derive(Clone, Debug, Default)]
pub struct DataHeads {
    heads: BTreeSet<Name>,
    /// Why the definition's equations are not shown confluent: one finding per pair of
    /// executable equations the full check does not join, per equation the evaluator does not
    /// apply to every subject it describes, and per precondition row the definition violates.
    /// When there is one, no term is data.
    findings: Vec<Finding>,
    /// The pair findings the client assumed joined ([`BackendDefinition::data_heads_assuming`]).
    assumed: Vec<Finding>,
    /// What the full check counted ([`crate::confluence::ValueClaims::counts`]), for a client
    /// that guards the check's completeness.
    counts: crate::confluence::CheckCounts,
    /// The witness equations the full check adopted
    /// ([`crate::confluence::ValueClaims::witnesses`]), for a client that compares two
    /// definitions' verdicts.
    witnesses: Vec<std::sync::Arc<crate::rule::RewriteRule>>,
}

/// One finding of a definition's full critical-pair check (the [module documentation](self),
/// "Findings: genuine or undecided").
#[derive(Clone, Debug)]
pub enum Finding {
    /// A violated precondition row: an equation outside the check's reasoning, or an overload
    /// family the argument does not cover.
    Precondition(Violation),
    /// An equation the evaluator does not apply to every subject it describes
    /// ([`UnjoinedReason::describes_one_equation`](crate::confluence::UnjoinedReason::describes_one_equation)),
    /// or an equation at an evaluated hook not shown to agree with the hook's written meaning
    /// (a hook pair, [`UnjoinedPair::hook`](crate::confluence::UnjoinedPair::hook)).
    Equation(UnjoinedPair),
    /// A pair of executable equations the check does not join, with a ground input that has two
    /// different results when one was found (a genuine finding); otherwise undecided.
    Pair {
        pair: UnjoinedPair,
        instance: Option<GroundInstance>,
    },
}

impl Finding {
    /// Whether the finding is genuine: a pair with a [`GroundInstance`].
    #[must_use]
    pub fn is_genuine(&self) -> bool {
        matches!(
            self,
            Self::Pair {
                instance: Some(_),
                ..
            }
        )
    }

    /// Whether the finding is a fact the check decides about the definition as written, which no
    /// assumption about it removes, so [`BackendDefinition::data_heads_assuming`] never moves
    /// it:
    /// - a precondition row about an executable equation's left-hand side: headed by a
    ///   constructor or an injection (it rewrites terms the data judgement reads as free), or
    ///   indexed at a collection or a bare variable (its axiom equates the collection terms it
    ///   describes with its right-hand side, or it is offered at every subject), so those terms
    ///   are not distinct normal forms. A `PinnedByInjectiveTotal` row, which names no equation,
    ///   is not decided;
    /// - an equation whose right-hand side or `ensures` has variables its left-hand side does
    ///   not bind
    ///   ([`UnjoinedReason::UnboundResultVariables`](crate::confluence::UnjoinedReason::UnboundResultVariables)).
    ///   Read as written, the axiom equates its left-hand side with every value of the unbound
    ///   variable's sort, and the evaluator never applies it, so "applied as written" is no
    ///   premise about it.
    #[must_use]
    pub fn is_decided(&self) -> bool {
        match self {
            // Only the rows about an executable equation's own left-hand side; a pinned
            // injective symbol (`PinnedByInjectiveTotal`), which also withdraws claims, names no
            // equation and is assumable.
            Self::Precondition(violation) => matches!(
                violation.kind,
                crate::confluence::ViolationKind::ConstructorHeaded(_)
                    | crate::confluence::ViolationKind::InjectionHeaded
                    | crate::confluence::ViolationKind::IndexedAt(_)
            ),
            Self::Equation(pair) => matches!(
                pair.reason,
                crate::confluence::UnjoinedReason::UnboundResultVariables
            ),
            Self::Pair { .. } => false,
        }
    }

    /// The pair, for a pair finding.
    #[must_use]
    pub fn pair(&self) -> Option<&UnjoinedPair> {
        match self {
            Self::Pair { pair, .. } => Some(pair),
            Self::Precondition(_) | Self::Equation(_) => None,
        }
    }

    /// The ground instance of a genuine finding.
    #[must_use]
    pub fn instance(&self) -> Option<&GroundInstance> {
        match self {
            Self::Pair { instance, .. } => instance.as_ref(),
            Self::Precondition(_) | Self::Equation(_) => None,
        }
    }

    /// One line naming the finding, each equation named by its diagnostic name with symbols
    /// written by `symbol` from their KORE names
    /// ([`RuleAttributes::diagnostic_name`](crate::rule::RuleAttributes::diagnostic_name)).
    /// A pair is "not shown to join", never a defect: only [`Self::is_genuine`] says that.
    pub fn describe(&self, symbol: impl Fn(&str) -> String + Copy) -> String {
        let name = |rule: &crate::rule::RewriteRule| rule.attributes.diagnostic_name(symbol);
        match self {
            Self::Precondition(violation) => match &violation.rule {
                Some(rule) => format!("{} ({})", violation.kind, name(rule)),
                None => violation.kind.to_string(),
            },
            Self::Equation(pair) => match &pair.hook {
                Some(hook) => format!(
                    "the equation {} is not shown to agree with its hook {hook} ({})",
                    name(&pair.first),
                    pair.reason
                ),
                None => format!(
                    "the equation {} is not applied to every subject it describes ({})",
                    name(&pair.first),
                    pair.reason
                ),
            },
            Self::Pair { pair, .. } => format!(
                "the equations {} and {} are not shown to join ({})",
                name(&pair.first),
                name(&pair.second),
                pair.reason
            ),
        }
    }
}

impl std::fmt::Display for Finding {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.describe(str::to_owned))
    }
}

impl DataHeads {
    /// The heads' symbol names, sorted.
    pub fn names(&self) -> impl Iterator<Item = &Name> {
        self.heads.iter()
    }

    /// Whether `name` is one of the heads.
    #[must_use]
    pub fn contains(&self, name: &Name) -> bool {
        self.heads.contains(name)
    }

    /// Whether there is no head.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.heads.is_empty()
    }

    /// Whether the full critical-pair check shows the definition's equations confluent: no
    /// finding. Otherwise no term is data.
    #[must_use]
    pub fn confluent(&self) -> bool {
        self.findings.is_empty()
    }

    /// Why the definition's equations are not shown confluent (empty when they are), the
    /// assumed pairs left out.
    #[must_use]
    pub fn findings(&self) -> &[Finding] {
        &self.findings
    }

    /// The findings assumed resolved ([`BackendDefinition::data_heads_assuming`]).
    #[must_use]
    pub fn assumed(&self) -> &[Finding] {
        &self.assumed
    }

    /// What the full critical-pair check counted on the whole definition (its
    /// [`CheckCounts`](crate::confluence::CheckCounts)): a client reading the findings as a
    /// report of every pair can check that the check read every executable equation and skipped
    /// no candidate pair.
    #[must_use]
    pub const fn check_counts(&self) -> crate::confluence::CheckCounts {
        self.counts
    }

    /// The witness equations the full critical-pair check adopted
    /// ([`ValueClaims::witnesses`](crate::confluence::ValueClaims::witnesses); empty when it
    /// kept its first pass, [`CheckCounts::witness_pass`](crate::confluence::CheckCounts::witness_pass)):
    /// the findings are those of the check on the executable equations and these. A client
    /// comparing two definitions' checks compares these too.
    #[must_use]
    pub fn witnesses(&self) -> &[std::sync::Arc<crate::rule::RewriteRule>] {
        &self.witnesses
    }
}

impl BackendDefinition {
    /// The data heads of this definition and the findings of its full critical-pair
    /// check (the [module documentation](self), "The class"). The check runs in
    /// [`CheckScope::All`](crate::confluence::CheckScope::All), which classifies every pair of
    /// executable equations, not only those that can change a value claim; it costs about as
    /// much as the definition's load (0.03 s on SIMPLE, 0.2 s on WASM), so a client computes
    /// this once per definition. A head meets H1-H3 of the module documentation: an `anywhere`
    /// production that is not a declared function, declared total or a `value-production`,
    /// with no hook, no lemma or ceil equation at its index, an index the load admits, and at
    /// least one equation rooted at it, all executable, the overload ones canonical; when the
    /// check has a finding there is no head.
    ///
    /// Each pair finding is searched for a [`GroundInstance`] (the [module
    /// documentation](self), "Findings: genuine or undecided"), a bounded search whose cost is
    /// a few evaluations of small ground terms per pair.
    #[must_use]
    pub fn data_heads(&self) -> DataHeads {
        let verdict = self.value_claims_in_scope(crate::confluence::CheckScope::All);
        let counts = verdict.counts();
        let witnesses = verdict.witnesses().to_vec();
        let findings = confluence_findings(self, &verdict);
        if !findings.is_empty() {
            return DataHeads {
                heads: BTreeSet::new(),
                findings,
                assumed: Vec::new(),
                counts,
                witnesses,
            };
        }
        DataHeads {
            heads: self.data_head_names(),
            findings,
            assumed: Vec::new(),
            counts,
            witnesses,
        }
    }

    /// `heads` (from [`Self::data_heads`] of this definition), with every finding for which
    /// `assumed` holds read as resolved (the [module documentation](self), "Assumed pairs"): a
    /// pair as joining, an equation as agreeing with its hook or applied to every subject it
    /// describes, a precondition row as met. Such findings move to [`DataHeads::assumed`], and
    /// when no other finding is left the definition has data, with its data heads. A
    /// decided finding ([`Finding::is_decided`]) is never moved, whatever `assumed` says.
    #[must_use]
    pub fn data_heads_assuming(
        &self,
        heads: &DataHeads,
        mut assumed: impl FnMut(&Finding) -> bool,
    ) -> DataHeads {
        let mut kept = Vec::new();
        let mut moved = heads.assumed.clone();
        for finding in &heads.findings {
            if !finding.is_decided() && assumed(finding) {
                moved.push(finding.clone());
            } else {
                kept.push(finding.clone());
            }
        }
        let names = if kept.is_empty() {
            self.data_head_names()
        } else {
            BTreeSet::new()
        };
        DataHeads {
            heads: names,
            findings: kept,
            assumed: moved,
            counts: heads.counts,
            witnesses: heads.witnesses.clone(),
        }
    }

    /// The data heads (the [module documentation](self), "The class": H1-H3), read without
    /// regard to the full check's findings.
    fn data_head_names(&self) -> BTreeSet<Name> {
        let mut heads = BTreeSet::new();
        for (name, symbol) in self.symbols() {
            let attributes = &symbol.attributes;
            // H1, and no hook (H3).
            if attributes.head_role() != HeadRole::EquationHead || attributes.hook.is_some() {
                continue;
            }
            // H2: an irreducible application is an element.
            if attributes.symbol_type == SymbolType::Function(FunctionType::Partial)
                && !self.is_value_production(name)
            {
                continue;
            }
            // H3: no lemma or ceil equation is offered at the index (the ceil equations as the
            // definedness walk offers them, a bare-variable one included), and the load admits it.
            let index = TermIndex::Symbol(name.clone());
            if self.simplification_theory().contains_key(&index)
                || !applicable_groups(self.ceil_theory(), &index).is_empty()
                || self.value_claims().admit(&index).is_none()
            {
                continue;
            }
            let Some(groups) = self.function_theory().get(&index) else {
                continue;
            };
            let mut rules = groups.values().flatten().peekable();
            let hygienic = rules.peek().is_some()
                && rules.all(|rule| {
                    rule.attributes.executable
                        && (rule.attributes.overload.is_none()
                            || canonical_overload_equation(name, rule))
                });
            if hygienic {
                heads.insert(name.clone());
            }
        }
        heads
    }

    /// Whether the ground term `term` is data in this definition (the
    /// [module documentation](self)), with the applications of the heads in `heads` admitted
    /// where they are instance-normal. `heads` must come from [`Self::data_heads`] of this
    /// definition. Ends compared across two definitions must be data in both, each judged by its
    /// own definition ("Two definitions").
    #[must_use]
    pub fn is_data(&self, term: &Term, heads: &DataHeads) -> bool {
        crate::instance_normal::with_scan_memo(|| self.is_data_walk(term, heads))
    }

    fn is_data_walk(&self, term: &Term, heads: &DataHeads) -> bool {
        if !heads.confluent() {
            return false;
        }
        self.built_from_data(term, &heads.heads)
    }

    /// Whether `term` is built only from domain values, injections, free-constructor
    /// applications, rest-free collections with distinct keys and elements, and instance-normal
    /// applications of the symbols in `heads`, whatever the full check says.
    fn built_from_data(&self, term: &Term, heads: &BTreeSet<Name>) -> bool {
        let mut pending = vec![term];
        // Invariant: every term popped is a subterm of `term`, and each subterm is pushed once by
        // its parent, so the loop visits at most the nodes of `term`.
        while let Some(term) = pending.pop() {
            if term.attributes().constructor_like {
                continue;
            }
            match term.kind() {
                TermKind::DomainValue { .. } => {}
                TermKind::Injection { term, .. } => pending.push(term),
                TermKind::Application {
                    symbol, arguments, ..
                } => match symbol.attributes.head_role() {
                    HeadRole::FreeConstructor => pending.extend(arguments),
                    HeadRole::EquationHead
                        if heads.contains(&symbol.name) && self.instance_normal(term).is_some() =>
                    {
                        pending.extend(arguments);
                    }
                    HeadRole::EquationHead
                    | HeadRole::Function { .. }
                    | HeadRole::Uninterpreted
                    | HeadRole::Residual => return false,
                },
                TermKind::Map { entries, rest, .. } => {
                    if rest.is_some() {
                        return false;
                    }
                    let mut previous: Option<&Term> = None;
                    for (key, value) in entries {
                        // Entries are sorted by key, so a key bound twice follows its first binding.
                        if previous == Some(key) {
                            return false;
                        }
                        previous = Some(key);
                        pending.push(key);
                        pending.push(value);
                    }
                }
                TermKind::List {
                    heads: items, rest, ..
                } => {
                    if rest.is_some() {
                        return false;
                    }
                    pending.extend(items);
                }
                TermKind::Set { elements, rest, .. } => {
                    if rest.is_some() {
                        return false;
                    }
                    let mut previous: Option<&Term> = None;
                    for element in elements {
                        if previous == Some(element) {
                            return false;
                        }
                        previous = Some(element);
                        pending.push(element);
                    }
                }
                TermKind::Variable(_) | TermKind::And(..) => return false,
            }
        }
        true
    }
}

/// Whether `rule`, an overload equation rooted at `head`, has the shape the overload axioms of
/// a K `overload` family have and the argument of the [module documentation](self) covers:
/// `head(p1, ..., pn) = inj{R,T}(lesser(x1, ..., xn))` or `= lesser(x1, ..., xn)`, where each
/// `pi` is the variable `xi` or an injection `inj{Si,Ti}(xi)` of it, the variables pairwise
/// distinct, `lesser` the equation's overload partner, and no `requires` or `ensures`. Whether
/// such an equation applies reads only each argument's injection source sort and the subsort
/// order. Any other shape (an overload placed across `K`, whose argument is `kseq(inj(X),
/// dotk)`, which the load reports as a precondition violation) is not covered.
fn canonical_overload_equation(head: &Name, rule: &crate::rule::RewriteRule) -> bool {
    let Some((_, lesser)) = &rule.attributes.overload else {
        return false;
    };
    if !rule.requires.is_empty() || !rule.ensures.is_empty() {
        return false;
    }
    let TermKind::Application {
        symbol, arguments, ..
    } = rule.lhs.kind()
    else {
        return false;
    };
    if &symbol.name != head {
        return false;
    }
    let mut variables = Vec::new();
    for argument in arguments {
        let variable = match argument.kind() {
            TermKind::Variable(variable) => variable,
            TermKind::Injection { term, .. } => match term.kind() {
                TermKind::Variable(variable) => variable,
                _ => return false,
            },
            _ => return false,
        };
        if variables.contains(&variable) {
            return false;
        }
        variables.push(variable);
    }
    let RuleRhs::Term(rhs) = &rule.rhs else {
        return false;
    };
    let lowered = match rhs.kind() {
        TermKind::Injection { term, .. } => term,
        _ => rhs,
    };
    let TermKind::Application {
        symbol, arguments, ..
    } = lowered.kind()
    else {
        return false;
    };
    &symbol.name == lesser
        && arguments.len() == variables.len()
        && arguments
            .iter()
            .zip(&variables)
            .all(|(argument, variable)| {
                matches!(argument.kind(), TermKind::Variable(found) if found == *variable)
            })
}

/// The findings of a full critical-pair check of `definition`: each precondition row the
/// definition violates, then each pair it does not join (and each equation the evaluator does not
/// apply to every subject it describes), every pair searched for a ground instance.
fn confluence_findings(
    definition: &BackendDefinition,
    verdict: &crate::confluence::ValueClaims,
) -> Vec<Finding> {
    let mut findings: Vec<Finding> = verdict
        .violations()
        .iter()
        .cloned()
        .map(Finding::Precondition)
        .collect();
    let mut search = instance::Search::new(definition);
    findings.extend(verdict.unjoined().iter().map(|pair| {
        // A hook pair's second equation is a written meaning of the hook, not an equation of
        // the definition: the finding is about the one equation, which is not shown to agree
        // with the builtin, and no input with two results is searched for.
        if pair.hook.is_some() || pair.reason.describes_one_equation() {
            Finding::Equation(pair.clone())
        } else {
            Finding::Pair {
                pair: pair.clone(),
                instance: search.ground_instance(pair),
            }
        }
    }));
    findings
}
