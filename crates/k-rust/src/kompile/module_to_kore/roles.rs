//! ```toml algorithm-site
//! id = "kompile.kore.axioms"
//! role = "part"
//! sites = ["SymbolRoles::classify"]
//! ```
//!
//! Every distinctness, functional and declaration claim KORE emission makes about a symbol,
//! decided once per emitted module.
//!
//! [`SymbolRoles::classify`] reads each production's [`ProductionKind`], the equations the
//! module's rules make it head, and its place in the overload order, and derives one
//! [`SymbolClaims`] from them. Both declaration loops, `symbol_attributes` and
//! `generated_axioms` (the functional axiom and the no-confusion axioms) read the claims and
//! nothing else, so no two claims about one symbol rest on two readings of its facts.
//!
//! Every claim is an axiom of the emitted theory, whose intended values are the normal forms of
//! its non-lemma equations. [`Freeness`] states `constructor`, `injective` and the no-confusion
//! axioms together: `constructor` (no equation heads the symbol, so its applications to values
//! are values) implies the no-confusion axioms (no equation equates its applications with those
//! of another no-confusion symbol of its sort), which imply `injective` (no equation equates two
//! of its applications with different arguments). The shape constructors of [`SymbolClaims`] give
//! a token, a function and a macro production no freeness that has no-confusion axioms.

#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::{BTreeMap, BTreeSet};

use crate::definition::production_kind::{BracketName, ProductionKind};
use crate::definition::{
    AttributeKey, LabelHead, OverloadOrder, ProductionCatalog, ProductionId, RuleCatalog, Sentence,
    SortHead, match_rule_label,
};
use crate::kast::Label;

/// The equations other sentences of the module make a production head, read under the label
/// its declaration is made under: its own label, or the `bracketLabel` of an unlabelled bracket.
///
/// Private: consumers read [`SymbolClaims`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct EquationHeads {
    /// An `anywhere` rule is headed by the label.
    anywhere_rule: bool,
    /// A macro-like equation is headed by the label: the label heads a macro-like rule, or a
    /// macro-like production has it, whose attribute makes every rule headed by the label a
    /// macro-like rule ([`RuleCatalog::all_macro_labels`]).
    macro_rule: bool,
    overload: OverloadPosition,
}

/// A production's place in its overload family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OverloadPosition {
    /// Greater than no production, so it heads no overload equation.
    NotGreater,
    /// Greater than at least one production `l` of its family, so it heads the overload equation
    /// `g(inj(x)) = inj(l(x))` for each such `l`, which sends an application to the injected
    /// application of the most specific lesser production that accepts its arguments.
    ///
    /// Both conditions range over the transitive overload order, so they cover every chain of
    /// lowerings.
    Greater {
        /// Condition (a): every production below it is locally injective
        /// ([`LabelHeads::locally_injective`]), so two of its applications reach one normal form
        /// only through the same production at the same arguments.
        lessers_locally_injective: bool,
        /// Condition (b): no other production related to it in the overload order (above it,
        /// below it, or sharing a lesser with it) has its result sort head. Then every value an
        /// application reaches is either the application itself in normal form or an injection
        /// from a strictly smaller sort, which differs from every application of another
        /// no-confusion symbol of the sort. Without it an overload equation equates an
        /// application with one of a sibling of the same sort (`asNumber(inj(x)) = asInt(x)`),
        /// or two greaters of one sort that share a lesser `l` both equal `inj(l(x))`.
        alone_in_sort: bool,
    },
}

/// The facts one production's claims are decided from.
#[derive(Clone, Copy, Debug)]
struct SymbolRole {
    /// [`ProductionKind::of`].
    kind: ProductionKind,
    /// [`ProductionKind::of_unbracketed`]: for a bracket, the kind of the production its syntax
    /// declaration states.
    unbracketed: ProductionKind,
    /// The production has its own label.
    labelled: bool,
    heads: EquationHeads,
}

/// What the emitted theory states about the distinctness of a symbol's applications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Freeness {
    /// `constructor`, `injective`, the injectivity axiom and disjointness from every other
    /// no-confusion symbol of its sort: no equation heads the symbol.
    Constructor,
    /// A free overload-greater: `injective` and the no-confusion axioms but no `constructor`,
    /// because its overload equations evaluate it. Every production below it is locally
    /// injective, and no production related to it in the overload order has its result sort
    /// head (conditions (a) and (b) of [`OverloadPosition::Greater`]).
    OverloadConstructor,
    /// `injective` only.
    Injective,
    /// No distinctness claim.
    None,
}

impl Freeness {
    /// Whether the declaration carries `constructor`.
    pub(super) fn declares_constructor(self) -> bool {
        match self {
            Self::Constructor => true,
            Self::OverloadConstructor | Self::Injective | Self::None => false,
        }
    }

    /// Whether the semantic module states the injectivity axiom `σ(X) ∧ σ(Y) → σ(X ∧ Y)` and
    /// disjointness from every other no-confusion symbol of the same sort.
    pub(super) fn has_no_confusion(self) -> bool {
        match self {
            Self::Constructor | Self::OverloadConstructor => true,
            Self::Injective | Self::None => false,
        }
    }

    /// Whether the declaration carries `injective`.
    pub(super) fn declares_injective(self) -> bool {
        match self {
            Self::Constructor | Self::OverloadConstructor | Self::Injective => true,
            Self::None => false,
        }
    }
}

/// The modules a production's symbol is declared in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Declaration {
    /// Both modules, under the production's label.
    SemanticAndSyntax,
    /// The syntax module only (a bracket, which no term contains), under its own label or its
    /// `bracketLabel`.
    SyntaxOnly(BracketName),
    /// Neither module: a subsort, a matching-logic builtin, an unlabelled production, or a
    /// bracket with no name to declare it under.
    None,
}

/// Every claim emission makes about one production's symbol.
///
/// Private fields; built only by the shape constructors below, which [`SymbolRole::claims`]
/// alone calls.
#[derive(Clone, Copy, Debug)]
pub(super) struct SymbolClaims {
    declaration: Declaration,
    freeness: Freeness,
    functional: bool,
    anywhere: bool,
}

impl SymbolClaims {
    /// A base or algebraic production: a generator of its sort's no-junk axiom, whose freeness
    /// its equation heads decide.
    fn generator(freeness: Freeness, functional: bool, anywhere: bool) -> Self {
        Self {
            declaration: Declaration::SemanticAndSyntax,
            freeness,
            functional,
            anywhere,
        }
    }

    /// A token production: its applications are the domain values of its sort, `\top` in the
    /// no-junk axiom. It is never a `constructor` and never in the no-confusion axioms, because
    /// its symbol is never applied and a domain value is no element of the term algebra, so
    /// `injective` is its only distinctness claim.
    /// An unlabelled one declares no symbol.
    fn domain_values(labelled: bool, injective: bool, anywhere: bool) -> Self {
        if !labelled {
            return Self::undeclared();
        }
        Self {
            declaration: Declaration::SemanticAndSyntax,
            freeness: if injective {
                Freeness::Injective
            } else {
                Freeness::None
            },
            functional: true,
            anywhere,
        }
    }

    /// A function or macro production: its equations evaluate or expand its applications, so it
    /// is absent from the no-junk axiom and makes no distinctness claim.
    /// An unlabelled one declares no symbol.
    fn defined_by_equations(labelled: bool, functional: bool, anywhere: bool) -> Self {
        if !labelled {
            return Self::undeclared();
        }
        Self {
            declaration: Declaration::SemanticAndSyntax,
            freeness: Freeness::None,
            functional,
            anywhere,
        }
    }

    /// A bracket: the claims of the production its syntax declaration states, on that
    /// declaration only.
    fn syntax_only(
        name: BracketName,
        freeness: Freeness,
        functional: bool,
        anywhere: bool,
    ) -> Self {
        Self {
            declaration: Declaration::SyntaxOnly(name),
            freeness,
            functional,
            anywhere,
        }
    }

    /// A production that declares no symbol.
    fn undeclared() -> Self {
        Self {
            declaration: Declaration::None,
            freeness: Freeness::None,
            functional: false,
            anywhere: false,
        }
    }

    pub(super) fn declaration(self) -> Declaration {
        self.declaration
    }

    /// The `constructor` and `injective` attributes, and the no-confusion axioms through
    /// [`SymbolClaims::no_confusion`].
    pub(super) fn freeness(self) -> Freeness {
        self.freeness
    }

    /// Whether the declaration carries `functional` and the semantic module the functional
    /// axiom: every application denotes exactly one value.
    pub(super) fn functional(self) -> bool {
        self.functional
    }

    /// Whether the declaration carries `anywhere`: an `anywhere` or overload equation heads the
    /// symbol.
    pub(super) fn anywhere(self) -> bool {
        self.anywhere
    }

    /// Whether the semantic module states the symbol's injectivity axiom and its disjointness
    /// from the other no-confusion symbols of its sort. A symbol declared only in the syntax
    /// module is mentioned by no axiom.
    pub(super) fn no_confusion(self) -> bool {
        match self.declaration {
            Declaration::SemanticAndSyntax => self.freeness.has_no_confusion(),
            Declaration::SyntaxOnly(_) | Declaration::None => false,
        }
    }
}

impl SymbolRole {
    /// The claims table: one exhaustive decision per kind.
    fn claims(self) -> SymbolClaims {
        let anywhere = self.heads.anywhere_rule
            || match self.heads.overload {
                OverloadPosition::NotGreater => false,
                OverloadPosition::Greater { .. } => true,
            };
        match self.kind {
            ProductionKind::Subsort
            | ProductionKind::Builtin
            | ProductionKind::Unlabelled
            | ProductionKind::Bracket(BracketName::Undeclared) => SymbolClaims::undeclared(),
            ProductionKind::Bracket(name @ (BracketName::OwnLabel | BracketName::BracketLabel)) => {
                // The syntax declaration states the production without `bracket`, labelled by
                // the bracket's own label or its `bracketLabel`, and carries that production's
                // claims; no semantic declaration or axiom mentions a bracket.
                let declared = Self {
                    kind: self.unbracketed,
                    labelled: true,
                    ..self
                };
                if let ProductionKind::Bracket(_) = declared.kind {
                    unreachable!("ProductionKind::of_unbracketed never classifies a bracket")
                }
                let claims = declared.claims();
                SymbolClaims::syntax_only(name, claims.freeness, claims.functional, claims.anywhere)
            }
            ProductionKind::Function { .. } | ProductionKind::MacroProduction => {
                SymbolClaims::defined_by_equations(self.labelled, self.kind.functional(), anywhere)
            }
            ProductionKind::Token { algebraic } => {
                SymbolClaims::domain_values(self.labelled, !algebraic && self.injective(), anywhere)
            }
            // Its `assoc`, `comm` or `idem` axioms identify applications with different
            // arguments.
            ProductionKind::Algebraic => {
                SymbolClaims::generator(Freeness::None, self.kind.functional(), anywhere)
            }
            ProductionKind::Base => {
                SymbolClaims::generator(self.base_freeness(), self.kind.functional(), anywhere)
            }
        }
    }

    /// The `injective` claim of a production whose own declaration identifies no two of its
    /// applications (neither a function nor algebraic, which the kind decides): it heads no
    /// `anywhere` or macro-like equation and, when it is an overload-greater, every production
    /// below it is locally injective (condition (a)).
    ///
    /// `injective` is an axiom: equal applications have equal arguments. A production that heads
    /// no equation has `c(a)` as a normal form for normal arguments `a`, so it is injective. An
    /// `anywhere` or macro-like equation headed by it may identify applications with different
    /// arguments (`wrap(s(X)) = wrap(X)` gives `wrap(s(z)) = wrap(z)`), and whether one does is
    /// undecidable in general, so such a head withholds the claim. The overload equations
    /// `g(inj(x)) = inj(l(x))` of an overload-greater `g` send `g(a)` to the injected normal
    /// form of the most specific lesser production that accepts `a`, or leave `g(a)` normal when
    /// none does; two argument tuples then reach one normal form only through the same
    /// production at the same arguments, and an injection is determined by its operand, so `g`
    /// is injective when every production below it is locally injective. `simplification` rules
    /// are lemmas, true in the model the other sentences define, so they cannot falsify an axiom
    /// that holds there and are not counted.
    fn injective(self) -> bool {
        !self.heads.anywhere_rule
            && !self.heads.macro_rule
            && match self.heads.overload {
                OverloadPosition::NotGreater => true,
                OverloadPosition::Greater {
                    lessers_locally_injective,
                    alone_in_sort: _,
                } => lessers_locally_injective,
            }
    }

    /// The freeness of a labelled production that is neither a function, a macro production, a
    /// token nor algebraic: its applications are values exactly when no equation heads it.
    fn base_freeness(self) -> Freeness {
        if self.heads.anywhere_rule || self.heads.macro_rule {
            // An `anywhere` or macro-like equation headed by the production may equate its
            // applications with other terms (`plain(X) = done(X)` for a rule
            // `plain(X) => done(X) [macro]`) or with each other, so it makes no distinctness
            // claim.
            return Freeness::None;
        }
        match self.heads.overload {
            OverloadPosition::NotGreater => Freeness::Constructor,
            OverloadPosition::Greater {
                lessers_locally_injective: true,
                alone_in_sort: true,
            } => Freeness::OverloadConstructor,
            // An overload equation equates one of its applications with an application of a
            // production of the same sort, so disjointness fails while injectivity holds.
            OverloadPosition::Greater {
                lessers_locally_injective: true,
                alone_in_sort: false,
            } => Freeness::Injective,
            // An overload equation reaches a production below it that may identify two
            // applications with different arguments.
            OverloadPosition::Greater {
                lessers_locally_injective: false,
                alone_in_sort: _,
            } => Freeness::None,
        }
    }
}

/// The label heads the module's sentences make equation heads.
struct LabelHeads {
    /// The heads of `anywhere` rules.
    anywhere_rules: BTreeSet<LabelHead>,
    /// The heads of macro-like equations ([`RuleCatalog::all_macro_labels`]).
    macro_rules: BTreeSet<LabelHead>,
}

impl LabelHeads {
    fn of(productions: &ProductionCatalog<'_>, rules: &RuleCatalog<'_>) -> Self {
        Self {
            anywhere_rules: rules
                .rules()
                .filter(|(_, rule)| rule.attributes().has(AttributeKey::Anywhere))
                .map(|(_, rule)| LabelHead::from(&match_rule_label(rule)))
                .collect(),
            macro_rules: rules.all_macro_labels(productions),
        }
    }

    /// The label a production's declaration is made under, which its equation heads are read
    /// under: the `bracketLabel` of an unlabelled bracket, the production's own label otherwise.
    fn declared_under(production: &Sentence, kind: ProductionKind) -> Option<LabelHead> {
        let Sentence::Production {
            label, attributes, ..
        } = production
        else {
            unreachable!("production catalogs contain productions")
        };
        if let ProductionKind::Bracket(BracketName::BracketLabel) = kind {
            attributes
                .label(AttributeKey::BracketLabel)
                .as_ref()
                .map(LabelHead::from)
        } else {
            label.as_ref().map(LabelHead::from)
        }
    }

    /// The `anywhere` and macro-like equations headed by a production, with its overload
    /// position.
    fn heads(
        &self,
        production: &Sentence,
        kind: ProductionKind,
        overload: OverloadPosition,
    ) -> EquationHeads {
        let declared_under = Self::declared_under(production, kind);
        EquationHeads {
            anywhere_rule: declared_under
                .as_ref()
                .is_some_and(|head| self.anywhere_rules.contains(head)),
            macro_rule: declared_under
                .as_ref()
                .is_some_and(|head| self.macro_rules.contains(head)),
            overload,
        }
    }

    /// Whether a production below an overload-greater is locally injective: neither its own
    /// declaration nor an equation other rules make it head identifies two of its applications
    /// with different arguments. It is not a `function` (whose equations evaluate it), carries
    /// no `assoc`, `comm` or `idem` (whose axioms `generated_axioms` emits for any production
    /// carrying them), and heads no `anywhere` or macro-like equation. Its own overload
    /// equations need no test: the overload order is transitive, so every production below it
    /// is also below the greater.
    fn locally_injective(&self, production: &Sentence) -> bool {
        let Sentence::Production { attributes, .. } = production else {
            unreachable!("production catalogs contain productions")
        };
        let heads = self.heads(
            production,
            ProductionKind::of(production),
            OverloadPosition::NotGreater,
        );
        !attributes.has_any(&[
            AttributeKey::Function,
            AttributeKey::Assoc,
            AttributeKey::Comm,
            AttributeKey::Idem,
        ]) && !heads.anywhere_rule
            && !heads.macro_rule
    }

    fn role(&self, production: &Sentence, overload: OverloadPosition) -> SymbolRole {
        let kind = ProductionKind::of(production);
        let Sentence::Production { label, .. } = production else {
            unreachable!("production catalogs contain productions")
        };
        SymbolRole {
            kind,
            unbracketed: ProductionKind::of_unbracketed(production),
            labelled: label.is_some(),
            heads: self.heads(production, kind, overload),
        }
    }
}

/// The result sort head of an overload-order production.
fn result_sort_head(overloads: &OverloadOrder<'_>, id: ProductionId) -> SortHead {
    let Sentence::Production { sort, .. } = overloads.production(id) else {
        unreachable!("overload catalogs contain productions")
    };
    SortHead::from(sort)
}

/// The claims of every production of one module, indexed by the [`ProductionId`] of the
/// production catalog they were classified from.
pub(super) struct SymbolRoles {
    claims: Vec<SymbolClaims>,
}

impl SymbolRoles {
    /// Classify every production of `productions`, whose rules are `rules` and whose overload
    /// order `overloads` was computed from the same catalog.
    ///
    /// O(P + R + O² log O) for P productions, R rules and O elements of the overload order.
    #[must_use]
    pub(super) fn classify(
        productions: &ProductionCatalog<'_>,
        rules: &RuleCatalog<'_>,
        overloads: &OverloadOrder<'_>,
    ) -> Self {
        let heads = LabelHeads::of(productions, rules);
        // Each greater, mapped to conditions (a) and (b) of `OverloadPosition::Greater`.
        let mut greaters = BTreeMap::<ProductionId, (bool, bool)>::new();
        // Invariant: `greaters` maps every greater of a lesser visited so far to whether every
        // visited lesser below it is locally injective (a) and whether, for every visited lesser
        // below it, no other member of that lesser's set {lesser} ∪ greaters has its result sort
        // head (b); `relations_from` is transitively closed, so a production above a greater `g` is
        // a greater of each lesser of `g` and one pass covers every relation and chain, O(O² log
        // O).
        for lesser in overloads.order().elements() {
            let Some(above) = overloads.order().relations_from(lesser) else {
                continue;
            };
            if above.is_empty() {
                continue;
            }
            let injective = heads.locally_injective(overloads.production(*lesser));
            let mut members = BTreeMap::<SortHead, usize>::new();
            for id in std::iter::once(lesser).chain(above) {
                *members.entry(result_sort_head(overloads, *id)).or_default() += 1;
            }
            for greater in above {
                let alone = members[&result_sort_head(overloads, *greater)] == 1;
                let (all_injective, all_alone) = greaters.entry(*greater).or_insert((true, true));
                *all_injective = *all_injective && injective;
                *all_alone = *all_alone && alone;
            }
        }
        let claims = productions
            .productions()
            .map(|(id, production)| {
                let overload = greaters.get(&id).map_or(
                    OverloadPosition::NotGreater,
                    |&(lessers_locally_injective, alone_in_sort)| OverloadPosition::Greater {
                        lessers_locally_injective,
                        alone_in_sort,
                    },
                );
                heads.role(production, overload).claims()
            })
            .collect();
        Self { claims }
    }

    /// The claims of production `id`.
    pub(super) fn claims(&self, id: ProductionId) -> SymbolClaims {
        self.claims[id.0]
    }

    /// Checks, in debug builds, that production `id` (labelled `label`) makes no distinctness
    /// claim, given that rule emission is about to emit an `equation` headed by it.
    ///
    /// An emitted non-lemma equation or macro axiom headed by a symbol evaluates or rewrites its
    /// applications, so they are not free values (I3, no `constructor`), and whether it
    /// identifies two applications with different arguments or an application with one of
    /// another symbol is undecidable in general (I1, no `injective`; I2, no no-confusion axioms).
    /// The claims read the module's rule catalog by label head; rule emission decides per rule,
    /// from the production the rule's left-hand side resolves to, that it emits an equation. The
    /// two derivations are independent, so a disagreement is a kind of equation the
    /// classification misses.
    ///
    /// # Panics
    ///
    /// With `debug_assertions` on, when the claims of `id` are not [`Freeness::None`].
    pub(super) fn debug_assert_heads_equation(
        &self,
        id: ProductionId,
        label: &Label,
        equation: EmittedEquation,
    ) {
        debug_assert!(
            self.claims(id).freeness() == Freeness::None,
            "production `{label}` ({id:?}) heads an emitted {} but its claims state {:?}; \
             I1-I3: a production that heads an emitted non-lemma equation or macro axiom makes \
             no distinctness claim (Freeness::None)",
            equation.describe(),
            self.claims(id).freeness(),
        );
    }

    /// Checks, in debug builds, that the overload axiom `greater(inj(x)) = inj(lesser(x))` being
    /// emitted agrees with the claims of both productions; `same_sort_head` states that their
    /// result sorts have one head, so the axiom equates an application of `greater` with an
    /// application of `lesser` of the same sort.
    ///
    /// The claims decide conditions (a) and (b) of [`OverloadPosition::Greater`] from the
    /// overload order as a whole; this check reads each emitted axiom on its own, so it rejects a
    /// classification that states a distinctness claim the emitted overload equations refute:
    /// - if `greater` is `injective`, so is `lesser`, because the axiom makes an application of
    ///   `greater` equal to the injected application of `lesser` (I1, condition (a));
    /// - with one result sort head, `greater` and `lesser` do not both have no-confusion
    ///   axioms, because the axiom equates an application of each and their disjointness axiom
    ///   denies it (I2, condition (b));
    /// - among the greaters of `lesser` with the result sort head of `greater`, at most one has
    ///   no-confusion axioms, because each of their overload axioms equates an application with
    ///   `inj(lesser(x))`, so two of them share a value (I2, condition (b)).
    ///
    /// `overloads` is the overload order the axioms are emitted from, which names the
    /// productions and gives the other greaters of `lesser`.
    ///
    /// # Panics
    ///
    /// With `debug_assertions` on, when one of the three conditions fails.
    pub(super) fn debug_assert_overload_axiom(
        &self,
        overloads: &OverloadOrder<'_>,
        lesser: ProductionId,
        greater: ProductionId,
        same_sort_head: bool,
    ) {
        if !cfg!(debug_assertions) {
            return;
        }
        let name = |id: ProductionId| {
            if let Sentence::Production {
                label: Some(label), ..
            } = overloads.production(id)
            {
                format!("`{label}` ({id:?})")
            } else {
                format!("{id:?}")
            }
        };
        let lesser_claims = self.claims(lesser);
        let greater_claims = self.claims(greater);
        debug_assert!(
            !greater_claims.freeness().declares_injective()
                || lesser_claims.freeness().declares_injective(),
            "overload axiom {} > {}: the greater is `injective` but the lesser is not ({:?} > \
             {:?}); I1, condition (a): the axiom equates an application of the greater with the \
             injected application of the lesser, so the greater is injective only when every \
             production below it is",
            name(greater),
            name(lesser),
            greater_claims.freeness(),
            lesser_claims.freeness(),
        );
        debug_assert!(
            !(same_sort_head && greater_claims.no_confusion() && lesser_claims.no_confusion()),
            "overload axiom {} > {}: both have no-confusion axioms but share their result sort \
             head ({:?} > {:?}); I2, condition (b): the axiom equates an application of each, \
             which their disjointness axiom denies",
            name(greater),
            name(lesser),
            greater_claims.freeness(),
            lesser_claims.freeness(),
        );
        if greater_claims.no_confusion() {
            let head = result_sort_head(overloads, greater);
            let sibling = overloads
                .order()
                .relations_from(&lesser)
                .into_iter()
                .flatten()
                .copied()
                .find(|&other| {
                    other != greater
                        && self.claims(other).no_confusion()
                        && result_sort_head(overloads, other) == head
                });
            debug_assert!(
                sibling.is_none(),
                "overload axiom {} > {}: another greater {} of the same lesser with result sort \
                 head {head} also has no-confusion axioms; I2, condition (b): both overload \
                 axioms equate an application with the injected application of the lesser, \
                 which their disjointness axiom denies",
                name(greater),
                name(lesser),
                sibling.map_or_else(String::new, name),
            );
        }
    }
}

/// The kind of sentence rule emission emits for a rule whose left-hand side a production heads.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum EmittedEquation {
    /// An equation of a `function` production that is neither a claim nor a `simplification`
    /// lemma.
    Function,
    /// An `anywhere` equation that is neither a claim nor a `simplification` lemma.
    Anywhere,
    /// A macro axiom, from a macro-like rule.
    Macro,
}

impl EmittedEquation {
    fn describe(self) -> &'static str {
        match self {
            Self::Function => "function equation",
            Self::Anywhere => "`anywhere` equation",
            Self::Macro => "macro axiom",
        }
    }
}

#[cfg(test)]
mod tests {
    use serde_json::Value;

    use super::*;
    use crate::definition::production_kind::NoJunk;
    use crate::definition::{Attributes, ProductionItem, ResolvedDefinition};
    use crate::kast::{InternalLabel, Label, Sort};

    /// The facts of one production's own declaration that the claims read.
    #[derive(Clone, Copy, Debug)]
    struct ProductionFacts {
        label: bool,
        builtin_label: bool,
        subsort_shape: bool,
        bracket: bool,
        bracket_label: bool,
        function: bool,
        total: bool,
        macro_like: bool,
        token: bool,
        algebraic: Option<AttributeKey>,
    }

    impl ProductionFacts {
        /// Every combination of the facts.
        fn all() -> Vec<Self> {
            let mut all = Vec::new();
            for bits in 0..1_u32 << 9 {
                let bit = |index: u32| bits & (1 << index) != 0;
                for algebraic in [
                    None,
                    Some(AttributeKey::Assoc),
                    Some(AttributeKey::Comm),
                    Some(AttributeKey::Idem),
                ] {
                    all.push(Self {
                        label: bit(0),
                        builtin_label: bit(1),
                        subsort_shape: bit(2),
                        bracket: bit(3),
                        bracket_label: bit(4),
                        function: bit(5),
                        total: bit(6),
                        macro_like: bit(7),
                        token: bit(8),
                        algebraic,
                    });
                }
            }
            all
        }

        fn own_label(self) -> Option<Label> {
            self.label.then(|| {
                Label::new(if self.builtin_label {
                    InternalLabel::And.as_str()
                } else {
                    "lbl"
                })
            })
        }

        /// The label the head facts are about: the own label, or else the `bracketLabel`.
        fn heads_label(self) -> Option<Label> {
            self.own_label()
                .or_else(|| self.bracket_label.then(|| Label::new("bracketLbl")))
        }

        fn production(self) -> Sentence {
            let mut attributes = Attributes::default();
            let mut mark = |key: AttributeKey| {
                attributes.insert(key.as_str(), Value::String(String::new()));
            };
            for (fact, key) in [
                (self.bracket, AttributeKey::Bracket),
                (self.function, AttributeKey::Function),
                (self.total, AttributeKey::Total),
                (self.macro_like, AttributeKey::Macro),
                (self.token, AttributeKey::Token),
            ] {
                if fact {
                    mark(key);
                }
            }
            if let Some(key) = self.algebraic {
                mark(key);
            }
            if self.bracket_label {
                attributes.insert(
                    AttributeKey::BracketLabel.as_str(),
                    Value::String("bracketLbl".into()),
                );
            }
            let inner = ProductionItem::NonTerminal {
                sort: Sort::new("Inner"),
                name: None,
            };
            Sentence::Production {
                label: self.own_label(),
                parameters: Vec::new(),
                sort: Sort::new("Outer"),
                items: if self.subsort_shape {
                    vec![inner]
                } else {
                    vec![
                        ProductionItem::Terminal("wrap(".into()),
                        inner,
                        ProductionItem::Terminal(")".into()),
                    ]
                },
                attributes,
            }
        }
    }

    /// Where a production stands in its overload family.
    #[derive(Clone, Copy, Debug)]
    enum Overload {
        NotGreater,
        Greater {
            /// Condition (a): every production below it is locally injective.
            lessers_locally_injective: bool,
            /// Condition (b): no production related to it in the overload order has its result
            /// sort head.
            alone_in_sort: bool,
        },
    }

    /// The facts other sentences state about the label a production's heads are read under
    /// ([`ProductionFacts::heads_label`]).
    #[derive(Clone, Copy, Debug)]
    struct HeadFacts {
        anywhere_rule: bool,
        macro_rule: bool,
        /// Another macro-like production has the same label.
        shared_macro_label: bool,
        overload: Overload,
    }

    impl HeadFacts {
        fn all() -> Vec<Self> {
            let mut all = Vec::new();
            for bits in 0..1_u32 << 3 {
                let bit = |index: u32| bits & (1 << index) != 0;
                for overload in [
                    Overload::NotGreater,
                    Overload::Greater {
                        lessers_locally_injective: false,
                        alone_in_sort: false,
                    },
                    Overload::Greater {
                        lessers_locally_injective: false,
                        alone_in_sort: true,
                    },
                    Overload::Greater {
                        lessers_locally_injective: true,
                        alone_in_sort: false,
                    },
                    Overload::Greater {
                        lessers_locally_injective: true,
                        alone_in_sort: true,
                    },
                ] {
                    all.push(Self {
                        anywhere_rule: bit(0),
                        macro_rule: bit(1),
                        shared_macro_label: bit(2),
                        overload,
                    });
                }
            }
            all
        }

        fn position(self) -> OverloadPosition {
            match self.overload {
                Overload::NotGreater => OverloadPosition::NotGreater,
                Overload::Greater {
                    lessers_locally_injective,
                    alone_in_sort,
                } => OverloadPosition::Greater {
                    lessers_locally_injective,
                    alone_in_sort,
                },
            }
        }
    }

    /// The claims about one production, as the declarations and axioms state them.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Stated {
        declaration: Declaration,
        constructor: bool,
        injective: bool,
        functional: bool,
        anywhere: bool,
        no_confusion: bool,
    }

    /// The kind of production a declaration states, as the claims table distinguishes it.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Declared {
        Function,
        Macro,
        Token { algebraic: bool },
        Algebraic,
        Base,
    }

    /// A fact-level restatement of the claims table (design CBC-01 section 2.3) and of the
    /// declaration loops, read directly from the facts of one production and its label.
    ///
    /// ```text
    /// declaration: none for a subsort, a builtin label or an unlabelled non-bracket; syntax
    ///   only for a bracket, under its own label or else its bracketLabel; both otherwise
    /// heads (under the declaration's label): anywhere = an anywhere rule;
    ///   macro = a macro-like rule, or a macro-like production with the label (all_macro_labels)
    /// equation head = anywhere || macro
    /// anywhere    = equation-head anywhere || greater
    /// functional  = !function || total
    /// constructor = Base && !equation head && !greater
    /// no-confusion (semantic declarations only)
    ///             = Base && !equation head && (!greater || (a) && (b))
    /// injective   = (Base || Token && !algebraic) && !equation head && (!greater || (a))
    /// ```
    fn restated(production: ProductionFacts, heads: HeadFacts) -> Stated {
        let p = production;
        let builtin = p.label && p.builtin_label;
        let subsort = !p.label && p.subsort_shape;
        let declaration = if subsort || builtin {
            Declaration::None
        } else if p.bracket {
            if p.label {
                Declaration::SyntaxOnly(BracketName::OwnLabel)
            } else if p.bracket_label {
                Declaration::SyntaxOnly(BracketName::BracketLabel)
            } else {
                Declaration::None
            }
        } else if p.label {
            Declaration::SemanticAndSyntax
        } else {
            Declaration::None
        };
        if declaration == Declaration::None {
            return Stated {
                declaration,
                constructor: false,
                injective: false,
                functional: false,
                anywhere: false,
                no_confusion: false,
            };
        }
        // A declared production is labelled, or a bracket with a `bracketLabel`; a macro-like
        // production with its own label puts that label among the macro-like labels.
        let macro_head = heads.macro_rule || p.label && (heads.shared_macro_label || p.macro_like);
        let equation_head = heads.anywhere_rule || macro_head;
        let declared = if p.function {
            Declared::Function
        } else if p.macro_like {
            Declared::Macro
        } else if p.token {
            Declared::Token {
                algebraic: p.algebraic.is_some(),
            }
        } else if p.algebraic.is_some() {
            Declared::Algebraic
        } else {
            Declared::Base
        };
        let (greater, a, b) = match heads.overload {
            Overload::NotGreater => (false, true, true),
            Overload::Greater {
                lessers_locally_injective,
                alone_in_sort,
            } => (true, lessers_locally_injective, alone_in_sort),
        };
        let base = declared == Declared::Base;
        let injective_kind = base || declared == (Declared::Token { algebraic: false });
        Stated {
            declaration,
            constructor: base && !equation_head && !greater,
            injective: injective_kind && !equation_head && (!greater || a),
            functional: !p.function || p.total,
            anywhere: heads.anywhere_rule || greater,
            no_confusion: declaration == Declaration::SemanticAndSyntax
                && base
                && !equation_head
                && (!greater || a && b),
        }
    }

    fn stated(role: SymbolRole) -> Stated {
        let claims = role.claims();
        Stated {
            declaration: claims.declaration(),
            constructor: claims.freeness().declares_constructor(),
            injective: claims.freeness().declares_injective(),
            functional: claims.functional(),
            anywhere: claims.anywhere(),
            no_confusion: claims.no_confusion(),
        }
    }

    /// The equation heads of a module whose other sentences state `heads` about `production`,
    /// with that production.
    fn label_heads(production: ProductionFacts, heads: HeadFacts) -> (LabelHeads, Sentence) {
        let sentence = production.production();
        let mut anywhere_rules = BTreeSet::new();
        let mut macro_rules = BTreeSet::new();
        let mut sentences = vec![sentence.clone()];
        if let Some(label) = production.heads_label() {
            if heads.anywhere_rule {
                anywhere_rules.insert(LabelHead::from(&label));
            }
            if heads.macro_rule {
                macro_rules.insert(LabelHead::from(&label));
            }
        }
        if let (Some(label), true) = (production.own_label(), heads.shared_macro_label) {
            let mut attributes = Attributes::default();
            attributes.insert(AttributeKey::Macro.as_str(), Value::String(String::new()));
            sentences.push(Sentence::Production {
                label: Some(label),
                parameters: Vec::new(),
                sort: Sort::new("Other"),
                items: Vec::new(),
                attributes,
            });
        }
        let catalog = ProductionCatalog::from_visible(&sentences);
        // `RuleCatalog::all_macro_labels`: the macro-like rules' heads and the macro-like
        // productions' labels.
        macro_rules.extend(catalog.macro_labels().iter().cloned());
        (
            LabelHeads {
                anywhere_rules,
                macro_rules,
            },
            sentence,
        )
    }

    /// The role of one production of a module whose other sentences state `heads`.
    fn role(production: ProductionFacts, heads: HeadFacts) -> SymbolRole {
        let (label_heads, sentence) = label_heads(production, heads);
        label_heads.role(&sentence, heads.position())
    }

    /// The claims table states, on every combination of production and head facts, exactly the
    /// claims its fact-level restatement states.
    #[test]
    fn claims_restate_the_claims_table_on_every_combination_of_facts() {
        let heads = HeadFacts::all();
        let mut checked = 0;
        let mut greater_positions = BTreeSet::new();
        for production in ProductionFacts::all() {
            for &head in &heads {
                assert_eq!(
                    stated(role(production, head)),
                    restated(production, head),
                    "{production:?} {head:?}"
                );
                checked += 1;
                if let Overload::Greater {
                    lessers_locally_injective,
                    alone_in_sort,
                } = head.overload
                {
                    greater_positions.insert((lessers_locally_injective, alone_in_sort));
                }
            }
        }
        assert_eq!(checked, 2048 * 40);
        assert_eq!(
            greater_positions.len(),
            4,
            "every overload-greater combination of the two conditions is checked"
        );
    }

    /// A production below an overload-greater is locally injective exactly when it is neither a
    /// function nor algebraic and heads no `anywhere` or macro-like equation under the label its
    /// declaration is made under.
    #[test]
    fn local_injectivity_restates_condition_a_on_every_combination_of_facts() {
        for production in ProductionFacts::all() {
            for head in HeadFacts::all() {
                let (label_heads, sentence) = label_heads(production, head);
                let under = if production.label {
                    true
                } else {
                    production.bracket && production.bracket_label && !production.subsort_shape
                };
                let macro_head = head.macro_rule
                    || production.label && (head.shared_macro_label || production.macro_like);
                let expected = !production.function
                    && production.algebraic.is_none()
                    && !(under && (head.anywhere_rule || macro_head));
                assert_eq!(
                    label_heads.locally_injective(&sentence),
                    expected,
                    "{production:?} {head:?}"
                );
            }
        }
    }

    /// Every variant, listed through an exhaustive match so that a new variant must be added.
    fn every_freeness() -> Vec<Freeness> {
        let listed = |freeness: Freeness| match freeness {
            Freeness::Constructor
            | Freeness::OverloadConstructor
            | Freeness::Injective
            | Freeness::None => freeness,
        };
        vec![
            listed(Freeness::Constructor),
            listed(Freeness::OverloadConstructor),
            listed(Freeness::Injective),
            listed(Freeness::None),
        ]
    }

    #[test]
    fn constructor_implies_no_confusion_implies_injective() {
        for freeness in every_freeness() {
            assert!(
                !freeness.declares_constructor() || freeness.has_no_confusion(),
                "{freeness:?}: constructor without no-confusion"
            );
            assert!(
                !freeness.has_no_confusion() || freeness.declares_injective(),
                "{freeness:?}: no-confusion without injective"
            );
        }
    }

    /// A labelled token production's applications are domain values: whatever rules and
    /// overloads say about its label, it is `\top` in the no-junk axiom and never a
    /// `constructor` or in the no-confusion axioms.
    #[test]
    fn a_labelled_token_classifies_as_domain_values_without_no_confusion() {
        let token = ProductionFacts {
            label: true,
            builtin_label: false,
            subsort_shape: false,
            bracket: false,
            bracket_label: false,
            function: false,
            total: false,
            macro_like: false,
            token: true,
            algebraic: None,
        };
        assert_eq!(
            ProductionKind::of(&token.production()).no_junk(),
            NoJunk::DomainValues
        );
        for heads in HeadFacts::all() {
            let claims = role(token, heads).claims();
            assert!(
                matches!(claims.freeness(), Freeness::Injective | Freeness::None),
                "{heads:?}: {:?}",
                claims.freeness()
            );
            assert!(!claims.no_confusion(), "{heads:?}");
        }
        let plain = HeadFacts {
            anywhere_rule: false,
            macro_rule: false,
            shared_macro_label: false,
            overload: Overload::NotGreater,
        };
        assert_eq!(role(token, plain).claims().freeness(), Freeness::Injective);
    }

    fn classified(source: &str) -> BTreeMap<String, SymbolClaims> {
        let parsed = crate::outer::parse("roles.k", source).expect("definition should parse");
        let lowered = crate::outer::lower(&parsed, "MAIN").expect("definition should lower");
        let definition =
            crate::inner::resolve_rule_bubbles(&lowered).expect("rule bubbles should resolve");
        let resolved = ResolvedDefinition::resolve(&definition).expect("definition should resolve");
        let module = resolved.module_id("MAIN").unwrap();
        let productions = resolved.production_catalog(module);
        let overloads = resolved.overloads(module).expect("no overload cycle");
        let roles = SymbolRoles::classify(&productions, &resolved.rule_catalog(module), &overloads);
        productions
            .productions()
            .filter_map(|(id, production)| {
                let Sentence::Production {
                    label: Some(label), ..
                } = production
                else {
                    return None;
                };
                Some((label.name.clone(), roles.claims(id)))
            })
            .collect()
    }

    /// A rule `plain(X) => done(X) [macro]` is the equation `plain(X) = done(X)`, so `plain`
    /// makes no distinctness claim although its own declaration is a base production, while
    /// `done`, which heads nothing, stays a constructor.
    #[test]
    fn a_base_production_heading_a_macro_like_rule_classifies_as_freeness_none() {
        let claims = classified(indoc::indoc! {r#"
            module MAIN
              syntax Exp ::= "done(" Exp ")" [symbol(done)]
              syntax Exp ::= "plain(" Exp ")" [symbol(plain)]
              syntax Exp ::= "leaf" [symbol(leaf)]

              rule plain(X:Exp) => done(X:Exp) [macro]
            endmodule
        "#});
        assert_eq!(claims["plain"].freeness(), Freeness::None);
        assert!(!claims["plain"].no_confusion());
        assert_eq!(claims["done"].freeness(), Freeness::Constructor);
        assert!(claims["done"].no_confusion());
    }

    /// An alias around a rule's left side leaves the head that the classification reads, so
    /// `wrap(X) #as _V => done(X) [anywhere]` makes `wrap` an equation head.
    #[test]
    fn an_aliased_anywhere_head_classifies_as_freeness_none() {
        let claims = classified(indoc::indoc! {r#"
            module MAIN
              syntax Exp ::= "done(" Exp ")" [symbol(done)]
              syntax Exp ::= "wrap(" Exp ")" [symbol(wrap)]

              rule wrap(X:Exp) #as _V:Exp => done(X:Exp) [anywhere]
            endmodule
        "#});
        assert_eq!(claims["wrap"].freeness(), Freeness::None);
        assert!(claims["wrap"].anywhere());
        assert_eq!(claims["done"].freeness(), Freeness::Constructor);
    }

    /// The labelled token of a module is declared with `injective` only.
    #[test]
    fn a_labelled_token_of_a_module_classifies_as_injective() {
        let claims = classified(indoc::indoc! {r#"
            module MAIN
              syntax Str ::= r"[a-z]+" [token, symbol(strLit)]
              syntax Exp ::= "wrap(" Str ")" [symbol(wrap)]
            endmodule
        "#});
        assert_eq!(claims["strLit"].freeness(), Freeness::Injective);
        assert_eq!(
            claims["strLit"].declaration(),
            Declaration::SemanticAndSyntax
        );
        assert!(!claims["strLit"].no_confusion());
        assert_eq!(claims["wrap"].freeness(), Freeness::Constructor);
    }

    /// The claims of one production, as the check reads them.
    fn roles_with(freeness: Freeness) -> SymbolRoles {
        SymbolRoles {
            claims: vec![SymbolClaims::generator(freeness, true, false)],
        }
    }

    /// A production with no distinctness claim may head every kind of emitted equation.
    #[test]
    fn a_production_without_distinctness_claims_heads_every_emitted_equation() {
        let roles = roles_with(Freeness::None);
        for equation in [
            EmittedEquation::Function,
            EmittedEquation::Anywhere,
            EmittedEquation::Macro,
        ] {
            roles.debug_assert_heads_equation(ProductionId(0), &Label::new("plain"), equation);
        }
    }

    /// 58ad83fc: a base production heading a macro-like rule was declared `constructor`, with
    /// no-confusion axioms, although the macro axiom `plain(X) = done(X)` evaluates it.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "heads an emitted macro axiom but its claims state Constructor")]
    fn a_constructor_heading_a_macro_axiom_fails_the_check() {
        roles_with(Freeness::Constructor).debug_assert_heads_equation(
            ProductionId(0),
            &Label::new("plain"),
            EmittedEquation::Macro,
        );
    }

    /// 1ab34aad: a production heading an `anywhere` rule was still declared `injective` (the
    /// state `let injective = base_constructor;`), although the equation may identify two of its
    /// applications with different arguments.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(
        expected = "heads an emitted `anywhere` equation but its claims state Injective"
    )]
    fn an_injective_production_heading_an_anywhere_equation_fails_the_check() {
        roles_with(Freeness::Injective).debug_assert_heads_equation(
            ProductionId(0),
            &Label::new("wrap"),
            EmittedEquation::Anywhere,
        );
    }

    /// An overload family whose greater `asNumber` shares its result sort `Value` with its
    /// lesser `asInt`: the overload axiom `asNumber(inj(x)) = asInt(x)` equates an application
    /// of each.
    const SAME_SORT_FAMILY: &str = r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Number ::= Int
          syntax Value ::= Number
          syntax K ::= Value

          syntax Value ::= "widest(" Value ")" [overload(project), symbol(widest)]
          syntax Value ::= "asInt(" Int ")" [overload(view), symbol(asInt)]
          syntax Value ::= "asNumber(" Number ")" [overload(view), symbol(asNumber)]
        endmodule
    "#;

    fn definition(source: &str) -> crate::definition::Definition {
        let parsed = crate::outer::parse("roles.k", source).expect("definition should parse");
        let lowered = crate::outer::lower(&parsed, "MAIN").expect("definition should lower");
        crate::inner::resolve_rule_bubbles(&lowered).expect("rule bubbles should resolve")
    }

    /// The semantic module emitted for `source`.
    fn semantics(source: &str) -> crate::kore::ast::Module {
        super::super::module_to_kore(&definition(source), "MAIN")
            .expect("KORE modules should emit")
            .semantics
    }

    /// The symbol names of an application pattern `σ(..)`.
    fn applied(pattern: &crate::kore::ast::Pattern) -> Option<&str> {
        if let crate::kore::ast::Pattern::Application { symbol, .. } = pattern {
            Some(symbol.name.as_str())
        } else {
            None
        }
    }

    /// The pairs of symbols of the disjointness axioms `\not(\and(σ(..), τ(..)))`.
    fn disjoint_pairs(module: &crate::kore::ast::Module) -> Vec<(String, String)> {
        use crate::kore::ast::{Pattern as KorePattern, Sentence as KoreSentence};
        module
            .sentences
            .iter()
            .filter_map(|sentence| {
                let KoreSentence::Axiom { pattern, .. } = sentence else {
                    return None;
                };
                let KorePattern::Not { argument, .. } = pattern.as_ref() else {
                    return None;
                };
                let KorePattern::And { arguments, .. } = argument.as_ref() else {
                    return None;
                };
                let [left, right] = arguments.as_slice() else {
                    return None;
                };
                Some((applied(left)?.to_owned(), applied(right)?.to_owned()))
            })
            .collect()
    }

    /// The symbols of the injectivity axioms `\implies(\and(σ(X), σ(Y)), σ(..))`.
    fn injectivity_axioms(module: &crate::kore::ast::Module) -> BTreeSet<String> {
        use crate::kore::ast::{Pattern as KorePattern, Sentence as KoreSentence};
        module
            .sentences
            .iter()
            .filter_map(|sentence| {
                let KoreSentence::Axiom { pattern, .. } = sentence else {
                    return None;
                };
                let KorePattern::Implies { left, right, .. } = pattern.as_ref() else {
                    return None;
                };
                let KorePattern::And { arguments, .. } = left.as_ref() else {
                    return None;
                };
                let [first, second] = arguments.as_slice() else {
                    return None;
                };
                let symbol = applied(right)?;
                (applied(first)? == symbol && applied(second)? == symbol).then(|| symbol.to_owned())
            })
            .collect()
    }

    /// The marker attributes of the declaration of `symbol`.
    fn declared_attributes(module: &crate::kore::ast::Module, symbol: &str) -> Vec<String> {
        use crate::kore::ast::Sentence as KoreSentence;
        module
            .sentences
            .iter()
            .find_map(|sentence| {
                let KoreSentence::SymbolDeclaration {
                    symbol: declared,
                    attributes,
                    ..
                } = sentence
                else {
                    return None;
                };
                (declared.name == symbol).then(|| {
                    attributes
                        .0
                        .iter()
                        .filter_map(|attribute| applied(attribute).map(str::to_owned))
                        .collect()
                })
            })
            .unwrap_or_else(|| panic!("{symbol} should be declared"))
    }

    /// The overload axiom `asNumber(inj(x)) = asInt(x)` equates an application of each, so the
    /// theory states no disjointness of the two, while `asInt`, which heads no equation, stays a
    /// constructor and `asNumber` keeps `injective` (its only lesser is a constructor).
    #[test]
    fn a_same_sort_overload_family_states_no_disjointness_of_its_members() {
        let module = semantics(SAME_SORT_FAMILY);
        let pairs = disjoint_pairs(&module);
        assert!(!pairs.is_empty(), "the family's constructors are disjoint");
        for (left, right) in &pairs {
            assert!(
                !([left.as_str(), right.as_str()].contains(&"LblasInt")
                    && [left.as_str(), right.as_str()].contains(&"LblasNumber")),
                "{left} and {right} are declared disjoint"
            );
            assert!(
                left != "LblasNumber" && right != "LblasNumber",
                "`asNumber` fails condition (b), since it equals `asInt` on an injected argument, \
                 so it has no no-confusion axioms: {left} and {right}"
            );
        }
        assert!(!injectivity_axioms(&module).contains("LblasNumber"));
        assert!(injectivity_axioms(&module).contains("LblasInt"));
        let as_number = declared_attributes(&module, "LblasNumber");
        assert!(as_number.contains(&"injective".to_owned()), "{as_number:?}");
        assert!(as_number.contains(&"anywhere".to_owned()), "{as_number:?}");
        assert!(
            !as_number.contains(&"constructor".to_owned()),
            "{as_number:?}"
        );
    }

    /// An overload-greater over a `function` lesser is not injective: `g(inj(1))` and
    /// `g(inj(-1))` both equal `inj(abs(1))` when `abs(1) = abs(-1)`. So `g` carries neither
    /// `injective` nor the injectivity axiom, nor any no-confusion axiom.
    #[test]
    fn an_overload_greater_over_a_function_lesser_states_no_injectivity() {
        let module = semantics(
            r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax Number ::= Int
              syntax K ::= Number

              syntax Int ::= "abs(" Int ")" [function, overload(abs), symbol(abs)]
              syntax Number ::= "g(" Number ")" [overload(abs), symbol(g)]
              syntax Number ::= "node(" Number ")" [symbol(node)]
            endmodule
            "#,
        );
        let g = declared_attributes(&module, "Lblg");
        assert!(!g.contains(&"injective".to_owned()), "{g:?}");
        assert!(!g.contains(&"constructor".to_owned()), "{g:?}");
        assert!(g.contains(&"anywhere".to_owned()), "{g:?}");
        assert!(!injectivity_axioms(&module).contains("Lblg"));
        assert!(
            disjoint_pairs(&module)
                .iter()
                .all(|(left, right)| left != "Lblg" && right != "Lblg")
        );
        assert!(injectivity_axioms(&module).contains("Lblnode"));
    }

    /// Condition (b) of each greater. A chain `high > middle > low` over three sorts relates no
    /// two members of one sort. A chain `asLarge > asMedium > asSmall` of one result sort relates
    /// `asLarge` to both others, directly and through the transitive order. Two greaters of one
    /// sort that share a lesser (`left`, `right` over `base`) both equal `inj(base(x))`.
    #[test]
    fn condition_b_covers_siblings_and_chains() {
        let claims = classified(indoc::indoc! {r#"
            module MAIN
              syntax Small ::= "z" [symbol(z)]
              syntax Medium ::= Small
              syntax Large ::= Medium
              syntax K ::= Large

              syntax Small ::= "low(" Small ")" [overload(chain), symbol(low)]
              syntax Medium ::= "middle(" Medium ")" [overload(chain), symbol(middle)]
              syntax Large ::= "high(" Large ")" [overload(chain), symbol(high)]

              syntax Large ::= "asSmall(" Small ")" [overload(view), symbol(asSmall)]
              syntax Large ::= "asMedium(" Medium ")" [overload(view), symbol(asMedium)]
              syntax Large ::= "asLarge(" Large ")" [overload(view), symbol(asLarge)]

              syntax Small ::= "base(" Small ")" [overload(twin), symbol(base)]
              syntax Large ::= "left(" Large ")" [overload(twin), symbol(left)]
              syntax Large ::= "right(" Large ")" [overload(twin), symbol(right)]
            endmodule
        "#});
        assert_eq!(claims["low"].freeness(), Freeness::Constructor);
        assert_eq!(claims["middle"].freeness(), Freeness::OverloadConstructor);
        assert_eq!(claims["high"].freeness(), Freeness::OverloadConstructor);
        assert_eq!(claims["asSmall"].freeness(), Freeness::Constructor);
        assert_eq!(claims["asMedium"].freeness(), Freeness::Injective);
        assert_eq!(claims["asLarge"].freeness(), Freeness::Injective);
        assert_eq!(claims["base"].freeness(), Freeness::Constructor);
        // `left` and `right` are unordered (same arguments, same sort) but share `base`.
        assert_eq!(claims["left"].freeness(), Freeness::Injective);
        assert_eq!(claims["right"].freeness(), Freeness::Injective);
    }

    /// Runs the overload-axiom check on the axiom `asNumber > asInt` of `SAME_SORT_FAMILY`, with
    /// the classified claims of `asInt` and `asNumber` replaced by `as_int` and `as_number` where
    /// given.
    fn check_same_sort_family(as_int: Option<Freeness>, as_number: Option<Freeness>) {
        let definition = definition(SAME_SORT_FAMILY);
        let resolved = ResolvedDefinition::resolve(&definition).expect("definition should resolve");
        let module = resolved.module_id("MAIN").unwrap();
        let productions = resolved.production_catalog(module);
        let overloads = resolved.overloads(module).expect("no overload cycle");
        let mut roles =
            SymbolRoles::classify(&productions, &resolved.rule_catalog(module), &overloads);
        let id = |name: &str| {
            productions
                .productions()
                .find_map(|(id, production)| {
                    let Sentence::Production {
                        label: Some(label), ..
                    } = production
                    else {
                        return None;
                    };
                    (label.name == name).then_some(id)
                })
                .unwrap_or_else(|| panic!("{name} should be a production"))
        };
        let (as_int_id, as_number_id) = (id("asInt"), id("asNumber"));
        for (id, freeness) in [(as_int_id, as_int), (as_number_id, as_number)] {
            if let Some(freeness) = freeness {
                roles.claims[id.0] = SymbolClaims::generator(freeness, true, true);
            }
        }
        roles.debug_assert_overload_axiom(&overloads, as_int_id, as_number_id, true);
    }

    /// Control for the demonstration below: the classified claims of the same-sort family pass
    /// the check.
    #[test]
    fn a_same_sort_overload_axiom_between_a_constructor_and_an_injective_greater_passes() {
        check_same_sort_family(None, None);
        check_same_sort_family(Some(Freeness::Constructor), Some(Freeness::Injective));
    }

    /// 62c50639: every overload-greater was given no-confusion axioms (the classifier arm
    /// `Greater { .. } => Freeness::OverloadConstructor`), so `asNumber` and `asInt`, which the
    /// overload axiom `asNumber(inj(x)) = asInt(x)` equates, were declared disjoint.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "both have no-confusion axioms but share their result sort head")]
    fn a_same_sort_overload_axiom_between_two_no_confusion_symbols_fails_the_check() {
        check_same_sort_family(None, Some(Freeness::OverloadConstructor));
    }

    /// 1ab34aad (overload half): an overload-greater over a lesser that is not injective was
    /// still declared `injective`.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "the greater is `injective` but the lesser is not")]
    fn an_injective_greater_over_a_non_injective_lesser_fails_the_check() {
        check_same_sort_family(Some(Freeness::None), Some(Freeness::Injective));
    }

    /// Two greaters of one sort that share a lesser, both with no-confusion axioms.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "also has no-confusion axioms")]
    fn two_no_confusion_greaters_of_one_lesser_and_sort_fail_the_check() {
        let definition = definition(indoc::indoc! {r#"
            module MAIN
              syntax Small ::= "z" [symbol(z)]
              syntax Large ::= Small
              syntax K ::= Large

              syntax Small ::= "base(" Small ")" [overload(twin), symbol(base)]
              syntax Large ::= "left(" Large ")" [overload(twin), symbol(left)]
              syntax Large ::= "right(" Large ")" [overload(twin), symbol(right)]
            endmodule
        "#});
        let resolved = ResolvedDefinition::resolve(&definition).expect("definition should resolve");
        let module = resolved.module_id("MAIN").unwrap();
        let productions = resolved.production_catalog(module);
        let overloads = resolved.overloads(module).expect("no overload cycle");
        let mut roles =
            SymbolRoles::classify(&productions, &resolved.rule_catalog(module), &overloads);
        let mut ids = BTreeMap::new();
        for (id, production) in productions.productions() {
            if let Sentence::Production {
                label: Some(label), ..
            } = production
            {
                ids.insert(label.name.clone(), id);
            }
        }
        for name in ["left", "right"] {
            roles.claims[ids[name].0] =
                SymbolClaims::generator(Freeness::OverloadConstructor, true, true);
        }
        roles.debug_assert_overload_axiom(&overloads, ids["base"], ids["left"], false);
    }
}
