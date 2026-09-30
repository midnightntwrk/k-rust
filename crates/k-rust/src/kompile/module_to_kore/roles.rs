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
//! axioms together: outside its transitional `Legacy` variant, `constructor` (no equation heads
//! the symbol, so its applications to values are values) implies the no-confusion axioms (no
//! equation equates its applications with those of another constructor of its sort), which imply
//! `injective` (no equation equates two of its applications with different arguments). The
//! shape constructors of [`SymbolClaims`] give a token, a function and a macro production no
//! freeness that has no-confusion axioms.

#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::{BTreeMap, BTreeSet};

use crate::definition::production_kind::{BracketName, ProductionKind};
use crate::definition::{
    AttributeKey, LabelHead, OverloadOrder, ProductionCatalog, ProductionId, RuleCatalog, Sentence,
    match_rule_label,
};

/// The equations other sentences of the module make a production head, read under the label
/// its declaration is made under: its own label, or the `bracketLabel` of an unlabelled bracket.
///
/// Private: consumers read [`SymbolClaims`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct EquationHeads {
    /// An `anywhere` rule is headed by the label.
    anywhere_rule: bool,
    /// A macro-like rule is headed by the label ([`RuleCatalog::macro_labels`]).
    ///
    /// This is the first of the two macro readings CBC-01-T2 keeps unchanged: it decides
    /// `constructor` and the no-confusion axioms, while `injective` reads
    /// [`SymbolRole::locally_injective`], which also counts a label shared with a macro-like
    /// production (`RuleCatalog::all_macro_labels`). CBC-01-T3 removes the difference by reading
    /// `all_macro_labels` here for every claim.
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
    Greater {
        /// Every production below it is locally injective ([`SymbolRole::locally_injective`]),
        /// so two of its applications reach one normal form only through the same production
        /// at the same arguments.
        lessers_locally_injective: bool,
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
    /// Neither the production's own declaration nor an equation other rules make it head
    /// identifies two of its applications with different arguments: it is not a `function`
    /// (whose equations evaluate it), carries no `assoc`, `comm` or `idem` (whose axioms
    /// `generated_axioms` emits for any production carrying them), and heads no `anywhere` or
    /// macro-like equation. Its overload equations are judged separately
    /// ([`OverloadPosition::Greater`]).
    ///
    /// This is the second macro reading CBC-01-T2 keeps unchanged, and it decides `injective`.
    /// It reads the heads under the production's own label, so an unlabelled bracket, whose
    /// other claims read them under its `bracketLabel`, counts none, and it reads a macro-like
    /// equation through `RuleCatalog::all_macro_labels`, so a label shared with a macro-like
    /// production counts although [`EquationHeads::macro_rule`] does not count it. CBC-01-T3
    /// reads both from [`EquationHeads`].
    locally_injective: bool,
}

/// What the emitted theory states about the distinctness of a symbol's applications.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Freeness {
    /// `constructor`, `injective`, the injectivity axiom and disjointness from every other
    /// no-confusion symbol of its sort: no equation heads the symbol.
    Constructor,
    /// An overload-greater with `injective` and the no-confusion axioms but no `constructor`:
    /// its overload equations evaluate it, and every production below it is locally injective.
    OverloadConstructor,
    /// `injective` only.
    Injective,
    /// No distinctness claim.
    None,
    /// Transitional, removed by CBC-01-T3: no-confusion axioms with independent `constructor`
    /// and `injective` flags, for the two states in which CBC-01-T2 keeps no-confusion axioms
    /// without `injective`. An overload-greater over a production that is not locally injective
    /// (`constructor: false`), and a production whose label is shared with a macro-like
    /// production (`constructor: true`), both with `injective: false`.
    Legacy { constructor: bool, injective: bool },
}

impl Freeness {
    /// Whether the declaration carries `constructor`.
    pub(super) fn declares_constructor(self) -> bool {
        match self {
            Self::Constructor => true,
            Self::OverloadConstructor | Self::Injective | Self::None => false,
            Self::Legacy { constructor, .. } => constructor,
        }
    }

    /// Whether the semantic module states the injectivity axiom `σ(X) ∧ σ(Y) → σ(X ∧ Y)` and
    /// disjointness from every other no-confusion symbol of the same sort.
    pub(super) fn has_no_confusion(self) -> bool {
        match self {
            Self::Constructor | Self::OverloadConstructor | Self::Legacy { .. } => true,
            Self::Injective | Self::None => false,
        }
    }

    /// Whether the declaration carries `injective`.
    pub(super) fn declares_injective(self) -> bool {
        match self {
            Self::Constructor | Self::OverloadConstructor | Self::Injective => true,
            Self::None => false,
            Self::Legacy { injective, .. } => injective,
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
                SymbolClaims::syntax_only(
                    name,
                    declared.syntax_freeness(claims.freeness),
                    claims.functional,
                    claims.anywhere,
                )
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

    /// The `injective` claim: the production is locally injective and, when it is an
    /// overload-greater, so is every production below it.
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
        self.locally_injective
            && match self.heads.overload {
                OverloadPosition::NotGreater => true,
                OverloadPosition::Greater {
                    lessers_locally_injective,
                } => lessers_locally_injective,
            }
    }

    /// The freeness of a labelled production that is neither a function, a macro production, a
    /// token nor algebraic: its applications are values exactly when no equation heads it.
    fn base_freeness(self) -> Freeness {
        let injective = self.injective();
        if self.heads.anywhere_rule || self.heads.macro_rule {
            // An `anywhere` or macro-like equation headed by the production may equate its
            // applications with other terms (`plain(X) = done(X)` for a rule
            // `plain(X) => done(X) [macro]`), so they are not free values. Its injectivity
            // reading counts these heads too, except for an unlabelled bracket (CBC-01-T3).
            return if injective {
                Freeness::Injective
            } else {
                Freeness::None
            };
        }
        match (self.heads.overload, injective) {
            (OverloadPosition::NotGreater, true) => Freeness::Constructor,
            // Its label is shared with a macro-like production, which only the injectivity
            // reading counts (CBC-01-T3).
            (OverloadPosition::NotGreater, false) => Freeness::Legacy {
                constructor: true,
                injective: false,
            },
            // The no-confusion axioms of an overload-greater are kept without checking that no
            // production related to it in the overload order has its result sort head, which
            // CBC-01-T3 adds.
            (OverloadPosition::Greater { .. }, true) => Freeness::OverloadConstructor,
            // A production below it is not locally injective (CBC-01-T3 withholds no-confusion).
            (OverloadPosition::Greater { .. }, false) => Freeness::Legacy {
                constructor: false,
                injective: false,
            },
        }
    }

    /// The freeness a bracket's syntax declaration states, given the claims of the production it
    /// declares: that production's freeness, except that a macro-like bracket is declared
    /// `injective` whenever [`SymbolRole::injective`] holds. That reading counts no equation
    /// heads for an unlabelled bracket, while an own label is always the label of a macro-like
    /// production, so only an unlabelled macro-like bracket's declaration is `injective`
    /// (CBC-01-T3 removes the exception).
    fn syntax_freeness(self, freeness: Freeness) -> Freeness {
        match self.kind {
            ProductionKind::MacroProduction => {
                if self.injective() {
                    Freeness::Injective
                } else {
                    Freeness::None
                }
            }
            ProductionKind::Subsort
            | ProductionKind::Builtin
            | ProductionKind::Bracket(_)
            | ProductionKind::Function { .. }
            | ProductionKind::Token { .. }
            | ProductionKind::Unlabelled
            | ProductionKind::Algebraic
            | ProductionKind::Base => freeness,
        }
    }
}

/// The label heads the module's sentences make equation heads.
struct LabelHeads<'a> {
    /// The heads of `anywhere` rules.
    anywhere_rules: BTreeSet<LabelHead>,
    /// The heads of macro-like rules ([`RuleCatalog::macro_labels`]).
    macro_rules: &'a BTreeSet<LabelHead>,
    /// The labels of macro-like productions ([`ProductionCatalog::macro_labels`]).
    macro_productions: &'a BTreeSet<LabelHead>,
}

impl<'a> LabelHeads<'a> {
    fn of(productions: &'a ProductionCatalog<'_>, rules: &'a RuleCatalog<'_>) -> Self {
        Self {
            anywhere_rules: rules
                .rules()
                .filter(|(_, rule)| rule.attributes().has(AttributeKey::Anywhere))
                .map(|(_, rule)| LabelHead::from(&match_rule_label(rule)))
                .collect(),
            macro_rules: rules.macro_labels(),
            macro_productions: productions.macro_labels(),
        }
    }

    /// See [`SymbolRole::locally_injective`].
    fn locally_injective(&self, production: &Sentence) -> bool {
        let Sentence::Production {
            label, attributes, ..
        } = production
        else {
            unreachable!("production catalogs contain productions")
        };
        let heads_equation = label.as_ref().is_some_and(|label| {
            let head = LabelHead::from(label);
            self.anywhere_rules.contains(&head)
                || self.macro_rules.contains(&head)
                || self.macro_productions.contains(&head)
        });
        !attributes.has_any(&[
            AttributeKey::Function,
            AttributeKey::Assoc,
            AttributeKey::Comm,
            AttributeKey::Idem,
        ]) && !heads_equation
    }

    fn role(&self, production: &Sentence, overload: OverloadPosition) -> SymbolRole {
        let kind = ProductionKind::of(production);
        let Sentence::Production {
            label, attributes, ..
        } = production
        else {
            unreachable!("production catalogs contain productions")
        };
        let declared_under = if let ProductionKind::Bracket(BracketName::BracketLabel) = kind {
            attributes
                .label(AttributeKey::BracketLabel)
                .as_ref()
                .map(LabelHead::from)
        } else {
            label.as_ref().map(LabelHead::from)
        };
        SymbolRole {
            kind,
            unbracketed: ProductionKind::of_unbracketed(production),
            labelled: label.is_some(),
            heads: EquationHeads {
                anywhere_rule: declared_under
                    .as_ref()
                    .is_some_and(|head| self.anywhere_rules.contains(head)),
                macro_rule: declared_under
                    .as_ref()
                    .is_some_and(|head| self.macro_rules.contains(head)),
                overload,
            },
            locally_injective: self.locally_injective(production),
        }
    }
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
    /// O(P + R + O²) for P productions, R rules and O elements of the overload order.
    #[must_use]
    pub(super) fn classify(
        productions: &ProductionCatalog<'_>,
        rules: &RuleCatalog<'_>,
        overloads: &OverloadOrder<'_>,
    ) -> Self {
        let heads = LabelHeads::of(productions, rules);
        // Each greater, mapped to whether every production below it is locally injective.
        let mut greaters = BTreeMap::<ProductionId, bool>::new();
        // Invariant: `greaters` maps every greater of a lesser visited so far to whether every visited lesser below it is locally injective; `relations_from` is transitively closed, so one pass covers every chain of overloads, O(O²).
        for lesser in overloads.order().elements() {
            let injective = heads.locally_injective(overloads.production(*lesser));
            for greater in overloads
                .order()
                .relations_from(lesser)
                .into_iter()
                .flatten()
            {
                let all = greaters.entry(*greater).or_insert(true);
                *all = *all && injective;
            }
        }
        let claims = productions
            .productions()
            .map(|(id, production)| {
                let overload = greaters.get(&id).map_or(
                    OverloadPosition::NotGreater,
                    |&lessers_locally_injective| OverloadPosition::Greater {
                        lessers_locally_injective,
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
            /// Every production below it is locally injective.
            lessers_locally_injective: bool,
            /// No production related to it in the overload order has its result sort head.
            /// Neither the predicates CBC-01-T2 deleted nor its claims read it; CBC-01-T3 adds it.
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
                    alone_in_sort: _,
                } => OverloadPosition::Greater {
                    lessers_locally_injective,
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
        /// Whether the production counts as locally injective below an overload-greater.
        locally_injective: bool,
    }

    /// A fact-level restatement of the predicates CBC-01-T2 replaced by [`SymbolRoles`]: the
    /// declaration loops (which `ProductionKind::of` filtered), `symbol_attributes` (the
    /// `constructor`, `injective`, `functional` and `anywhere` attributes, computed with
    /// `ProductionKind::of_unbracketed`), `constructor_productions` (the no-confusion axioms) and
    /// `injectivity_withheld`, each written as it read the facts.
    ///
    /// ```text
    /// fn is_base_constructor(a) = !a.has_any([function, assoc, comm, idem])
    ///
    /// injectivity_withheld: withheld = { p | heads_equation(p) }
    ///     ∪ { g > l | !(is_base_constructor(l) && !heads_equation(l)) }
    ///   heads_equation(p) = p is labelled && its label ∈ anywhere_labels ∪ all_macro_labels
    ///   all_macro_labels = RuleCatalog::macro_labels ∪ ProductionCatalog::macro_labels
    ///
    /// symbol_attributes(label = the declaration's label, kind = of_unbracketed(p)):
    ///   injective   = is_base_constructor && id ∉ withheld
    ///   anywhere    = id ∈ overloaded_greater || label ∈ anywhere_labels
    ///   constructor = is_base_constructor && !kind.is_macro_like()
    ///                 && label ∉ RuleCatalog::macro_labels && !anywhere && kind is not Token
    ///   functional  = !function || total
    ///
    /// constructor_productions = { p | of(p) == Base && own label ∉ RuleCatalog::macro_labels
    ///                                 && own label ∉ anywhere heads }
    /// ```
    fn restated(production: ProductionFacts, heads: HeadFacts) -> Stated {
        let p = production;
        let builtin = p.label && p.builtin_label;
        let subsort = !p.label && p.subsort_shape;
        // Labelled loop: `of` is Builtin, Bracket(OwnLabel) or a semantic kind; unlabelled
        // loop: `of` is Bracket(BracketLabel).
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
        let declared = !matches!(declaration, Declaration::None);
        let own = p.label;
        let (greater, lessers_locally_injective) = match heads.overload {
            Overload::NotGreater => (false, true),
            Overload::Greater {
                lessers_locally_injective,
                ..
            } => (true, lessers_locally_injective),
        };
        let base_constructor = !p.function && p.algebraic.is_none();
        // The heads under the production's own label, as `injectivity_withheld` read them; a
        // labelled macro-like production's label is one of `ProductionCatalog::macro_labels`.
        let own_macro_production = own && (heads.shared_macro_label || p.macro_like);
        let heads_equation =
            own && (heads.anywhere_rule || heads.macro_rule || own_macro_production);
        let locally_injective = base_constructor && !heads_equation;
        let withheld = heads_equation || (greater && !lessers_locally_injective);
        // `symbol_attributes` reads the declaration's label: own, or `bracketLabel`.
        let anywhere = greater || heads.anywhere_rule;
        // `of_unbracketed` of a declared production is Function { macro_like }, MacroProduction,
        // Token, Algebraic or Base.
        let macro_like = p.macro_like;
        let token = p.token && !p.function && !p.macro_like;
        let constructor =
            base_constructor && !macro_like && !heads.macro_rule && !anywhere && !token;
        let injective = base_constructor && !withheld;
        let functional = !p.function || p.total;
        let of_is_base = own
            && !builtin
            && !p.bracket
            && !p.function
            && !p.macro_like
            && !p.token
            && p.algebraic.is_none();
        let no_confusion = of_is_base && !heads.macro_rule && !heads.anywhere_rule;
        Stated {
            declaration,
            constructor: declared && constructor,
            injective: declared && injective,
            functional: declared && functional,
            anywhere: declared && anywhere,
            no_confusion,
            locally_injective,
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
            locally_injective: role.locally_injective,
        }
    }

    /// The role of one production of a module whose other sentences state `heads`.
    fn role(production: ProductionFacts, heads: HeadFacts) -> SymbolRole {
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
        let label_heads = LabelHeads {
            anywhere_rules,
            macro_rules: &macro_rules,
            macro_productions: catalog.macro_labels(),
        };
        label_heads.role(&sentence, heads.position())
    }

    /// The claims table reproduces, on every combination of production and head facts, what
    /// the predicates it replaced stated.
    #[test]
    fn claims_restate_the_replaced_predicates_on_every_combination_of_facts() {
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

    /// Every variant, listed through an exhaustive match so that a new variant must be added.
    fn every_freeness() -> Vec<Freeness> {
        let listed = |freeness: Freeness| match freeness {
            Freeness::Constructor
            | Freeness::OverloadConstructor
            | Freeness::Injective
            | Freeness::None
            | Freeness::Legacy { .. } => freeness,
        };
        let mut all = vec![
            listed(Freeness::Constructor),
            listed(Freeness::OverloadConstructor),
            listed(Freeness::Injective),
            listed(Freeness::None),
        ];
        for constructor in [false, true] {
            for injective in [false, true] {
                all.push(listed(Freeness::Legacy {
                    constructor,
                    injective,
                }));
            }
        }
        all
    }

    #[test]
    fn constructor_implies_no_confusion_implies_injective_outside_legacy() {
        for freeness in every_freeness() {
            match freeness {
                Freeness::Legacy { .. } => continue,
                Freeness::Constructor
                | Freeness::OverloadConstructor
                | Freeness::Injective
                | Freeness::None => {}
            }
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
}
