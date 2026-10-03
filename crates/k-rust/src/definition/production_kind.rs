//! This definition-layer module holds no algorithm of its own: the kind of a production is a
//! constant number of attribute lookups, and [`NoJunkAxiom::of`] is one scan of a production
//! catalog and one of a sort catalog per sort, which the `kompile.kore.axioms` card of its caller
//! (`no_junk_axioms`) counts.
//!
//! What a production's own declaration makes its symbol, decided once.
//!
//! [`ProductionKind::of`] classifies a production by its declaration alone, before rules and
//! overloads are consulted, in one precedence order. Every consumer that decides a claim of the
//! emitted theory from whether a production is a subsort, a matching-logic builtin, a bracket, a
//! function, a macro production or a token reads that decision from the kind, so no two claims
//! about one production can rest on two different readings of its attributes.
//! [`ResultSorts`] reads the result sort under the production's own binder, so a result that
//! is a formal parameter contributes at every sort, rather than a head with that spelling.
//! [`NoJunkAxiom`] derives a sort's alternatives ([`SortGenerators`]) from those classifications:
//! schemas extend existing axioms at free sorts, and a generator with unbound parameters makes
//! an existing axiom unstatable.

#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::BTreeMap;

use super::{
    AttributeKey, Attributes, PartialOrder, ProductionCatalog, ProductionId, ProductionItem,
    Sentence, SortCatalog, SortHead,
};
use crate::kast::{InternalLabel, Label, Sort};
use crate::kompile::Injectable;

/// The concrete sorts whose values a production's applications are, read from its result sort
/// and its own binder.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ResultSorts {
    /// The sorts with this head: the result is closed (`Foo`) or applies a head to arguments
    /// that may mention parameters (`Box{W}`, `MInt{W}`), so every instance keeps the head.
    Head(SortHead),
    /// Every sort: the result is one of the production's own parameters
    /// (`syntax {S} S ::= wrap(S)`, `amb`, `#location`), so instantiating it at σ gives a
    /// production of σ.
    Every,
}

impl ResultSorts {
    pub(crate) fn of(production: &Sentence) -> Self {
        let Sentence::Production {
            parameters, sort, ..
        } = production
        else {
            unreachable!("result sorts classify productions")
        };
        if parameters.contains(sort) {
            Self::Every
        } else {
            Self::Head(SortHead::from(sort))
        }
    }
}

/// Whether each application of a function production denotes exactly one value, as its
/// declaration states.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Totality {
    /// The declaration carries `total`.
    Total,
    /// The declaration carries no `total`: an application may denote no value.
    Partial,
}

/// The name a bracket's syntax-module declaration is made under.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum BracketName {
    /// The bracket is labelled, and its label names the declaration.
    OwnLabel,
    /// The bracket is unlabelled and carries a readable `bracketLabel`, which names the
    /// declaration.
    BracketLabel,
    /// The bracket has neither, so it is declared in neither module.
    Undeclared,
}

/// What a production's own declaration makes its symbol, before rules and overloads.
///
/// [`ProductionKind::of`] tests the variants in declaration order; the first that holds is the
/// kind. Where one combination of attributes would fit two variants, the earlier variant keeps the
/// later one's fact as a field (`Function { macro_like }`, `Token { algebraic }`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ProductionKind {
    /// Unlabelled `S ::= T`: an injection, stated by the subsort axiom; declares no symbol.
    Subsort,
    /// Labelled with a matching-logic connective: the prelude declares it.
    Builtin,
    /// Carries `bracket`, which only groups program or rule text.
    ///
    /// Every parser erases a bracket node before a term exists, and the generated bison grammar
    /// reduces a bracket to its child, so no term the frontend builds contains a bracket's
    /// symbol, whatever its label. A bracket's label (or `bracketLabel` when it has none) names
    /// only its syntax-module declaration and its priority and associativity tag: it is never
    /// declared in the semantic module, and no generated axiom mentions it.
    Bracket(BracketName),
    /// Carries `function`: its applications are evaluated by its equations.
    ///
    /// `macro_like` keeps a macro-like attribute, which the declaration still carries as `macro`
    /// and which keeps the label from counting as defined in the definedness judgement.
    Function {
        totality: Totality,
        macro_like: bool,
    },
    /// Carries a macro-like attribute: its applications are replaced by its macro equations.
    MacroProduction,
    /// Carries `token`: it defines the lexical form of its sort's domain values.
    ///
    /// Every term it parses is a domain value, its sort is declared `hasDomainValues`, and its
    /// label is never applied. Its symbol therefore denotes no element of the term algebra, and
    /// classifying it as a constructor would assert a rigid element provably distinct from every
    /// domain value of the sort. `algebraic` keeps an `assoc`/`comm`/`idem` attribute, which
    /// withholds `injective`.
    Token { algebraic: bool },
    /// Unlabelled and none of the above: declares no symbol.
    Unlabelled,
    /// Carries `assoc`, `comm` or `idem`: its algebraic axioms identify applications with
    /// different arguments.
    Algebraic,
    /// Any other labelled production: its applications are values unless an equation heads it.
    Base,
}

/// A production's alternative in its sort's no-junk axiom.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NoJunk {
    /// `\top`: the production parses domain values of its sort, which no symbol generates.
    DomainValues,
    /// The production's symbol applied to fresh variables.
    Generator,
    /// The production's applications are no value of the sort that another alternative does not
    /// already cover, or it declares no symbol.
    Absent,
}

impl ProductionKind {
    /// Whether rewrite steps meet applications of this kind as terms, so that a rewrite rule, and in
    /// particular the heating and cooling rules of an evaluation context, can match one: `Base` and
    /// `Algebraic`. A function application is evaluated by its equations, a macro-like application
    /// is expanded before rewriting, a bracket is erased by every parser, a token production's terms
    /// are domain values, a builtin is a matching-logic connective, and a subsort or unlabelled
    /// production declares no symbol.
    pub(crate) fn rewrite_steps_meet_applications(self) -> bool {
        match self {
            Self::Base | Self::Algebraic => true,
            Self::Subsort
            | Self::Builtin
            | Self::Bracket(_)
            | Self::Function { .. }
            | Self::MacroProduction
            | Self::Token { .. }
            | Self::Unlabelled => false,
        }
    }

    /// The kind of `production`.
    ///
    /// # Panics
    ///
    /// When `production` is not a [`Sentence::Production`]; every caller reads a production
    /// catalog.
    pub(crate) fn of(production: &Sentence) -> Self {
        Self::classify(production, true)
    }

    /// [`ProductionKind::of`] with the `bracket` test skipped: the kind whose claims a bracket's
    /// syntax-module declaration carries.
    ///
    /// That declaration is made under the bracket's label, or under its `bracketLabel` when it
    /// has none, so a readable `bracketLabel` counts as a label here: an unlabelled bracket is
    /// classified as the labelled production its declaration states, never as `Unlabelled`.
    pub(crate) fn of_unbracketed(production: &Sentence) -> Self {
        Self::classify(production, false)
    }

    fn classify(production: &Sentence, bracket_test: bool) -> Self {
        let Sentence::Production {
            label,
            items,
            attributes,
            ..
        } = production
        else {
            unreachable!("production kinds classify productions")
        };
        if label.is_none() && matches!(items.as_slice(), [ProductionItem::NonTerminal { .. }]) {
            return Self::Subsort;
        }
        if label
            .as_ref()
            .is_some_and(|label| is_builtin_label(&label.name))
        {
            return Self::Builtin;
        }
        if bracket_test && attributes.has(AttributeKey::Bracket) {
            return Self::Bracket(if label.is_some() {
                BracketName::OwnLabel
            } else if attributes.label(AttributeKey::BracketLabel).is_some() {
                BracketName::BracketLabel
            } else {
                BracketName::Undeclared
            });
        }
        let macro_like = attributes.has_any(&AttributeKey::MACRO_LIKE);
        if attributes.has(AttributeKey::Function) {
            return Self::Function {
                totality: if attributes.has(AttributeKey::Total) {
                    Totality::Total
                } else {
                    Totality::Partial
                },
                macro_like,
            };
        }
        if macro_like {
            return Self::MacroProduction;
        }
        let algebraic = is_algebraic(attributes);
        if attributes.has(AttributeKey::Token) {
            return Self::Token { algebraic };
        }
        if label.is_none()
            && (bracket_test || attributes.label(AttributeKey::BracketLabel).is_none())
        {
            return Self::Unlabelled;
        }
        if algebraic {
            return Self::Algebraic;
        }
        Self::Base
    }

    /// Whether the semantic declaration carries `functional` and the functional axiom: every
    /// application of the symbol denotes exactly one value.
    ///
    /// A symbol that is not declared in the semantic module (a subsort, a builtin, a bracket or
    /// an unlabelled production) has no such claim.
    pub(crate) fn functional(self) -> bool {
        match self {
            Self::Subsort | Self::Builtin | Self::Bracket(_) | Self::Unlabelled => false,
            Self::Function { totality, .. } => totality == Totality::Total,
            Self::MacroProduction | Self::Token { .. } | Self::Algebraic | Self::Base => true,
        }
    }

    /// `MacroProduction`, or `Function` with `macro_like`.
    pub(crate) fn is_macro_like(self) -> bool {
        match self {
            Self::MacroProduction => true,
            Self::Function { macro_like, .. } => macro_like,
            Self::Subsort
            | Self::Builtin
            | Self::Bracket(_)
            | Self::Token { .. }
            | Self::Unlabelled
            | Self::Algebraic
            | Self::Base => false,
        }
    }

    /// The production's alternative in its sort's no-junk axiom.
    ///
    /// A token production parses domain values, so `\top` is its complete alternative whatever
    /// its label. A function or macro production is evaluated or expanded away, a bracket is
    /// erased, a builtin is no symbol of the sort, and a subsort production is covered by the
    /// injection alternatives, so none of them is listed.
    pub(crate) fn no_junk(self) -> NoJunk {
        match self {
            Self::Token { .. } => NoJunk::DomainValues,
            Self::Algebraic | Self::Base => NoJunk::Generator,
            Self::Subsort
            | Self::Builtin
            | Self::Bracket(_)
            | Self::Function { .. }
            | Self::MacroProduction
            | Self::Unlabelled => NoJunk::Absent,
        }
    }

    /// Whether a named nonterminal of a labelled production of this kind gets a field
    /// projection `field(source(X0, .., Xn)) = Xi`.
    ///
    /// The projection's equation applies the source's symbol, so the source must declare a
    /// symbol of the semantic module whose applications are built from their arguments. A base
    /// or algebraic production declares such a symbol, and so does a labelled token production:
    /// a program parses its text as a domain value, but its label is still a declared symbol a
    /// rule may apply. A bracket is erased by every parser and declared only in the syntax
    /// module, so no term applies it and a projection through it would name a symbol the
    /// semantic module does not have. A function or a macro production is evaluated or expanded
    /// away, so an application of it is not the term its arguments build, and reading an
    /// argument back out of it is no projection. A subsort or unlabelled production declares no
    /// symbol, and a builtin is a matching-logic connective, not a term constructor.
    ///
    /// Eligibility reads the declaration alone; whether the source's own equations identify
    /// applications with different arguments is not decided here. The rule grammar and the
    /// projection pass both read this predicate through [`FieldProjectionSource::of`], which also
    /// requires the source to bind no sort parameter, so they agree on which productions a field
    /// projection passes through.
    pub(crate) fn admits_field_projection(self) -> bool {
        match self {
            Self::Base | Self::Algebraic | Self::Token { .. } => true,
            Self::Subsort
            | Self::Builtin
            | Self::Bracket(_)
            | Self::Function { .. }
            | Self::MacroProduction
            | Self::Unlabelled => false,
        }
    }
}

/// A labelled production whose named nonterminals get field projections
/// `project:<label>:<field>`: its kind admits one ([`ProductionKind::admits_field_projection`]),
/// it binds no sort parameter, and it has a named nonterminal.
///
/// A production's `parameters` are sort variables bound by that sentence alone, spelled like
/// sorts. A source with sort parameters (`syntax {W} Foo ::= pick(x: MInt{W}, y: Int)`) is a
/// family of symbols `pick{W}`, one per instantiation: the sort of a field that mentions a
/// parameter depends on the member that built the value, and the equation of every field
/// quantifies over the parameters, so no projection of a fixed signature inverts the family.
/// Copying such a field's sort into a projection with no binder would turn `W` into a concrete
/// sort named `W`. A source with sort parameters therefore gets no projection; its named
/// nonterminals still name its record syntax. For the same reason it is never judged the sole
/// generator of its sort: it generates one sort per instantiation, and each instance may have
/// further productions of its own, so no single no-junk axiom makes it sole.
///
/// The fields are private, so [`FieldProjectionSource::of`] is the only way to obtain one, and
/// [`FieldProjectionSource::projection_production`] is the only builder of a field projection
/// production. Every sort that production mentions is a sort of the source, which binds no
/// parameter, so no projection mentions a sort parameter.
#[derive(Clone, Copy, Debug)]
pub(crate) struct FieldProjectionSource<'a> {
    label: &'a Label,
    sort: &'a Sort,
    items: &'a [ProductionItem],
}

impl<'a> FieldProjectionSource<'a> {
    /// `Some` exactly when `sentence` is a labelled production, its kind admits a field
    /// projection, its `parameters` are empty, and it has a named nonterminal.
    pub(crate) fn of(sentence: &'a Sentence) -> Option<Self> {
        let Sentence::Production {
            label: Some(label),
            parameters,
            sort,
            items,
            ..
        } = sentence
        else {
            return None;
        };
        if !parameters.is_empty() || !ProductionKind::of(sentence).admits_field_projection() {
            return None;
        }
        let source = Self { label, sort, items };
        source
            .nonterminals()
            .any(|(_, name)| name.is_some())
            .then_some(source)
    }

    /// The source's label, which the projection equations apply.
    pub(crate) fn label(&self) -> &'a Label {
        self.label
    }

    /// The source's result sort, the argument sort of each of its projections.
    pub(crate) fn sort(&self) -> &'a Sort {
        self.sort
    }

    /// The source's nonterminals in item order, with their names.
    pub(crate) fn nonterminals(&self) -> impl Iterator<Item = (&'a Sort, Option<&'a str>)> {
        self.items.iter().filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, name } => Some((sort, name.as_deref())),
            ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
        })
    }

    /// `field_sort ::= name "(" sort ")"`, labelled `project:<label>:<name>`, with no sort
    /// parameters and `function` marked on top of `attributes`.
    ///
    /// `field_sort` is the sort of the source's nonterminal named `name`, so every sort the
    /// production mentions is a sort of the source, which binds no sort parameter.
    pub(crate) fn projection_production(
        &self,
        field_sort: &Sort,
        name: &str,
        mut attributes: Attributes,
    ) -> Sentence {
        debug_assert!(
            self.nonterminals()
                .any(|(sort, field)| sort == field_sort && field == Some(name)),
            "`{name}: {field_sort}` is no named nonterminal of `{}`",
            self.label.name
        );
        attributes.mark(AttributeKey::Function);
        Sentence::Production {
            label: Some(Label::field_projection(&self.label.name, name)),
            parameters: Vec::new(),
            sort: field_sort.clone(),
            items: vec![
                ProductionItem::Terminal(name.to_owned()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: self.sort.clone(),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
            attributes,
        }
    }
}

fn is_algebraic(attributes: &Attributes) -> bool {
    attributes.has_any(&[AttributeKey::Assoc, AttributeKey::Comm, AttributeKey::Idem])
}

/// Whether `label` is a matching-logic connective, which the prelude declares.
pub(crate) fn is_builtin_label(label: &str) -> bool {
    InternalLabel::of(label).is_some_and(|label| InternalLabel::MATCHING_LOGIC.contains(&label))
}

/// Bind the sort parameters `parameters` occurring in `pattern` so that `pattern` becomes
/// `concrete`, extending `substitution`; `None` when no binding consistent with `substitution`
/// does.
// Invariant: each call matches one node of `pattern` against `concrete` and recurses only into
// their `parameters`, so the finite `pattern` bounds the calls; `substitution` binds every element
// of `parameters` met so far to one concrete sort.
pub(crate) fn match_sort_parameters(
    pattern: &Sort,
    concrete: &Sort,
    parameters: &[Sort],
    substitution: &mut BTreeMap<Sort, Sort>,
) -> Option<()> {
    if parameters.contains(pattern) {
        return match substitution.get(pattern) {
            Some(existing) if existing != concrete => None,
            Some(_) => Some(()),
            None => {
                substitution.insert(pattern.clone(), concrete.clone());
                Some(())
            }
        };
    }
    if pattern.name != concrete.name || pattern.parameters.len() != concrete.parameters.len() {
        return None;
    }
    for (pattern, concrete) in pattern.parameters.iter().zip(&concrete.parameters) {
        match_sort_parameters(pattern, concrete, parameters, substitution)?;
    }
    Some(())
}

/// Whether `sort`, or any sort inside it at any depth, is an element of `parameters`.
///
/// This is the one test of whether a sort taken from a sentence mentions a sort parameter that
/// sentence binds: a parameter may occur as the sort itself (`W`) or nested inside an argument
/// (`MInt{MInt{W}}`).
// Invariant: each call tests one node of `sort` and recurses only into its `parameters`, so the
// finite `sort` bounds the calls.
pub(crate) fn mentions_parameter(sort: &Sort, parameters: &[Sort]) -> bool {
    parameters.contains(sort)
        || sort
            .parameters
            .iter()
            .any(|argument| mentions_parameter(argument, parameters))
}

/// A generator of a concrete sort with the substitution that binds every one of its sort
/// parameters so that its result sort is that sort.
///
/// Minted only by [`NoJunkAxiom::of`], after matching the generator's result sort against the
/// sort bound each element of the production's `parameters`, so applying the substitution to any
/// sort of the production leaves no sort parameter of it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ClosedInstance {
    production: ProductionId,
    substitution: BTreeMap<Sort, Sort>,
}

impl ClosedInstance {
    /// The generator.
    pub(crate) fn production(&self) -> ProductionId {
        self.production
    }

    /// The binding of each of the generator's sort parameters, with every parameter a key.
    pub(crate) fn substitution(&self) -> &BTreeMap<Sort, Sort> {
        &self.substitution
    }
}

/// One alternative of a concrete sort's no-junk axiom, in axiom order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NoJunkAlternative<'g> {
    /// `\top`: the domain values of the sort.
    DomainValues,
    /// The symbol of this production, instantiated at the sort by the instance's substitution,
    /// applied to fresh variables.
    Generator(&'g ClosedInstance),
    /// The injection of a strict subsort into the sort, along the subsort axioms of the emitted
    /// theory.
    Injection(&'g Injectable),
}

/// An alternative a production of the sort contributes.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Alternative {
    DomainValues,
    Generator(ClosedInstance),
}

/// What the no-junk axiom of one concrete sort can state.
///
/// A schema whose result is its own parameter contributes at every free sort that already has
/// an own alternative, injection or token-sort `\top`; it never creates an axiom on its own.
/// Hooked and domain-value sorts have fixed values, so no schema generator is listed there.
///
/// A no-junk axiom is one sentence `axiom{} \or{S}(..)` with no sort parameters, so each
/// alternative must be a pattern over closed sorts. A generator whose result sort, matched against
/// the sort, binds every one of its sort parameters contributes one such pattern. A generator with
/// a parameter that the match leaves free (`syntax {W} Foo ::= pick(MInt{W}, Int)` at `Foo`, or a
/// phantom `syntax {W} Foo ::= pick(Int)`, whose symbols `pick{W}` still differ per `W`) puts its
/// application at every instantiation of that parameter among the sort's values, which no finite
/// disjunction lists. Listing only some instantiations, or leaving that generator out, would state
/// a false axiom, and a false finite no-junk axiom lets a prover discard a branch that has a
/// solution, and could make a sibling the sole generator whose field projections are then judged
/// total. Stating no axiom only loses that pruning for the sort, so it is the sound choice.
#[must_use]
#[derive(Debug)]
pub(crate) enum NoJunkAxiom {
    /// Every value of the sort is one of these alternatives (none: the sort gets no axiom).
    Stated(SortGenerators),
    /// The generator `generator`'s sort parameters are not all bound by matching its result sort
    /// against the sort, so the theory states no no-junk axiom for the sort.
    Unstatable { generator: ProductionId },
}

impl NoJunkAxiom {
    /// What the no-junk axiom of the concrete sort `sort` can state, in a module whose
    /// productions, sorts and subsort order are `productions`, `sorts` and `subsorts`.
    ///
    /// A parametric production generates `sort` when its result sort matches `sort` by
    /// instantiating its sort parameters ([`match_sort_parameters`]); when that match leaves an
    /// element of its `parameters` unbound, an existing axiom is [`NoJunkAxiom::Unstatable`].
    /// A sort-polymorphic generator contributes only at free sorts with an existing axiom.
    pub(crate) fn of(
        productions: &ProductionCatalog<'_>,
        sorts: &SortCatalog<'_>,
        subsorts: &PartialOrder<Sort>,
        sort: &Sort,
    ) -> Self {
        match SortGenerators::of(productions, sorts, subsorts, sort) {
            Ok(generators) => Self::Stated(generators),
            Err(generator) => Self::Unstatable { generator },
        }
    }
}

/// The no-junk alternatives of one concrete sort whose generators all instantiate closed at it:
/// every value of the sort is one of them.
///
/// The productions of the sort contribute their [`ProductionKind::no_junk`] alternatives in
/// catalog order, with a single `\top` at the position of the first token production however many
/// token productions the sort has, since each of them contributes the same alternative. The
/// closed schema instances follow in catalog order at free sorts, with a schema `\top` only
/// when the sort has none of its own. Schemas never create an axiom. The
/// injections of the strict subsorts along subsort axioms follow ([`injected_subsorts`]), and a
/// sort whose own declaration carries `token` but
/// that has no token production ends with `\top`. Only [`NoJunkAxiom::of`] builds one, so a sort
/// with a generator that does not instantiate closed ([`NoJunkAxiom::Unstatable`]) has none.
#[derive(Debug)]
pub(crate) struct SortGenerators {
    alternatives: Vec<Alternative>,
    injections: Vec<Injectable>,
    token_sort: bool,
}

impl SortGenerators {
    /// The no-junk alternatives of the concrete sort `sort`, or `Err` with a generator whose
    /// sort parameters matching its result sort against `sort` leaves unbound.
    fn of(
        productions: &ProductionCatalog<'_>,
        sorts: &SortCatalog<'_>,
        subsorts: &PartialOrder<Sort>,
        sort: &Sort,
    ) -> Result<Self, ProductionId> {
        let head = SortHead::from(sort);
        let closed = sorts.has_fixed_values(&head);
        let mut alternatives = Vec::new();
        let mut schemas = Vec::new();
        let mut schema_unstatable = None;
        // Invariant: the own and schema lists each keep catalog order and only closed instances,
        // with at most one domain-values alternative each. `schema_unstatable` records the first
        // schema with an unbound parameter; it matters only if an own alternative, injection or
        // token-sort top states an axiom. This scan runs once per sort, O(|productions|).
        for (id, production) in productions.productions() {
            let Sentence::Production {
                parameters,
                sort: production_sort,
                ..
            } = production
            else {
                unreachable!("production catalogs contain productions")
            };
            let schema = match ResultSorts::of(production) {
                ResultSorts::Head(h) if h != head => continue,
                ResultSorts::Head(_) => false,
                ResultSorts::Every => true,
            };
            let destination = if schema {
                &mut schemas
            } else {
                &mut alternatives
            };
            match ProductionKind::of(production).no_junk() {
                NoJunk::DomainValues => {
                    if !destination.contains(&Alternative::DomainValues) {
                        destination.push(Alternative::DomainValues);
                    }
                }
                NoJunk::Generator => {
                    if schema && closed {
                        continue;
                    }
                    let mut substitution = BTreeMap::new();
                    if match_sort_parameters(production_sort, sort, parameters, &mut substitution)
                        .is_none()
                    {
                        continue;
                    }
                    // Every element of `parameters`, not only those the items mention: a phantom
                    // parameter still indexes distinct symbols.
                    if !parameters
                        .iter()
                        .all(|parameter| substitution.contains_key(parameter))
                    {
                        if schema {
                            schema_unstatable.get_or_insert(id);
                            continue;
                        }
                        return Err(id);
                    }
                    destination.push(Alternative::Generator(ClosedInstance {
                        production: id,
                        substitution,
                    }));
                }
                NoJunk::Absent => {}
            }
        }
        let token_sort = !alternatives.contains(&Alternative::DomainValues)
            && sorts
                .attributes_for(&head)
                .is_some_and(|attributes| attributes.has(AttributeKey::Token));
        let injections = injected_subsorts(sorts, subsorts, sort);
        if alternatives.is_empty() && injections.is_empty() && !token_sort {
            return Ok(Self {
                alternatives,
                injections,
                token_sort,
            });
        }
        if let Some(generator) = schema_unstatable {
            return Err(generator);
        }
        let own_domain_values = token_sort || alternatives.contains(&Alternative::DomainValues);
        alternatives.extend(
            schemas.into_iter().filter(|alternative| {
                !own_domain_values || *alternative != Alternative::DomainValues
            }),
        );
        Ok(Self {
            alternatives,
            injections,
            token_sort,
        })
    }

    /// Whether the sort has no alternative at all, so that it gets no no-junk axiom.
    pub(crate) fn is_empty(&self) -> bool {
        self.alternatives.is_empty() && self.injections.is_empty() && !self.token_sort
    }

    /// The alternatives in axiom order.
    pub(crate) fn alternatives(&self) -> impl Iterator<Item = NoJunkAlternative<'_>> {
        self.alternatives
            .iter()
            .map(|alternative| match alternative {
                Alternative::DomainValues => NoJunkAlternative::DomainValues,
                Alternative::Generator(instance) => NoJunkAlternative::Generator(instance),
            })
            .chain(self.injections.iter().map(NoJunkAlternative::Injection))
            .chain(self.token_sort.then_some(NoJunkAlternative::DomainValues))
    }

    /// The production that is the only alternative of the sort's no-junk axiom, if there is one.
    ///
    /// Then every value of the sort is an application of that production's symbol, which is what
    /// makes each field projection through it total.
    pub(crate) fn sole_generator(&self) -> Option<ProductionId> {
        if self.injections.is_empty()
            && !self.token_sort
            && let [Alternative::Generator(instance)] = self.alternatives.as_slice()
        {
            Some(instance.production())
        } else {
            None
        }
    }
}

/// The injections of the strict subsorts of `sort` that are alternatives of its no-junk axiom, in
/// the sort catalog's order: one for every declared strict subsort from which a chain of subsort
/// axioms of the emitted theory leads to `sort` ([`Injectable::between`]).
///
/// An alternative is a disjunct of an axiom stating what every value of `sort` is, so it may only
/// name an embedding the theory defines. A declared subsort without such a chain is left out: the
/// theory has no subsort axiom into `K`, whose values are sequences of `KItem`s, so `K` gets no
/// injection alternative, and a sort above `K` gets none from the sorts below `K` (its values of
/// those sorts are covered by the alternative for `K`). The declared order bounds the candidates:
/// a subsort axiom is emitted only for a declared subsort, while the witness also counts the
/// `S < KItem` subsorts that a definition declares only once `subsort KItem` has run.
///
/// This is the one place that enumerates the injection alternatives.
fn injected_subsorts(
    sorts: &SortCatalog<'_>,
    subsorts: &PartialOrder<Sort>,
    sort: &Sort,
) -> Vec<Injectable> {
    sorts
        .sorted_all_sorts()
        .filter(|subsort| subsorts.less_than(subsort, sort))
        .filter_map(|subsort| Injectable::between(subsort, sort, subsorts))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn production(
        label: Option<&str>,
        sort: &str,
        items: Vec<ProductionItem>,
        keys: &[AttributeKey],
    ) -> Sentence {
        let mut attributes = Attributes::default();
        for key in keys {
            attributes.insert(key.as_str(), serde_json::Value::String(String::new()));
        }
        Sentence::Production {
            label: label.map(Label::new),
            parameters: Vec::new(),
            sort: Sort::new(sort),
            items,
            attributes,
        }
    }

    fn token(label: &str, regex: &str) -> Sentence {
        production(
            Some(label),
            "Id",
            vec![ProductionItem::regex(regex)],
            &[AttributeKey::Token],
        )
    }

    fn no_junk_axiom(
        productions: &[&Sentence],
        sorts: &SortCatalog<'_>,
        sort: &Sort,
    ) -> NoJunkAxiom {
        let catalog = ProductionCatalog::from_visible(productions.iter().copied());
        let subsorts = PartialOrder::new(std::iter::empty()).expect("no subsort cycle");
        NoJunkAxiom::of(&catalog, sorts, &subsorts, sort)
    }

    fn generators(
        productions: &[&Sentence],
        sorts: &SortCatalog<'_>,
        sort: &Sort,
    ) -> SortGenerators {
        match no_junk_axiom(productions, sorts, sort) {
            NoJunkAxiom::Stated(generators) => generators,
            NoJunkAxiom::Unstatable { generator } => {
                panic!("expected a statable axiom, found the open generator {generator:?}")
            }
        }
    }

    /// The alternatives with each generator named by its production.
    #[derive(Debug, Eq, PartialEq)]
    enum Named {
        DomainValues,
        Generator(ProductionId),
        Injection,
    }

    fn named(generators: &SortGenerators) -> Vec<Named> {
        generators
            .alternatives()
            .map(|alternative| match alternative {
                NoJunkAlternative::DomainValues => Named::DomainValues,
                NoJunkAlternative::Generator(instance) => Named::Generator(instance.production()),
                NoJunkAlternative::Injection(_) => Named::Injection,
            })
            .collect()
    }

    fn declaration(parameters: &[&str], sort: Sort) -> Sentence {
        Sentence::SyntaxSort {
            parameters: parameters.iter().map(|name| Sort::new(*name)).collect(),
            sort,
            attributes: Attributes::default(),
        }
    }

    fn parametric_production(
        label: &str,
        parameters: &[&str],
        sort: Sort,
        arguments: Vec<Sort>,
    ) -> Sentence {
        Sentence::Production {
            label: Some(Label::new(label)),
            parameters: parameters.iter().map(|name| Sort::new(*name)).collect(),
            sort,
            items: arguments
                .into_iter()
                .map(|sort| ProductionItem::NonTerminal { sort, name: None })
                .collect(),
            attributes: Attributes::default(),
        }
    }

    fn schema_token(label: &str, regex: &str) -> Sentence {
        let mut schema = token(label, regex);
        let Sentence::Production {
            parameters, sort, ..
        } = &mut schema
        else {
            unreachable!()
        };
        *parameters = vec![Sort::new("S")];
        *sort = Sort::new("S");
        schema
    }

    #[test]
    fn result_sorts_are_classified_under_the_productions_own_binder() {
        let formal = Sort::new("S");
        let wrap = parametric_production("wrap", &["S"], formal.clone(), vec![formal]);
        assert_eq!(ResultSorts::of(&wrap), ResultSorts::Every);
        let boxed = Sort::with_parameters("Box", vec![Sort::new("W")]);
        let r#box = parametric_production("box", &["W"], boxed.clone(), vec![Sort::new("W")]);
        assert_eq!(
            ResultSorts::of(&r#box),
            ResultSorts::Head(SortHead::from(&boxed))
        );

        let foo = Sort::new("Foo");
        let declared = declaration(&[], foo.clone());
        let sorts = SortCatalog::from_visible([&declared]);
        assert!(sorts.attributes_for(&SortHead::from(&foo)).is_some());
        let w = parametric_production("w", &["Foo"], foo.clone(), vec![foo.clone()]);
        assert_eq!(ResultSorts::of(&w), ResultSorts::Every);
        let g = parametric_production("g", &[], foo.clone(), Vec::new());
        assert_eq!(ResultSorts::of(&g), ResultSorts::Head(SortHead::from(&foo)));
    }

    #[test]
    fn polymorphic_generators_extend_free_sorts_with_closed_instances() {
        let foo = Sort::new("Foo");
        let declared = declaration(&[], foo.clone());
        let sorts = SortCatalog::from_visible([&declared]);
        let g = parametric_production("g", &[], foo.clone(), Vec::new());
        let wrap = parametric_production("wrap", &["S"], Sort::new("S"), vec![Sort::new("S")]);
        for (order, own_id, schema_id) in [([&g, &wrap], 0, 1), ([&wrap, &g], 1, 0)] {
            let generated = generators(&order, &sorts, &foo);
            assert_eq!(
                named(&generated),
                [
                    Named::Generator(ProductionId(own_id)),
                    Named::Generator(ProductionId(schema_id))
                ]
            );
            let instances = generated
                .alternatives()
                .map(|alternative| match alternative {
                    NoJunkAlternative::Generator(instance) => instance.substitution().clone(),
                    NoJunkAlternative::DomainValues | NoJunkAlternative::Injection(_) => {
                        panic!("expected a generator")
                    }
                })
                .collect::<Vec<_>>();
            assert_eq!(
                instances,
                [
                    BTreeMap::new(),
                    BTreeMap::from([(Sort::new("S"), foo.clone())])
                ]
            );
            assert_eq!(generated.sole_generator(), None);
        }
    }

    #[test]
    fn schemas_do_not_create_an_axiom_for_a_sort_without_own_alternatives() {
        let foo = Sort::new("Foo");
        let baz = Sort::new("Baz");
        let declarations = [declaration(&[], foo.clone()), declaration(&[], baz.clone())];
        let sorts = SortCatalog::from_visible(declarations.iter());
        let g = parametric_production("g", &[], foo, Vec::new());
        let wrap = parametric_production("wrap", &["S"], Sort::new("S"), vec![Sort::new("S")]);
        let generated = generators(&[&g, &wrap], &sorts, &baz);
        assert!(generated.is_empty());
        assert_eq!(named(&generated), []);
    }

    #[test]
    fn schema_generators_are_absent_at_sorts_with_fixed_values() {
        let wrap = parametric_production("wrap", &["S"], Sort::new("S"), vec![Sort::new("S")]);
        for keys in [
            vec![AttributeKey::Hook],
            vec![AttributeKey::Hook, AttributeKey::Token],
            vec![AttributeKey::Token],
        ] {
            let id = Sort::new("Id");
            let mut declared = declaration(&[], id.clone());
            let Sentence::SyntaxSort { attributes, .. } = &mut declared else {
                unreachable!()
            };
            for key in keys {
                attributes.mark(key);
            }
            let lexed = token("idLit", "[a-z]+");
            let sorts = SortCatalog::from_visible([&declared, &lexed, &wrap]);
            assert_eq!(
                named(&generators(&[&lexed, &wrap], &sorts, &id)),
                [Named::DomainValues]
            );
        }
        // A hook can fix values without defining a literal domain.
        let mut declared = declaration(&[], Sort::new("Map"));
        let Sentence::SyntaxSort { attributes, .. } = &mut declared else {
            unreachable!()
        };
        attributes.mark(AttributeKey::Hook);
        let g = parametric_production("g", &[], Sort::new("Map"), Vec::new());
        let sorts = SortCatalog::from_visible([&declared, &g, &wrap]);
        assert!(sorts.declares_hooked_sort(&SortHead::from(&Sort::new("Map"))));
        assert_eq!(
            named(&generators(&[&g, &wrap], &sorts, &Sort::new("Map"))),
            [Named::Generator(ProductionId(0))]
        );
    }

    #[test]
    fn an_open_schema_makes_only_an_existing_free_sort_axiom_unstatable() {
        let foo = Sort::new("Foo");
        let baz = Sort::new("Baz");
        let declarations = [declaration(&[], foo.clone()), declaration(&[], baz.clone())];
        let sorts = SortCatalog::from_visible(declarations.iter());
        let g = parametric_production("g", &[], foo.clone(), Vec::new());
        let wrap = parametric_production("wrap", &["S"], Sort::new("S"), vec![Sort::new("S")]);
        let conv = parametric_production("conv", &["S", "T"], Sort::new("S"), vec![Sort::new("T")]);
        for (order, position) in [([&g, &wrap, &conv], 2), ([&conv, &wrap, &g], 0)] {
            let NoJunkAxiom::Unstatable { generator } = no_junk_axiom(&order, &sorts, &foo) else {
                panic!("conv leaves T free at Foo")
            };
            assert_eq!(generator, ProductionId(position));
            assert!(generators(&order, &sorts, &baz).is_empty());
        }
    }

    #[test]
    fn schema_tokens_keep_the_own_token_productions_position() {
        let id = Sort::new("Id");
        let declared = declaration(&[], id.clone());
        let first = production(Some("first"), "Id", Vec::new(), &[]);
        let own_token = token("own", "[a-z]+");
        let last = production(Some("last"), "Id", Vec::new(), &[]);
        let schema = schema_token("all", "[A-Z]+");
        let sorts = SortCatalog::from_visible([&declared, &first, &own_token, &last, &schema]);
        assert_eq!(
            named(&generators(
                &[&schema, &first, &own_token, &last],
                &sorts,
                &id
            )),
            [
                Named::Generator(ProductionId(1)),
                Named::DomainValues,
                Named::Generator(ProductionId(3)),
            ]
        );
    }

    #[test]
    fn schema_tokens_keep_the_declarations_domain_values_last() {
        let id = Sort::new("Id");
        let mut declared = declaration(&[], id.clone());
        declared.attributes_mut().mark(AttributeKey::Token);
        let g = production(Some("g"), "Id", Vec::new(), &[]);
        let schema = schema_token("all", "[a-z]+");
        let sorts = SortCatalog::from_visible([&declared, &g, &schema]);
        assert_eq!(
            named(&generators(&[&schema, &g], &sorts, &id)),
            [Named::Generator(ProductionId(1)), Named::DomainValues]
        );
    }

    #[test]
    fn schema_tokens_follow_own_generators_with_one_domain_values_alternative() {
        let id = Sort::new("Id");
        let declared = declaration(&[], id.clone());
        let first = production(Some("first"), "Id", Vec::new(), &[]);
        let last = production(Some("last"), "Id", Vec::new(), &[]);
        let lower = schema_token("allLower", "[a-z]+");
        let upper = schema_token("allUpper", "[A-Z]+");
        let sorts = SortCatalog::from_visible([&declared, &first, &last, &lower, &upper]);
        assert_eq!(
            named(&generators(&[&lower, &first, &upper, &last], &sorts, &id)),
            [
                Named::Generator(ProductionId(1)),
                Named::Generator(ProductionId(3)),
                Named::DomainValues,
            ]
        );
    }

    #[test]
    fn schemas_extend_an_injection_only_axiom_before_its_injections() {
        let foo = Sort::new("Foo");
        let bar = Sort::new("Bar");
        let declarations = [declaration(&[], foo.clone()), declaration(&[], bar.clone())];
        let wrap = parametric_production("wrap", &["S"], Sort::new("S"), vec![Sort::new("S")]);
        let sorts = SortCatalog::from_visible(declarations.iter().chain([&wrap]));
        let subsorts = PartialOrder::new([(bar, foo.clone())]).expect("one strict subsort");
        for (productions, expected) in [
            (Vec::new(), vec![Named::Injection]),
            (
                vec![&wrap],
                vec![Named::Generator(ProductionId(0)), Named::Injection],
            ),
        ] {
            let catalog = ProductionCatalog::from_visible(productions);
            let NoJunkAxiom::Stated(generated) = NoJunkAxiom::of(&catalog, &sorts, &subsorts, &foo)
            else {
                panic!("wrap binds S at Foo")
            };
            assert_eq!(named(&generated), expected);
        }
    }

    #[test]
    fn hooked_k_and_kitem_declarations_still_admit_schema_generators() {
        let wrap = parametric_production("wrap", &["S"], Sort::new("S"), vec![Sort::new("S")]);
        for name in ["K", "KItem"] {
            let sort = Sort::new(name);
            let mut declared = declaration(&[], sort.clone());
            declared.attributes_mut().mark(AttributeKey::Hook);
            let g = production(Some("g"), name, Vec::new(), &[]);
            let sorts = SortCatalog::from_visible([&declared, &g, &wrap]);
            assert!(!sorts.declares_hooked_sort(&SortHead::from(&sort)));
            assert_eq!(
                named(&generators(&[&g, &wrap], &sorts, &sort)),
                [
                    Named::Generator(ProductionId(0)),
                    Named::Generator(ProductionId(1))
                ]
            );
        }
    }

    /// `syntax {W} Foo ::= pick(MInt{W}, Bar)` at `Foo` leaves `W` free, and so does the phantom
    /// `syntax {W} Foo ::= pick(Bar)`: `Foo`'s values include `pick{W}(..)` for every `W`, which no
    /// finite disjunction lists, so `Foo`'s no-junk axiom is unstatable, whatever the order of
    /// its closed sibling `g`.
    #[test]
    fn a_generator_whose_result_leaves_a_sort_parameter_free_makes_the_axiom_unstatable() {
        let foo = Sort::new("Foo");
        let bar = Sort::new("Bar");
        let mint = |argument: Sort| Sort::with_parameters("MInt", vec![argument]);
        let declarations = [
            declaration(&["W"], mint(Sort::new("W"))),
            declaration(&[], bar.clone()),
            declaration(&[], foo.clone()),
        ];
        let sorts = SortCatalog::from_visible(declarations.iter());
        let open = parametric_production(
            "pick",
            &["W"],
            foo.clone(),
            vec![mint(Sort::new("W")), bar.clone()],
        );
        let phantom = parametric_production("pick", &["W"], foo.clone(), vec![bar.clone()]);
        let g = parametric_production("g", &[], foo.clone(), Vec::new());
        for generator in [&open, &phantom] {
            for (order, position) in [([generator, &g], 0), ([&g, generator], 1)] {
                let NoJunkAxiom::Unstatable { generator: id } = no_junk_axiom(&order, &sorts, &foo)
                else {
                    panic!("{generator:?} leaves W free at Foo");
                };
                assert_eq!(id, ProductionId(position));
            }
        }
    }

    /// `syntax {W} Box{W} ::= box(W)` at `Box{Bar}` binds `W` to `Bar`: one closed instance.
    #[test]
    fn a_generator_whose_result_binds_every_sort_parameter_is_a_closed_instance() {
        let bar = Sort::new("Bar");
        let boxed = |argument: Sort| Sort::with_parameters("Box", vec![argument]);
        let declarations = [
            declaration(&["W"], boxed(Sort::new("W"))),
            declaration(&[], bar.clone()),
        ];
        let sorts = SortCatalog::from_visible(declarations.iter());
        let r#box =
            parametric_production("box", &["W"], boxed(Sort::new("W")), vec![Sort::new("W")]);
        let NoJunkAxiom::Stated(generators) = no_junk_axiom(&[&r#box], &sorts, &boxed(bar.clone()))
        else {
            panic!("box binds W at Box{{Bar}}");
        };
        let instances = generators
            .alternatives()
            .map(|alternative| match alternative {
                NoJunkAlternative::Generator(instance) => {
                    (instance.production(), instance.substitution().clone())
                }
                NoJunkAlternative::DomainValues | NoJunkAlternative::Injection(_) => {
                    panic!("box is the only alternative, found {alternative:?}")
                }
            })
            .collect::<Vec<_>>();
        assert_eq!(
            instances,
            [(ProductionId(0), BTreeMap::from([(Sort::new("W"), bar)]))]
        );
    }

    #[test]
    fn two_labelled_token_productions_contribute_one_domain_values_alternative_in_either_order() {
        let sort = Sort::new("Id");
        let declaration = Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: sort.clone(),
            attributes: Attributes::default(),
        };
        let sorts = SortCatalog::from_visible([&declaration]);
        let lower = token("idLower", "[a-z]+");
        let upper = token("idUpper", "[A-Z]+");
        for order in [[&lower, &upper], [&upper, &lower]] {
            let generated = generators(&order, &sorts, &sort);
            assert_eq!(
                named(&generated),
                [Named::DomainValues],
                "a labelled token production is never a generator, whatever its position"
            );
        }
    }

    #[test]
    fn domain_values_keep_the_position_of_the_first_token_production() {
        let sort = Sort::new("Id");
        let declaration = Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: sort.clone(),
            attributes: Attributes::default(),
        };
        let sorts = SortCatalog::from_visible([&declaration]);
        let first = production(Some("first"), "Id", Vec::new(), &[]);
        let lexed = token("idLit", "[a-z]+");
        let last = production(Some("last"), "Id", Vec::new(), &[]);
        let relexed = token("idUpper", "[A-Z]+");
        let generated = generators(&[&first, &lexed, &last, &relexed], &sorts, &sort);
        assert_eq!(
            named(&generated),
            [
                Named::Generator(ProductionId(0)),
                Named::DomainValues,
                Named::Generator(ProductionId(2)),
            ]
        );
    }

    #[test]
    fn precedence_keeps_the_later_fact_as_a_field() {
        let function_macro = production(
            Some("f"),
            "Int",
            Vec::new(),
            &[AttributeKey::Function, AttributeKey::Macro],
        );
        assert_eq!(
            ProductionKind::of(&function_macro),
            ProductionKind::Function {
                totality: Totality::Partial,
                macro_like: true,
            }
        );
        let assoc_token = production(
            None,
            "Id",
            vec![ProductionItem::regex("[a-z]+")],
            &[AttributeKey::Token, AttributeKey::Assoc],
        );
        assert_eq!(
            ProductionKind::of(&assoc_token),
            ProductionKind::Token { algebraic: true }
        );
        let bracket = production(
            None,
            "Exp",
            vec![
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("Exp"),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
            &[AttributeKey::Bracket],
        );
        assert_eq!(
            ProductionKind::of(&bracket),
            ProductionKind::Bracket(BracketName::Undeclared)
        );
        assert_eq!(
            ProductionKind::of_unbracketed(&bracket),
            ProductionKind::Unlabelled
        );
    }

    /// `syntax {W} Foo ::= pick(x: MInt{W}, y: Int)` is a family of symbols, one per `W`, so no
    /// projection of a fixed signature inverts it; the same production without the binder is a
    /// source. A bracket, a function and a production with no named nonterminal are none.
    #[test]
    fn only_a_parameterless_labelled_constructor_with_a_named_nonterminal_is_a_projection_source() {
        let pick = |parameters: Vec<Sort>, keys: &[AttributeKey]| {
            let mut pick = production(
                Some("pick"),
                "Foo",
                vec![
                    ProductionItem::Terminal("pick".into()),
                    ProductionItem::Terminal("(".into()),
                    ProductionItem::NonTerminal {
                        sort: Sort::with_parameters("MInt", vec![Sort::new("W")]),
                        name: Some("x".into()),
                    },
                    ProductionItem::Terminal(",".into()),
                    ProductionItem::NonTerminal {
                        sort: Sort::new("Int"),
                        name: Some("y".into()),
                    },
                    ProductionItem::Terminal(")".into()),
                ],
                keys,
            );
            let Sentence::Production {
                parameters: binder, ..
            } = &mut pick
            else {
                unreachable!()
            };
            *binder = parameters;
            pick
        };

        let parametric = pick(vec![Sort::new("W")], &[]);
        assert!(FieldProjectionSource::of(&parametric).is_none());

        let closed = pick(Vec::new(), &[]);
        let source = FieldProjectionSource::of(&closed).expect("a parameterless constructor");
        assert_eq!(source.label().name, "pick");
        assert_eq!(source.sort(), &Sort::new("Foo"));
        assert_eq!(
            source.nonterminals().collect::<Vec<_>>(),
            [
                (
                    &Sort::with_parameters("MInt", vec![Sort::new("W")]),
                    Some("x")
                ),
                (&Sort::new("Int"), Some("y")),
            ]
        );

        assert!(FieldProjectionSource::of(&pick(Vec::new(), &[AttributeKey::Bracket])).is_none());
        assert!(FieldProjectionSource::of(&pick(Vec::new(), &[AttributeKey::Function])).is_none());
        let unnamed = production(
            Some("pair"),
            "Foo",
            vec![
                ProductionItem::NonTerminal {
                    sort: Sort::new("Int"),
                    name: None,
                },
                ProductionItem::NonTerminal {
                    sort: Sort::new("Int"),
                    name: None,
                },
            ],
            &[],
        );
        assert!(FieldProjectionSource::of(&unnamed).is_none());
    }

    /// The syntax declaration of an unlabelled bracket is made under its `bracketLabel`, so the
    /// kind it states is that of a labelled production.
    #[test]
    fn an_unlabelled_bracket_is_classified_under_its_bracket_label_without_the_bracket_test() {
        let bracket = |keys: &[AttributeKey]| {
            let mut bracket = production(
                None,
                "Exp",
                vec![
                    ProductionItem::Terminal("(".into()),
                    ProductionItem::NonTerminal {
                        sort: Sort::new("Exp"),
                        name: None,
                    },
                    ProductionItem::Terminal(")".into()),
                ],
                keys,
            );
            let Sentence::Production { attributes, .. } = &mut bracket else {
                unreachable!()
            };
            attributes.insert(
                AttributeKey::BracketLabel.as_str(),
                serde_json::Value::String("(_)_MAIN_Exp_Exp".into()),
            );
            bracket
        };
        let plain = bracket(&[AttributeKey::Bracket]);
        assert_eq!(
            ProductionKind::of(&plain),
            ProductionKind::Bracket(BracketName::BracketLabel)
        );
        assert_eq!(ProductionKind::of_unbracketed(&plain), ProductionKind::Base);
        assert_eq!(
            ProductionKind::of_unbracketed(&bracket(&[AttributeKey::Bracket, AttributeKey::Assoc])),
            ProductionKind::Algebraic
        );
    }
}
