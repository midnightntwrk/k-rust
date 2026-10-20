//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Remove semantic-cast applications while retaining their inferred sorts, and give the root
//! alias of a rule that defines its head at the head's sort that sort
//! ([`narrow_head_aliases`]).
#![deny(clippy::wildcard_enum_match_arm)]

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use crate::definition::AttributeKey;
use crate::names::BuiltinSort;
use crate::{
    definition::{Definition, LabelHead, PartialOrder, ProductionCatalog, RuleHead, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode},
    kast::{Label, Sort, SortRole, Term, TermParts, sort_role::KernelSort},
    provenance::GeneratingPass,
};

#[derive(Default)]
struct VariableBounds {
    explicit: Option<(Sort, Term)>,
    casts: Vec<(Sort, Term)>,
}

// A cast bounds the sort of the value at its position, so a variable's sort is acceptable under
// a bound when compilation can place a term of that sort at a position of the bound's sort
// (`subsort_kitem::placeable`, the relation sort injection places terms by). This pass runs
// before `subsort_kitem` declares the implicit `KItem` subsorts, which that relation includes.
fn below(actual: &Sort, expected: &Sort, subsorts: &PartialOrder<Sort>) -> bool {
    super::subsort_kitem::placeable(actual, expected, subsorts)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveSemanticCastsError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ResolveSemanticCastsError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(diagnostic) = self.diagnostics.first() {
            write!(formatter, "{}", diagnostic.message)
        } else {
            write!(formatter, "semantic-cast resolution failed")
        }
    }
}

impl std::error::Error for ResolveSemanticCastsError {}

fn error(message: impl Into<String>, sentence: &Sentence) -> ResolveSemanticCastsError {
    ResolveSemanticCastsError {
        diagnostics: vec![Diagnostic::error(
            DiagnosticCode::InvalidSemanticCast,
            message,
            sentence,
        )],
    }
}

fn sentence_error(message: impl Into<String>, sentence: &Sentence) -> ResolveSemanticCastsError {
    let label = sentence
        .attributes()
        .string(AttributeKey::Label)
        .unwrap_or("<unlabelled>");
    error(format!("sentence {label}: {}", message.into()), sentence)
}

fn unlocated_error(message: impl Into<String>) -> ResolveSemanticCastsError {
    ResolveSemanticCastsError {
        diagnostics: vec![Diagnostic {
            severity: crate::diagnostic::Severity::Error,
            code: DiagnosticCode::InvalidSemanticCast,
            message: message.into(),
            source: None,
            location: None,
            input_addresses: Vec::new(),
        }],
    }
}

/// Resolve the semantic casts of every rule, claim and context of `definition` into compiler
/// sort metadata.
///
/// A cast adds no `isSort` side condition here: a variable the cast types matches only terms of
/// its sort, and sort injection judges the cast of any other operand (an injection or a
/// rejection), so the condition would constrain nothing more. Casted variables
/// retain their inferred sort in the public variable node as well.
pub fn resolve_semantic_casts(
    definition: &Definition,
) -> Result<Definition, ResolveSemanticCastsError> {
    super::super::pipeline::run_standalone(
        definition,
        resolve_semantic_casts_pass,
        Some(GeneratingPass::SemanticCasts),
    )
}

pub(crate) fn resolve_semantic_casts_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveSemanticCastsError> {
    let resolved = input
        .resolved_raw()
        .map_err(|error| unlocated_error(error.to_string()))?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let subsorts = views.subsorts(module_id).map_err(|cycle| {
            let message = format!("module {} has cyclic subsorts: {cycle}", module.name);
            module.local_sentences.first().map_or_else(
                || unlocated_error(&message),
                |sentence| sentence_error(&message, sentence),
            )
        })?;
        let productions = views.production_catalog(module_id);
        for sentence in &mut module.local_sentences {
            let sentence = crate::definition::sentence_mut(sentence);
            resolve_semantic_casts_in_sentence_mut(sentence, false, subsorts)?;
            narrow_head_aliases(sentence, productions, subsorts);
        }
    }
    Ok(output)
}

/// Give each root alias variable of a rule that compilation states at its head's sort the
/// head's sort, at every occurrence of the variable in the rule.
///
/// A function, macro, `anywhere` or `simplification` rule `h(P) #as V => R` defines `h` at the
/// result sort `S` of `h`: it states `h(P) = R[h(P)/V]`, an equation between terms of `S`, and is
/// never placed in a cell. `V` names the matched term, an application of `h`, so every value `V`
/// can take is a term of `S`. Sort inference reads the rule body at the sort of a rule body,
/// though, and an alias that nothing else bounds takes that sort, `K`, there: the alias would
/// then lift the whole left side to `K`, and the rule would be read as a `K` rewrite rather than
/// as an equation of `h`. Narrowing `V` from a sort `T` above `S` to `S` excludes no value `V`
/// can take, and keeps every occurrence well placed, since each position `V` stood at accepted a
/// term of `T` and so accepts one of `S`. An alias whose sort is `S` already, is not above `S`,
/// or is not a variable is left as written; so is the alias of a head whose result sort is not
/// one fixed sort (a parametric production, or an overloaded label the term does not resolve).
///
/// Variable names are unique within a sentence by this point (`rename bound variables apart`),
/// so every occurrence of the alias's name is the alias.
fn narrow_head_aliases(
    sentence: &mut Sentence,
    productions: &ProductionCatalog<'_>,
    subsorts: &PartialOrder<Sort>,
) {
    let sorts = {
        let Sentence::Rule {
            body, attributes, ..
        } = &*sentence
        else {
            return;
        };
        let head = RuleHead::of(body);
        let Some((application, label, _)) = head.application() else {
            return;
        };
        if head.right.is_none() {
            return;
        }
        let at_head_sort = super::add_implicit_computation_cell::is_function(body, productions)
            || productions.macro_labels().contains(&LabelHead::from(label))
            || attributes.has_any(&AttributeKey::MACRO_LIKE)
            || attributes.has(AttributeKey::Anywhere)
            || attributes.has(AttributeKey::Simplification);
        if !at_head_sort {
            return;
        }
        let Some(result) = head_result_sort(application, label, productions) else {
            return;
        };
        let mut sorts = BTreeMap::new();
        let mut term = head.left;
        while let Term::As { pattern, alias } = term.unannotated() {
            if let Term::Variable {
                name,
                sort: Some(sort),
            } = alias.unannotated()
                && *sort != result
                && below(&result, sort, subsorts)
            {
                sorts.insert(name.clone(), result.clone());
            }
            term = pattern;
        }
        sorts
    };
    if sorts.is_empty() {
        return;
    }
    let Sentence::Rule {
        body,
        requires,
        ensures,
        ..
    } = sentence
    else {
        unreachable!("the sorts were read from a rule")
    };
    for root in [body, requires, ensures] {
        retype_variables(root, &sorts);
    }
}

/// The result sort of the head application `application` of `label`: that of the production
/// the application resolves to, or of the label's one production, when that production is not
/// parametric.
fn head_result_sort(
    application: &Term,
    label: &Label,
    productions: &ProductionCatalog<'_>,
) -> Option<Sort> {
    let resolved = application
        .metadata()
        .and_then(|metadata| metadata.production)
        .and_then(|identity| productions.lookup(&identity))
        .filter(|id| {
            matches!(
                productions.production(*id),
                Sentence::Production { label: Some(candidate), .. } if candidate.name == label.name
            )
        });
    let id = match resolved {
        Some(id) => id,
        None => match productions.productions_for(&LabelHead::from(label)) {
            [only] => *only,
            _ => return None,
        },
    };
    match productions.production(id) {
        Sentence::Production {
            parameters, sort, ..
        } if parameters.is_empty() && sort.parameters.is_empty() => Some(sort.clone()),
        _ => None,
    }
}

/// Give every variable of `term` named in `sorts` the sort `sorts` maps it to.
fn retype_variables(term: &mut Term, sorts: &BTreeMap<String, Sort>) {
    let mut pending = vec![term];
    while let Some(mut node) = pending.pop() {
        while let Term::Annotated { term: inner, .. } = node {
            node = inner;
        }
        if let Term::Variable { name, sort } = node {
            if let Some(narrowed) = sorts.get(name) {
                *sort = Some(narrowed.clone());
            }
            continue;
        }
        pending.extend(node.children_mut());
    }
}

/// Resolve semantic casts across all term-bearing roots of one sentence.
///
/// `subsorts` must be the visible subsort order of the sentence's module. Callers resolving
/// several sentences from one module should obtain it once from the same `DefinitionViews`.
pub fn resolve_semantic_casts_in_sentence(
    subsorts: &PartialOrder<Sort>,
    mut sentence: Sentence,
) -> Result<Sentence, ResolveSemanticCastsError> {
    resolve_semantic_casts_in_sentence_mut(&mut sentence, false, subsorts)?;
    Ok(sentence)
}

/// Resolve semantic casts and add their sort predicates to the sentence condition.
///
/// A cast adds `isS` of its operand only when `cast_condition` gives it a condition: a sort
/// with a sort predicate, or `Bag`; a cast to any other sort adds nothing.
///
/// The predicate's argument is the left projection of the cast's resolved operand, the value the
/// pattern denotes there.
///
/// Standalone search patterns (`compile_search_pattern`) use this mode. Macro and alias
/// sentences suppress predicates because their casts describe matching syntax rather than
/// runtime side conditions. `subsorts` is the visible order of the sentence's module.
///
/// The sort predicates are conjoined with the prior condition by `#And` when either reads as a
/// predicate as the sentence stands and by `_andBool_` otherwise. `compile_search_pattern` makes
/// that choice after macro expansion instead, so a condition spelled through a macro that expands
/// to a predicate is conjoined as a predicate there and as a Bool term here.
pub fn resolve_semantic_casts_with_predicates_in_sentence(
    subsorts: &PartialOrder<Sort>,
    sentence: Sentence,
) -> Result<Sentence, ResolveSemanticCastsError> {
    resolve_semantic_casts_with_pending_predicates_in_sentence(subsorts, sentence)
        .map(crate::kompile::ml_constructs::resolve_condition_conjunctions_in_sentence)
}

/// [`resolve_semantic_casts_with_predicates_in_sentence`] with the conjunction of the sort
/// predicates and the prior condition left pending when a later macro expansion may change its
/// choice; the caller resolves it after macro expansion
/// ([`crate::kompile::ml_constructs::resolve_condition_conjunctions`]).
pub(crate) fn resolve_semantic_casts_with_pending_predicates_in_sentence(
    subsorts: &PartialOrder<Sort>,
    mut sentence: Sentence,
) -> Result<Sentence, ResolveSemanticCastsError> {
    resolve_semantic_casts_in_sentence_mut(&mut sentence, true, subsorts)?;
    Ok(sentence)
}

/// What a semantic cast to a sort adds to the condition of a search pattern (predicate mode).
enum CastCondition {
    /// `isS(operand)`: compilation declares the sort predicate of `S`.
    SortPredicate,
    /// `isBag(operand)`: the cell-fragment membership test that cell concretization replaces by
    /// the sort predicates of the fragment's cells (`concretize_cells`).
    CellFragment,
    /// Nothing: the cast only fixes the operand's sort.
    Static,
}

/// The condition a semantic cast to a sort of `role` adds to a search pattern.
///
/// A sort with a sort predicate ([`SortRole::has_sort_predicate`]) gets `isS` of the operand,
/// which tests at run time that the matched K term is a term of `S`.
///
/// `Bag` has no K terms of its own, but `isBag(R)` over a cell-fragment variable `R` is the
/// fragment-membership test that cell concretization rewrites into the sort predicates of the
/// fragment's generated cell sorts, so it is kept.
///
/// Every other sort (`KBott`, `KLabel`, `KList`, `KString`, `Cell`, a numeral, a rigid
/// variable, scaffolding) adds nothing. No compiled K term has such a sort, so its `isS` would
/// be declared nowhere and would be false on every argument. The cast still has its static
/// meaning: its sort is the sort of the operand in the compiled pattern, where a variable is
/// emitted with that sort and matches only terms of it, and sort injection checks a non-variable
/// operand against the cast (an upcast is placed, any other cast rejected), so leaving out the
/// conjunct admits no ill-sorted pattern.
const fn cast_condition(role: SortRole) -> CastCondition {
    use KernelSort as S;
    match role {
        SortRole::Kernel(S::K | S::KItem | S::KConfigVar | S::Bool) | SortRole::Defined => {
            CastCondition::SortPredicate
        }
        SortRole::Kernel(S::Bag) => CastCondition::CellFragment,
        SortRole::Kernel(S::KBott | S::KLabel | S::KList | S::KString | S::Cell)
        | SortRole::RigidVariable
        | SortRole::Scaffolding
        | SortRole::Nat => CastCondition::Static,
    }
}

fn resolve_semantic_casts_in_sentence_mut(
    sentence: &mut Sentence,
    add_predicates: bool,
    subsorts: &PartialOrder<Sort>,
) -> Result<(), ResolveSemanticCastsError> {
    let macro_like = sentence.attributes().has_any(&AttributeKey::MACRO_LIKE);
    let roots = match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => vec![body, requires, ensures],
        Sentence::Context { body, requires, .. } => vec![body, requires],
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => return Ok(()),
    };

    let (casts, typed_variables, errors) = {
        let shared = roots.iter().map(|root| &**root).collect::<Vec<&Term>>();
        collect_cast_bounds(&shared, subsorts)
    };
    if !errors.is_empty() {
        drop(roots);
        return Err(ResolveSemanticCastsError {
            diagnostics: errors
                .into_iter()
                .flat_map(|message| sentence_error(message, sentence).diagnostics)
                .collect(),
        });
    }
    let predicates = add_predicates && !casts.is_empty() && !macro_like;
    let tests = CastTests {
        casts: &casts,
        typed_variables: &typed_variables,
        subsorts,
    };
    // The casts with an occurrence that no quantifier owns: their tests go at the top of the
    // condition. A test a quantifier owns goes inside it (`CastTests::place`).
    let mut unowned = BTreeSet::new();
    for root in roots {
        let mut taken = std::mem::replace(root, Term::Sequence(Vec::new()));
        if predicates {
            tests.collect_unowned(&taken, &mut Vec::new(), &mut unowned);
            taken = tests.place(taken);
        }
        *root = transform(taken, &casts, &typed_variables, subsorts);
    }

    if !predicates {
        return Ok(());
    }

    // The sort tests of casts to one sort are conjoined in the order the casts first occur, and
    // those of casts to different sorts in the order of the sorts' cast labels. Neither order
    // reads a variable's name, so a renaming of the sentence's variables gives its tests in the
    // same order.
    fn cast_label(cast: &Term) -> &Label {
        let Term::Apply { label, .. } = cast else {
            unreachable!("only semantic-cast applications were collected")
        };
        label
    }
    let mut ordered = casts.iter().collect::<Vec<_>>();
    ordered.sort_by(|(left, left_first), (right, right_first)| {
        cast_label(left)
            .cmp(cast_label(right))
            .then(left_first.cmp(right_first))
    });
    let conjuncts = ordered
        .into_iter()
        .filter(|(cast, _)| unowned.contains(*cast))
        .filter_map(|(cast, _)| tests.test(cast));
    let Some(predicate) =
        conjuncts.reduce(|left, right| Term::apply("_andBool_", vec![left, right]))
    else {
        return Ok(());
    };

    let requires = match sentence {
        Sentence::Rule { requires, .. }
        | Sentence::Claim { requires, .. }
        | Sentence::Context { requires, .. }
        | Sentence::ContextAlias { requires, .. } => requires,
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => return Ok(()),
    };
    let prior = std::mem::replace(requires, bool_true());
    *requires = if is_true(&prior) {
        predicate
    } else {
        crate::kompile::ml_constructs::conjoin_condition(predicate, prior)
    };
    Ok(())
}

/// The sort tests the casts of a search pattern add (predicate mode), and where each goes.
///
/// A quantifier's binder is in scope only in its body, so the test of a cast whose operand names
/// a variable the quantifier binds reads that variable only inside the quantifier. The innermost
/// quantifier binding one of the operand's variables owns the cast's occurrence, and the test
/// goes inside it. A cast of the bound variable itself is the binder's annotation, which restricts
/// the values the binder ranges over: `#Exists Y . P` becomes `#Exists Y . (test #And P)` and
/// `#Forall Y . P` becomes `#Forall Y . (test #Implies P)`. A cast of a compound operand states
/// that the operand's value is of the cast's sort, a conjunct of the body under either quantifier:
/// `#Forall Y . (test #And P)`. Where the cast's operand is the bound
/// variable itself and the variable's own sort is the cast's sort, the test holds for every value
/// the binder ranges over and is dropped. An occurrence no quantifier owns gets its test at the
/// top of the condition, where every variable it reads is free. Bound names are compared by
/// spelling, which is the binding rule of the term as written.
struct CastTests<'a> {
    casts: &'a BTreeMap<Term, usize>,
    typed_variables: &'a BTreeMap<String, Sort>,
    subsorts: &'a PartialOrder<Sort>,
}

impl CastTests<'_> {
    /// The sort test of the cast `cast`, or `None` for a cast that adds none (`cast_condition`).
    ///
    /// A search pattern denotes its left projection (`compile_search_pattern` projects the body),
    /// so the cast constrains the value of its operand's left side: `(L => R):S` adds the test
    /// `L:S` adds.
    fn test(&self, cast: &Term) -> Option<Term> {
        let Term::Apply { label, .. } = cast.unannotated() else {
            unreachable!("only semantic-cast applications were collected")
        };
        let sort = label
            .semantic_cast_sort()
            .expect("the cast set contains semantic-cast applications");
        match cast_condition(sort.role()) {
            CastCondition::SortPredicate | CastCondition::CellFragment => Some(Term::Apply {
                label: Label::sort_predicate(&sort),
                arguments: vec![crate::kompile::sort_injections::rewrite_projection(
                    &transform(
                        cast.unannotated().clone(),
                        self.casts,
                        self.typed_variables,
                        self.subsorts,
                    ),
                    false,
                    self.subsorts,
                )],
            }),
            CastCondition::Static => None,
        }
    }

    /// Whether the test of `cast`, owned by a quantifier binding `bound`, holds for every value
    /// the binder ranges over: the cast's operand, read through nested casts, is a variable the
    /// quantifier binds, whose own sort is the cast's sort.
    fn implied(&self, cast: &Term, bound: &[String]) -> bool {
        let Term::Apply { label, .. } = cast.unannotated() else {
            return false;
        };
        let Some(sort) = label.semantic_cast_sort() else {
            return false;
        };
        Self::annotated_variable(cast, bound)
            .is_some_and(|name| self.typed_variables.get(name) == Some(&sort))
    }

    /// The bound variable `cast` annotates: its operand, read through nested casts, when that is a
    /// variable in `bound`; `None` for a cast of a compound operand.
    fn annotated_variable<'c>(cast: &'c Term, bound: &[String]) -> Option<&'c str> {
        let Term::Apply { arguments, .. } = cast.unannotated() else {
            return None;
        };
        let [operand] = arguments.as_slice() else {
            return None;
        };
        let mut operand = operand.unannotated();
        // Invariant: `operand` is the operand of `cast` with the casts above it removed; each
        // step removes one, so the finite term bounds the loop.
        while let Term::Apply { label, arguments } = operand
            && label.semantic_cast_sort().is_some()
            && let [inner] = arguments.as_slice()
        {
            operand = inner.unannotated();
        }
        match operand {
            Term::Variable { name, .. } if bound.contains(name) => Some(name),
            Term::Apply { .. }
            | Term::Variable { .. }
            | Term::InjectedLabel(_)
            | Term::Token { .. }
            | Term::Rewrite { .. }
            | Term::As { .. }
            | Term::Sequence(_)
            | Term::Annotated { .. } => None,
        }
    }

    /// The named variables of the operand of the cast `cast`.
    fn operand_variables(cast: &Term) -> BTreeSet<String> {
        let mut names = BTreeSet::new();
        cast.visit_preorder(&mut |node| {
            if let Term::Variable { name, .. } = node.unannotated()
                && !is_anonymous(name)
            {
                names.insert(name.clone());
            }
        });
        names
    }

    /// Add to `unowned` each cast of `term` with an occurrence that no quantifier owns: no
    /// quantifier enclosing it (`scope`, the bound names of the enclosing quantifiers) binds a
    /// variable of its operand.
    fn collect_unowned(
        &self,
        term: &Term,
        scope: &mut Vec<Vec<String>>,
        unowned: &mut BTreeSet<Term>,
    ) {
        crate::stack::guarded(|| {
            if self.casts.contains_key(term.unannotated()) {
                let variables = Self::operand_variables(term);
                if !scope.iter().flatten().any(|name| variables.contains(name)) {
                    unowned.insert(term.unannotated().clone());
                }
            }
            if let Some(quantifier) = crate::kast::binding::quantifier(term) {
                scope.push(quantifier.bound().into_iter().map(str::to_owned).collect());
                self.collect_unowned(quantifier.binder, scope, unowned);
                self.collect_unowned(quantifier.body, scope, unowned);
                scope.pop();
                return;
            }
            for child in term.unannotated().children() {
                self.collect_unowned(child, scope, unowned);
            }
        });
    }

    /// The casts of `term` that a quantifier binding `bound` owns, in their order of first
    /// occurrence: those whose operand names a variable in `bound` and no variable a quantifier
    /// inside `term` binds around the cast (`inner`).
    fn owned<'t>(
        &self,
        term: &'t Term,
        bound: &[String],
        inner: &mut Vec<Vec<String>>,
        owned: &mut Vec<&'t Term>,
    ) {
        crate::stack::guarded(|| {
            if self.casts.contains_key(term.unannotated()) {
                let variables = Self::operand_variables(term);
                if bound.iter().any(|name| variables.contains(name))
                    && !inner.iter().flatten().any(|name| variables.contains(name))
                    && !owned
                        .iter()
                        .any(|cast| cast.unannotated() == term.unannotated())
                {
                    owned.push(term);
                }
            }
            if let Some(quantifier) = crate::kast::binding::quantifier(term) {
                inner.push(quantifier.bound().into_iter().map(str::to_owned).collect());
                self.owned(quantifier.binder, bound, inner, owned);
                self.owned(quantifier.body, bound, inner, owned);
                inner.pop();
                return;
            }
            for child in term.unannotated().children() {
                self.owned(child, bound, inner, owned);
            }
        });
    }

    /// `term` with the tests each of its quantifiers owns placed inside it (see the type's
    /// documentation); every node keeps its metadata.
    fn place(&self, term: Term) -> Term {
        crate::stack::guarded(|| {
            if let Some(quantifier) = crate::kast::binding::quantifier(&term) {
                let bound = quantifier
                    .bound()
                    .into_iter()
                    .map(str::to_owned)
                    .collect::<Vec<_>>();
                let forall = quantifier.kind == crate::kast::binding::QuantifierKind::Forall;
                let mut owned = Vec::new();
                self.owned(quantifier.binder, &bound, &mut Vec::new(), &mut owned);
                self.owned(quantifier.body, &bound, &mut Vec::new(), &mut owned);
                owned.sort_by(|left, right| {
                    let label = |cast: &Term| {
                        let Term::Apply { label, .. } = cast.unannotated() else {
                            unreachable!("only semantic-cast applications were collected")
                        };
                        label.clone()
                    };
                    label(left)
                        .cmp(&label(right))
                        .then(self.casts[left.unannotated()].cmp(&self.casts[right.unannotated()]))
                });
                // A test of the bound variable itself is the binder's annotation, which restricts
                // the values the binder ranges over; a test of a compound operand states that its
                // value is of the cast's sort, a conjunct of the body.
                let (annotations, operands): (Vec<&Term>, Vec<&Term>) = owned
                    .into_iter()
                    .filter(|cast| !self.implied(cast, &bound))
                    .partition(|cast| Self::annotated_variable(cast, &bound).is_some());
                let conjoined = |casts: Vec<&Term>| {
                    casts
                        .into_iter()
                        .filter_map(|cast| self.test(cast))
                        .reduce(|left, right| Term::apply("_andBool_", vec![left, right]))
                };
                let (annotation, operand) = (conjoined(annotations), conjoined(operands));
                let metadata = term.metadata().cloned();
                let TermParts::Apply { label, arguments } = term.into_unannotated().into_parts()
                else {
                    unreachable!("a quantifier is an application")
                };
                let [binder, body]: [Term; 2] = arguments
                    .try_into()
                    .unwrap_or_else(|_| unreachable!("a quantifier has two arguments"));
                let body = self.place(body);
                let body = match operand {
                    None => body,
                    Some(test) => crate::kompile::ml_constructs::conjoin_condition(test, body),
                };
                let body = match annotation {
                    None => body,
                    Some(test) if forall => Term::Apply {
                        label: Label::new(crate::kast::InternalLabel::Implies.as_str()),
                        arguments: vec![test, body],
                    },
                    Some(test) => crate::kompile::ml_constructs::conjoin_condition(test, body),
                };
                let rebuilt = Term::Apply {
                    label,
                    arguments: vec![binder, body],
                };
                return match metadata {
                    Some(metadata) => rebuilt.with_metadata(metadata),
                    None => rebuilt,
                };
            }
            let metadata = term.metadata().cloned();
            let rebuilt = match term.into_unannotated().into_parts() {
                TermParts::Rewrite { left, right } => Term::Rewrite {
                    left: Box::new(self.place(*left)),
                    right: Box::new(self.place(*right)),
                },
                TermParts::As { pattern, alias } => Term::As {
                    pattern: Box::new(self.place(*pattern)),
                    alias: Box::new(self.place(*alias)),
                },
                TermParts::Sequence(items) => {
                    Term::Sequence(items.into_iter().map(|item| self.place(item)).collect())
                }
                TermParts::Apply { label, arguments } => Term::Apply {
                    label,
                    arguments: arguments
                        .into_iter()
                        .map(|argument| self.place(argument))
                        .collect(),
                },
                leaf @ (TermParts::InjectedLabel(_)
                | TermParts::Variable { .. }
                | TermParts::Token { .. }) => Term::from(leaf),
                TermParts::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
            };
            match metadata {
                Some(metadata) => rebuilt.with_metadata(metadata),
                None => rebuilt,
            }
        })
    }
}

/// The sort semantic-cast resolution gives each named variable of a sentence with the term roots
/// `roots`: its explicit sort, or else the least of its direct cast bounds.
///
/// Returns the semantic casts seen, each with the number of distinct casts that first occur
/// before it in preorder over the roots, the variable sorts, and one message per conflict (an
/// explicit sort outside a cast bound, conflicting explicit sorts, or cast bounds without a least
/// one).
fn collect_cast_bounds(
    roots: &[&Term],
    subsorts: &PartialOrder<Sort>,
) -> (BTreeMap<Term, usize>, BTreeMap<String, Sort>, Vec<String>) {
    let mut casts = BTreeMap::new();
    let mut variables = BTreeMap::<String, VariableBounds>::new();
    let mut errors = Vec::new();
    // Invariant: `casts` holds semantic casts seen so far, and `variables` holds every explicit sort and direct cast bound of each named variable in the visited roots.
    for root in roots {
        root.visit_preorder(&mut |term| {
            if let Term::Variable {
                name,
                sort: Some(sort),
            } = term.unannotated()
                && !is_anonymous(name)
            {
                let variable = variables.entry(name.clone()).or_default();
                if let Some((previous, occurrence)) = &variable.explicit {
                    if previous != sort {
                        errors.push(format!(
                            "variable {name} has conflicting explicit sorts {previous} and {sort} at {occurrence} and {term}"
                        ));
                    }
                } else {
                    variable.explicit = Some((sort.clone(), term.clone()));
                }
            }
            let Term::Apply { label, arguments } = term.unannotated() else {
                return;
            };
            let Some(sort) = label.semantic_cast_sort() else {
                return;
            };
            let [argument] = arguments.as_slice() else {
                return;
            };
            let first = casts.len();
            casts.entry(term.unannotated().clone()).or_insert(first);
            for value in cast_values(argument) {
                match value.unannotated() {
                    Term::Variable {
                        name,
                        sort: existing,
                    } => {
                        if is_anonymous(name) {
                            if let Some(existing) = existing
                                && !below(existing, &sort, subsorts)
                            {
                                errors.push(format!(
                                    "variable {name} has sort {existing} outside semantic cast sort {sort} at {term}"
                                ));
                            }
                        } else {
                            variables
                                .entry(name.clone())
                                .or_default()
                                .casts
                                .push((sort.clone(), term.clone()));
                        }
                    }
                    Term::Apply { label, .. } => {
                        if let Some(nested) = label.semantic_cast_sort()
                            && !below(&nested, &sort, subsorts)
                            && !below(&sort, &nested, subsorts)
                        {
                            errors.push(format!(
                                "semantic cast sort {sort} is incomparable with the nested cast sort {nested} at {term}"
                            ));
                        }
                    }
                    Term::InjectedLabel(_)
                    | Term::Token { .. }
                    | Term::Rewrite { .. }
                    | Term::As { .. }
                    | Term::Sequence(_)
                    | Term::Annotated { .. } => {}
                }
            }
        });
    }
    let mut typed_variables = BTreeMap::<String, Sort>::new();
    for (name, bounds) in variables {
        if let Some((explicit, occurrence)) = bounds.explicit {
            for (cast, cast_occurrence) in &bounds.casts {
                if !below(&explicit, cast, subsorts) {
                    errors.push(format!(
                        "variable {name} has explicit sort {explicit} outside semantic cast sort {cast} at {occurrence} and {cast_occurrence}"
                    ));
                }
            }
            typed_variables.insert(name, explicit);
            continue;
        }
        if bounds.casts.is_empty() {
            continue;
        }
        if let Some((least, _)) = bounds.casts.iter().find(|(candidate, _)| {
            bounds
                .casts
                .iter()
                .all(|(bound, _)| below(candidate, bound, subsorts))
        }) {
            typed_variables.insert(name, least.clone());
        } else {
            if let Some(((left, left_occurrence), (right, right_occurrence))) =
                bounds.casts.iter().enumerate().find_map(|(index, left)| {
                    bounds.casts[index + 1..].iter().find_map(|right| {
                        (!below(&left.0, &right.0, subsorts) && !below(&right.0, &left.0, subsorts))
                            .then_some((left, right))
                    })
                })
            {
                errors.push(format!(
                    "variable {name} has incomparable cast bounds {left} and {right} at {left_occurrence} and {right_occurrence}"
                ));
            } else {
                let bounds = bounds
                    .casts
                    .iter()
                    .map(|(sort, _)| sort.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                errors.push(format!(
                    "variable {name} has no least cast bound among {bounds}"
                ));
            }
        }
    }
    (casts, typed_variables, errors)
}

/// The terms whose value a semantic cast with operand `operand` constrains: the operand, the
/// operand of each nested semantic cast (a cast denotes the value of its operand), each side
/// of a rewrite (`C[L => R]` denotes `C[L]` on the left of the rule and `C[R]` on the right, so
/// `(L => R):S` constrains `L` and `R` as `L:S => R:S` does), and the pattern and the alias of an
/// `as` pattern (`P #as A` is one value, matched by `P` and bound to `A`, so `(P #as A):S`
/// constrains both as `(P:S) #as (A:S)` does).
fn cast_values(operand: &Term) -> Vec<&Term> {
    let mut values = Vec::new();
    let mut pending = vec![operand];
    // Invariant: `values` holds the visited terms and `pending` the unvisited ones whose value
    // the cast constrains; each step descends one level of the finite term.
    while let Some(value) = pending.pop() {
        values.push(value);
        match value.unannotated() {
            Term::Apply { label, arguments } if label.semantic_cast_sort().is_some() => {
                if let [inner] = arguments.as_slice() {
                    pending.push(inner);
                }
            }
            Term::Rewrite { left, right } => {
                pending.push(right);
                pending.push(left);
            }
            Term::As { pattern, alias } => {
                pending.push(alias);
                pending.push(pattern);
            }
            Term::Apply { .. }
            | Term::InjectedLabel(_)
            | Term::Token { .. }
            | Term::Variable { .. }
            | Term::Sequence(_)
            | Term::Annotated { .. } => {}
        }
    }
    values
}

/// The sorts semantic-cast resolution gives the named variables of a rule-like sentence, or the
/// resolution's error when its variables' annotations and casts disagree.
///
/// `subsorts` is the visible subsort order of the sentence's module. A variable with neither an
/// explicit sort nor a direct cast has no entry; anonymous variables have none either, since each
/// occurrence is a distinct variable.
pub(crate) fn semantic_cast_variable_sorts(
    sentence: &Sentence,
    subsorts: &PartialOrder<Sort>,
) -> Result<BTreeMap<String, Sort>, ResolveSemanticCastsError> {
    let roots: Vec<&Term> = match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => vec![body, requires, ensures],
        Sentence::Context { body, requires, .. } => vec![body, requires],
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => return Ok(BTreeMap::new()),
    };
    let (_, typed_variables, errors) = collect_cast_bounds(&roots, subsorts);
    if errors.is_empty() {
        Ok(typed_variables)
    } else {
        Err(ResolveSemanticCastsError {
            diagnostics: errors
                .into_iter()
                .flat_map(|message| sentence_error(message, sentence).diagnostics)
                .collect(),
        })
    }
}

fn is_anonymous(name: &str) -> bool {
    matches!(name, "_" | "?_" | "!_" | "@_")
}

fn bool_true() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::builtin(BuiltinSort::Bool),
    }
}

fn is_true(term: &Term) -> bool {
    matches!(
        term.unannotated(),
        Term::Token { token, sort } if token == "true" && sort.is_builtin(BuiltinSort::Bool)
    )
}

// Invariant: each call replaces an application in `casts` by its transformed argument carrying the cast sort, gives a variable its sort from `typed_variables`, and otherwise recurses into the immediate subterms of `term`; the finite `term` bounds the recursion.
fn transform(
    term: Term,
    casts: &BTreeMap<Term, usize>,
    typed_variables: &BTreeMap<String, Sort>,
    subsorts: &PartialOrder<Sort>,
) -> Term {
    let source_metadata = term.metadata().cloned();
    if casts.contains_key(term.unannotated()) {
        let TermParts::Apply { label, arguments } = term.into_unannotated().into_parts() else {
            unreachable!("the cast set contains applications only")
        };
        let sort = label
            .semantic_cast_sort()
            .expect("the cast set contains semantic casts");
        let [argument] = arguments
            .try_into()
            .unwrap_or_else(|_| unreachable!("only unary semantic casts enter the cast set"));
        return attach_sort(
            transform(argument, casts, typed_variables, subsorts),
            sort,
            subsorts,
        );
    }

    let rebuilt = match term.into_unannotated().into_parts() {
        TermParts::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(transform(*left, casts, typed_variables, subsorts)),
            right: Box::new(transform(*right, casts, typed_variables, subsorts)),
        },
        TermParts::As { pattern, alias } => Term::As {
            pattern: Box::new(transform(*pattern, casts, typed_variables, subsorts)),
            alias: Box::new(transform(*alias, casts, typed_variables, subsorts)),
        },
        TermParts::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| transform(item, casts, typed_variables, subsorts))
                .collect(),
        ),
        TermParts::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| transform(argument, casts, typed_variables, subsorts))
                .collect(),
        },
        TermParts::Variable { name, sort } => Term::Variable {
            sort: typed_variables.get(&name).cloned().or(sort),
            name,
        },
        leaf @ (TermParts::InjectedLabel(_) | TermParts::Token { .. }) => Term::from(leaf),
        TermParts::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
    };
    match source_metadata {
        Some(metadata) => rebuilt.with_metadata(metadata),
        None => rebuilt,
    }
}

/// `term`, the resolved operand of a semantic cast to `sort`, carrying that cast.
///
/// A variable keeps a sort of its own: cast-bound collection made it at or below every cast
/// that constrains its value. Another term carries the cast as its metadata sort. A term already
/// carrying a cast (a nested cast `t:T:S`) is constrained by both, and bound collection rejected
/// incomparable ones, so it keeps the narrower: `T` when `T` is at or below `S` (the outer cast
/// is then an upcast, which places nothing), else `S`. A rewrite carries the cast, and each of
/// its sides carries it as a cast written on that side would, since `(L => R):S` means
/// `L:S => R:S`; likewise an `as` pattern and its two sides, since `(P #as A):S` means
/// `(P:S) #as (A:S)`.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
fn attach_sort(term: Term, sort: Sort, subsorts: &PartialOrder<Sort>) -> Term {
    let metadata = term.metadata().cloned();
    let term = match term.into_unannotated().into_parts() {
        TermParts::Variable {
            name,
            sort: existing,
        } => {
            let variable = Term::Variable {
                name,
                sort: existing.or(Some(sort)),
            };
            return metadata.map_or(variable.clone(), |metadata| {
                variable.with_metadata(metadata)
            });
        }
        TermParts::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(attach_sort(*left, sort.clone(), subsorts)),
            right: Box::new(attach_sort(*right, sort.clone(), subsorts)),
        },
        TermParts::As { pattern, alias } => Term::As {
            pattern: Box::new(attach_sort(*pattern, sort.clone(), subsorts)),
            alias: Box::new(attach_sort(*alias, sort.clone(), subsorts)),
        },
        term => Term::from(term),
    };
    let mut metadata = metadata.unwrap_or_default();
    metadata.sort = Some(match metadata.sort.take() {
        Some(inner) if below(&inner, &sort, subsorts) => inner,
        _ => sort,
    });
    term.with_metadata(metadata)
}

#[cfg(test)]
mod tests {
    use super::{CastCondition, cast_condition};
    use crate::kast::{SortRole, sort_role::KernelSort};

    fn every_role() -> Vec<SortRole> {
        KernelSort::ALL
            .into_iter()
            .map(SortRole::Kernel)
            .chain([
                SortRole::RigidVariable,
                SortRole::Scaffolding,
                SortRole::Nat,
                SortRole::Defined,
            ])
            .collect()
    }

    #[test]
    fn a_cast_adds_a_sort_predicate_exactly_for_a_sort_that_has_one() {
        for role in every_role() {
            assert_eq!(
                matches!(cast_condition(role), CastCondition::SortPredicate),
                role.has_sort_predicate(),
                "{role:?}"
            );
            assert_eq!(
                matches!(cast_condition(role), CastCondition::CellFragment),
                role == SortRole::Kernel(KernelSort::Bag),
                "{role:?}"
            );
        }
    }
}

#[cfg(test)]
mod head_alias_tests {
    use crate::definition::{RuleHead, Sentence};
    use crate::kast::{Sort, Term};
    use crate::kompile::stage_harness::{labelled, run_to_stage};

    /// The sort of the root alias of the rule labelled `label` in module `MAIN` of `definition`.
    fn alias_sort(definition: &crate::definition::Definition, label: &str) -> Option<Sort> {
        let rules = labelled(definition, "MAIN", label);
        assert_eq!(rules.len(), 1, "{label}");
        let Sentence::Rule { body, .. } = rules[0] else {
            panic!("{label} is not a rule")
        };
        let Term::As { alias, .. } = RuleHead::of(body).left.unannotated() else {
            panic!("{label} has no root alias")
        };
        let Term::Variable { sort, .. } = alias.unannotated() else {
            panic!("the alias of {label} is not a variable")
        };
        sort.clone()
    }

    /// `f(X) #as _V => done(X)` states `f(X) = done(X)` at the result sort `Exp` of `f`, and `_V`
    /// names the matched application of `f`, so `_V` is a variable of `Exp`, whatever sort the
    /// rule body's position gave it. A rule placed in a cell keeps its alias's inferred sort.
    #[test]
    fn a_root_alias_of_a_function_rule_has_the_head_sort() {
        let run = run_to_stage(
            r#"
module MAIN
  syntax K
  syntax Exp ::= "a" [symbol(a)] | "b" [symbol(b)] | done(Exp) [symbol(done)]
  syntax Exp ::= f(Exp) [function, symbol(f)]
  configuration <k> a </k>
  rule f(X) #as _V => done(X) [label(aliased)]
  rule b #as _W => a [label(cell)]
  rule a => f(b) [label(step)]
endmodule
"#,
            "resolve semantic casts",
        );
        let exp = Sort::new("Exp");
        assert_eq!(alias_sort(run.output(), "aliased"), Some(exp.clone()));
        assert_ne!(alias_sort(run.output(), "cell"), Some(exp));
    }
}
