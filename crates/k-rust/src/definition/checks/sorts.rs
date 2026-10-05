//! These definition checks traverse module sentences and terms linearly, plus one closure-free cycle search for kernel sort positions and one synonym closure per module view; callers supply derived catalogs and no dedicated counter is recorded.
//!
//! Sort, synonym, user-list and kernel-sort-position checks performed while outer modules are constructed.

use std::collections::{BTreeMap, BTreeSet};

use super::super::partial_order::{Cycle, PartialOrder, first_cycle};
use super::super::relations::{
    SubsortDeclaration, disambiguation_subsort_pairs, states_disambiguation_subsort,
};
use super::super::sort_catalog::SortShape;
use super::super::synonyms::{AliasMeaning, FixedAliasRole, synonym_overlaps};
use super::super::{
    ProductionItem, ResolvedDefinition, ResolvedModule, Sentence, SortCatalog, SortHead,
    SortSynonyms, Spelling, SynonymDefect,
};
use crate::definition::AttributeKey;
use crate::definition::production_kind::mentions_parameter;
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::sort_role::{KernelSort, NumeralSpelling, numeral_spelling};
use crate::kast::{FrontendSort, Sort, SortRole};

/// Check declared sort shapes and nonterminal denotations in the module's view.
pub fn check_sorts(module: &ResolvedModule, sorts: &SortCatalog<'_>) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    // Invariant: `diagnostics` holds the numeral-sort, parametric-sort and undefined-sort errors of every entry of `module.local_sentences` before `sentence`; each iteration consumes one local sentence.
    for sentence in module.local_sentences.iter().map(std::sync::Arc::as_ref) {
        numeral_sort_diagnostics(sentence, sorts, &mut diagnostics);
        match sentence {
            Sentence::SyntaxSort {
                parameters, sort, ..
            } => {
                if parameters.contains(sort) {
                    diagnostics.push(Diagnostic::error(
                        DiagnosticCode::UnsupportedParametricSort,
                        format!(
                            "syntax {{{}}} {sort} declares no sort: {sort} is a sort parameter of this declaration, so it names every sort, and the declaration's attributes would apply to all of them; declare each sort by name",
                            parameters.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ")
                        ),
                        sentence,
                    ));
                } else {
                    check_declared_sort(sort, parameters, sorts, sentence, &mut diagnostics);
                }
            }
            Sentence::SortSynonym { new_sort, .. } => match SortShape::of(new_sort, &[]) {
                SortShape::UnsupportedHead => {
                    diagnostics.push(unsupported_head(new_sort, sentence));
                }
                SortShape::NestedArgument => {
                    diagnostics.push(nested_argument(new_sort, sentence));
                }
                SortShape::Parameter
                | SortShape::Nullary
                | SortShape::Instance { .. }
                | SortShape::Schematic { .. } => {}
            },
            Sentence::Production {
                parameters,
                sort,
                items,
                attributes,
                ..
            } => {
                if parameters.contains(sort) && attributes.has(AttributeKey::Token) {
                    diagnostics.push(Diagnostic::error(
                        DiagnosticCode::InvalidTokenProduction,
                        format!("A token production whose sort is its own sort parameter {sort} gives every sort domain values, including every sort that has constructors, and a sort with domain values has no constructors; declare the token production at each sort that has these tokens"),
                        sentence,
                    ));
                }
                match SubsortDeclaration::of(sentence) {
                    Some(SubsortDeclaration::Parametric) => {
                        let [ProductionItem::NonTerminal { sort: child, .. }] = items.as_slice()
                        else {
                            unreachable!("a subsort declaration has exactly one nonterminal");
                        };
                        diagnostics.push(Diagnostic::error(
                            DiagnosticCode::UnsupportedParametricSort,
                            format!("Parametric subsort declarations are currently unsupported: {sort} ::= {child}; declare the subsort of each instance instead"),
                            sentence,
                        ));
                    }
                    Some(
                        SubsortDeclaration::Pair { .. }
                        | SubsortDeclaration::KernelTop
                        | SubsortDeclaration::KernelBottom,
                    )
                    | None => {}
                }
                check_declared_sort(sort, parameters, sorts, sentence, &mut diagnostics);

                let missing = items
                    .iter()
                    .filter_map(|item| {
                        let ProductionItem::NonTerminal { sort, .. } = item else {
                            return None;
                        };
                        if parameters.contains(sort) {
                            return None;
                        }
                        let sort = match sorts.sort_synonyms().spelling(sort) {
                            Spelling::Sort => sort,
                            Spelling::Synonym { denotes } => denotes,
                            Spelling::Undenoted => return None,
                        };
                        if !sort.role().has_terms() {
                            return None;
                        }
                        match SortShape::of(sort, parameters) {
                            // A nested operand names no instance, so it is reported as nested
                            // and not also as a missing sort.
                            SortShape::NestedArgument => {
                                diagnostics.push(nested_argument(sort, sentence));
                                return None;
                            }
                            SortShape::Parameter
                            | SortShape::Nullary
                            | SortShape::Instance { .. }
                            | SortShape::Schematic { .. }
                            | SortShape::UnsupportedHead => {}
                        }
                        let head = SortHead::from(sort);
                        let missing_head =
                            !parameters.contains(sort) && !sorts.defined_heads().contains(&head);
                        // An operand that mentions no formal parameter at any depth names one
                        // sort, so it must be a declared instance; one that mentions a parameter
                        // names a family and is instantiated with the production.
                        let missing_instantiation = !sort.parameters.is_empty()
                            && !mentions_parameter(sort, parameters)
                            && !sorts
                                .instantiations()
                                .get(&head)
                                .is_some_and(|instances| instances.contains(sort));
                        (missing_head || missing_instantiation).then_some(sort)
                    })
                    .collect::<Vec<_>>();

                if !missing.is_empty() {
                    diagnostics.push(Diagnostic::error(
                        DiagnosticCode::UndefinedSort,
                        format!(
                            "Could not find sorts: [{}]",
                            missing
                                .iter()
                                .map(ToString::to_string)
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                        sentence,
                    ));
                }
            }
            Sentence::SyntaxLexical { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => {}
        }
    }

    diagnostics
}

/// N1: production results and operands have terms, numeral declarations carry neither `token`
/// nor `hook`, and synonym aliases and sentence sort parameters are not numerals.
/// A compiled numeral declaration names a natural-number width so a parametric sort such as
/// `MInt{8}` is well formed; it does not name a set of terms that a sentence can produce or accept.
/// Every written numeral, including arguments at any depth, must use that width's one spelling.
fn numeral_sort_diagnostics(
    sentence: &Sentence,
    sorts: &SortCatalog<'_>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let mut written = Vec::new();
    match sentence {
        Sentence::Production {
            parameters,
            sort,
            items,
            ..
        } => {
            written.extend(parameters);
            written.push(sort);
            written.extend(items.iter().filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort),
                ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
            }));
        }
        Sentence::SyntaxSort {
            parameters, sort, ..
        } => {
            written.extend(parameters);
            written.push(sort);
        }
        Sentence::SortSynonym {
            new_sort, old_sort, ..
        } => written.extend([new_sort, old_sort]),
        Sentence::SyntaxLexical { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Rule { .. }
        | Sentence::Claim { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => {}
    }
    let mut noncanonical = BTreeSet::new();
    while let Some(sort) = written.pop() {
        if let NumeralSpelling::NonCanonical { canonical } = numeral_spelling(&sort.name)
            && noncanonical.insert(&sort.name)
        {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::InvalidNumeralSort,
                format!("Sort {} is a numeral written with a leading zero; a width is spelled {canonical}.", sort.name),
                sentence,
            ));
        }
        written.extend(&sort.parameters);
    }
    let mut reported = BTreeSet::new();
    let mut check = |sort: &Sort, place| {
        if !sort.role().has_terms() && reported.insert((place, sort.clone())) {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::InvalidNumeralSort,
                format!("Sort {sort} is a numeral: it names a width, such as the argument of MInt{{{sort}}}, and has no terms, so it cannot be {place}."),
                sentence,
            ));
        }
    };
    match sentence {
        Sentence::Production {
            parameters,
            sort,
            items,
            ..
        } => {
            for parameter in parameters {
                check(parameter, "a sort parameter");
            }
            if !parameters.contains(sort) {
                check(sort, "the sort of a production");
            }
            for item in items {
                if let ProductionItem::NonTerminal { sort, .. } = item {
                    if parameters.contains(sort) {
                        continue;
                    }
                    match sorts.sort_synonyms().spelling(sort) {
                        Spelling::Sort => check(sort, "an operand of a production"),
                        Spelling::Synonym { denotes } => {
                            check(denotes, "an operand of a production")
                        }
                        Spelling::Undenoted => {}
                    }
                }
            }
        }
        Sentence::SyntaxSort {
            parameters,
            sort,
            attributes,
        } => {
            for parameter in parameters {
                check(parameter, "a sort parameter");
            }
            if attributes.has(AttributeKey::Token) || attributes.has(AttributeKey::Hook) {
                check(sort, "a token or hooked sort");
            }
        }
        Sentence::SortSynonym { new_sort, .. } => check(new_sort, "a sort synonym"),
        Sentence::SyntaxLexical { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Rule { .. }
        | Sentence::Claim { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => {}
    }
}

/// Check the sort a declaration or a production result writes, with the sentence's formal sort
/// `parameters`, against the admitted shapes ([`SortShape`]).
///
/// A declared instance `MInt{a}` whose argument is not a formal parameter must name a width or a
/// sort the module knows: a numeral or a defined sort head. A synonym argument is rejected because
/// application does not rewrite inside sort arguments.
fn check_declared_sort(
    sort: &Sort,
    parameters: &[Sort],
    sorts: &SortCatalog<'_>,
    sentence: &Sentence,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match SortShape::of(sort, parameters) {
        SortShape::UnsupportedHead => diagnostics.push(unsupported_head(sort, sentence)),
        SortShape::NestedArgument => diagnostics.push(nested_argument(sort, sentence)),
        SortShape::Instance { argument } => {
            if matches!(
                numeral_spelling(&argument.name),
                NumeralSpelling::NonCanonical { .. }
            ) {
                return;
            }
            match sorts.sort_synonyms().spelling(argument) {
                Spelling::Sort => {
                    if argument.role() != SortRole::Nat
                        && !sorts.defined_heads().contains(&SortHead::from(argument))
                    {
                        diagnostics.push(Diagnostic::error(
                            DiagnosticCode::UndefinedSort,
                            format!("Could not find sorts: [{argument}]"),
                            sentence,
                        ));
                    }
                }
                Spelling::Synonym { denotes } => {
                    diagnostics.push(Diagnostic::error(
                    DiagnosticCode::UndefinedSort,
                    format!(
                        "Could not find sorts: [{argument}] ({argument} is a sort synonym of {denotes}, and synonyms are not applied inside the arguments of {sort})"
                    ),
                    sentence,
                ));
                }
                Spelling::Undenoted => {}
            }
        }
        SortShape::Parameter | SortShape::Nullary | SortShape::Schematic { .. } => {}
    }
}

fn unsupported_head(sort: &Sort, sentence: &Sentence) -> Diagnostic {
    Diagnostic::error(
        DiagnosticCode::UnsupportedParametricSort,
        format!("User-defined parametric sorts are currently unsupported: {sort}"),
        sentence,
    )
}

fn nested_argument(sort: &Sort, sentence: &Sentence) -> Diagnostic {
    Diagnostic::error(
        DiagnosticCode::UnsupportedParametricSort,
        format!("Nested parametric sorts are currently unsupported: {sort}"),
        sentence,
    )
}

/// Report each synonym defect once, at the first module whose view contains it.
/// Views only grow under import, so an importer does not repeat its importee's defect.
/// Equations with neither source nor location are deduplicated by spelling, so identical defects
/// in unrelated modules without origins produce one diagnostic.
pub fn check_sort_synonyms(definition: &ResolvedDefinition) -> Vec<Diagnostic> {
    if !definition.modules().any(|(_, module)| {
        module
            .local_sentences
            .iter()
            .any(|sentence| matches!(sentence.as_ref(), Sentence::SortSynonym { .. }))
    }) {
        return Vec::new();
    }
    let mut diagnostics = Vec::new();
    let mut reported = BTreeSet::new();
    let synonyms = definition
        .modules()
        .map(|(id, _)| (id, SortSynonyms::of_module(definition, id)))
        .collect::<BTreeMap<_, _>>();
    for (module_id, module) in definition.modules() {
        for defect in synonyms[&module_id].defects() {
            let (declarations, message) = match defect {
                SynonymDefect::Cycle { declarations } => {
                    let equations = declarations
                        .iter()
                        .map(|sentence| {
                            let Sentence::SortSynonym {
                                new_sort, old_sort, ..
                            } = sentence
                            else {
                                unreachable!("a synonym cycle contains only synonym declarations");
                            };
                            format!("{new_sort} = {old_sort}{}", synonym_location(sentence))
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    (
                        declarations.clone(),
                        format!("sort synonyms {equations} form a cycle, so they denote no sort"),
                    )
                }
                SynonymDefect::Ambiguous {
                    alias,
                    declarations,
                } => {
                    let denotations = declarations
                        .iter()
                        .map(|(sentence, denotes)| {
                            format!("{denotes}{}", synonym_location(sentence))
                        })
                        .collect::<Vec<_>>()
                        .join(" and ");
                    (
                        declarations.iter().map(|(sentence, _)| *sentence).collect(),
                        format!(
                            "sort synonym {alias} denotes both {denotations} in the view of module {}",
                            module.name
                        ),
                    )
                }
            };
            // A view may order the same declarations differently; their origins and equations,
            // not that order, identify the defect already reported by an importee.
            let key = declarations
                .iter()
                .map(|sentence| {
                    let Sentence::SortSynonym {
                        new_sort, old_sort, ..
                    } = sentence
                    else {
                        unreachable!("a synonym defect contains only synonym declarations");
                    };
                    (
                        new_sort.clone(),
                        old_sort.clone(),
                        sentence.attributes().source().map(str::to_owned),
                        sentence.attributes().location(),
                    )
                })
                .collect::<BTreeSet<_>>();
            if reported.insert(key) {
                let first = declarations
                    .first()
                    .expect("a synonym defect has at least one declaration");
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidSortSynonym,
                    message,
                    first,
                ));
            }
        }
    }
    for (module_id, overlap) in synonym_overlaps(definition, &synonyms) {
        let alias = &overlap.alias;
        let referent = overlap.referent;
        let meaning = match overlap.meaning {
            AliasMeaning::Declared(sentence) => {
                synonym_position_meaning(alias, sentence, "declared as a sort")
            }
            AliasMeaning::Positioned(sentence) => synonym_position_meaning(
                alias,
                sentence,
                "given a sort position in generated or injected grammar syntax",
            ),
            AliasMeaning::GeneratedCell(cell) => format!(
                "{alias} names the compiler-generated {} configuration cell",
                cell.label()
            ),
            AliasMeaning::Role(role) => match role {
                FixedAliasRole::Kernel => {
                    format!("{alias} is a kernel sort, whose meaning K fixes")
                }
                FixedAliasRole::Scaffolding => {
                    format!("{alias} is a parser sort (#), which has no terms")
                }
                FixedAliasRole::RigidVariable => format!("{alias} is the rigid sort variable"),
            },
        };
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::InvalidSortSynonym,
            format!("Sort synonym {alias} = {referent} gives {alias} a second meaning in module {}: {meaning}.", definition.module(module_id).name),
            overlap.synonym,
        ));
    }
    diagnostics
}

fn synonym_position_meaning(alias: &Sort, sentence: &Sentence, position: &str) -> String {
    let summary = match sentence {
        Sentence::SyntaxSort { sort, .. } => format!("syntax {sort}"),
        Sentence::Production { sort, items, .. } => {
            let items = items
                .iter()
                .map(|item| match item {
                    ProductionItem::NonTerminal { sort, .. } => sort.to_string(),
                    ProductionItem::Terminal(text) => format!("{text:?}"),
                    ProductionItem::RegexTerminal { regex, .. } => {
                        format!("r{regex:?}")
                    }
                })
                .collect::<Vec<_>>()
                .join(" ");
            format!("syntax {sort} ::= {items}")
        }
        Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Rule { .. }
        | Sentence::Claim { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => {
            unreachable!("only sort declarations and productions declare sort heads")
        }
    };
    format!(
        "{alias} is {position} by {summary}{}",
        synonym_location(sentence)
    )
}

fn synonym_location(sentence: &Sentence) -> String {
    let attributes = sentence.attributes();
    match (attributes.source(), attributes.location()) {
        (Some(source), Some(location)) => {
            format!(
                " ({source}:{}:{})",
                location.start_line, location.start_column
            )
        }
        (Some(source), None) => format!(" ({source})"),
        (None, Some(location)) => {
            format!(" ({}:{})", location.start_line, location.start_column)
        }
        (None, None) => String::new(),
    }
}

/// Reject a sort declared as a user list by two declarations from different origins. A user
/// list sort takes its constructor, terminator and element sort from its declaration, so a
/// second one would give the sort two list structures; one declaration seen through several
/// imports keeps one origin and is accepted.
pub fn check_user_lists(module: &ResolvedModule, visible: &[&Sentence]) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    // Start with local declarations so an imported declaration retained by sentence deduplication can still be compared with its equivalent local declaration.
    // Also inspect non-local visible declarations to reject conflicts between sibling imports before rule grammar construction.
    let candidates = module
        .local_sentences
        .iter()
        .map(std::sync::Arc::as_ref)
        // Invariant: the chain yields every entry of `module.local_sentences`, then each entry of `visible` that is not pointer-equal to a local sentence; the filter scans `module.local_sentences` once per entry of `visible`, O(|visible| * |local_sentences|).
        .chain(visible.iter().copied().filter(|candidate| {
            !module
                .local_sentences
                .iter()
                .any(|local| std::ptr::eq(local.as_ref(), *candidate))
        }));
    // Invariant: `diagnostics` holds an error for every entry of `candidates` before `sentence` whose sort has a user-list production in `visible` from another origin; each iteration consumes one candidate and scans `visible` once with `find`, O(|candidates| * |visible|).
    for sentence in candidates {
        let Sentence::Production {
            sort, attributes, ..
        } = sentence
        else {
            continue;
        };
        if !attributes.has(AttributeKey::UserList) {
            continue;
        }

        let own_origin = (attributes.source(), attributes.location());
        let previous = visible.iter().copied().find(|candidate| {
            let Sentence::Production {
                sort: candidate_sort,
                attributes: candidate_attributes,
                ..
            } = candidate
            else {
                return false;
            };
            candidate_sort == sort
                && candidate_attributes.has(AttributeKey::UserList)
                && (
                    candidate_attributes.source(),
                    candidate_attributes.location(),
                ) != own_origin
        });
        let Some(previous) = previous else {
            continue;
        };
        let (Some(source), Some(location)) = (
            previous.attributes().source(),
            previous.attributes().location(),
        ) else {
            continue;
        };
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::DuplicateUserList,
            format!(
                "Sort {sort} previously declared as a user list at Source({source}) and Location({},{},{},{})",
                location.start_line,
                location.start_column,
                location.end_line,
                location.end_column
            ),
            sentence,
        ));
    }

    diagnostics
}

/// The pairs `K` fixes among its kernel sorts and the sorts of `sorts`, each with the reason it
/// holds: the kernel completion of `sorts`.
///
/// - `KItem < K`;
/// - `S < KItem` for every `S` whose terms are all K items and which is neither `K` nor `KItem`
///   ([`crate::kast::SortRole::has_implicit_kitem_subsort`]);
/// - `KBott < S`, `#KVariable < S` and `KConfigVar < S` for every `S` a variable may stand at
///   ([`crate::kast::SortRole::admits_variables`]);
/// - `#KVariable < KBott`, `KConfigVar < KBott` and `Cell < Bag`.
///
/// The completion alone is acyclic: its pairs lead from the variable tokens through `KBott`, then
/// `Cell`, then the other sorts of `sorts`, to `KItem` and finally `K`, and no pair leads back.
fn kernel_completion(sorts: &BTreeSet<Sort>) -> BTreeMap<(Sort, Sort), String> {
    let k = KernelSort::K.sort();
    let kitem = KernelSort::KItem.sort();
    let kbott = KernelSort::KBott.sort();
    let kconfigvar = KernelSort::KConfigVar.sort();
    let kvariable = Sort::frontend(FrontendSort::KVariable);
    let mut completion = BTreeMap::new();
    let mut add = |lesser: &Sort, greater: &Sort, reason: String| {
        completion
            .entry((lesser.clone(), greater.clone()))
            .or_insert(reason);
    };
    add(&kitem, &k, "KItem is below K".to_owned());
    add(&kvariable, &kbott, "a variable is a KBott".to_owned());
    add(
        &kconfigvar,
        &kbott,
        "a configuration variable is a KBott".to_owned(),
    );
    add(
        &KernelSort::Cell.sort(),
        &KernelSort::Bag.sort(),
        "every Cell is a Bag".to_owned(),
    );
    // Invariant: `completion` holds the fixed pairs and the pairs of every entry of `sorts` before `sort`; each iteration consumes one sort and adds at most four pairs.
    for sort in sorts {
        let role = sort.role();
        if role.has_implicit_kitem_subsort() {
            add(sort, &kitem, format!("every {sort} is a KItem"));
        }
        if role.admits_variables() {
            add(&kbott, sort, format!("a variable may stand at {sort}"));
            add(&kvariable, sort, format!("a variable may stand at {sort}"));
            add(
                &kconfigvar,
                sort,
                format!("a configuration variable may stand at {sort}"),
            );
        }
    }
    completion
}

/// The first cycle of a module view's declared subsorts completed with the kernel positions of its
/// sorts, when the declared subsorts alone are acyclic.
///
/// A cycle found places a sort of K items at or above `KItem` or `K`, or a sort a variable stands
/// at at or below `KBott`, `#KVariable` or `KConfigVar`: the declarations contradict a kernel
/// position, so no grammar built from the view has an order of its sorts. A cycle of the declared
/// subsorts alone is the definition's circular subsort error, which its own checks report, so it is
/// not searched for here. The grammar builders call this before generating any production; the
/// load reports the same contradiction with a diagnostic through [`check_outer_modules`].
pub(crate) fn kernel_position_cycle(visible: &[&Sentence]) -> Option<Cycle<Sort>> {
    kernel_position_search(visible, &BTreeSet::new()).map(|search| search.cycle)
}

/// A cycle of a module view's declared subsorts and their kernel completion, with the relations
/// that close it.
struct KernelPositionSearch {
    declared: BTreeSet<(Sort, Sort)>,
    completion: BTreeMap<(Sort, Sort), String>,
    cycle: Cycle<Sort>,
}

/// The declared pairs a view's rule grammar starts from, [`disambiguation_subsort_pairs`], and
/// their kernel completion over the sorts they mention and the sorts the view declares.
struct RuleGrammarRelation {
    declared: BTreeSet<(Sort, Sort)>,
    completion: BTreeMap<(Sort, Sort), String>,
}

fn rule_grammar_relation(visible: &[&Sentence]) -> RuleGrammarRelation {
    let declared = disambiguation_subsort_pairs(visible);
    let mut sorts = declared
        .iter()
        .flat_map(|(lesser, greater)| [lesser.clone(), greater.clone()])
        .collect::<BTreeSet<_>>();
    // Invariant: `sorts` holds the sorts of `declared` and the sort declared by every entry of `visible` before `sentence`; each iteration consumes one sentence.
    for sentence in visible {
        match sentence {
            Sentence::SyntaxSort { sort, .. } => {
                sorts.insert(sort.clone());
            }
            // The result sort of a parametric production that is one of its sort parameters is a
            // sort variable, not a declared sort.
            Sentence::Production {
                parameters, sort, ..
            } if !parameters.contains(sort) => {
                sorts.insert(sort.clone());
            }
            Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => {}
        }
    }
    let completion = kernel_completion(&sorts);
    RuleGrammarRelation {
        declared,
        completion,
    }
}

/// The order of a module view's rule grammar: the declared pairs it starts from completed with
/// the kernel positions of its sorts ([`kernel_completion`]).
///
/// It is the order in which that grammar admits a term at an argument position: a term of sort
/// `S` stands at a nonterminal of sort `T` exactly when `S <= T` in it. Every sort of K items lies
/// below `KItem` and `K` in it, though the definition's declared subsort order does not state
/// those pairs. An error is a cycle of the declared pairs or a kernel position contradiction,
/// which the definition's own checks report.
pub(crate) fn rule_grammar_subsorts(
    visible: &[&Sentence],
) -> Result<PartialOrder<Sort>, Cycle<Sort>> {
    let RuleGrammarRelation {
        declared,
        completion,
    } = rule_grammar_relation(visible);
    PartialOrder::new(declared.into_iter().chain(completion.into_keys()))
}

/// Search `visible`'s declared subsorts, less the pairs of `excluded`, completed with the kernel
/// positions of its sorts for a cycle; `None` when the declared subsorts alone are cyclic.
fn kernel_position_search(
    visible: &[&Sentence],
    excluded: &BTreeSet<(Sort, Sort)>,
) -> Option<KernelPositionSearch> {
    let RuleGrammarRelation {
        declared,
        completion,
    } = rule_grammar_relation(visible);
    if first_cycle(declared.iter().cloned()).is_some() {
        return None;
    }
    let cycle = first_cycle(
        declared
            .iter()
            .filter(|pair| !excluded.contains(*pair))
            .chain(completion.keys())
            .cloned(),
    )?;
    Some(KernelPositionSearch {
        declared,
        completion,
        cycle,
    })
}

/// Reject a module view whose declared subsorts contradict the positions `K` fixes for its kernel
/// sorts.
///
/// The declared relation `D` is the one the view's rule grammar starts from: the semantic subsort
/// pairs of its unlabeled, non-parametric unary productions and the `(element, list)` pairs of its
/// user lists. Completed with the kernel positions of the sorts it mentions or the view declares
/// ([`kernel_completion`], itself acyclic), it must stay acyclic: a cycle then places a sort of K
/// items at or above `KItem` or `K`, or a sort a variable stands at at or below `KBott`,
/// `#KVariable` or `KConfigVar`, which no order of K terms can have.
///
/// A cycle of `D` alone is the definition's circular subsort error and is left to the checks that
/// report it.
/// The declared steps of every contradiction already reported, at an earlier module of the dependency order, are left out of the search.
/// A view that only repeats an earlier contradiction therefore finds no cycle, and a cycle still found is a contradiction independent of those already reported.
/// It is reported once, on the first step of its cycle that is declared and not a kernel position.
fn check_kernel_sort_positions(
    visible: &[&Sentence],
    reported: &mut BTreeSet<(Sort, Sort)>,
) -> Option<Diagnostic> {
    let KernelPositionSearch {
        declared,
        completion,
        cycle,
    } = kernel_position_search(visible, reported)?;

    let steps = cycle
        .path
        .windows(2)
        .map(|step| (step[0].clone(), step[1].clone()))
        .collect::<Vec<_>>();
    // A declared pair that the completion also holds (the prelude's `K ::= KItem`) restates a
    // kernel position and contradicts nothing, so the steps to blame are the declared pairs the
    // completion does not hold.
    let contradicting =
        |step: &(Sort, Sort)| declared.contains(step) && !completion.contains_key(step);
    let declared_steps = steps
        .iter()
        .filter(|step| contradicting(step))
        .cloned()
        .collect::<BTreeSet<_>>();
    let (first_lesser, first_greater) = steps.iter().find(|step| contradicting(step)).expect(
        "the completion is acyclic, so a cycle of the union has a declared step outside it",
    );
    let stating = |lesser: &Sort, greater: &Sort| {
        visible
            .iter()
            .copied()
            .find(|sentence| states_disambiguation_subsort(sentence, lesser, greater))
            .expect("every declared pair is stated by a visible sentence")
    };
    let sentence = stating(first_lesser, first_greater);
    reported.extend(declared_steps.iter().cloned());

    let explanation = steps
        .iter()
        .map(|(lesser, greater)| {
            if declared_steps.contains(&(lesser.clone(), greater.clone())) {
                format!(
                    "{lesser} < {greater} is declared by {}",
                    declared_step_text(stating(lesser, greater), lesser, greater)
                )
            } else {
                format!(
                    "{lesser} < {greater} because {}",
                    completion[&(lesser.clone(), greater.clone())]
                )
            }
        })
        .collect::<Vec<_>>()
        .join("; ");
    let path = cycle
        .path
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" < ");
    Some(Diagnostic::error(
        DiagnosticCode::KernelSortPosition,
        format!(
            "the declared subsorts contradict the positions K fixes for its kernel sorts, closing the cycle {path}: {explanation}"
        ),
        sentence,
    ))
}

/// The text of the declaration that states the declared subsort `lesser < greater`.
fn declared_step_text(sentence: &Sentence, lesser: &Sort, greater: &Sort) -> String {
    let user_list = matches!(sentence, Sentence::Production { attributes, .. }
        if attributes.has(AttributeKey::UserList));
    if user_list {
        format!("the user list {greater} of {lesser}")
    } else {
        format!("`syntax {greater} ::= {lesser}`")
    }
}

/// Run the outer-module checks over every module in dependency order: the sorts and user lists
/// each module declares, and the kernel sort positions of each module view's declared subsorts,
/// leaving declared steps of previously reported kernel-position contradictions out of later searches.
/// Synonym cycles, ambiguities and overlaps are reported once at the first module whose view contains them.
pub fn check_outer_modules(definition: &ResolvedDefinition) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let mut reported_kernel_contradictions = BTreeSet::new();
    for (module_id, module) in definition.modules() {
        let visible = definition.sentences(module_id);
        let sorts = definition.sort_catalog(module_id);
        diagnostics.extend(check_sorts(module, &sorts));
        diagnostics.extend(check_user_lists(module, &visible));
        diagnostics.extend(super::production_shapes::check_cell_attributes(
            module, &sorts,
        ));
        diagnostics.extend(check_kernel_sort_positions(
            &visible,
            &mut reported_kernel_contradictions,
        ));
    }
    diagnostics.extend(check_sort_synonyms(definition));
    diagnostics
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_kernel_completion_of_every_role_is_acyclic() {
        let sorts = KernelSort::ALL
            .iter()
            .map(|kernel| kernel.sort())
            .chain([
                Sort::new("Exp"),
                Sort::new("8"),
                Sort::frontend(FrontendSort::SortParam),
                Sort::frontend(FrontendSort::KVariable),
                Sort::frontend(FrontendSort::RuleBody),
            ])
            .collect::<BTreeSet<_>>();
        let completion = kernel_completion(&sorts);
        assert_eq!(first_cycle(completion.keys().cloned()), None);
        let kitem = KernelSort::KItem.sort();
        assert!(completion.contains_key(&(Sort::new("Exp"), kitem.clone())));
        assert!(!completion.contains_key(&(KernelSort::KList.sort(), kitem)));
        assert!(completion.contains_key(&(KernelSort::KBott.sort(), KernelSort::KList.sort())));
    }
}
