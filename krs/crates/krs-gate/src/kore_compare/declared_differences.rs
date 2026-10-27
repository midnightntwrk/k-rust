//! Declared k-rust/Java K differences that the comparator removes before comparing.
//!
//! Each normalization ports one entry of k-rust's `scripts/reference-normalisations.toml` at the pinned commit.
//! Each acts only on the exact generated shapes that entry names and fails closed otherwise.
//! upstream k-rust/declared-difference-normalizations (reviewed, not a request): both are documented k-rust contract differences.
//! For N33, upstream k/injective-on-anywhere-macro-alias-heads asks whether K's `injective` on such heads is sound.

use std::collections::BTreeSet;

use k_rust::kore::ast::{
    Attributes, Module, Pattern, Sentence, Sort, Symbol, Variable, VariableKind,
};
use k_rust::kore::parser::parse_pattern;

use super::{
    CompareError, has_nullary_attribute, is_application_over_variables, visit_pattern_symbols,
    visit_sentence_symbols,
};

const CONFIG_VALUE_BOX: &str = "Lbl'Hash'KConfigValue";
const CONFIG_VALUE_UNBOX: &str = "Lbl'Hash'unboxKConfigValue";
const PROJECTION_PREFIX: &str = "Lblproject'Coln'";
const EQUATION_HEAD_ATTRIBUTES: [&str; 5] =
    ["anywhere", "macro", "macro-rec", "alias", "alias-rec"];

/// The sole decoder equation k-rust generates for the private configuration-value box.
const CONFIG_VALUE_DECODER: &str = r"\implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortKItem{},R}(X0:SortKItem{}, Lbl'Hash'KConfigValue{}(VarKS:SortK{})), \top{R}())), \equals{SortK{},R}(Lbl'Hash'unboxKConfigValue{}(X0:SortKItem{}), \and{SortK{}}(VarKS:SortK{}, \top{SortK{}}())))";

/// Drop `injective` from reference declarations of equation heads that the native route declares without it (k-rust N33).
///
/// A symbol that heads an `anywhere`, macro-like, or alias equation may have two applications with different arguments identified by that equation, so k-rust withholds `injective` from it (`docs/compatibility.md`, "Anywhere rules").
/// Only a reference declaration that also carries one of those equation-head attributes changes, and only when the native module declares the same symbol without `injective`.
/// The native route can never gain `injective` this way, and every other attribute stays compared.
/// Returns the number of reference declarations changed.
pub(super) fn withhold_reference_injective(reference: &mut Module, native: &Module) -> usize {
    let native_without_injective = native
        .sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::SymbolDeclaration {
                symbol, attributes, ..
            } if !has_nullary_attribute(attributes, "injective") => Some(symbol.name.as_str()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let mut changed = 0;
    for sentence in &mut reference.sentences {
        let Sentence::SymbolDeclaration {
            symbol, attributes, ..
        } = sentence
        else {
            continue;
        };
        if !native_without_injective.contains(symbol.name.as_str())
            || !has_nullary_attribute(attributes, "injective")
            || !EQUATION_HEAD_ATTRIBUTES
                .iter()
                .any(|name| has_nullary_attribute(attributes, name))
        {
            continue;
        }
        attributes.0.retain(|attribute| {
            !matches!(
                attribute,
                Pattern::Application { symbol, arguments }
                    if symbol.name == "injective" && arguments.is_empty()
            )
        });
        changed += 1;
    }
    changed
}

/// Remove k-rust's private configuration-value transport from the native module (k-rust N37).
///
/// k-rust carries every configuration-map value as `#KConfigValue(K):KItem` and decodes it with the partial `#unboxKConfigValue(KItem):K` (`docs/compatibility.md`, "Configuration value transport"); Java K uses item transport.
/// This removes the two private declarations, the box's functional, injectivity, and no-confusion axioms, its no-junk alternative, and its sole decoder equation.
/// It translates only cell-initializer projections of decoded configuration-map lookups back to the reference's `kseq(lookup, dotk)` item transport.
/// Returns the number of removed sentences, removed no-junk alternatives, and translated reads.
///
/// # Errors
///
/// Fails when the reference mentions either private symbol, when only one private declaration or a malformed one is present, and when any mention of either symbol survives the normalization.
pub(super) fn remove_configuration_value_transport(
    reference: &Module,
    native: &mut Module,
) -> Result<usize, CompareError> {
    if module_mentions_transport(reference) {
        return Err(CompareError::new(
            "reference declares or uses k-rust's private configuration-value transport",
        ));
    }
    let declarations = native
        .sentences
        .iter()
        .filter(|sentence| transport_declaration(sentence))
        .count();
    if declarations == 0 && !module_mentions_transport(native) {
        return Ok(0);
    }
    if declarations != 2 {
        return Err(CompareError::new(format!(
            "native configuration-value transport has {declarations} of its 2 well-formed private declarations"
        )));
    }
    let decoder = parse_pattern(CONFIG_VALUE_DECODER)
        .map_err(|error| CompareError::new(format!("cannot parse decoder shape: {error}")))?;

    let before = native.sentences.len();
    native.sentences.retain(|sentence| {
        !(transport_declaration(sentence)
            || box_functional_axiom(sentence)
            || box_constructor_axiom(sentence)
            || matches!(sentence, Sentence::Axiom { pattern, .. } if **pattern == decoder))
    });
    let mut count = before - native.sentences.len();
    for sentence in &mut native.sentences {
        let Sentence::Axiom {
            pattern,
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        if has_nullary_attribute(attributes, "constructor") {
            count += remove_box_no_junk(pattern);
        }
        if initializer_equation(pattern) {
            count += translate_configuration_reads(pattern);
        }
    }
    if module_mentions_transport(native) {
        return Err(CompareError::new(
            "native configuration-value transport is used outside its generated declarations, axioms, and cell-initializer reads",
        ));
    }
    Ok(count)
}

fn module_mentions_transport(module: &Module) -> bool {
    let mut found = false;
    let mut visit = |name: &str| found |= name == CONFIG_VALUE_BOX || name == CONFIG_VALUE_UNBOX;
    for attribute in &module.attributes.0 {
        visit_pattern_symbols(attribute, &mut visit);
    }
    for sentence in &module.sentences {
        if let Sentence::SymbolDeclaration { symbol, .. } = sentence {
            visit(&symbol.name);
        }
        visit_sentence_symbols(sentence, &mut visit);
    }
    found
}

fn sort(name: &str) -> Sort {
    Sort::Application {
        name: name.to_owned(),
        arguments: Vec::new(),
    }
}

fn application(name: &str, arguments: Vec<Pattern>) -> Pattern {
    Pattern::Application {
        symbol: Symbol {
            name: name.to_owned(),
            sort_parameters: Vec::new(),
        },
        arguments,
    }
}

fn unary_argument<'a>(pattern: &'a Pattern, name: &str) -> Option<&'a Pattern> {
    match pattern {
        Pattern::Application { symbol, arguments }
            if symbol.name == name && symbol.sort_parameters.is_empty() =>
        {
            match arguments.as_slice() {
                [argument] => Some(argument),
                _ => None,
            }
        }
        _ => None,
    }
}

fn boxed_k_variable(pattern: &Pattern) -> bool {
    matches!(
        unary_argument(pattern, CONFIG_VALUE_BOX),
        Some(Pattern::Variable(argument)) if argument.sort == sort("SortK")
    )
}

fn transport_declaration(sentence: &Sentence) -> bool {
    let Sentence::SymbolDeclaration {
        hooked: false,
        symbol,
        argument_sorts,
        result_sort,
        attributes,
    } = sentence
    else {
        return false;
    };
    symbol.sort_parameters.is_empty()
        && (symbol.name == CONFIG_VALUE_BOX
            && argument_sorts.as_slice() == [sort("SortK")]
            && *result_sort == sort("SortKItem")
            || symbol.name == CONFIG_VALUE_UNBOX
                && argument_sorts.as_slice() == [sort("SortKItem")]
                && *result_sort == sort("SortK")
                && !has_nullary_attribute(attributes, "functional")
                && !has_nullary_attribute(attributes, "total"))
}

/// `\exists(Val:KItem, \equals(Val, #KConfigValue(K0:K))) [functional]`.
fn box_functional_axiom(sentence: &Sentence) -> bool {
    let Sentence::Axiom {
        pattern,
        attributes,
        ..
    } = sentence
    else {
        return false;
    };
    if !has_nullary_attribute(attributes, "functional") {
        return false;
    }
    let Pattern::Exists { variable, body, .. } = pattern.as_ref() else {
        return false;
    };
    let Pattern::Equals {
        operand_sort,
        left,
        right,
        ..
    } = body.as_ref()
    else {
        return false;
    };
    **operand_sort == sort("SortKItem")
        && variable.sort == sort("SortKItem")
        && matches!(left.as_ref(), Pattern::Variable(value) if value == variable.as_ref())
        && boxed_k_variable(right)
}

/// The box's constructor-tagged injectivity axiom, or a no-confusion axiom pairing it with another constructor.
fn box_constructor_axiom(sentence: &Sentence) -> bool {
    let Sentence::Axiom {
        pattern,
        attributes,
        ..
    } = sentence
    else {
        return false;
    };
    if !has_nullary_attribute(attributes, "constructor") {
        return false;
    }
    match pattern.as_ref() {
        Pattern::Implies {
            sort: axiom_sort,
            left,
            right,
        } => {
            let Pattern::And {
                sort: left_sort,
                arguments,
            } = left.as_ref()
            else {
                return false;
            };
            let [first, second] = arguments.as_slice() else {
                return false;
            };
            let (Some(Pattern::Variable(x)), Some(Pattern::Variable(y))) = (
                unary_argument(first, CONFIG_VALUE_BOX),
                unary_argument(second, CONFIG_VALUE_BOX),
            ) else {
                return false;
            };
            *axiom_sort == sort("SortKItem")
                && left_sort == axiom_sort
                && x.sort == sort("SortK")
                && y.sort == x.sort
                && unary_argument(right, CONFIG_VALUE_BOX)
                    == Some(&Pattern::And {
                        sort: x.sort.clone(),
                        arguments: vec![Pattern::Variable(x.clone()), Pattern::Variable(y.clone())],
                    })
        }
        Pattern::Not { argument, .. } => {
            let Pattern::And { arguments, .. } = argument.as_ref() else {
                return false;
            };
            let [left, right] = arguments.as_slice() else {
                return false;
            };
            is_application_over_variables(left)
                && is_application_over_variables(right)
                && (boxed_k_variable(left) || boxed_k_variable(right))
        }
        _ => false,
    }
}

/// Remove `\exists(X:K, #KConfigValue(X))` from a constructor no-junk disjunction of sort `KItem`.
fn remove_box_no_junk(pattern: &mut Pattern) -> usize {
    let Pattern::Or {
        sort: or_sort,
        arguments,
    } = pattern
    else {
        return 0;
    };
    if *or_sort != sort("SortKItem") {
        return 0;
    }
    let before = arguments.len();
    arguments.retain(|alternative| {
        !matches!(
            alternative,
            Pattern::Exists { sort: exists_sort, variable, body }
                if *exists_sort == sort("SortKItem")
                    && variable.sort == sort("SortK")
                    && unary_argument(body, CONFIG_VALUE_BOX)
                        == Some(&Pattern::Variable((**variable).clone()))
        )
    });
    let removed = before - arguments.len();
    removed + arguments.iter_mut().map(remove_box_no_junk).sum::<usize>()
}

/// `... \equals{SortXCell}(LblinitXCell(Init:Map), ...)`: a generated cell-initializer equation.
fn initializer_equation(pattern: &Pattern) -> bool {
    let Pattern::Implies { right, .. } = pattern else {
        return false;
    };
    let Pattern::Equals {
        operand_sort, left, ..
    } = right.as_ref()
    else {
        return false;
    };
    matches!(
        left.as_ref(),
        Pattern::Application { symbol, arguments }
            if symbol.sort_parameters.is_empty()
                && symbol.name.strip_prefix("Lblinit").is_some_and(|cell| {
                    cell.ends_with("Cell") && **operand_sort == sort(&format!("Sort{cell}"))
                })
                && matches!(arguments.as_slice(), [Pattern::Variable(variable)]
                    if variable.sort == sort("SortMap"))
    )
}

/// `Map:lookup(Init:Map, inj{KConfigVar, KItem}(\dv{KConfigVar}(..)))`.
fn configuration_lookup(pattern: &Pattern) -> bool {
    let Pattern::Application { symbol, arguments } = pattern else {
        return false;
    };
    let [Pattern::Variable(map), key] = arguments.as_slice() else {
        return false;
    };
    symbol.name == "LblMap'Coln'lookup"
        && symbol.sort_parameters.is_empty()
        && map.sort == sort("SortMap")
        && matches!(
            key,
            Pattern::Application { symbol, arguments }
                if symbol.name == "inj"
                    && symbol.sort_parameters == [sort("SortKConfigVar"), sort("SortKItem")]
                    && matches!(arguments.as_slice(), [Pattern::DomainValue { sort: value_sort, .. }]
                        if *value_sort == sort("SortKConfigVar"))
        )
}

/// Translate `project:S(#unboxKConfigValue(lookup))` to the reference's `project:S(kseq(lookup, dotk))`.
/// A K read becomes `kseq(project:KItem(kseq(lookup, dotk)), dotk)`, the reference's singleton.
fn translated_read(pattern: &Pattern) -> Option<Pattern> {
    let Pattern::Application { symbol, arguments } = pattern else {
        return None;
    };
    if !symbol.name.starts_with(PROJECTION_PREFIX) || !symbol.sort_parameters.is_empty() {
        return None;
    }
    let [argument] = arguments.as_slice() else {
        return None;
    };
    let lookup = unary_argument(argument, CONFIG_VALUE_UNBOX)?;
    if !configuration_lookup(lookup) {
        return None;
    }
    let item = application(
        "kseq",
        vec![lookup.clone(), application("dotk", Vec::new())],
    );
    Some(if symbol.name == "Lblproject'Coln'K" {
        application(
            "kseq",
            vec![
                application("Lblproject'Coln'KItem", vec![item]),
                application("dotk", Vec::new()),
            ],
        )
    } else {
        application(&symbol.name, vec![item])
    })
}

fn translate_configuration_reads(pattern: &mut Pattern) -> usize {
    if let Some(replacement) = translated_read(pattern) {
        *pattern = replacement;
        return 1;
    }
    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => arguments
            .iter_mut()
            .map(translate_configuration_reads)
            .sum(),
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. }
        | Pattern::Exists { body: argument, .. }
        | Pattern::Forall { body: argument, .. }
        | Pattern::Mu { body: argument, .. }
        | Pattern::Nu { body: argument, .. } => translate_configuration_reads(argument),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            translate_configuration_reads(left) + translate_configuration_reads(right)
        }
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => 0,
    }
}

const UNIQUE_ID: &str = "UNIQUE'Unds'ID";
const SELECTOR_DOMAIN: &str = "selector-domain";
const SELECTOR_INVERSE: &str = "selector-inverse";
/// The free variable over `K` that k-rust's selector contracts quantify.
const SELECTOR_INPUT: &str = "SelectorInput";

/// Remove k-rust's selector contracts from the native module (k-rust N51).
///
/// For a canonical compiler sort projection, k-rust states beside the identity equation `project:S(E[V]) = V` two companion axioms marked `<id>.selector-domain` and `<id>.selector-inverse`, where `<id>` is the equation's `UNIQUE'Unds'ID` and `E` its embedding of `S` in `K` (`docs/compatibility.md`, "Semantic casts compute nothing").
/// The domain axiom `\ceil(project:S(X)) = \exists V. X = E[V]` states that the projection is defined exactly on the image of the embedding; the inverse `\ceil(project:S(X)) -> E[project:S(X)] = X` follows from it and the identity equation.
/// A pair is removed only when its identity equation is the one native axiom with id `<id>`, has exactly that shape over an embedding built from `inj` and the `kseq`/`dotk` singleton alone, and both marked axioms are the only ones with their ids and equal the pair rebuilt from that equation, attributes included.
/// A marked axiom that differs, a pair member without its partner or equation, and an unmarked copy all stay compared, as does the identity equation itself.
/// Returns the number of removed axioms.
pub(super) fn remove_selector_contracts(native: &mut Module) -> usize {
    let ids = native.sentences.iter().map(unique_id).collect::<Vec<_>>();
    // The index of the one axiom with identifier `id`.
    let sole = |id: &str| {
        let mut matches = ids
            .iter()
            .enumerate()
            .filter(|(_, candidate)| **candidate == Some(id))
            .map(|(index, _)| index);
        let index = matches.next()?;
        matches.next().is_none().then_some(index)
    };
    let bases = ids
        .iter()
        .flatten()
        .filter_map(|id| {
            id.strip_suffix(SELECTOR_DOMAIN)
                .or_else(|| id.strip_suffix(SELECTOR_INVERSE))?
                .strip_suffix('.')
        })
        .collect::<BTreeSet<_>>();
    let mut removed = BTreeSet::new();
    for base in bases {
        let domain_id = format!("{base}.{SELECTOR_DOMAIN}");
        let inverse_id = format!("{base}.{SELECTOR_INVERSE}");
        let (Some(forward), Some(domain), Some(inverse)) =
            (sole(base), sole(&domain_id), sole(&inverse_id))
        else {
            continue;
        };
        let Sentence::Axiom {
            parameters,
            attributes: forward_attributes,
            ..
        } = &native.sentences[forward]
        else {
            continue;
        };
        let Some([expected_domain, expected_inverse]) =
            identity_equation(&native.sentences[forward])
                .and_then(|equation| selector_contracts(&equation))
        else {
            continue;
        };
        if contract_matches(
            &native.sentences[domain],
            parameters,
            &expected_domain,
            &contract_attributes(forward_attributes, &domain_id),
            false,
        ) && contract_matches(
            &native.sentences[inverse],
            parameters,
            &expected_inverse,
            &contract_attributes(forward_attributes, &inverse_id),
            true,
        ) {
            removed.extend([domain, inverse]);
        }
    }
    let mut index = 0;
    native.sentences.retain(|_| {
        let keep = !removed.contains(&index);
        index += 1;
        keep
    });
    removed.len()
}

fn unique_id(sentence: &Sentence) -> Option<&str> {
    let Sentence::Axiom { attributes, .. } = sentence else {
        return None;
    };
    let mut ids = attributes.0.iter().filter_map(|attribute| match attribute {
        Pattern::Application { symbol, arguments } if symbol.name == UNIQUE_ID => {
            match arguments.as_slice() {
                [Pattern::String(id)] => id.as_utf8().ok(),
                _ => None,
            }
        }
        _ => None,
    });
    let id = ids.next()?;
    ids.next().is_none().then_some(id)
}

/// The identity equation's attributes with its `UNIQUE'Unds'ID` replaced by `id`.
fn contract_attributes(forward: &Attributes, id: &str) -> Vec<Pattern> {
    forward
        .0
        .iter()
        .map(|attribute| match attribute {
            Pattern::Application { symbol, .. } if symbol.name == UNIQUE_ID => {
                application(UNIQUE_ID, vec![Pattern::String(id.into())])
            }
            attribute => attribute.clone(),
        })
        .collect()
}

/// `simplification{}()`, or `simplification{}("")` in a definition that gives some simplification a priority: the attribute without a priority.
fn unprioritized_simplification(attribute: &Pattern) -> bool {
    matches!(attribute, Pattern::Application { symbol, arguments }
    if symbol.name == "simplification"
        && symbol.sort_parameters.is_empty()
        && match arguments.as_slice() {
            [] => true,
            [Pattern::String(priority)] => priority.is_empty(),
            _ => false,
        })
}

fn contract_matches(
    sentence: &Sentence,
    expected_parameters: &[String],
    expected_pattern: &Pattern,
    expected_attributes: &[Pattern],
    simplification: bool,
) -> bool {
    let Sentence::Axiom {
        parameters,
        pattern,
        attributes,
    } = sentence
    else {
        return false;
    };
    let mut attributes = attributes.0.clone();
    if simplification {
        let Some(position) = attributes.iter().position(unprioritized_simplification) else {
            return false;
        };
        attributes.remove(position);
    }
    let mut expected_attributes = expected_attributes.to_vec();
    attributes.sort();
    expected_attributes.sort();
    parameters == expected_parameters
        && **pattern == *expected_pattern
        && attributes == expected_attributes
}

/// A compiler sort projection's identity equation `project:S(X) = V` over `X` bound to `E[V]`.
struct IdentityEquation<'a> {
    /// The axiom's one sort parameter, the sort of its predicates.
    predicate: Sort,
    projection: &'a Symbol,
    embedding: &'a Pattern,
    value: &'a Variable,
}

/// `forward` as an identity equation: `\implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortK{},R}(X:SortK{}, E), \top{R}())), \equals{S,R}(project:S(X), \and{S}(V:S, \top{S}())))`.
fn identity_equation(forward: &Sentence) -> Option<IdentityEquation<'_>> {
    let Sentence::Axiom {
        parameters,
        pattern,
        ..
    } = forward
    else {
        return None;
    };
    let (
        [parameter],
        Pattern::Implies {
            sort: axiom_sort,
            left,
            right,
        },
    ) = (parameters.as_slice(), pattern.as_ref())
    else {
        return None;
    };
    let predicate = Sort::Variable(parameter.clone());
    let (input, embedding) = input_binding(left, &predicate)?;
    let Pattern::Equals {
        operand_sort: value_sort,
        result_sort: equation_sort,
        left: head,
        right: result,
    } = right.as_ref()
    else {
        return None;
    };
    let Pattern::Application {
        symbol: projection,
        arguments,
    } = head.as_ref()
    else {
        return None;
    };
    let Pattern::And {
        sort: result_sort,
        arguments: result,
    } = result.as_ref()
    else {
        return None;
    };
    let [Pattern::Variable(value), Pattern::Top { sort: unit_sort }] = result.as_slice() else {
        return None;
    };
    let well_formed = *axiom_sort == predicate
        && *equation_sort == predicate
        && projection.name.starts_with(PROJECTION_PREFIX)
        && projection.sort_parameters.is_empty()
        && arguments.as_slice() == [Pattern::Variable(input.clone())]
        && value.sort == **value_sort
        && *result_sort == value.sort
        && *unit_sort == value.sort;
    well_formed.then_some(IdentityEquation {
        predicate,
        projection,
        embedding,
        value,
    })
}

/// The variable `X` and its pattern `E` of an equation's unconditional guard `\and{R}(\top{R}(), \and{R}(\in{SortK{},R}(X:SortK{}, E), \top{R}()))`.
fn input_binding<'a>(guard: &'a Pattern, predicate: &Sort) -> Option<(&'a Variable, &'a Pattern)> {
    let Pattern::And {
        sort: guard_sort,
        arguments: guard,
    } = guard
    else {
        return None;
    };
    let [
        Pattern::Top {
            sort: requires_sort,
        },
        Pattern::And {
            sort: conjunction_sort,
            arguments: conjunction,
        },
    ] = guard.as_slice()
    else {
        return None;
    };
    let [
        Pattern::In {
            operand_sort,
            result_sort: membership_sort,
            left: input,
            right: embedding,
        },
        Pattern::Top { sort: ensures_sort },
    ] = conjunction.as_slice()
    else {
        return None;
    };
    let Pattern::Variable(input) = input.as_ref() else {
        return None;
    };
    let well_formed = [
        guard_sort,
        requires_sort,
        conjunction_sort,
        membership_sort,
        ensures_sort,
    ]
    .iter()
    .all(|sort| *sort == predicate)
        && **operand_sort == sort("SortK")
        && input.sort == sort("SortK");
    well_formed.then_some((input, embedding.as_ref()))
}

/// The selector domain and inverse that k-rust states for `equation`.
fn selector_contracts(equation: &IdentityEquation<'_>) -> Option<[Pattern; 2]> {
    let IdentityEquation {
        predicate,
        projection,
        embedding,
        value,
    } = equation;
    let k = sort("SortK");
    let selector_input = Variable {
        kind: VariableKind::Element,
        name: SELECTOR_INPUT.to_owned(),
        sort: k.clone(),
    };
    if **value == selector_input {
        return None;
    }
    let application = Pattern::Application {
        symbol: (*projection).clone(),
        arguments: vec![Pattern::Variable(selector_input.clone())],
    };
    let reconstruction = reconstruct(embedding, value, &application)?;
    let ceil = Pattern::Ceil {
        operand_sort: Box::new(value.sort.clone()),
        result_sort: predicate.clone(),
        argument: Box::new(application),
    };
    let domain = Pattern::Implies {
        sort: predicate.clone(),
        left: Box::new(Pattern::Top {
            sort: predicate.clone(),
        }),
        right: Box::new(Pattern::Equals {
            operand_sort: Box::new(predicate.clone()),
            result_sort: predicate.clone(),
            left: Box::new(ceil.clone()),
            right: Box::new(Pattern::Exists {
                sort: predicate.clone(),
                variable: Box::new((*value).clone()),
                body: Box::new(Pattern::Equals {
                    operand_sort: Box::new(k.clone()),
                    result_sort: predicate.clone(),
                    left: Box::new(Pattern::Variable(selector_input.clone())),
                    right: Box::new((*embedding).clone()),
                }),
            }),
        }),
    };
    let inverse = Pattern::Implies {
        sort: predicate.clone(),
        left: Box::new(ceil),
        right: Box::new(Pattern::Equals {
            operand_sort: Box::new(k.clone()),
            result_sort: predicate.clone(),
            left: Box::new(reconstruction),
            right: Box::new(Pattern::And {
                sort: k.clone(),
                arguments: vec![Pattern::Variable(selector_input), Pattern::Top { sort: k }],
            }),
        }),
    };
    Some([domain, inverse])
}

/// `embedding` with its one occurrence of `value` replaced by `replacement`, when `embedding` wraps `value` only in `inj` and the `kseq`/`dotk` singleton.
fn reconstruct(embedding: &Pattern, value: &Variable, replacement: &Pattern) -> Option<Pattern> {
    match embedding {
        Pattern::Variable(variable) if variable == value => Some(replacement.clone()),
        Pattern::Application { symbol, arguments }
            if symbol.name == "inj" && symbol.sort_parameters.len() == 2 =>
        {
            let [inner] = arguments.as_slice() else {
                return None;
            };
            Some(Pattern::Application {
                symbol: symbol.clone(),
                arguments: vec![reconstruct(inner, value, replacement)?],
            })
        }
        Pattern::Application { symbol, arguments }
            if symbol.name == "kseq" && symbol.sort_parameters.is_empty() =>
        {
            let [inner, end] = arguments.as_slice() else {
                return None;
            };
            if *end != application("dotk", Vec::new()) {
                return None;
            }
            Some(Pattern::Application {
                symbol: symbol.clone(),
                arguments: vec![reconstruct(inner, value, replacement)?, end.clone()],
            })
        }
        _ => None,
    }
}

const SOURCE_ATTRIBUTE: &str = "org'Stop'kframework'Stop'attributes'Stop'Source";
const LOCATION_ATTRIBUTE: &str = "org'Stop'kframework'Stop'attributes'Stop'Location";
const BUILTIN_DOMAINS_SOURCE: &str = "Source(krust-builtin://domains.md)";

/// k-rust's builtin `INT-SYMBOLIC-KORE` rule `#Ceil(@I1:Int divInt @I2:Int) => {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [simplification]`.
const DIV_INT_DEFINEDNESS: &str = r#"\implies{R}(\top{R}(), \equals{Q0,R}(\ceil{SortInt{},Q0}(Lbl'Unds'divInt'Unds'{}(@VarI1:SortInt{}, @VarI2:SortInt{})), \and{Q0}(\and{Q0}(\and{Q0}(\equals{SortBool{},Q0}(Lbl'UndsEqlsSlshEqls'Int'Unds'{}(@VarI2:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")), \ceil{SortInt{},Q0}(@VarI1:SortInt{})), \ceil{SortInt{},Q0}(@VarI2:SortInt{})), \top{Q0}())))"#;

/// k-rust's builtin `INT-SYMBOLIC-KORE` rule `#Ceil(bitRangeInt(@I:Int, @O:Int, @L:Int)) => {(@O >=Int 0 andBool @L >=Int 0) #Equals true} #And #Ceil(@I) #And #Ceil(@O) #And #Ceil(@L) [simplification]`.
const BIT_RANGE_INT_DEFINEDNESS: &str = r#"\implies{R}(\top{R}(), \equals{Q0,R}(\ceil{SortInt{},Q0}(LblbitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int{}(@VarI:SortInt{}, @VarO:SortInt{}, @VarL:SortInt{})), \and{Q0}(\and{Q0}(\and{Q0}(\and{Q0}(\equals{SortBool{},Q0}(Lbl'Unds'andBool'Unds'{}(Lbl'Unds-GT-Eqls'Int'Unds'{}(@VarO:SortInt{}, \dv{SortInt{}}("0")), Lbl'Unds-GT-Eqls'Int'Unds'{}(@VarL:SortInt{}, \dv{SortInt{}}("0"))), \dv{SortBool{}}("true")), \ceil{SortInt{},Q0}(@VarI:SortInt{})), \ceil{SortInt{},Q0}(@VarO:SortInt{})), \ceil{SortInt{},Q0}(@VarL:SortInt{})), \top{Q0}())))"#;

/// Remove two definedness rules of k-rust's builtin library from the native module (k-rust N52).
///
/// `#Ceil(bitRangeInt(I, O, L))` is entailed by the unconditional equation `bitRangeInt(I, O, L) = (I >>Int O) modInt (1 <<Int L)` and the definedness rules of `>>Int`, `<<Int` and `modInt`, since `1 <<Int L` is positive for `L >=Int 0`.
/// `#Ceil(I1 divInt I2)` states that the quotient of a division by zero is no integer, the domain of the hooked partial operation, which the conditional equation of `divInt` leaves open at zero.
/// An axiom is removed only when its sort parameters and pattern are exactly one of the two rules, its source is `krust-builtin://domains.md`, it carries `simplification` without a priority, and its only other attributes are its identifier and location.
/// Returns the number of removed axioms.
///
/// # Errors
///
/// Fails only when a rule's own KORE text does not parse.
pub(super) fn remove_builtin_definedness_rules(native: &mut Module) -> Result<usize, CompareError> {
    let rules = [DIV_INT_DEFINEDNESS, BIT_RANGE_INT_DEFINEDNESS]
        .into_iter()
        .map(|rule| {
            parse_pattern(rule).map_err(|error| {
                CompareError::new(format!("cannot parse builtin definedness rule: {error}"))
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let source = application(
        SOURCE_ATTRIBUTE,
        vec![Pattern::String(BUILTIN_DOMAINS_SOURCE.into())],
    );
    let before = native.sentences.len();
    native.sentences.retain(|sentence| {
        let Sentence::Axiom {
            parameters,
            pattern,
            attributes,
        } = sentence
        else {
            return true;
        };
        !(parameters.as_slice() == ["R", "Q0"]
            && rules.iter().any(|rule| **pattern == *rule)
            && attributes.0.contains(&source)
            && attributes
                .0
                .iter()
                .filter(|attribute| unprioritized_simplification(attribute))
                .count()
                == 1
            && attributes.0.iter().all(|attribute| {
                *attribute == source
                    || unprioritized_simplification(attribute)
                    || matches!(attribute, Pattern::Application { symbol, .. }
                        if symbol.name == UNIQUE_ID || symbol.name == LOCATION_ATTRIBUTE)
            }))
    });
    Ok(before - native.sentences.len())
}

#[cfg(test)]
mod tests {
    use super::*;
    use k_rust::kore::parser::parse_definition;

    fn module(source: &str) -> Module {
        let definition = parse_definition(&format!("[] module M {source} endmodule []"))
            .expect("test KORE parses");
        definition.modules.into_iter().next().expect("one module")
    }

    const TRANSPORT: &str = r"
        symbol Lbl'Hash'KConfigValue{}(SortK{}) : SortKItem{} [constructor{}(), functional{}(), injective{}()]
        symbol Lbl'Hash'unboxKConfigValue{}(SortKItem{}) : SortK{} [function{}()]
        axiom{R} \exists{R}(Val:SortKItem{}, \equals{SortKItem{},R}(Val:SortKItem{}, Lbl'Hash'KConfigValue{}(K0:SortK{}))) [functional{}()]
        axiom{} \implies{SortKItem{}}(\and{SortKItem{}}(Lbl'Hash'KConfigValue{}(X0:SortK{}), Lbl'Hash'KConfigValue{}(Y0:SortK{})), Lbl'Hash'KConfigValue{}(\and{SortK{}}(X0:SortK{}, Y0:SortK{}))) [constructor{}()]
        axiom{} \not{SortKItem{}}(\and{SortKItem{}}(Lbl'Hash'KConfigValue{}(X0:SortK{}), a{}(Y0:SortK{}))) [constructor{}()]
        axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortKItem{},R}(X0:SortKItem{}, Lbl'Hash'KConfigValue{}(VarKS:SortK{})), \top{R}())), \equals{SortK{},R}(Lbl'Hash'unboxKConfigValue{}(X0:SortKItem{}), \and{SortK{}}(VarKS:SortK{}, \top{SortK{}}()))) []
    ";

    fn initializer(projection: &str, read: &str) -> String {
        format!(
            r"axiom{{R}} \implies{{R}}(\top{{R}}(), \equals{{SortKCell{{}},R}}(LblinitKCell{{}}(X0:SortMap{{}}), Lbl'-LT-'k'-GT-'{{}}({projection}({read})))) []"
        )
    }

    const LOOKUP: &str = r#"LblMap'Coln'lookup{}(X0:SortMap{}, inj{SortKConfigVar{}, SortKItem{}}(\dv{SortKConfigVar{}}("$PGM")))"#;

    #[test]
    fn transport_is_removed_and_initializer_reads_use_item_transport() {
        let unboxed = format!("Lbl'Hash'unboxKConfigValue{{}}({LOOKUP})");
        let item = format!("kseq{{}}({LOOKUP}, dotk{{}}())");
        let native_source = format!(
            r"{TRANSPORT}
            axiom{{}} \or{{SortKItem{{}}}}(\exists{{SortKItem{{}}}}(X0:SortK{{}}, Lbl'Hash'KConfigValue{{}}(X0:SortK{{}})), a{{}}(X0:SortK{{}})) [constructor{{}}()]
            {}
            {}",
            initializer("Lblproject'Coln'Stmt{}", &unboxed),
            initializer("Lblproject'Coln'K{}", &unboxed),
        );
        let reference = module(&format!(
            r"axiom{{}} \or{{SortKItem{{}}}}(a{{}}(X0:SortK{{}})) [constructor{{}}()]
            {}
            {}",
            initializer("Lblproject'Coln'Stmt{}", &item),
            initializer(
                "kseq{}",
                &format!("Lblproject'Coln'KItem{{}}({item}), dotk{{}}()")
            ),
        ));
        let mut native = module(&native_source);
        // 2 declarations, 4 axioms, 1 no-junk alternative, 2 reads.
        assert_eq!(
            remove_configuration_value_transport(&reference, &mut native),
            Ok(9)
        );
        let reference_sentences = reference
            .sentences
            .iter()
            .map(|sentence| format!("{sentence:?}"))
            .collect::<Vec<_>>();
        let native_sentences = native
            .sentences
            .iter()
            .map(|sentence| format!("{sentence:?}"))
            .collect::<Vec<_>>();
        assert_eq!(native_sentences, reference_sentences);
    }

    #[test]
    fn absent_transport_is_a_no_op() {
        let reference = module(r"axiom{} \top{SortK{}}() []");
        let mut native = reference.clone();
        assert_eq!(
            remove_configuration_value_transport(&reference, &mut native),
            Ok(0)
        );
        assert_eq!(native, reference);
    }

    #[test]
    fn transport_normalization_fails_closed() {
        let mut native = module(TRANSPORT);
        assert!(
            remove_configuration_value_transport(&module(TRANSPORT), &mut native)
                .unwrap_err()
                .to_string()
                .contains("reference declares or uses")
        );

        let empty = module("");
        let mut one_declaration =
            module(r"symbol Lbl'Hash'KConfigValue{}(SortK{}) : SortKItem{} [constructor{}()]");
        assert!(
            remove_configuration_value_transport(&empty, &mut one_declaration)
                .unwrap_err()
                .to_string()
                .contains("1 of its 2")
        );

        // A decoded read outside a cell initializer is not translated.
        let mut stray = module(&format!(
            r"{TRANSPORT}
            axiom{{R}} \equals{{SortK{{}},R}}(f{{}}(), Lbl'Hash'unboxKConfigValue{{}}({LOOKUP})) []"
        ));
        assert!(
            remove_configuration_value_transport(&empty, &mut stray)
                .unwrap_err()
                .to_string()
                .contains("used outside")
        );
    }

    #[test]
    fn reference_injective_is_withheld_only_for_equation_heads_the_native_route_withholds() {
        let mut reference = module(
            r"symbol zero{}() : SortE{} [alias'Kywd'{}(), functional{}(), injective{}(), macro{}()]
            symbol keep{}() : SortE{} [macro{}(), injective{}()]
            symbol plain{}() : SortE{} [injective{}()]",
        );
        let native = module(
            r"symbol zero{}() : SortE{} [alias'Kywd'{}(), functional{}(), macro{}()]
            symbol keep{}() : SortE{} [macro{}(), injective{}()]
            symbol plain{}() : SortE{} []",
        );
        assert_eq!(withhold_reference_injective(&mut reference, &native), 1);
        let expected = module(
            r"symbol zero{}() : SortE{} [alias'Kywd'{}(), functional{}(), macro{}()]
            symbol keep{}() : SortE{} [macro{}(), injective{}()]
            symbol plain{}() : SortE{} [injective{}()]",
        );
        assert_eq!(reference, expected);
    }

    const BOOL_SELECTOR: &str = r#"
        axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortK{}, R}(X0:SortK{}, kseq{}(inj{SortBool{}, SortKItem{}}(VarK:SortBool{}), dotk{}())), \top{R}())), \equals{SortBool{}, R}(Lblproject'Coln'Bool{}(X0:SortK{}), \and{SortBool{}}(VarK:SortBool{}, \top{SortBool{}}()))) [UNIQUE'Unds'ID{}("b")]
    "#;
    const BOOL_DOMAIN: &str = r#"
        axiom{R} \implies{R}(\top{R}(), \equals{R, R}(\ceil{SortBool{}, R}(Lblproject'Coln'Bool{}(SelectorInput:SortK{})), \exists{R}(VarK:SortBool{}, \equals{SortK{}, R}(SelectorInput:SortK{}, kseq{}(inj{SortBool{}, SortKItem{}}(VarK:SortBool{}), dotk{}()))))) [UNIQUE'Unds'ID{}("b.selector-domain")]
    "#;
    const BOOL_INVERSE: &str = r#"
        axiom{R} \implies{R}(\ceil{SortBool{}, R}(Lblproject'Coln'Bool{}(SelectorInput:SortK{})), \equals{SortK{}, R}(kseq{}(inj{SortBool{}, SortKItem{}}(Lblproject'Coln'Bool{}(SelectorInput:SortK{})), dotk{}()), \and{SortK{}}(SelectorInput:SortK{}, \top{SortK{}}()))) [UNIQUE'Unds'ID{}("b.selector-inverse"), simplification{}()]
    "#;
    /// `project:K`, whose embedding is the value itself, with the valued spelling of `simplification`.
    const K_SELECTOR: &str = r#"
        axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortK{}, R}(X0:SortK{}, VarK:SortK{}), \top{R}())), \equals{SortK{}, R}(Lblproject'Coln'K{}(X0:SortK{}), \and{SortK{}}(VarK:SortK{}, \top{SortK{}}()))) [UNIQUE'Unds'ID{}("k")]
        axiom{R} \implies{R}(\top{R}(), \equals{R, R}(\ceil{SortK{}, R}(Lblproject'Coln'K{}(SelectorInput:SortK{})), \exists{R}(VarK:SortK{}, \equals{SortK{}, R}(SelectorInput:SortK{}, VarK:SortK{})))) [UNIQUE'Unds'ID{}("k.selector-domain")]
        axiom{R} \implies{R}(\ceil{SortK{}, R}(Lblproject'Coln'K{}(SelectorInput:SortK{})), \equals{SortK{}, R}(Lblproject'Coln'K{}(SelectorInput:SortK{}), \and{SortK{}}(SelectorInput:SortK{}, \top{SortK{}}()))) [UNIQUE'Unds'ID{}("k.selector-inverse"), simplification{}("")]
    "#;

    #[test]
    fn exact_selector_contract_pairs_are_removed_and_their_equations_stay() {
        let mut native = module(&format!(
            "{BOOL_SELECTOR}{BOOL_DOMAIN}{BOOL_INVERSE}{K_SELECTOR}"
        ));
        assert_eq!(remove_selector_contracts(&mut native), 4);
        let ids = native
            .sentences
            .iter()
            .filter_map(unique_id)
            .collect::<Vec<_>>();
        assert_eq!(ids, ["b", "k"]);
    }

    #[test]
    fn selector_contracts_that_are_not_rebuilt_exactly_stay_compared() {
        let unchanged = |source: &str| {
            let mut native = module(source);
            let before = native.clone();
            assert_eq!(remove_selector_contracts(&mut native), 0, "{source}");
            assert_eq!(native, before);
        };
        // A domain over another embedding than the equation's.
        let altered = BOOL_DOMAIN.replace(
            r"\equals{SortK{}, R}(SelectorInput:SortK{}, kseq{}(inj{SortBool{}, SortKItem{}}(VarK:SortBool{}), dotk{}()))",
            r"\equals{SortK{}, R}(SelectorInput:SortK{}, kseq{}(inj{SortBool{}, SortKItem{}}(VarK:SortBool{}), SelectorInput:SortK{}))",
        );
        assert_ne!(altered, BOOL_DOMAIN);
        unchanged(&format!("{BOOL_SELECTOR}{altered}{BOOL_INVERSE}"));
        // An inverse that is not a simplification, or carries a priority.
        unchanged(&format!(
            "{BOOL_SELECTOR}{BOOL_DOMAIN}{}",
            BOOL_INVERSE.replace(", simplification{}()", "")
        ));
        unchanged(&format!(
            "{BOOL_SELECTOR}{BOOL_DOMAIN}{}",
            BOOL_INVERSE.replace("simplification{}()", r#"simplification{}("40")"#)
        ));
        // A domain without its inverse, and a pair without its equation.
        unchanged(&format!("{BOOL_SELECTOR}{BOOL_DOMAIN}"));
        unchanged(&format!("{BOOL_DOMAIN}{BOOL_INVERSE}"));
        // A conditional equation is not the identity the pair is rebuilt from.
        unchanged(&format!(
            "{}{BOOL_DOMAIN}{BOOL_INVERSE}",
            BOOL_SELECTOR.replacen(r"\and{R}(\top{R}(),", r"\and{R}(\bottom{R}(),", 1)
        ));
        // A second marked domain makes the pair ambiguous.
        unchanged(&format!(
            "{BOOL_SELECTOR}{BOOL_DOMAIN}{BOOL_DOMAIN}{BOOL_INVERSE}"
        ));
        // An unmarked copy of an exact pair.
        unchanged(&format!(
            "{BOOL_SELECTOR}{}{}",
            BOOL_DOMAIN.replace("b.selector-domain", "copy"),
            BOOL_INVERSE.replace("b.selector-inverse", "b.inverse")
        ));
    }

    const DIV_INT_RULE: &str = r#"
        axiom{R, Q0} \implies{R}(\top{R}(), \equals{Q0, R}(\ceil{SortInt{}, Q0}(Lbl'Unds'divInt'Unds'{}(@VarI1:SortInt{}, @VarI2:SortInt{})), \and{Q0}(\and{Q0}(\and{Q0}(\equals{SortBool{}, Q0}(Lbl'UndsEqlsSlshEqls'Int'Unds'{}(@VarI2:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")), \ceil{SortInt{}, Q0}(@VarI1:SortInt{})), \ceil{SortInt{}, Q0}(@VarI2:SortInt{})), \top{Q0}()))) [UNIQUE'Unds'ID{}("d"), org'Stop'kframework'Stop'attributes'Stop'Location{}("Location(1395,3,1395,119)"), org'Stop'kframework'Stop'attributes'Stop'Source{}("Source(krust-builtin://domains.md)"), simplification{}("")]
    "#;
    const BIT_RANGE_INT_RULE: &str = r#"
        axiom{R, Q0} \implies{R}(\top{R}(), \equals{Q0, R}(\ceil{SortInt{}, Q0}(LblbitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int{}(@VarI:SortInt{}, @VarO:SortInt{}, @VarL:SortInt{})), \and{Q0}(\and{Q0}(\and{Q0}(\and{Q0}(\equals{SortBool{}, Q0}(Lbl'Unds'andBool'Unds'{}(Lbl'Unds-GT-Eqls'Int'Unds'{}(@VarO:SortInt{}, \dv{SortInt{}}("0")), Lbl'Unds-GT-Eqls'Int'Unds'{}(@VarL:SortInt{}, \dv{SortInt{}}("0"))), \dv{SortBool{}}("true")), \ceil{SortInt{}, Q0}(@VarI:SortInt{})), \ceil{SortInt{}, Q0}(@VarO:SortInt{})), \ceil{SortInt{}, Q0}(@VarL:SortInt{})), \top{Q0}()))) [UNIQUE'Unds'ID{}("r"), org'Stop'kframework'Stop'attributes'Stop'Source{}("Source(krust-builtin://domains.md)"), simplification{}()]
    "#;

    #[test]
    fn builtin_definedness_rules_are_removed_only_exactly() {
        let mut native = module(&format!("{DIV_INT_RULE}{BIT_RANGE_INT_RULE}"));
        assert_eq!(remove_builtin_definedness_rules(&mut native), Ok(2));
        assert!(native.sentences.is_empty());

        for changed in [
            // Another condition, another source, no source, a priority, and an extra attribute.
            DIV_INT_RULE.replace(r#"\dv{SortInt{}}("0")"#, r#"\dv{SortInt{}}("1")"#),
            DIV_INT_RULE.replace("krust-builtin://domains.md", "imp.k"),
            DIV_INT_RULE.replace(
                r#"org'Stop'kframework'Stop'attributes'Stop'Source{}("Source(krust-builtin://domains.md)"), "#,
                "",
            ),
            DIV_INT_RULE.replace(r#"simplification{}("")"#, r#"simplification{}("40")"#),
            DIV_INT_RULE.replace(r#"simplification{}("")"#, r#"simplification{}(""), concrete{}()"#),
            DIV_INT_RULE.replace("axiom{R, Q0}", "axiom{Q0, R}"),
        ] {
            assert_ne!(changed, DIV_INT_RULE);
            let mut native = module(&changed);
            assert_eq!(
                remove_builtin_definedness_rules(&mut native),
                Ok(0),
                "{changed}"
            );
            assert_eq!(native.sentences.len(), 1);
        }
    }
}
