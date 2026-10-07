use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    env, fs,
    path::Path,
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

use k_rust::kore::{
    ast::{Attributes, Definition, Pattern, Sentence, Sort, Symbol, Variable},
    parser::parse_definition,
    parser::parse_pattern,
    printer::Printer,
};
use k_rust::{
    definition::{
        json as definition_json,
        regex::{self, CharClass, RegexBody},
    },
    kast::json as kast_json,
};
use serde::Serialize;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct AmbiguityStats {
    nodes: usize,
    alternatives: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum BisonComparison {
    Exact,
    Amb,
}

#[test]
#[ignore = "requires K_REFERENCE_BISON_PARSER_OUTPUT and K_RUST_BISON_PARSER_OUTPUT"]
fn generated_bison_parser_outputs_match() {
    let reference_path = env::var("K_REFERENCE_BISON_PARSER_OUTPUT")
        .expect("K_REFERENCE_BISON_PARSER_OUTPUT is required");
    let actual_path =
        env::var("K_RUST_BISON_PARSER_OUTPUT").expect("K_RUST_BISON_PARSER_OUTPUT is required");
    let allow_ambiguity = env::var("K_BISON_PARSER_ALLOW_AMBIGUITY").as_deref() == Ok("1");
    let fixture = env::var("K_BISON_PARSER_INPUT").unwrap_or_else(|_| "<unknown input>".into());
    let reference = fs::read(reference_path).unwrap();
    let actual = fs::read(actual_path).unwrap();
    let (comparison, reference_stats, actual_stats) =
        compare_bison_parser_outputs(&reference, &actual, allow_ambiguity)
            .unwrap_or_else(|error| panic!("{fixture}: {error}"));
    println!(
        "bison-parser-comparison = '{}'",
        match comparison {
            BisonComparison::Exact => "exact",
            BisonComparison::Amb => "amb",
        }
    );
    println!(
        "bison-parser-reference-ambiguity-nodes = {}",
        reference_stats.nodes
    );
    println!(
        "bison-parser-reference-alternatives = {}",
        reference_stats.alternatives
    );
    println!(
        "bison-parser-krust-ambiguity-nodes = {}",
        actual_stats.nodes
    );
    println!(
        "bison-parser-krust-alternatives = {}",
        actual_stats.alternatives
    );
}

fn compare_bison_parser_outputs(
    reference_bytes: &[u8],
    actual_bytes: &[u8],
    allow_ambiguity: bool,
) -> Result<(BisonComparison, AmbiguityStats, AmbiguityStats), String> {
    let reference_source = std::str::from_utf8(reference_bytes)
        .map_err(|error| format!("reference parser stdout is not UTF-8: {error}"))?;
    let actual_source = std::str::from_utf8(actual_bytes)
        .map_err(|error| format!("krust parser stdout is not UTF-8: {error}"))?;
    let reference = parse_pattern(reference_source).map_err(|error| {
        format!("reference parser stdout is not one complete KORE pattern: {error}")
    })?;
    let actual = parse_pattern(actual_source).map_err(|error| {
        format!("krust parser stdout is not one complete KORE pattern: {error}")
    })?;
    let reference_stats = ambiguity_stats(&reference)?;
    let actual_stats = ambiguity_stats(&actual)?;
    let ambiguous = reference_stats.nodes != 0 || actual_stats.nodes != 0;

    if !ambiguous {
        if reference_bytes != actual_bytes {
            return Err(format!(
                "unambiguous parser stdout differs byte-for-byte\nreference: {}\nkrust: {}",
                bounded_text(reference_source),
                bounded_text(actual_source),
            ));
        }
        if allow_ambiguity {
            return Err("manifest authorizes amb comparison, but neither parser produced Lblamb; review the fixture classification".into());
        }
        return Ok((BisonComparison::Exact, reference_stats, actual_stats));
    }
    if !allow_ambiguity {
        return Err("unexpected Lblamb under exact comparison; review this fixture before authorizing ambiguity canonicalization".into());
    }

    let reference = canonicalize_ambiguities(&reference)?;
    let actual = canonicalize_ambiguities(&actual)?;
    if reference != actual {
        return Err(format!(
            "ambiguous parser outputs differ after flattening and sorting same-sort Lblamb alternatives\nreference: {}\nkrust: {}",
            bounded_text(&Printer::compact().print_pattern(&reference)),
            bounded_text(&Printer::compact().print_pattern(&actual)),
        ));
    }
    Ok((BisonComparison::Amb, reference_stats, actual_stats))
}

fn bounded_text(value: &str) -> String {
    const LIMIT: usize = 2_000;
    if value.len() <= LIMIT {
        return value.into();
    }
    let mut end = LIMIT;
    while !value.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}… <{} bytes omitted>", &value[..end], value.len() - end)
}

fn ambiguity_stats(root: &Pattern) -> Result<AmbiguityStats, String> {
    struct Entry<'a> {
        pattern: &'a Pattern,
        parent_amb_sort: Option<&'a k_rust::kore::ast::Sort>,
    }
    let mut stats = AmbiguityStats::default();
    let mut stack = vec![Entry {
        pattern: root,
        parent_amb_sort: None,
    }];
    while let Some(Entry {
        pattern,
        parent_amb_sort,
    }) = stack.pop()
    {
        let amb_sort = valid_amb_sort(pattern)?;
        if let Some(sort) = amb_sort {
            stats.nodes += 1;
            if parent_amb_sort != Some(sort) {
                stats.alternatives += flattened_amb_alternative_count(pattern, sort)?;
            }
        }
        let child_parent = amb_sort;
        for child in pattern_children(pattern).into_iter().rev() {
            stack.push(Entry {
                pattern: child,
                parent_amb_sort: child_parent,
            });
        }
    }
    Ok(stats)
}

fn valid_amb_sort(pattern: &Pattern) -> Result<Option<&k_rust::kore::ast::Sort>, String> {
    let Pattern::Application { symbol, arguments } = pattern else {
        return Ok(None);
    };
    if symbol.name != "Lblamb" {
        return Ok(None);
    }
    if symbol.sort_parameters.len() != 1 || arguments.len() != 2 {
        return Err(format!(
            "malformed Lblamb: expected one sort parameter and two arguments, found {} sort parameter(s) and {} argument(s)",
            symbol.sort_parameters.len(),
            arguments.len()
        ));
    }
    Ok(symbol.sort_parameters.first())
}

fn flattened_amb_alternative_count(
    root: &Pattern,
    sort: &k_rust::kore::ast::Sort,
) -> Result<usize, String> {
    let mut count = 0;
    let mut stack = vec![root];
    while let Some(pattern) = stack.pop() {
        if valid_amb_sort(pattern)? == Some(sort) {
            let Pattern::Application { arguments, .. } = pattern else {
                unreachable!()
            };
            stack.extend(arguments.iter().rev());
        } else {
            count += 1;
        }
    }
    Ok(count)
}

// This duplicates the private kore::walk shape deliberately: ambiguity normalization is a
// differential-test transform, not a production KORE API. Both traversal and rebuilding remain
// iterative for generated parsers configured with very deep Bison stacks.
fn pattern_children(pattern: &Pattern) -> Vec<&Pattern> {
    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => arguments.iter().collect(),
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => vec![argument],
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => vec![left, right],
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => vec![body],
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => Vec::new(),
    }
}

fn canonicalize_ambiguities(root: &Pattern) -> Result<Pattern, String> {
    struct Frame<'a> {
        pattern: &'a Pattern,
        children: Vec<&'a Pattern>,
        next: usize,
        built: Vec<Pattern>,
    }
    impl<'a> Frame<'a> {
        fn new(pattern: &'a Pattern) -> Self {
            Self {
                pattern,
                children: pattern_children(pattern),
                next: 0,
                built: Vec::new(),
            }
        }
    }

    let mut stack = vec![Frame::new(root)];
    loop {
        let frame = stack
            .last_mut()
            .expect("the root frame remains until return");
        if let Some(child) = frame.children.get(frame.next).copied() {
            frame.next += 1;
            stack.push(Frame::new(child));
            continue;
        }
        let frame = stack.pop().expect("the completed frame is present");
        let mut built = rebuild_pattern_node(frame.pattern, frame.built);
        if let Some(sort) = valid_amb_sort(&built)?.cloned() {
            let Pattern::Application { arguments, .. } = &mut built else {
                unreachable!()
            };
            let mut work = std::mem::take(arguments);
            let mut alternatives = Vec::new();
            while let Some(mut candidate) = work.pop() {
                if valid_amb_sort(&candidate)? == Some(&sort) {
                    let Pattern::Application { arguments, .. } = &mut candidate else {
                        unreachable!()
                    };
                    work.extend(std::mem::take(arguments));
                } else {
                    alternatives.push(candidate);
                }
            }
            alternatives.sort_by_cached_key(|pattern| {
                Printer::compact().print_pattern(pattern).into_bytes()
            });
            let mut alternatives = alternatives.into_iter();
            let first = alternatives
                .next()
                .expect("a valid binary Lblamb has alternatives");
            built = alternatives.fold(first, |left, right| Pattern::Application {
                symbol: Symbol {
                    name: "Lblamb".into(),
                    sort_parameters: vec![sort.clone()],
                },
                arguments: vec![left, right],
            });
        }
        if let Some(parent) = stack.last_mut() {
            parent.built.push(built);
        } else {
            return Ok(built);
        }
    }
}

fn rebuild_pattern_node(pattern: &Pattern, children: Vec<Pattern>) -> Pattern {
    let mut children = children.into_iter();
    let mut child = || Box::new(children.next().expect("the traversal supplies every child"));
    match pattern {
        Pattern::String(value) => Pattern::String(value.clone()),
        Pattern::Variable(variable) => Pattern::Variable(variable.clone()),
        Pattern::Application { symbol, .. } => Pattern::Application {
            symbol: symbol.clone(),
            arguments: children.collect(),
        },
        Pattern::Top { sort } => Pattern::Top { sort: sort.clone() },
        Pattern::Bottom { sort } => Pattern::Bottom { sort: sort.clone() },
        Pattern::And { sort, .. } => Pattern::And {
            sort: sort.clone(),
            arguments: children.collect(),
        },
        Pattern::Or { sort, .. } => Pattern::Or {
            sort: sort.clone(),
            arguments: children.collect(),
        },
        Pattern::Not { sort, .. } => Pattern::Not {
            sort: sort.clone(),
            argument: child(),
        },
        Pattern::Next { sort, .. } => Pattern::Next {
            sort: sort.clone(),
            argument: child(),
        },
        Pattern::Implies { sort, .. } => Pattern::Implies {
            sort: sort.clone(),
            left: child(),
            right: child(),
        },
        Pattern::Iff { sort, .. } => Pattern::Iff {
            sort: sort.clone(),
            left: child(),
            right: child(),
        },
        Pattern::Rewrites { sort, .. } => Pattern::Rewrites {
            sort: sort.clone(),
            left: child(),
            right: child(),
        },
        Pattern::Exists { sort, variable, .. } => Pattern::Exists {
            sort: sort.clone(),
            variable: variable.clone(),
            body: child(),
        },
        Pattern::Forall { sort, variable, .. } => Pattern::Forall {
            sort: sort.clone(),
            variable: variable.clone(),
            body: child(),
        },
        Pattern::Mu { variable, .. } => Pattern::Mu {
            variable: variable.clone(),
            body: child(),
        },
        Pattern::Nu { variable, .. } => Pattern::Nu {
            variable: variable.clone(),
            body: child(),
        },
        Pattern::Ceil {
            operand_sort,
            result_sort,
            ..
        } => Pattern::Ceil {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            argument: child(),
        },
        Pattern::Floor {
            operand_sort,
            result_sort,
            ..
        } => Pattern::Floor {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            argument: child(),
        },
        Pattern::Equals {
            operand_sort,
            result_sort,
            ..
        } => Pattern::Equals {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            left: child(),
            right: child(),
        },
        Pattern::In {
            operand_sort,
            result_sort,
            ..
        } => Pattern::In {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            left: child(),
            right: child(),
        },
        Pattern::DomainValue { sort, value } => Pattern::DomainValue {
            sort: sort.clone(),
            value: value.clone(),
        },
        Pattern::AssociativeApplication {
            associativity,
            symbol,
            ..
        } => Pattern::AssociativeApplication {
            associativity: *associativity,
            symbol: symbol.clone(),
            arguments: children.collect(),
        },
    }
}

#[test]
fn bison_parser_comparator_is_byte_exact_for_unambiguous_output() {
    let bytes = b"f{}(a{}())\n";
    assert_eq!(
        compare_bison_parser_outputs(bytes, bytes, false).unwrap().0,
        BisonComparison::Exact
    );
    assert!(compare_bison_parser_outputs(b"f{}(a{}())\n", b"f{}( a{}() )\n", false).is_err());
}

#[test]
fn bison_parser_comparator_canonicalizes_same_sort_ambiguity_only() {
    let left = b"wrap{}(Lblamb{SortA{}}(Lblamb{SortA{}}(m{}(),z{}()),a{}()),Lblamb{SortB{}}(x{}(),y{}()))\n";
    let right = b"wrap{}(Lblamb{SortA{}}(z{}(),Lblamb{SortA{}}(a{}(),m{}())),Lblamb{SortB{}}(y{}(),x{}()))\n";
    let compared = compare_bison_parser_outputs(left, right, true).unwrap();
    assert_eq!(compared.0, BisonComparison::Amb);
    assert_eq!(
        compared.1,
        AmbiguityStats {
            nodes: 3,
            alternatives: 5
        }
    );
    assert_eq!(
        compared.2,
        AmbiguityStats {
            nodes: 3,
            alternatives: 5
        }
    );
}

#[test]
fn bison_parser_comparator_keeps_different_sort_ambiguity_as_one_alternative() {
    let left = b"Lblamb{SortA{}}(z{}(),Lblamb{SortB{}}(b{}(),a{}()))";
    let right = b"Lblamb{SortA{}}(Lblamb{SortB{}}(a{}(),b{}()),z{}())";
    let compared = compare_bison_parser_outputs(left, right, true).unwrap();
    assert_eq!(
        compared.1,
        AmbiguityStats {
            nodes: 2,
            alternatives: 4
        }
    );
    assert_eq!(
        compared.2,
        AmbiguityStats {
            nodes: 2,
            alternatives: 4
        }
    );
}

#[test]
fn bison_parser_comparator_rejects_bad_ambiguity_contracts() {
    assert!(
        compare_bison_parser_outputs(b"Lblamb{}(a{}(),b{}())", b"Lblamb{}(a{}(),b{}())", true)
            .is_err()
    );
    assert!(compare_bison_parser_outputs(b"Lblamb{S{},T{}}(a{}(),b{}())", b"a{}()", true).is_err());
    assert!(compare_bison_parser_outputs(b"Lblamb{S{}}(a{}())", b"a{}()", true).is_err());
    assert!(
        compare_bison_parser_outputs(
            b"Lblamb{S{}}(a{}(),b{}())",
            b"Lblamb{S{}}(b{}(),a{}())",
            false
        )
        .is_err()
    );
    assert!(compare_bison_parser_outputs(b"a{}()", b"a{}()", true).is_err());
    assert!(compare_bison_parser_outputs(b"Lblamb{S{}}(a{}(),a{}())", b"a{}()", true).is_err());
    assert!(
        compare_bison_parser_outputs(
            br#"\dv{S{}}("Lblamb{S{}}(a{}(),b{}())")"#,
            br#"\dv{S{}}("Lblamb{S{}}(a{}(),b{}())")"#,
            false
        )
        .is_ok()
    );
}

#[test]
fn bison_parser_comparator_handles_a_deep_unambiguous_term_iteratively() {
    let depth = 20_000;
    let mut source = String::with_capacity(depth * 12 + 16);
    for _ in 0..depth {
        source.push_str(r"\not{S{}}(");
    }
    source.push_str(r"\top{S{}}()");
    for _ in 0..depth {
        source.push(')');
    }
    assert_eq!(
        compare_bison_parser_outputs(source.as_bytes(), source.as_bytes(), false)
            .unwrap()
            .0,
        BisonComparison::Exact,
    );
}

#[test]
#[ignore = "requires K_REFERENCE_KORE and K_RUST_KORE outputs"]
fn emitted_kore_matches_the_reference_frontend() {
    let reference_path = env::var("K_REFERENCE_KORE").expect("K_REFERENCE_KORE is required");
    let actual_path = env::var("K_RUST_KORE").expect("K_RUST_KORE is required");
    let reference_source = fs::read_to_string(&reference_path).unwrap();
    let actual_source = fs::read_to_string(&actual_path).unwrap();
    let mut reference = parse_definition(&reference_source).unwrap();
    let mut actual = parse_definition(&actual_source).unwrap();
    let transport = normalize_configuration_value_transport(&reference, &mut actual)
        .expect("N37 requires a reference without configuration-value transport");
    println!("configuration-value transport normalized (N37): {transport} rewrites");
    let (removed, owise) = normalize_unsupported_sort_predicates(&mut reference);
    println!("unsupported sort-predicate axioms normalized: {removed} true, {owise} owise");
    let withheld_predicates = normalize_withheld_sort_predicates(&mut reference, &actual);
    println!(
        "constantly false sort predicates of sorts without K terms dropped (N35): \
         {withheld_predicates}"
    );
    let withheld = normalize_withheld_injective(&mut reference, &actual);
    println!("injective withheld from equation-headed symbols (N33): {withheld}");
    let functional = normalize_withheld_functional(&mut reference, &mut actual);
    println!(
        "functional withheld from equation-headed symbols (N36): {}",
        functional.declarations
    );
    println!(
        "value-production attributes removed from k-rust declarations (N36): {}",
        functional.value_production_attributes
    );
    println!(
        "extra function attributes removed from k-rust declarations (N36): {}",
        functional.function_attributes
    );
    let dropped = normalize_withheld_overload_no_confusion(&mut reference, &actual);
    println!(
        "constructor-family axioms of overload-greaters without no-confusion dropped (N34): \
         {dropped}"
    );
    let projections = normalize_derived_projection_totality(&mut reference);
    println!("field-projection totality derived from the reference's axioms (N43): {projections}");
    let lambdas = normalize_unsupported_lambda_totality(&mut reference);
    println!("lambda totality the reference's equations do not support withdrawn (N44): {lambdas}");
    let lifted = lifted_cells_from_environment();
    let lifted_cells = normalize_lifted_cells(&reference, &mut actual, &lifted)
        .unwrap_or_else(|error| panic!("{error}"));
    println!(
        "cells written inside another cell, which the reference discards, compared as its \
         variable (N45): {lifted_cells} in {} axioms",
        lifted.len()
    );
    compare_definitions(reference, actual);
}

const CONFIG_VALUE_BOX: &str = "Lbl'Hash'KConfigValue";
const CONFIG_VALUE_UNBOX: &str = "Lbl'Hash'unboxKConfigValue";

/// N37 removes only the private map transport from the port's compile artifact.
/// Initializer reads are translated back to item transport, without changing other uses of
/// projections or lookup. Declaration-derived axioms and the box's no-junk alternative carry
/// no information about the source language once its private constructor has been removed.
fn normalize_configuration_value_transport(
    reference: &Definition,
    actual: &mut Definition,
) -> Result<usize, String> {
    let private_symbols =
        BTreeSet::from([CONFIG_VALUE_BOX.to_owned(), CONFIG_VALUE_UNBOX.to_owned()]);
    if reference
        .attributes
        .0
        .iter()
        .chain(
            reference
                .modules
                .iter()
                .flat_map(|module| &module.attributes.0),
        )
        .any(|attribute| pattern_mentions_any_symbol(attribute, &private_symbols))
    {
        return Err("reference names private configuration-value transport in an attribute".into());
    }
    for module in &reference.modules {
        for sentence in &module.sentences {
            if [CONFIG_VALUE_BOX, CONFIG_VALUE_UNBOX]
                .iter()
                .any(|name| sentence_mentions_symbol(sentence, name))
            {
                return Err(
                    "reference declares or uses private configuration-value transport".into(),
                );
            }
        }
    }
    let valid_declaration = |sentence: &Sentence| {
        matches!(sentence, Sentence::SymbolDeclaration {
            symbol, argument_sorts, result_sort, attributes, ..
        } if symbol.sort_parameters.is_empty() && (
            symbol.name == CONFIG_VALUE_BOX
                && argument_sorts.as_slice() == [kore_sort("SortK")]
                && *result_sort == kore_sort("SortKItem")
            || symbol.name == CONFIG_VALUE_UNBOX
                && argument_sorts.as_slice() == [kore_sort("SortKItem")]
                && *result_sort == kore_sort("SortK")
                && !has_kore_attribute(attributes, "functional")
                && !has_kore_attribute(attributes, "total")))
    };
    let names = actual
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter(|sentence| valid_declaration(sentence))
        .filter_map(|sentence| match sentence {
            Sentence::SymbolDeclaration { symbol, .. } => Some(symbol.name.as_str()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    if !names.contains(CONFIG_VALUE_BOX) || !names.contains(CONFIG_VALUE_UNBOX) {
        return Ok(0);
    }
    let mut count = 0;
    for module in &mut actual.modules {
        let reference_module = reference
            .modules
            .iter()
            .find(|other| other.name == module.name);
        module.sentences.retain(|sentence| {
            let remove = valid_declaration(sentence)
                || box_functional_axiom(sentence)
                || box_no_confusion_axiom(sentence)
                || configuration_decoder_equation(sentence);
            count += usize::from(remove);
            !remove
        });
        for sentence in &mut module.sentences {
            let Sentence::Axiom {
                pattern,
                attributes,
                ..
            } = sentence
            else {
                continue;
            };
            if has_kore_attribute(attributes, "constructor") {
                count += remove_box_no_junk(pattern);
            }
            if initializer_equation(pattern) {
                let before = count;
                **pattern = normalize_configuration_read(pattern, &mut count);
                if count != before {
                    count += usize::from(align_configuration_initializer_id(
                        sentence,
                        reference_module,
                    ));
                }
            }
        }
    }
    Ok(count)
}

/// The generated identifier hashes the initializer before transport normalization.
/// Replace it only after the entire translated sentence, including semantic attributes,
/// matches a reference initializer under the comparison's existing source-metadata policy.
fn align_configuration_initializer_id(
    sentence: &mut Sentence,
    reference_module: Option<&k_rust::kore::ast::Module>,
) -> bool {
    let without_id = |sentence: &Sentence| {
        let mut sentence = sentence.clone();
        if let Sentence::Axiom { attributes, .. } = &mut sentence {
            strip_unique_id_attributes(attributes);
            strip_attributes(attributes);
        }
        canonicalized_sentence(&sentence)
    };
    let expected = without_id(sentence);
    let mut matches = reference_module
        .into_iter()
        .flat_map(|module| &module.sentences)
        .filter(|candidate| without_id(candidate) == expected);
    let Some(Sentence::Axiom {
        attributes: reference_attributes,
        ..
    }) = matches.next()
    else {
        return false;
    };
    if matches.next().is_some() {
        return false;
    }
    let identities = |attributes: &Attributes| {
        attributes
            .0
            .iter()
            .filter(|attribute| {
                matches!(attribute, Pattern::Application { symbol, arguments }
                if symbol.name == "UNIQUE'Unds'ID" && symbol.sort_parameters.is_empty()
                    && matches!(arguments.as_slice(), [Pattern::String(_)]))
            })
            .cloned()
            .collect::<Vec<_>>()
    };
    let reference_ids = identities(reference_attributes);
    let [reference_id] = reference_ids.as_slice() else {
        return false;
    };
    let Sentence::Axiom { attributes, .. } = sentence else {
        return false;
    };
    let actual_ids = identities(attributes);
    let [actual_id] = actual_ids.as_slice() else {
        return false;
    };
    if actual_id == reference_id {
        return false;
    }
    for attribute in &mut attributes.0 {
        if attribute == actual_id {
            attribute.clone_from(reference_id);
        }
    }
    true
}

fn has_kore_attribute(attributes: &Attributes, name: &str) -> bool {
    attributes.0.iter().any(|attribute| {
        matches!(attribute,
        Pattern::Application { symbol, arguments }
            if symbol.name == name && symbol.sort_parameters.is_empty() && arguments.is_empty())
    })
}

fn unary_application<'a>(pattern: &'a Pattern, name: &str) -> Option<&'a Pattern> {
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

fn box_functional_axiom(sentence: &Sentence) -> bool {
    let Sentence::Axiom {
        pattern,
        attributes,
        ..
    } = sentence
    else {
        return false;
    };
    if !has_kore_attribute(attributes, "functional") {
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
    **operand_sort == kore_sort("SortKItem")
        && variable.sort == kore_sort("SortKItem")
        && matches!(left.as_ref(), Pattern::Variable(value) if value == variable.as_ref())
        && matches!(unary_application(right, CONFIG_VALUE_BOX), Some(Pattern::Variable(argument))
            if argument.sort == kore_sort("SortK"))
}

fn box_no_confusion_axiom(sentence: &Sentence) -> bool {
    if !constructor_family_symbols(sentence).is_some_and(|names| names.contains(&CONFIG_VALUE_BOX))
    {
        return false;
    }
    let Sentence::Axiom { pattern, .. } = sentence else {
        return false;
    };
    if let Pattern::Implies { sort, left, right } = pattern.as_ref() {
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
            unary_application(first, CONFIG_VALUE_BOX),
            unary_application(second, CONFIG_VALUE_BOX),
        ) else {
            return false;
        };
        return *sort == kore_sort("SortKItem")
            && *left_sort == *sort
            && x.sort == kore_sort("SortK")
            && y.sort == x.sort
            && unary_application(right, CONFIG_VALUE_BOX)
                == Some(&Pattern::And {
                    sort: x.sort.clone(),
                    arguments: vec![Pattern::Variable(x.clone()), Pattern::Variable(y.clone())],
                });
    }
    let mut work = vec![pattern.as_ref()];
    while let Some(node) = work.pop() {
        if let Pattern::Application { symbol, .. } = node
            && symbol.name == CONFIG_VALUE_BOX
            && !matches!(unary_application(node, CONFIG_VALUE_BOX), Some(Pattern::Variable(argument))
                if argument.sort == kore_sort("SortK"))
        {
            return false;
        }
        work.extend(pattern_children(node));
    }
    true
}

fn configuration_decoder_equation(sentence: &Sentence) -> bool {
    let Sentence::Axiom { pattern, .. } = sentence else {
        return false;
    };
    if !sentence_mentions_symbol(sentence, CONFIG_VALUE_UNBOX) {
        return false;
    }
    // The sole decoder equation has one match against box(KS) and returns that same KS.
    // Checking the whole generated pattern keeps a changed condition or payload observable.
    let expected = parse_pattern(r"\implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortKItem{},R}(X0:SortKItem{}, Lbl'Hash'KConfigValue{}(VarKS:SortK{})), \top{R}())), \equals{SortK{},R}(Lbl'Hash'unboxKConfigValue{}(X0:SortKItem{}), \and{SortK{}}(VarKS:SortK{}, \top{SortK{}}())))").unwrap();
    pattern.as_ref() == &expected
}

fn remove_box_no_junk(pattern: &mut Pattern) -> usize {
    let Pattern::Or { sort, arguments } = pattern else {
        return 0;
    };
    if *sort != kore_sort("SortKItem") {
        return 0;
    }
    let before = arguments.len();
    arguments.retain(|alternative| {
        !matches!(alternative,
        Pattern::Exists { sort, variable, body }
            if *sort == kore_sort("SortKItem") && variable.sort == kore_sort("SortK")
                && unary_application(body, CONFIG_VALUE_BOX)
                    == Some(&Pattern::Variable((**variable).clone())))
    });
    let removed = before - arguments.len();
    // The reference emits binary right-associated disjunctions; nested Or nodes preserve them.
    removed + arguments.iter_mut().map(remove_box_no_junk).sum::<usize>()
}

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
    matches!(left.as_ref(), Pattern::Application { symbol, arguments }
        if symbol.name.strip_prefix("Lblinit").is_some_and(|cell|
            cell.ends_with("Cell") && **operand_sort == kore_sort(&format!("Sort{cell}")))
            && symbol.sort_parameters.is_empty()
            && matches!(arguments.as_slice(), [Pattern::Variable(variable)]
                if variable.sort == kore_sort("SortMap")))
}

fn normalize_configuration_read(pattern: &Pattern, count: &mut usize) -> Pattern {
    if let Pattern::Application { symbol, arguments } = pattern
        && symbol.name.starts_with("Lblproject'Coln'")
        && symbol.sort_parameters.is_empty()
        && let [argument] = arguments.as_slice()
        && let Some(lookup) = unary_application(argument, CONFIG_VALUE_UNBOX)
        && configuration_lookup(lookup)
    {
        *count += 1;
        let item = kore_application(
            "kseq",
            vec![lookup.clone(), kore_application("dotk", vec![])],
        );
        let project = kore_application(
            if symbol.name == "Lblproject'Coln'K" {
                "Lblproject'Coln'KItem"
            } else {
                &symbol.name
            },
            vec![item],
        );
        return if symbol.name == "Lblproject'Coln'K" {
            *count += 1;
            kore_application("kseq", vec![project, kore_application("dotk", vec![])])
        } else {
            project
        };
    }
    rebuild_pattern_node(
        pattern,
        pattern_children(pattern)
            .into_iter()
            .map(|child| normalize_configuration_read(child, count))
            .collect(),
    )
}

fn configuration_lookup(pattern: &Pattern) -> bool {
    let Pattern::Application { symbol, arguments } = pattern else {
        return false;
    };
    let [Pattern::Variable(map), key] = arguments.as_slice() else {
        return false;
    };
    symbol.name == "LblMap'Coln'lookup"
        && symbol.sort_parameters.is_empty()
        && map.sort == kore_sort("SortMap")
        && matches!(key, Pattern::Application { symbol, arguments }
            if symbol.name == "inj" && symbol.sort_parameters == [kore_sort("SortKConfigVar"), kore_sort("SortKItem")]
                && matches!(arguments.as_slice(), [Pattern::DomainValue { sort, .. }]
                    if *sort == kore_sort("SortKConfigVar")))
}

fn kore_application(name: &str, arguments: Vec<Pattern>) -> Pattern {
    Pattern::Application {
        symbol: Symbol {
            name: name.into(),
            sort_parameters: vec![],
        },
        arguments,
    }
}

#[test]
fn configuration_transport_normalizer_is_rust_only_and_counts_its_scope() {
    let source = |transport: bool, read: &str, extra: &str| {
        let private = if transport {
            r"symbol Lbl'Hash'KConfigValue{}(SortK{}) : SortKItem{} [constructor{}(), functional{}(), injective{}()]
            symbol Lbl'Hash'unboxKConfigValue{}(SortKItem{}) : SortK{} [function{}()]
            axiom{R} \exists{R}(Val:SortKItem{}, \equals{SortKItem{},R}(Val:SortKItem{}, Lbl'Hash'KConfigValue{}(K0:SortK{}))) [functional{}()]
            axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortKItem{},R}(X0:SortKItem{}, Lbl'Hash'KConfigValue{}(VarKS:SortK{})), \top{R}())), \equals{SortK{},R}(Lbl'Hash'unboxKConfigValue{}(X0:SortKItem{}), \and{SortK{}}(VarKS:SortK{}, \top{SortK{}}()))) []
            axiom{} \or{SortKItem{}}(\exists{SortKItem{}}(X0:SortK{}, Lbl'Hash'KConfigValue{}(X0:SortK{})), a{}(), \bottom{SortKItem{}}()) [constructor{}()]"
        } else {
            r"axiom{} \or{SortKItem{}}(a{}(), \bottom{SortKItem{}}()) [constructor{}()]"
        };
        parse_definition(&format!(r"[] module TEST
            {private}
            axiom{{R}} \implies{{R}}(\top{{R}}(), \equals{{SortKCell{{}}, R}}(LblinitKCell{{}}(Init:SortMap{{}}), cell{{}}({read}))) []
            {extra}
            endmodule []")).unwrap()
    };
    let lookup = r#"LblMap'Coln'lookup{}(Init:SortMap{}, inj{SortKConfigVar{},SortKItem{}}(\dv{SortKConfigVar{}}("$PGM")))"#;
    let boxed_read = format!("Lblproject'Coln'K{{}}(Lbl'Hash'unboxKConfigValue{{}}({lookup}))");
    let old_read =
        format!("kseq{{}}(Lblproject'Coln'KItem{{}}(kseq{{}}({lookup},dotk{{}}())),dotk{{}}())");
    let reference = source(false, &old_read, "");
    let mut actual = source(true, &boxed_read, "");
    assert_eq!(
        normalize_configuration_value_transport(&reference, &mut actual),
        Ok(7)
    );
    assert_eq!(actual, reference);
    assert_eq!(
        normalize_configuration_value_transport(&reference, &mut actual),
        Ok(0)
    );

    let with_id = |mut definition: Definition, id: &str| {
        let Sentence::Axiom { attributes, .. } =
            definition.modules[0].sentences.last_mut().unwrap()
        else {
            unreachable!()
        };
        attributes.0.push(kore_application(
            "UNIQUE'Unds'ID",
            vec![Pattern::String(id.into())],
        ));
        definition
    };
    let identified_reference = with_id(reference.clone(), "item-body-id");
    let mut identified_actual = with_id(source(true, &boxed_read, ""), "boxed-body-id");
    assert_eq!(
        normalize_configuration_value_transport(&identified_reference, &mut identified_actual),
        Ok(8)
    );
    assert_eq!(identified_actual, identified_reference);

    // A changed semantic attribute must prevent alignment of the generated identifier.
    let mut changed_attribute = with_id(source(true, &boxed_read, ""), "boxed-body-id");
    let Sentence::Axiom { attributes, .. } =
        changed_attribute.modules[0].sentences.last_mut().unwrap()
    else {
        unreachable!()
    };
    attributes.0.push(kore_application("owise", vec![]));
    assert_eq!(
        normalize_configuration_value_transport(&identified_reference, &mut changed_attribute),
        Ok(7)
    );
    assert_eq!(
        sentence_identity(changed_attribute.modules[0].sentences.last().unwrap()),
        Some("boxed-body-id".into())
    );

    // An untouched initializer's identifier remains part of the comparison.
    let mut untouched = with_id(reference.clone(), "changed-id");
    assert_eq!(
        normalize_configuration_value_transport(&identified_reference, &mut untouched),
        Ok(0)
    );
    assert_ne!(untouched, identified_reference);

    // A changed decoder payload must remain an extra axiom in the comparison.
    let mut changed = source(true, &boxed_read, "");
    let Sentence::Axiom { pattern, .. } = &mut changed.modules[0].sentences[3] else {
        unreachable!()
    };
    let Pattern::Implies { right, .. } = pattern.as_mut() else {
        unreachable!()
    };
    let Pattern::Equals { right, .. } = right.as_mut() else {
        unreachable!()
    };
    **right = kore_application("dotk", vec![]);
    normalize_configuration_value_transport(&reference, &mut changed).unwrap();
    assert!(
        changed.modules[0]
            .sentences
            .iter()
            .any(|sentence| sentence_mentions_symbol(sentence, CONFIG_VALUE_UNBOX))
    );

    let boxed_reference = source(true, &boxed_read, "");
    let mut unchanged = boxed_reference.clone();
    assert!(normalize_configuration_value_transport(&boxed_reference, &mut unchanged).is_err());
    assert_eq!(unchanged, boxed_reference);

    // A projection in a source equation is not an initializer read.
    let extra = format!("axiom{{R}} \\equals{{SortK{{}},R}}({boxed_read}, dotk{{}}()) []");
    let mut unrelated = source(true, &boxed_read, &extra);
    normalize_configuration_value_transport(&reference, &mut unrelated).unwrap();
    assert!(
        unrelated.modules[0]
            .sentences
            .iter()
            .any(|sentence| sentence_mentions_symbol(sentence, CONFIG_VALUE_UNBOX))
    );
}

#[test]
fn configuration_transport_read_normalizer_preserves_non_k_projections_and_lookup_keys() {
    let lookup = r#"LblMap'Coln'lookup{}(Init:SortMap{}, inj{SortKConfigVar{},SortKItem{}}(\dv{SortKConfigVar{}}("$X")))"#;
    for sort in ["Int", "KItem", "String"] {
        let read = parse_pattern(&format!(
            "Lblproject'Coln'{sort}{{}}(Lbl'Hash'unboxKConfigValue{{}}({lookup}))"
        ))
        .unwrap();
        let expected = parse_pattern(&format!(
            "Lblproject'Coln'{sort}{{}}(kseq{{}}({lookup},dotk{{}}()))"
        ))
        .unwrap();
        let mut count = 0;
        assert_eq!(normalize_configuration_read(&read, &mut count), expected);
        assert_eq!(count, 1);
    }
    let foreign =
        parse_pattern("Lblproject'Coln'K{}(Lbl'Hash'unboxKConfigValue{}(ordinary{}()))").unwrap();
    let mut count = 0;
    assert_eq!(normalize_configuration_read(&foreign, &mut count), foreign);
    assert_eq!(count, 0);
}

/// N33: on the reference side, drop `injective{}()` from a symbol declaration that carries
/// `anywhere{}()` or a macro-like attribute, only when the port declares the same symbol without
/// `injective`. Such a symbol heads an anywhere, overload or macro equation, which may identify
/// applications with different arguments, so the port declares `injective` only where the
/// equations provably preserve it (docs/compatibility.md#anywhere-rules). Every other attribute
/// and every other symbol stays compared, and the port can never gain `injective` this way.
/// Returns the number of declarations changed.
fn normalize_withheld_injective(reference: &mut Definition, actual: &Definition) -> usize {
    const EQUATION_HEAD_ATTRIBUTES: [&str; 5] =
        ["anywhere", "macro", "macro-rec", "alias", "alias-rec"];
    let has = |attributes: &Attributes, name: &str| {
        attributes.0.iter().any(|attribute| {
            matches!(attribute, Pattern::Application { symbol, arguments }
                if symbol.name == name && arguments.is_empty())
        })
    };
    let without_injective = actual
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            Sentence::SymbolDeclaration {
                symbol, attributes, ..
            } if !has(attributes, "injective") => Some(symbol.name.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let mut changed = 0;
    for sentence in reference
        .modules
        .iter_mut()
        .flat_map(|module| &mut module.sentences)
    {
        let Sentence::SymbolDeclaration {
            symbol, attributes, ..
        } = sentence
        else {
            continue;
        };
        if !without_injective.contains(&symbol.name)
            || !has(attributes, "injective")
            || !EQUATION_HEAD_ATTRIBUTES
                .iter()
                .any(|name| has(attributes, name))
        {
            continue;
        }
        attributes.0.retain(|attribute| {
            !matches!(attribute, Pattern::Application { symbol, arguments }
                if symbol.name == "injective" && arguments.is_empty())
        });
        changed += 1;
    }
    changed
}

#[test]
fn withheld_injective_normalizer_applies_only_to_equation_heads_the_port_withholds() {
    let definition = |wrap: &str, plain: &str| {
        parse_definition(&format!(
            r#"[]
            module TEST
              sort S{{}} []
              symbol Lblwrap{{}}(S{{}}) : S{{}} [{wrap}]
              symbol Lblplain{{}}(S{{}}) : S{{}} [{plain}]
            endmodule []"#
        ))
        .unwrap()
    };
    let port = definition(
        "anywhere{}(), functional{}()",
        "constructor{}(), functional{}()",
    );
    let mut reference = definition(
        "anywhere{}(), functional{}(), injective{}()",
        "constructor{}(), functional{}(), injective{}()",
    );
    assert_eq!(normalize_withheld_injective(&mut reference, &port), 1);
    assert_eq!(
        reference,
        definition(
            "anywhere{}(), functional{}()",
            "constructor{}(), functional{}(), injective{}()",
        ),
        "a symbol without an equation-head attribute keeps its difference"
    );
    // The port declaring `injective` leaves the reference untouched.
    let mut reference = definition(
        "anywhere{}(), functional{}(), injective{}()",
        "constructor{}(), functional{}()",
    );
    let original = reference.clone();
    let port = definition(
        "anywhere{}(), functional{}(), injective{}()",
        "constructor{}(), functional{}()",
    );
    assert_eq!(normalize_withheld_injective(&mut reference, &port), 0);
    assert_eq!(reference, original);
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct WithheldFunctionalCounts {
    declarations: usize,
    value_production_attributes: usize,
    function_attributes: usize,
}

/// N36: withhold the reference's totality claim only for the same equation head for which
/// the port withholds both `functional` and its functional axiom. Equations can equate a head
/// with an undefined right-hand side, and self-reference cannot establish its definedness.
/// The port marks a partial value production with `value-production{}()` and adds
/// `function{}()` only for a consumer that reads the marker to retain irreducible values.
/// Remove the marker and any extra function only opposite a reference value production;
/// a source `function{}()` remains compared. Every other attribute and axiom stays compared.
/// Returns counts of changed reference declarations and each removed port attribute.
fn normalize_withheld_functional(
    reference: &mut Definition,
    actual: &mut Definition,
) -> WithheldFunctionalCounts {
    const EQUATION_HEAD_ATTRIBUTES: [&str; 6] = [
        "anywhere",
        "macro",
        "macro-rec",
        "alias",
        "alias'Kywd'",
        "alias-rec",
    ];
    let is_marker = |attribute: &Pattern, name: &str| {
        matches!(attribute, Pattern::Application { symbol, arguments }
            if symbol.name == name && symbol.sort_parameters.is_empty() && arguments.is_empty())
    };
    let has = |attributes: &Attributes, name: &str| {
        attributes
            .0
            .iter()
            .any(|attribute| is_marker(attribute, name))
    };
    let mut without_functional = BTreeMap::new();
    let mut claimed = BTreeSet::new();
    for sentence in actual.modules.iter().flat_map(|module| &module.sentences) {
        if let Some(name) = functional_axiom_symbol(sentence) {
            claimed.insert(name.to_owned());
        }
        if let Sentence::SymbolDeclaration {
            symbol, attributes, ..
        } = sentence
        {
            if has(attributes, "functional") {
                claimed.insert(symbol.name.clone());
            } else {
                without_functional.insert(symbol.name.clone(), attributes.clone());
            }
        }
    }
    let mut counts = WithheldFunctionalCounts::default();
    let mut changed_symbols = BTreeSet::new();
    let mut value_productions = BTreeSet::new();
    for sentence in reference
        .modules
        .iter_mut()
        .flat_map(|module| &mut module.sentences)
    {
        let Sentence::SymbolDeclaration {
            symbol, attributes, ..
        } = sentence
        else {
            continue;
        };
        let Some(port_attributes) = without_functional.get(&symbol.name) else {
            continue;
        };
        if claimed.contains(&symbol.name)
            || !has(attributes, "functional")
            || !EQUATION_HEAD_ATTRIBUTES
                .iter()
                .any(|name| has(attributes, name) && has(port_attributes, name))
        {
            continue;
        }
        let value_production = has(port_attributes, "value-production");
        let reference_function = has(attributes, "function");
        let port_function = has(port_attributes, "function");
        let malformed_function_only = !port_function
            && port_attributes.0.iter().any(|attribute| {
                matches!(attribute, Pattern::Application { symbol, .. } if symbol.name == "function")
            });
        if (value_production && (reference_function || malformed_function_only))
            || (!value_production && !(reference_function && port_function))
        {
            continue;
        }
        attributes
            .0
            .retain(|attribute| !is_marker(attribute, "functional"));
        changed_symbols.insert(symbol.name.clone());
        if value_production {
            value_productions.insert(symbol.name.clone());
        }
        counts.declarations += 1;
    }
    for module in &mut reference.modules {
        module.sentences.retain(|sentence| {
            // An axiom with further attributes has further claims and stays compared.
            let bare_claim = matches!(sentence, Sentence::Axiom { attributes, .. }
                if attributes.0.len() == 1 && is_marker(&attributes.0[0], "functional"));
            !(bare_claim
                && functional_axiom_symbol(sentence)
                    .is_some_and(|name| changed_symbols.contains(name)))
        });
    }
    for sentence in actual
        .modules
        .iter_mut()
        .flat_map(|module| &mut module.sentences)
    {
        let Sentence::SymbolDeclaration {
            symbol, attributes, ..
        } = sentence
        else {
            continue;
        };
        if !value_productions.contains(&symbol.name) {
            continue;
        }
        attributes.0.retain(|attribute| {
            if is_marker(attribute, "value-production") {
                counts.value_production_attributes += 1;
                false
            } else if is_marker(attribute, "function") {
                counts.function_attributes += 1;
                false
            } else {
                true
            }
        });
    }
    counts
}

/// A functional axiom states `exists Val. Val = head(K0, ...)`, for unconstrained, distinct
/// argument variables. A nested application, constant argument, or constrained value is a
/// different axiom and must stay compared.
fn functional_axiom_symbol(sentence: &Sentence) -> Option<&str> {
    let Sentence::Axiom {
        pattern,
        attributes,
        ..
    } = sentence
    else {
        return None;
    };
    if !attributes.0.iter().any(|attribute| {
        matches!(attribute, Pattern::Application { symbol, arguments }
            if symbol.name == "functional" && arguments.is_empty())
    }) {
        return None;
    }
    let Pattern::Exists {
        sort,
        variable,
        body,
    } = pattern.as_ref()
    else {
        return None;
    };
    let Pattern::Equals {
        operand_sort,
        result_sort,
        left,
        right,
    } = body.as_ref()
    else {
        return None;
    };
    let Pattern::Application { symbol, arguments } = right.as_ref() else {
        return None;
    };
    if sort != result_sort
        || **operand_sort != variable.sort
        || !matches!(left.as_ref(), Pattern::Variable(value) if value == variable.as_ref())
        || !arguments.iter().all(|argument| {
            matches!(argument, Pattern::Variable(argument) if argument != variable.as_ref())
        })
        || arguments.iter().filter_map(|argument| match argument {
            Pattern::Variable(variable) => Some(variable),
            _ => None,
        }).collect::<BTreeSet<_>>().len() != arguments.len()
    {
        return None;
    }
    Some(&symbol.name)
}

/// The conjuncts of a nested `\and`, without its `\top` units.
fn conjuncts(pattern: &Pattern) -> Vec<&Pattern> {
    match pattern {
        Pattern::And { arguments, .. } => arguments.iter().flat_map(conjuncts).collect(),
        Pattern::Top { .. } => Vec::new(),
        _ => vec![pattern],
    }
}

/// One function equation `\implies(\and(requires, \and(\in(X0, P0), ...)), \equals(f(X0, ...),
/// \and(rhs, ensures)))` as the frontends emit it: the head, whether `requires` is `\top`, the
/// argument patterns `P0, ...` in argument order, and the right-hand side.
struct EmittedEquation<'a> {
    head: &'a str,
    unconditional: bool,
    arguments: Vec<&'a Pattern>,
    right: &'a Pattern,
}

fn emitted_equation(sentence: &Sentence) -> Option<EmittedEquation<'_>> {
    let Sentence::Axiom { pattern, .. } = sentence else {
        return None;
    };
    let Pattern::Implies { left, right, .. } = pattern.as_ref() else {
        return None;
    };
    let Pattern::And {
        arguments: guard, ..
    } = left.as_ref()
    else {
        return None;
    };
    let [requires, bindings] = guard.as_slice() else {
        return None;
    };
    let Pattern::Equals {
        left: head,
        right: result,
        ..
    } = right.as_ref()
    else {
        return None;
    };
    let Pattern::Application {
        symbol,
        arguments: parameters,
    } = head.as_ref()
    else {
        return None;
    };
    let Pattern::And {
        arguments: result, ..
    } = result.as_ref()
    else {
        return None;
    };
    let [right, Pattern::Top { .. }] = result.as_slice() else {
        return None;
    };
    let bindings = conjuncts(bindings);
    if bindings.len() != parameters.len() {
        return None;
    }
    let mut arguments = Vec::new();
    for (parameter, binding) in parameters.iter().zip(bindings) {
        let (Pattern::Variable(parameter), Pattern::In { left, right, .. }) = (parameter, binding)
        else {
            return None;
        };
        if !matches!(left.as_ref(), Pattern::Variable(bound) if bound == parameter) {
            return None;
        }
        arguments.push(right.as_ref());
    }
    Some(EmittedEquation {
        head: &symbol.name,
        unconditional: matches!(requires, Pattern::Top { .. }),
        arguments,
        right,
    })
}

/// Insert the totality claim `functional{}(), total{}()` after `function{}()`, as both frontends
/// order a claimed function's attributes once source metadata is stripped.
fn declare_totality_claim(attributes: &mut Attributes) {
    let position = attributes
        .0
        .iter()
        .position(|attribute| {
            matches!(attribute, Pattern::Application { symbol, arguments }
                if symbol.name == "function" && arguments.is_empty())
        })
        .map_or(0, |position| position + 1);
    for (offset, name) in ["functional", "total"].into_iter().enumerate() {
        attributes.0.insert(
            position + offset,
            Pattern::Application {
                symbol: Symbol {
                    name: name.into(),
                    sort_parameters: Vec::new(),
                },
                arguments: Vec::new(),
            },
        );
    }
}

/// N43: give a reference field projection the totality claim exactly when the reference's own
/// definition derives it. `project:S:f` (one argument of a sort `S` without parameters) is total
/// when the reference states (i) the no-junk axiom of `S` with the single alternative
/// `\exists X0 ... . C(X0, ...)` of a constructor `C`, so every value of `S` is an application of
/// `C`, and (ii) the unconditional equation `project:S:f(C(Y0, ...)) = Yi` over distinct
/// variables, which gives each such application the value `Yi`: together `exists T. T =
/// project:S:f(x)` for every `x`. The port claims exactly this totality (the `SoleGenerator`
/// evidence); a derivable axiom does not change the definition's models. The declaration gains
/// `functional{}(), total{}()` and the module the functional axiom; a port that claims totality
/// the reference cannot derive, or omits a derivable one, still differs. Returns the number of
/// declarations changed.
fn normalize_derived_projection_totality(reference: &mut Definition) -> usize {
    let simple_sort = |sort: &Sort| match sort {
        Sort::Application { name, arguments } if arguments.is_empty() => Some(name.clone()),
        Sort::Application { .. } | Sort::Variable(_) => None,
    };
    let mut constructors = BTreeSet::new();
    let mut sole_generator = BTreeMap::<String, (String, usize)>::new();
    let mut equations = BTreeMap::<String, Vec<(bool, String, Vec<String>, String)>>::new();
    for sentence in reference
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
    {
        match sentence {
            Sentence::SymbolDeclaration {
                symbol, attributes, ..
            } if has_kore_attribute(attributes, "constructor") => {
                constructors.insert(symbol.name.clone());
            }
            Sentence::Axiom {
                pattern,
                attributes,
                ..
            } if has_kore_attribute(attributes, "constructor") => {
                let Pattern::Or { sort, arguments } = pattern.as_ref() else {
                    continue;
                };
                let (Some(sort), [alternative, Pattern::Bottom { .. }]) =
                    (simple_sort(sort), arguments.as_slice())
                else {
                    continue;
                };
                let mut bound = Vec::new();
                let mut body = alternative;
                while let Pattern::Exists {
                    variable,
                    body: inner,
                    ..
                } = body
                {
                    bound.push(variable.as_ref());
                    body = inner;
                }
                if let Pattern::Application { symbol, arguments } = body
                    && symbol.sort_parameters.is_empty()
                    && arguments.len() == bound.len()
                    && arguments
                        .iter()
                        .zip(&bound)
                        .all(|(argument, bound)| matches!(argument, Pattern::Variable(variable) if variable == *bound))
                {
                    sole_generator.insert(sort, (symbol.name.clone(), arguments.len()));
                }
            }
            _ => {
                let Some(equation) = emitted_equation(sentence) else {
                    continue;
                };
                let [Pattern::Application { symbol, arguments }] = equation.arguments.as_slice()
                else {
                    continue;
                };
                let variables = arguments
                    .iter()
                    .map(|argument| match argument {
                        Pattern::Variable(variable) => Some(variable.name.clone()),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>();
                let (Some(variables), Pattern::Variable(result)) = (variables, equation.right)
                else {
                    continue;
                };
                equations
                    .entry(equation.head.to_owned())
                    .or_default()
                    .push((
                        equation.unconditional,
                        symbol.name.clone(),
                        variables,
                        result.name.clone(),
                    ));
            }
        }
    }
    let mut count = 0;
    for module in &mut reference.modules {
        let mut axioms = Vec::new();
        for sentence in &mut module.sentences {
            let Sentence::SymbolDeclaration {
                symbol,
                argument_sorts,
                result_sort,
                attributes,
                ..
            } = sentence
            else {
                continue;
            };
            let (Some(argument), Some(result)) = (
                argument_sorts
                    .first()
                    .filter(|_| argument_sorts.len() == 1)
                    .and_then(simple_sort),
                simple_sort(result_sort),
            ) else {
                continue;
            };
            if !symbol.name.starts_with("Lblproject'Coln'")
                || !symbol.sort_parameters.is_empty()
                || !has_kore_attribute(attributes, "function")
                || has_kore_attribute(attributes, "functional")
                || has_kore_attribute(attributes, "total")
            {
                continue;
            }
            let Some((generator, arity)) = sole_generator.get(&argument) else {
                continue;
            };
            let derived = constructors.contains(generator)
                && matches!(equations.get(&symbol.name).map(Vec::as_slice),
                    Some([(true, source, variables, result)])
                        if source == generator
                            && variables.len() == *arity
                            && variables.iter().collect::<BTreeSet<_>>().len() == *arity
                            && variables.contains(result));
            if !derived {
                continue;
            }
            declare_totality_claim(attributes);
            let source = format!(
                r"[] module M axiom{{R}} \exists{{R}}(Val:{result}{{}}, \equals{{{result}{{}}, R}}(Val:{result}{{}}, {}{{}}(K0:{argument}{{}}))) [functional{{}}()] endmodule []",
                symbol.name
            );
            let mut parsed = parse_definition(&source).expect("functional axiom should parse");
            axioms.append(&mut parsed.modules[0].sentences);
            count += 1;
        }
        module.sentences.append(&mut axioms);
    }
    count
}

/// N44: withdraw a reference totality claim on a generated `#lambda` symbol that the
/// reference's own equations do not support. A lambda is the function of one `#fun`/`#let`
/// rule, and nothing gives a value to an argument that rule does not match. Its claim is
/// supported only when it has exactly one equation, unconditional, whose every argument
/// pattern is a variable of the declared parameter sort (it matches every argument) and whose
/// right-hand side applies no lambda whose claim is withdrawn (least fixed point). Otherwise
/// `total`, `functional` and the functional axiom are removed. A supported claim stays, so a
/// port that withholds it still differs, and so does the claim of a lambda whose equations the
/// definition does not state (a syntax definition). Returns the number of declarations changed.
fn normalize_unsupported_lambda_totality(reference: &mut Definition) -> usize {
    let is_lambda = |name: &str| name.starts_with("Lbl'Hash'lambda");
    let mut parameters = BTreeMap::<String, Vec<Sort>>::new();
    for sentence in reference
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
    {
        if let Sentence::SymbolDeclaration {
            symbol,
            argument_sorts,
            attributes,
            ..
        } = sentence
            && is_lambda(&symbol.name)
            && (has_kore_attribute(attributes, "total")
                || has_kore_attribute(attributes, "functional"))
        {
            parameters.insert(symbol.name.clone(), argument_sorts.clone());
        }
    }
    let mut equations = BTreeMap::<String, Vec<EmittedEquation<'_>>>::new();
    for sentence in reference
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
    {
        if let Some(equation) = emitted_equation(sentence)
            && parameters.contains_key(equation.head)
        {
            equations
                .entry(equation.head.to_owned())
                .or_default()
                .push(equation);
        }
    }
    let covering = |name: &str| {
        matches!(equations.get(name).map(Vec::as_slice), Some([equation])
        if equation.unconditional
            && equation.arguments.iter().zip(&parameters[name]).all(|(argument, sort)| {
                matches!(argument, Pattern::Variable(variable) if variable.sort == *sort)
            }))
    };
    // A definition without the lambda's equations (a syntax definition) gives no evidence
    // either way, and its claim stays compared as written.
    let mut withdrawn = parameters
        .keys()
        .filter(|name| equations.contains_key(*name) && !covering(name))
        .cloned()
        .collect::<BTreeSet<_>>();
    loop {
        let more = parameters
            .keys()
            .filter(|name| equations.contains_key(*name) && !withdrawn.contains(*name))
            .filter(|name| {
                equations[name.as_str()]
                    .iter()
                    .any(|equation| pattern_mentions_any_symbol(equation.right, &withdrawn))
            })
            .cloned()
            .collect::<Vec<_>>();
        if more.is_empty() {
            break;
        }
        withdrawn.extend(more);
    }
    for module in &mut reference.modules {
        module.sentences.retain(|sentence| {
            let bare_claim = matches!(sentence, Sentence::Axiom { attributes, .. }
                if attributes.0.len() == 1 && has_kore_attribute(attributes, "functional"));
            !(bare_claim
                && functional_axiom_symbol(sentence).is_some_and(|name| withdrawn.contains(name)))
        });
        for sentence in &mut module.sentences {
            if let Sentence::SymbolDeclaration {
                symbol, attributes, ..
            } = sentence
                && withdrawn.contains(&symbol.name)
            {
                attributes.0.retain(|attribute| {
                    !matches!(attribute, Pattern::Application { symbol, arguments }
                        if (symbol.name == "total" || symbol.name == "functional")
                            && arguments.is_empty())
                });
            }
        }
    }
    withdrawn.len()
}

/// N45: one entry of a compile case's `lifted-cells` manifest key. The rule whose KORE axiom
/// carries the label `rule` writes the cell `<cell>` inside a cell that the configuration does not
/// place it under; the port compiles it into the instance of its configured parent that holds the
/// cell it was written in (docs/compatibility.md#cells-written-inside-another-cell).
#[derive(Clone, Debug, Eq, PartialEq)]
struct LiftedCell {
    rule: String,
    cell: String,
}

/// N45: the `lifted-cells` entries the compile gate passes in `K_DIFFERENTIAL_LIFTED_CELLS`, a
/// JSON array of `{"rule": ..., "cell": ...}` objects; none when the variable is unset or empty.
fn lifted_cells_from_environment() -> Vec<LiftedCell> {
    let Ok(json) = env::var("K_DIFFERENTIAL_LIFTED_CELLS") else {
        return Vec::new();
    };
    if json.trim().is_empty() {
        return Vec::new();
    }
    let entries: serde_json::Value = serde_json::from_str(&json)
        .unwrap_or_else(|error| panic!("K_DIFFERENTIAL_LIFTED_CELLS is not JSON: {error}"));
    entries
        .as_array()
        .expect("K_DIFFERENTIAL_LIFTED_CELLS is a JSON array")
        .iter()
        .map(|entry| {
            let field = |name: &str| {
                entry[name]
                    .as_str()
                    .filter(|value| !value.is_empty())
                    .unwrap_or_else(|| panic!("lifted-cells entry {entry} needs a string {name}"))
                    .to_owned()
            };
            LiftedCell {
                rule: field("rule"),
                cell: field("cell"),
            }
        })
        .collect()
}

/// N45: compare an axiom whose rule writes a cell inside a cell that does not contain it in the
/// configuration against the reference axiom in which that cell is absent. For each entry, the
/// axiom labelled `rule` must exist exactly once on each side; the two axioms are walked in
/// parallel through equal heads, and wherever the port has an application of the cell symbol
/// `<cell>` (declared with `cell{}()`) and the reference has a variable of that symbol's sort that
/// its own cell completion generated (`Var'Unds'<stem>N`), the port's application is replaced
/// by one fresh generated variable of that stem per reference variable, so N4 numbers it as the
/// reference's. Everything else in the axiom is compared afterwards exactly as before. An entry
/// that replaces nothing is stale: the reference states the cell there (or the axioms differ
/// before reaching it), and the entry is refused. A named reference variable at that position
/// is refused as well: a rule that names the cell's content is not one whose cell was dropped.
/// Returns the number of applications replaced.
fn normalize_lifted_cells(
    reference: &Definition,
    actual: &mut Definition,
    lifted: &[LiftedCell],
) -> Result<usize, String> {
    let labelled = |definition: &Definition, rule: &str| {
        definition
            .modules
            .iter()
            .enumerate()
            .flat_map(|(module, declarations)| {
                declarations
                    .sentences
                    .iter()
                    .enumerate()
                    .map(move |(index, sentence)| (module, index, sentence))
            })
            .filter(|(_, _, sentence)| {
                matches!(sentence, Sentence::Axiom { .. })
                    && sentence_attribute(sentence, "label").as_deref() == Some(rule)
            })
            .map(|(module, index, _)| (module, index))
            .collect::<Vec<_>>()
    };
    let mut replaced = 0;
    for entry in lifted {
        let symbol = format!("Lbl'-LT-'{}'-GT-'", entry.cell);
        let sort = actual
            .modules
            .iter()
            .flat_map(|module| &module.sentences)
            .find_map(|sentence| match sentence {
                Sentence::SymbolDeclaration {
                    symbol: declared,
                    result_sort,
                    attributes,
                    ..
                } if declared.name == symbol && has_kore_attribute(attributes, "cell") => {
                    Some(result_sort.clone())
                }
                _ => None,
            })
            .ok_or_else(|| {
                format!(
                    "N45: k-rust declares no cell symbol {symbol} for <{}>",
                    entry.cell
                )
            })?;
        let [(reference_module, reference_index)] = labelled(reference, &entry.rule)[..] else {
            return Err(format!(
                "N45: the reference must state exactly one axiom labelled {}",
                entry.rule
            ));
        };
        let [(actual_module, actual_index)] = labelled(actual, &entry.rule)[..] else {
            return Err(format!(
                "N45: k-rust must state exactly one axiom labelled {}",
                entry.rule
            ));
        };
        let Sentence::Axiom {
            pattern: reference_pattern,
            ..
        } = &reference.modules[reference_module].sentences[reference_index]
        else {
            unreachable!("labelled selects axioms");
        };
        let Sentence::Axiom {
            pattern: actual_pattern,
            ..
        } = &mut actual.modules[actual_module].sentences[actual_index]
        else {
            unreachable!("labelled selects axioms");
        };
        let mut lifting = CellLifting {
            symbol: &symbol,
            sort: &sort,
            used: BTreeSet::new(),
            fresh: BTreeMap::new(),
            replaced: 0,
            error: None,
        };
        collect_variable_names(actual_pattern, &mut lifting.used);
        lifting.walk(reference_pattern, actual_pattern);
        if let Some(error) = lifting.error {
            return Err(format!("N45: {}: {error}", entry.rule));
        }
        if lifting.replaced == 0 {
            return Err(format!(
                "N45: {} has no position where k-rust states <{}> and the reference a variable \
                 its cell completion generated; the reference no longer discards the cell (or \
                 the axioms differ before it), so the lifted-cells entry is stale",
                entry.rule, entry.cell
            ));
        }
        replaced += lifting.replaced;
    }
    Ok(replaced)
}

/// N45: the parallel walk of one reference axiom and its port counterpart.
struct CellLifting<'a> {
    symbol: &'a str,
    sort: &'a Sort,
    /// Every variable name of the port axiom, and the fresh names chosen so far.
    used: BTreeSet<String>,
    /// The fresh port name chosen for each generated reference variable.
    fresh: BTreeMap<String, String>,
    replaced: usize,
    error: Option<String>,
}

impl CellLifting<'_> {
    fn walk(&mut self, reference: &Pattern, actual: &mut Pattern) {
        if let (Pattern::Variable(variable), Pattern::Application { symbol, .. }) =
            (reference, &*actual)
            && symbol.name == self.symbol
            && variable.sort == *self.sort
        {
            let Some(stem) = generated_stem(&variable.name) else {
                self.error.get_or_insert_with(|| {
                    format!(
                        "the reference names the variable {} where k-rust states the cell",
                        variable.name
                    )
                });
                return;
            };
            let name = match self.fresh.get(&variable.name) {
                Some(name) => name.clone(),
                None => {
                    let name = (0..)
                        .map(|index| format!("Var'Unds'{stem}{index}"))
                        .find(|name| !self.used.contains(name))
                        .expect("an unused generated name exists");
                    self.used.insert(name.clone());
                    self.fresh.insert(variable.name.clone(), name.clone());
                    name
                }
            };
            *actual = Pattern::Variable(Variable {
                kind: variable.kind,
                name,
                sort: variable.sort.clone(),
            });
            self.replaced += 1;
            return;
        }
        match (reference, actual) {
            (
                Pattern::Application {
                    symbol: reference_symbol,
                    arguments: reference_arguments,
                },
                Pattern::Application { symbol, arguments },
            ) if reference_symbol == symbol && reference_arguments.len() == arguments.len() => {
                self.walk_all(reference_arguments, arguments);
            }
            (
                Pattern::AssociativeApplication {
                    associativity: reference_associativity,
                    symbol: reference_symbol,
                    arguments: reference_arguments,
                },
                Pattern::AssociativeApplication {
                    associativity,
                    symbol,
                    arguments,
                },
            ) if reference_associativity == associativity
                && reference_symbol == symbol
                && reference_arguments.len() == arguments.len() =>
            {
                self.walk_all(reference_arguments, arguments);
            }
            (
                Pattern::And {
                    sort: reference_sort,
                    arguments: reference_arguments,
                },
                Pattern::And { sort, arguments },
            )
            | (
                Pattern::Or {
                    sort: reference_sort,
                    arguments: reference_arguments,
                },
                Pattern::Or { sort, arguments },
            ) if reference_sort == sort && reference_arguments.len() == arguments.len() => {
                self.walk_all(reference_arguments, arguments);
            }
            (
                Pattern::Not {
                    argument: reference_argument,
                    ..
                },
                Pattern::Not { argument, .. },
            )
            | (
                Pattern::Next {
                    argument: reference_argument,
                    ..
                },
                Pattern::Next { argument, .. },
            )
            | (
                Pattern::Ceil {
                    argument: reference_argument,
                    ..
                },
                Pattern::Ceil { argument, .. },
            )
            | (
                Pattern::Floor {
                    argument: reference_argument,
                    ..
                },
                Pattern::Floor { argument, .. },
            ) => self.walk(reference_argument, argument),
            (
                Pattern::Implies {
                    left: reference_left,
                    right: reference_right,
                    ..
                },
                Pattern::Implies { left, right, .. },
            )
            | (
                Pattern::Iff {
                    left: reference_left,
                    right: reference_right,
                    ..
                },
                Pattern::Iff { left, right, .. },
            )
            | (
                Pattern::Rewrites {
                    left: reference_left,
                    right: reference_right,
                    ..
                },
                Pattern::Rewrites { left, right, .. },
            )
            | (
                Pattern::Equals {
                    left: reference_left,
                    right: reference_right,
                    ..
                },
                Pattern::Equals { left, right, .. },
            )
            | (
                Pattern::In {
                    left: reference_left,
                    right: reference_right,
                    ..
                },
                Pattern::In { left, right, .. },
            ) => {
                self.walk(reference_left, left);
                self.walk(reference_right, right);
            }
            (
                Pattern::Exists {
                    variable: reference_variable,
                    body: reference_body,
                    ..
                },
                Pattern::Exists { variable, body, .. },
            )
            | (
                Pattern::Forall {
                    variable: reference_variable,
                    body: reference_body,
                    ..
                },
                Pattern::Forall { variable, body, .. },
            )
            | (
                Pattern::Mu {
                    variable: reference_variable,
                    body: reference_body,
                },
                Pattern::Mu { variable, body },
            )
            | (
                Pattern::Nu {
                    variable: reference_variable,
                    body: reference_body,
                },
                Pattern::Nu { variable, body },
            ) if reference_variable == variable => self.walk(reference_body, body),
            _ => {}
        }
    }

    fn walk_all(&mut self, reference: &[Pattern], actual: &mut [Pattern]) {
        for (reference, actual) in reference.iter().zip(actual) {
            self.walk(reference, actual);
        }
    }
}

/// N45: every variable name in `pattern`, bound or free.
fn collect_variable_names(pattern: &Pattern, names: &mut BTreeSet<String>) {
    match pattern {
        Pattern::Variable(variable) => {
            names.insert(variable.name.clone());
        }
        Pattern::Application { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. } => {
            for argument in arguments {
                collect_variable_names(argument, names);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => collect_variable_names(argument, names),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            collect_variable_names(left, names);
            collect_variable_names(right, names);
        }
        Pattern::Exists { variable, body, .. }
        | Pattern::Forall { variable, body, .. }
        | Pattern::Mu { variable, body }
        | Pattern::Nu { variable, body } => {
            names.insert(variable.name.clone());
            collect_variable_names(body, names);
        }
        Pattern::String(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }
}

/// N43 adds the claim and the functional axiom the reference's own no-junk axiom and projection
/// equation derive (the port's output for `project:FInt:one`), and leaves every projection whose
/// derivation is missing a premise unchanged.
#[test]
fn derived_projection_totality_normalizer_adds_only_derivable_claims() {
    let definition = |no_junk: &str, requires: &str, result: &str, claim: &str| {
        parse_definition(&format!(
            r#"[] module TEST
            sort SortInt{{}} []
            sort SortFInt{{}} []
            symbol LblFInt{{}}(SortInt{{}}, SortInt{{}}) : SortFInt{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol Lblother{{}}() : SortFInt{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol Lblproject'Coln'FInt'Coln'one{{}}(SortFInt{{}}) : SortInt{{}} [function{{}}(){claim}]
            axiom{{}} \or{{SortFInt{{}}}}({no_junk}, \bottom{{SortFInt{{}}}}()) [constructor{{}}()]
            axiom{{R}} \implies{{R}}(
                \and{{R}}({requires}, \and{{R}}(\in{{SortFInt{{}}, R}}(X0:SortFInt{{}}, LblFInt{{}}(VarK0:SortInt{{}}, VarK1:SortInt{{}})), \top{{R}}())),
                \equals{{SortInt{{}}, R}}(Lblproject'Coln'FInt'Coln'one{{}}(X0:SortFInt{{}}), \and{{SortInt{{}}}}({result}, \top{{SortInt{{}}}}())))
                [UNIQUE'Unds'ID{{}}("a")]
            endmodule []"#
        ))
        .unwrap()
    };
    let sole = r"\exists{SortFInt{}}(X0:SortInt{}, \exists{SortFInt{}}(X1:SortInt{}, LblFInt{}(X0:SortInt{}, X1:SortInt{})))";
    let top = r"\top{R}()";
    let mut reference = definition(sole, top, "VarK1:SortInt{}", "");
    assert_eq!(normalize_derived_projection_totality(&mut reference), 1);
    let mut expected = definition(sole, top, "VarK1:SortInt{}", ", functional{}(), total{}()");
    expected.modules[0].sentences.append(
        &mut parse_definition(
            r"[] module M axiom{R} \exists{R}(Val:SortInt{}, \equals{SortInt{}, R}(Val:SortInt{}, Lblproject'Coln'FInt'Coln'one{}(K0:SortFInt{}))) [functional{}()] endmodule []",
        )
        .unwrap()
        .modules[0]
            .sentences,
    );
    assert_eq!(reference, expected);

    let two_alternatives = format!(r"\or{{SortFInt{{}}}}({sole}, Lblother{{}}())");
    for (no_junk, requires, result, claim) in [
        (two_alternatives.as_str(), top, "VarK1:SortInt{}", ""),
        (
            sole,
            r#"\equals{SortBool{}, R}(VarK1:SortInt{}, \dv{SortBool{}}("true"))"#,
            "VarK1:SortInt{}",
            "",
        ),
        (sole, top, r#"\dv{SortInt{}}("0")"#, ""),
        (sole, top, "VarK1:SortInt{}", ", functional{}()"),
    ] {
        let mut reference = definition(no_junk, requires, result, claim);
        let original = reference.clone();
        assert_eq!(normalize_derived_projection_totality(&mut reference), 0);
        assert_eq!(reference, original);
    }
}

/// N44 withdraws the claims of `#lambdaF__`, whose pattern covers only the Int-injected
/// expressions (`let-test`), and of `#lambdaG__`, which returns `#lambdaF__` of an arbitrary
/// argument; the covering `#lambdaH__` keeps its claim and its functional axiom.
#[test]
fn unsupported_lambda_totality_normalizer_withdraws_only_uncovered_claims() {
    let definition = |f: &str, g: &str| {
        parse_definition(&format!(
            r#"[] module TEST
            sort SortInt{{}} []
            sort SortExp{{}} []
            symbol inj{{From, To}}(From) : To [sortInjection{{}}()]
            symbol Lblfoo{{}}(SortExp{{}}) : SortExp{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol Lbl'Hash'lambdaF'UndsUnds'{{}}(SortExp{{}}) : SortExp{{}} [function{{}}(){f}]
            symbol Lbl'Hash'lambdaG'UndsUnds'{{}}(SortExp{{}}) : SortExp{{}} [function{{}}(){g}]
            symbol Lbl'Hash'lambdaH'UndsUnds'{{}}(SortExp{{}}) : SortExp{{}} [function{{}}(), functional{{}}(), total{{}}()]
            axiom{{R}} \exists{{R}}(Val:SortExp{{}}, \equals{{SortExp{{}}, R}}(Val:SortExp{{}}, Lbl'Hash'lambdaH'UndsUnds'{{}}(K0:SortExp{{}}))) [functional{{}}()]
            {fa}
            axiom{{R}} \implies{{R}}(
                \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortExp{{}}, R}}(X0:SortExp{{}}, inj{{SortInt{{}}, SortExp{{}}}}(VarB:SortInt{{}})), \top{{R}}())),
                \equals{{SortExp{{}}, R}}(Lbl'Hash'lambdaF'UndsUnds'{{}}(X0:SortExp{{}}), \and{{SortExp{{}}}}(Lblfoo{{}}(inj{{SortInt{{}}, SortExp{{}}}}(VarB:SortInt{{}})), \top{{SortExp{{}}}}())))
                [UNIQUE'Unds'ID{{}}("f")]
            axiom{{R}} \implies{{R}}(
                \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortExp{{}}, R}}(X0:SortExp{{}}, VarE:SortExp{{}}), \top{{R}}())),
                \equals{{SortExp{{}}, R}}(Lbl'Hash'lambdaG'UndsUnds'{{}}(X0:SortExp{{}}), \and{{SortExp{{}}}}(Lbl'Hash'lambdaF'UndsUnds'{{}}(VarE:SortExp{{}}), \top{{SortExp{{}}}}())))
                [UNIQUE'Unds'ID{{}}("g")]
            axiom{{R}} \implies{{R}}(
                \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortExp{{}}, R}}(X0:SortExp{{}}, VarE:SortExp{{}}), \top{{R}}())),
                \equals{{SortExp{{}}, R}}(Lbl'Hash'lambdaH'UndsUnds'{{}}(X0:SortExp{{}}), \and{{SortExp{{}}}}(Lblfoo{{}}(VarE:SortExp{{}}), \top{{SortExp{{}}}}())))
                [UNIQUE'Unds'ID{{}}("h")]
            endmodule []"#,
            fa = if f.is_empty() {
                ""
            } else {
                r"axiom{R} \exists{R}(Val:SortExp{}, \equals{SortExp{}, R}(Val:SortExp{}, Lbl'Hash'lambdaF'UndsUnds'{}(K0:SortExp{}))) [functional{}()]"
            },
        ))
        .unwrap()
    };
    let claim = ", functional{}(), total{}()";
    let mut reference = definition(claim, claim);
    assert_eq!(normalize_unsupported_lambda_totality(&mut reference), 2);
    assert_eq!(reference, definition("", ""));

    // Without the equations (a syntax definition) nothing is withdrawn.
    let mut syntax = definition(claim, claim);
    syntax.modules[0]
        .sentences
        .retain(|sentence| !matches!(sentence, Sentence::Axiom { attributes, .. } if !has_kore_attribute(attributes, "functional")));
    let original = syntax.clone();
    assert_eq!(normalize_unsupported_lambda_totality(&mut syntax), 0);
    assert_eq!(syntax, original);

    // A covering lambda keeps its claim: without the uncovered `#lambdaF__` in its body,
    // `#lambdaG__` is supported.
    let mut covered = definition(claim, claim);
    for sentence in &mut covered.modules[0].sentences {
        if let Sentence::Axiom { pattern, .. } = sentence {
            let text = format!("{pattern:?}");
            if text.contains("lambdaG") && text.contains("Implies") {
                **pattern = parse_pattern(
                        r"\implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortExp{}, R}(X0:SortExp{}, VarE:SortExp{}), \top{R}())),
                \equals{SortExp{}, R}(Lbl'Hash'lambdaG'UndsUnds'{}(X0:SortExp{}), \and{SortExp{}}(Lblfoo{}(VarE:SortExp{}), \top{SortExp{}}())))",
                    )
                    .unwrap();
            }
        }
    }
    assert_eq!(normalize_unsupported_lambda_totality(&mut covered), 1);
    assert!(covered.modules[0].sentences.iter().any(|sentence| matches!(sentence,
        Sentence::SymbolDeclaration { symbol, attributes, .. }
            if symbol.name == "Lbl'Hash'lambdaG'UndsUnds'" && has_kore_attribute(attributes, "total"))));
}

/// N45 fixtures: the configuration `<generatedTop> <k/> <frame/> <stack/> </generatedTop>` and
/// a rule `probe` that, like KMIR's `setupCalleeClosure`, writes `<stack>` inside `<frame>`. The
/// port matches the head of the stack and updates it; a reference that discards the cell has a
/// generated `SortStackCell` variable in the stack's place on both sides.
const LIFTED_PORT_LEFT: &str = r"Lbl'-LT-'stack'-GT-'{}(Lbl'Unds'List'Unds'{}(LblListItem{}(VarCALLER:SortInt{}), Var'Unds'Gen0:SortList{}))";
const LIFTED_PORT_RIGHT: &str = r#"Lbl'-LT-'stack'-GT-'{}(Lbl'Unds'List'Unds'{}(LblListItem{}(\dv{SortInt{}}("0")), Var'Unds'Gen0:SortList{}))"#;
const LIFTED_REFERENCE_STACK: &str = r"Var'Unds'Gen7:SortStackCell{}";

fn lifted_cell_definition(k_result: &str, stack_left: &str, stack_right: &str) -> Definition {
    let source = r#"[] module TEST
        sort SortInt{} []
        sort SortList{} []
        sort SortKCell{} []
        sort SortFrameCell{} []
        sort SortStackCell{} []
        sort SortGeneratedTopCell{} []
        symbol LblListItem{}(SortInt{}) : SortList{} [function{}()]
        symbol Lbl'Unds'List'Unds'{}(SortList{}, SortList{}) : SortList{} [function{}()]
        symbol Lbl'-LT-'k'-GT-'{}(SortInt{}) : SortKCell{} [cell{}(), constructor{}()]
        symbol Lbl'-LT-'frame'-GT-'{}(SortInt{}) : SortFrameCell{} [cell{}(), constructor{}()]
        symbol Lbl'-LT-'stack'-GT-'{}(SortList{}) : SortStackCell{} [cell{}(), constructor{}()]
        symbol Lbl'-LT-'generatedTop'-GT-'{}(SortKCell{}, SortFrameCell{}, SortStackCell{}) : SortGeneratedTopCell{} [cell{}(), constructor{}()]
        axiom{} \rewrites{SortGeneratedTopCell{}}(
            \and{SortGeneratedTopCell{}}(
                Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(\dv{SortInt{}}("1")), Lbl'-LT-'frame'-GT-'{}(VarF:SortInt{}), STACK_LEFT),
                \top{SortGeneratedTopCell{}}()),
            \and{SortGeneratedTopCell{}}(
                Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(\dv{SortInt{}}("K_RESULT")), Lbl'-LT-'frame'-GT-'{}(VarF:SortInt{}), STACK_RIGHT),
                \top{SortGeneratedTopCell{}}()))
            [UNIQUE'Unds'ID{}("p"), label{}("TEST.probe")]
        endmodule []"#;
    parse_definition(
        &source
            .replace("K_RESULT", k_result)
            .replace("STACK_LEFT", stack_left)
            .replace("STACK_RIGHT", stack_right),
    )
    .unwrap()
}

fn lifted_cell_entry(rule: &str, cell: &str) -> [LiftedCell; 1] {
    [LiftedCell {
        rule: rule.into(),
        cell: cell.into(),
    }]
}

/// N45 accepts the lifted shape: with the port's `<stack>` applications replaced by the
/// reference's generated variable, the axioms are equal. Without the entry they differ, and an
/// entry for another rule or for a cell both sides state does not apply.
#[test]
fn lifted_cell_normalizer_accepts_the_axiom_with_the_discarded_cell_present() {
    let reference = lifted_cell_definition("2", LIFTED_REFERENCE_STACK, LIFTED_REFERENCE_STACK);
    let port = || lifted_cell_definition("2", LIFTED_PORT_LEFT, LIFTED_PORT_RIGHT);
    let report = compare_definitions_with(reference.clone(), port(), CompareOptions::default());
    assert!(matches!(report.verdict, CompareVerdict::Differs(_)));

    let mut actual = port();
    assert_eq!(
        normalize_lifted_cells(
            &reference,
            &mut actual,
            &lifted_cell_entry("TEST.probe", "stack")
        ),
        Ok(2)
    );
    let report = compare_definitions_with(reference.clone(), actual, CompareOptions::default());
    assert_eq!(report.verdict, CompareVerdict::Equal);

    let mut actual = port();
    let error = normalize_lifted_cells(
        &reference,
        &mut actual,
        &lifted_cell_entry("TEST.other", "stack"),
    )
    .unwrap_err();
    assert!(
        error.contains("exactly one axiom labelled TEST.other"),
        "{error}"
    );
    let error = normalize_lifted_cells(
        &reference,
        &mut actual,
        &lifted_cell_entry("TEST.probe", "frame"),
    )
    .unwrap_err();
    assert!(error.contains("stale"), "{error}");
    assert_eq!(actual, port());
    assert_eq!(normalize_lifted_cells(&reference, &mut actual, &[]), Ok(0));
    assert_eq!(actual, port());
}

/// N45 compares everything else in the axiom: a port axiom that differs outside the lifted
/// cell, or that states the cell on one side only where the reference shares one variable
/// between both, still differs after the normalization.
#[test]
fn lifted_cell_normalizer_rejects_a_port_axiom_that_differs_elsewhere() {
    let entry = lifted_cell_entry("TEST.probe", "stack");
    let reference = lifted_cell_definition("2", LIFTED_REFERENCE_STACK, LIFTED_REFERENCE_STACK);
    for (k_result, right, replaced) in [
        ("3", LIFTED_PORT_RIGHT, 2),
        ("2", r"Var'Unds'Gen9:SortStackCell{}", 1),
    ] {
        let mut actual = lifted_cell_definition(k_result, LIFTED_PORT_LEFT, right);
        assert_eq!(
            normalize_lifted_cells(&reference, &mut actual, &entry),
            Ok(replaced)
        );
        let report = compare_definitions_with(reference.clone(), actual, CompareOptions::default());
        assert!(
            matches!(report.verdict, CompareVerdict::Differs(_)),
            "{k_result} {right}"
        );
    }
}

/// N45 refuses an entry whose reference states the cell (the reference no longer discards it,
/// so the entry is stale) and a reference that names the cell's variable (a rule that names
/// the cell is not one whose cell was dropped).
#[test]
fn lifted_cell_normalizer_rejects_a_reference_with_a_concrete_cell_in_that_position() {
    let entry = lifted_cell_entry("TEST.probe", "stack");
    let mut actual = lifted_cell_definition("2", LIFTED_PORT_LEFT, LIFTED_PORT_RIGHT);
    let original = actual.clone();
    let reference = lifted_cell_definition("2", LIFTED_PORT_LEFT, LIFTED_PORT_RIGHT);
    let error = normalize_lifted_cells(&reference, &mut actual, &entry).unwrap_err();
    assert!(error.contains("stale"), "{error}");
    assert_eq!(actual, original);

    let reference = lifted_cell_definition("2", LIFTED_PORT_LEFT, LIFTED_PORT_LEFT);
    let error = normalize_lifted_cells(&reference, &mut actual, &entry).unwrap_err();
    assert!(error.contains("stale"), "{error}");

    let named = r"VarSTACK:SortStackCell{}";
    let reference = lifted_cell_definition("2", named, named);
    let error = normalize_lifted_cells(&reference, &mut actual, &entry).unwrap_err();
    assert!(error.contains("names the variable VarSTACK"), "{error}");
}

/// A value-production head loses its compiler-added marker and optional verifier function;
/// an existing source function retains its function attribute. The reference loses only its
/// totality claim.
#[test]
fn withheld_functional_normalizer_removes_only_the_matching_claim() {
    for marker in ["anywhere", "macro", "macro-rec", "alias'Kywd'", "alias-rec"] {
        for source_function in [false, true] {
            let definition = |attributes: &str, axiom: bool| {
                let axiom = if axiom {
                    r"axiom{R} \exists{R}(Val:S{}, \equals{S{}, R}(Val:S{}, Lblwrap{}(K0:S{}))) [functional{}()]"
                } else {
                    ""
                };
                parse_definition(&format!(r"[] module TEST
                    sort S{{}} []
                    symbol Lblwrap{{}}(S{{}}) : S{{}} [{marker}{{}}(), injective{{}}(), {attributes}]
                    symbol Lblplain{{}}(S{{}}) : S{{}} [constructor{{}}(), functional{{}}()]
                    {axiom}
                    axiom{{R}} \exists{{R}}(Val:S{{}}, \equals{{S{{}}, R}}(Val:S{{}}, Lblplain{{}}(K0:S{{}}))) [functional{{}}()]
                    axiom{{}} \equals{{S{{}}, S{{}}}}(Lblwrap{{}}(X:S{{}}), Lblplain{{}}(X:S{{}})) [{marker}{{}}()]
                    axiom{{R}} \exists{{R}}(Val:S{{}}, \equals{{S{{}}, R}}(Val:S{{}}, Lblwrap{{}}(Lblplain{{}}(K0:S{{}})))) [functional{{}}()]
                    endmodule []")).unwrap()
            };
            let mut port = definition(
                if source_function {
                    "function{}()"
                } else {
                    "function{}(), value-production{}()"
                },
                false,
            );
            let mut reference = definition(
                if source_function {
                    "function{}(), functional{}()"
                } else {
                    "functional{}()"
                },
                true,
            );
            let removed = usize::from(!source_function);
            assert_eq!(
                normalize_withheld_functional(&mut reference, &mut port),
                WithheldFunctionalCounts {
                    declarations: 1,
                    value_production_attributes: removed,
                    function_attributes: removed,
                },
                "{marker}, source function: {source_function}"
            );
            assert_eq!(
                reference, port,
                "only the claim, its axiom and the verifier pair go"
            );
            assert_eq!(
                normalize_withheld_functional(&mut reference, &mut port),
                WithheldFunctionalCounts::default(),
                "idempotent"
            );
        }
    }
}

#[test]
fn withheld_functional_normalizer_accepts_the_llvm_value_production_without_function() {
    let definition = |attributes: &str, axiom: bool| {
        let axiom = if axiom {
            r"axiom{R} \exists{R}(Val:S{}, \equals{S{}, R}(Val:S{}, Lblwrap{}(K0:S{}))) [functional{}()]"
        } else {
            ""
        };
        parse_definition(&format!(
            r"[] module TEST sort S{{}} []
            symbol Lblwrap{{}}(S{{}}) : S{{}} [{attributes}]
            {axiom} endmodule []"
        ))
        .unwrap()
    };
    let mut reference = definition("anywhere{}(), functional{}()", true);
    let mut port = definition("anywhere{}(), value-production{}()", false);
    assert_eq!(
        normalize_withheld_functional(&mut reference, &mut port),
        WithheldFunctionalCounts {
            declarations: 1,
            value_production_attributes: 1,
            function_attributes: 0,
        }
    );
    assert_eq!(reference, port);
    assert_eq!(
        normalize_withheld_functional(&mut reference, &mut port),
        WithheldFunctionalCounts::default(),
        "idempotent"
    );
}

#[test]
fn withheld_functional_normalizer_requires_the_ports_matching_equation_head_and_no_claim() {
    let definition = |attributes: &str, axiom: bool, declare: bool| {
        let declaration = if declare {
            format!("symbol Lblwrap{{}}(S{{}}) : S{{}} [{attributes}]")
        } else {
            String::new()
        };
        let axiom = if axiom {
            r"axiom{R} \exists{R}(Val:S{}, \equals{S{}, R}(Val:S{}, Lblwrap{}(K0:S{}))) [functional{}()]"
        } else {
            ""
        };
        parse_definition(&format!(
            r"[] module TEST sort S{{}} [] {declaration} {axiom} endmodule []"
        ))
        .unwrap()
    };
    for mut port in [
        definition(
            "anywhere{}(), function{}(), value-production{}(), functional{}()",
            false,
            true,
        ),
        definition(
            "anywhere{}(), function{}(), value-production{}()",
            true,
            true,
        ),
        definition("anywhere{}(), function{}()", false, true),
        definition("anywhere{}()", false, true),
        definition(
            "anywhere{}(), function{S{}}(), value-production{}()",
            false,
            true,
        ),
        definition(
            "anywhere{}(), function{}(), value-production{S{}}()",
            false,
            true,
        ),
        definition(
            "alias'Kywd'{}(), function{}(), value-production{}()",
            false,
            true,
        ),
        definition("function{}(), value-production{}()", false, true),
        definition("constructor{}()", false, true),
        definition("", false, false),
    ] {
        let mut reference = definition("anywhere{}(), functional{}()", true, true);
        let original = (reference.clone(), port.clone());
        assert_eq!(
            normalize_withheld_functional(&mut reference, &mut port),
            WithheldFunctionalCounts::default()
        );
        assert_eq!((reference, port), original);
    }
    for reference_attributes in [
        "functional{}()",
        "anywhere{}(), function{}(), functional{}()",
    ] {
        let mut port = definition(
            "anywhere{}(), function{}(), value-production{}()",
            false,
            true,
        );
        let mut reference = definition(reference_attributes, true, true);
        let original = (reference.clone(), port.clone());
        assert_eq!(
            normalize_withheld_functional(&mut reference, &mut port),
            WithheldFunctionalCounts::default()
        );
        assert_eq!(
            (reference, port),
            original,
            "source function and equation-marker mismatches stay compared"
        );
    }
}

#[test]
fn withheld_functional_normalizer_preserves_unrelated_declaration_attributes() {
    let definition = |attributes: &str, axiom_attributes: Option<&str>| {
        let axiom = axiom_attributes.map_or_else(String::new, |attributes| format!(
            r"axiom{{R}} \exists{{R}}(Val:S{{}}, \equals{{S{{}}, R}}(Val:S{{}}, Lblwrap{{}}(K0:S{{}}))) [{attributes}]"
        ));
        parse_definition(&format!(
            r"[] module TEST sort S{{}} []
            symbol Lblwrap{{}}(S{{}}) : S{{}} [{attributes}]
            {axiom} endmodule []"
        ))
        .unwrap()
    };
    let pair = "anywhere{}(), function{}(), value-production{}()";
    for unrelated in [
        "constructor{}()",
        "total{}()",
        "injective{}()",
        r#"hook{}("TEST.wrap")"#,
        "function{S{}}()",
        "function{}(Lblwrap{}(X:S{}))",
        "value-production{S{}}()",
        "value-production{}(Lblwrap{}(X:S{}))",
    ] {
        for port_has_attribute in [false, true] {
            let mut port = definition(
                &format!(
                    "{pair}{}",
                    if port_has_attribute {
                        format!(", {unrelated}")
                    } else {
                        String::new()
                    }
                ),
                None,
            );
            let mut reference = definition(
                &format!(
                    "anywhere{{}}(), functional{{}}(){}",
                    if !port_has_attribute {
                        format!(", {unrelated}")
                    } else {
                        String::new()
                    }
                ),
                Some("functional{}()"),
            );
            assert_eq!(
                normalize_withheld_functional(&mut reference, &mut port),
                WithheldFunctionalCounts {
                    declarations: 1,
                    value_production_attributes: 1,
                    function_attributes: 1,
                }
            );
            let expected = definition(
                &format!(
                    "anywhere{{}}(){}",
                    if !port_has_attribute {
                        format!(", {unrelated}")
                    } else {
                        String::new()
                    }
                ),
                None,
            );
            assert_eq!(reference, expected, "{unrelated}");
            assert_ne!(reference, port, "{unrelated} must still cause a difference");
        }
    }
    let mut reference = definition(
        "anywhere{}(), functional{}()",
        Some("functional{}(), trusted{}()"),
    );
    let mut port = definition(pair, None);
    assert_eq!(
        normalize_withheld_functional(&mut reference, &mut port).declarations,
        1
    );
    assert_eq!(
        reference,
        definition("anywhere{}()", Some("functional{}(), trusted{}()"))
    );
    assert_ne!(
        reference, port,
        "an axiom's unrelated attributes stay compared"
    );
}

/// N34: on the reference side, drop the `constructor{}()` axioms of the injectivity shape
/// `\implies(\and(g(X..), g(Y..)), g(..))` and of the pairwise no-confusion shape
/// `\not(\and(P(X..), Q(Y..)))` that mention an overload-greater `g` (the first symbol of a
/// `symbol-overload` attribute) which the port declares `anywhere` and states no axiom of either
/// shape for. Returns the number of axioms dropped.
///
/// The port states them for an overload-greater only when every production below it is locally
/// injective and no production related to it in the overload order has its result sort head
/// (docs/compatibility.md#anywhere-rules). Otherwise an overload equation equates an application
/// of `g` with an application of a same-sort production (`asNumber(inj(x)) = asInt(x)` against
/// `\not(asInt(X) ∧ asNumber(Y))`) or two applications of `g` with different arguments, so the
/// dropped axioms are false in every model of the equations. A port that states any such axiom
/// for `g` leaves the reference untouched, so the port can never lose an axiom it states this way,
/// and every other axiom stays compared.
fn normalize_withheld_overload_no_confusion(
    reference: &mut Definition,
    actual: &Definition,
) -> usize {
    let has = |attributes: &Attributes, name: &str| {
        attributes.0.iter().any(|attribute| {
            matches!(attribute, Pattern::Application { symbol, arguments }
                if symbol.name == name && arguments.is_empty())
        })
    };
    let sentences = || actual.modules.iter().flat_map(|module| &module.sentences);
    let anywhere = sentences()
        .filter_map(|sentence| match sentence {
            Sentence::SymbolDeclaration {
                symbol, attributes, ..
            } if has(attributes, "anywhere") => Some(symbol.name.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let stated = sentences()
        .filter_map(constructor_family_symbols)
        .flatten()
        .collect::<BTreeSet<_>>();
    let withheld = sentences()
        .filter_map(overload_greater)
        .filter(|greater| anywhere.contains(*greater) && !stated.contains(*greater))
        .map(str::to_owned)
        .collect::<BTreeSet<_>>();
    let mut dropped = 0;
    for module in &mut reference.modules {
        module.sentences.retain(|sentence| {
            let drop = constructor_family_symbols(sentence)
                .is_some_and(|symbols| symbols.iter().any(|symbol| withheld.contains(*symbol)));
            dropped += usize::from(drop);
            !drop
        });
    }
    dropped
}

/// N34: the greater symbol of an axiom's `symbol-overload{}(greater{}(), lesser{}())` attribute.
fn overload_greater(sentence: &Sentence) -> Option<&str> {
    let Sentence::Axiom { attributes, .. } = sentence else {
        return None;
    };
    attributes.0.iter().find_map(|attribute| match attribute {
        Pattern::Application { symbol, arguments } if symbol.name == "symbol-overload" => {
            match arguments.first() {
                Some(Pattern::Application { symbol, .. }) => Some(symbol.name.as_str()),
                _ => None,
            }
        }
        _ => None,
    })
}

/// N34: the symbols a `constructor{}()` axiom of the injectivity or pairwise no-confusion shape
/// mentions; `None` for every other sentence, including the no-junk axiom that carries the same
/// attribute.
fn constructor_family_symbols(sentence: &Sentence) -> Option<Vec<&str>> {
    let Sentence::Axiom {
        pattern,
        attributes,
        ..
    } = sentence
    else {
        return None;
    };
    let constructor = attributes.0.iter().any(|attribute| {
        matches!(attribute, Pattern::Application { symbol, arguments }
            if symbol.name == "constructor" && arguments.is_empty())
    });
    if !constructor {
        return None;
    }
    fn head(pattern: &Pattern) -> Option<&str> {
        match pattern {
            Pattern::Application { symbol, .. } => Some(symbol.name.as_str()),
            _ => None,
        }
    }
    match pattern.as_ref() {
        Pattern::Not { argument, .. } => {
            let Pattern::And { arguments, .. } = argument.as_ref() else {
                return None;
            };
            let [left, right] = arguments.as_slice() else {
                return None;
            };
            (is_application_over_variables(left) && is_application_over_variables(right))
                .then(|| Some(vec![head(left)?, head(right)?]))
                .flatten()
        }
        Pattern::Implies { left, right, .. } => {
            let Pattern::And { arguments, .. } = left.as_ref() else {
                return None;
            };
            let [first, second] = arguments.as_slice() else {
                return None;
            };
            let symbol = head(right)?;
            (is_application_over_variables(first)
                && is_application_over_variables(second)
                && head(first)? == symbol
                && head(second)? == symbol)
                .then(|| vec![symbol])
        }
        _ => None,
    }
}

#[test]
fn withheld_overload_no_confusion_normalizer_drops_only_axioms_the_port_withholds() {
    let definition = |greater: &str, axioms: &str| {
        parse_definition(&format!(
            r#"[]
            module TEST
              sort S{{}} []
              symbol Lblg{{}}(S{{}}) : S{{}} [{greater}]
              symbol Lbll{{}}(S{{}}) : S{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
              symbol Lblc{{}}(S{{}}) : S{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
              axiom{{R}} \equals{{S{{}}, R}}(Lblg{{}}(K0:S{{}}), Lbll{{}}(K0:S{{}}))
                [symbol-overload{{}}(Lblg{{}}(), Lbll{{}}())]
              axiom{{}} \or{{S{{}}}}(
                  \exists{{S{{}}}}(X0:S{{}}, Lblg{{}}(X0:S{{}})),
                  \exists{{S{{}}}}(X0:S{{}}, Lbll{{}}(X0:S{{}})),
                  \exists{{S{{}}}}(X0:S{{}}, Lblc{{}}(X0:S{{}})),
                  \bottom{{S{{}}}}())
                [constructor{{}}()]
              axiom{{}} \not{{S{{}}}}(\and{{S{{}}}}(Lbll{{}}(X0:S{{}}), Lblc{{}}(Y0:S{{}})))
                [constructor{{}}()]
              {axioms}
            endmodule []"#
        ))
        .unwrap()
    };
    let greater_axioms = r"
        axiom{} \implies{S{}}(
            \and{S{}}(Lblg{}(X0:S{}), Lblg{}(Y0:S{})),
            Lblg{}(\and{S{}}(X0:S{}, Y0:S{})))
          [constructor{}()]
        axiom{} \not{S{}}(\and{S{}}(Lblg{}(X0:S{}), Lbll{}(Y0:S{}))) [constructor{}()]
        axiom{} \not{S{}}(\and{S{}}(Lblc{}(X0:S{}), Lblg{}(Y0:S{}))) [constructor{}()]";
    let anywhere = "anywhere{}(), functional{}(), injective{}()";
    let port = definition(anywhere, "");
    let mut reference = definition(anywhere, greater_axioms);
    assert_eq!(
        normalize_withheld_overload_no_confusion(&mut reference, &port),
        3
    );
    assert_eq!(
        reference, port,
        "the no-junk axiom and the pairs without the greater stay"
    );
    // A port that states one axiom of the family for the greater leaves the reference untouched.
    let port = definition(
        anywhere,
        r"axiom{} \not{S{}}(\and{S{}}(Lblg{}(X0:S{}), Lbll{}(Y0:S{}))) [constructor{}()]",
    );
    let mut reference = definition(anywhere, greater_axioms);
    let original = reference.clone();
    assert_eq!(
        normalize_withheld_overload_no_confusion(&mut reference, &port),
        0
    );
    assert_eq!(reference, original);
    // A greater the port does not declare `anywhere` stays compared.
    let plain = "functional{}(), injective{}()";
    let port = definition(plain, "");
    let mut reference = definition(plain, greater_axioms);
    let original = reference.clone();
    assert_eq!(
        normalize_withheld_overload_no_confusion(&mut reference, &port),
        0
    );
    assert_eq!(reference, original);
}

/// Remove only sort-predicate equations whose injected argument has no declared embedding into
/// `KItem`, along with that equation's one negated applicability disjunct in its owise companion.
fn normalize_unsupported_sort_predicates(definition: &mut Definition) -> (usize, usize) {
    let supported = kitem_subsorts(definition);
    let mut removed = 0;
    let mut rewritten = 0;
    for module in &mut definition.modules {
        let dropped = module
            .sentences
            .iter()
            .filter_map(|sentence| unsupported_sort_predicate_axiom(sentence, &supported))
            .collect::<BTreeSet<_>>();
        removed += module.sentences.len();
        module
            .sentences
            .retain(|sentence| unsupported_sort_predicate_axiom(sentence, &supported).is_none());
        removed -= module.sentences.len();
        for sentence in &mut module.sentences {
            if let Some(key) = owise_unsupported_disjunct(sentence)
                && dropped.contains(&key)
                && let Sentence::Axiom { pattern, .. } = sentence
                && let Pattern::Implies { left, .. } = pattern.as_mut()
                && let Pattern::And { arguments, .. } = left.as_mut()
                && let Pattern::Not { argument, .. } = &mut arguments[0]
                && let Pattern::Or { arguments, .. } = argument.as_mut()
            {
                let bottom = arguments
                    .iter()
                    .find(|pattern| matches!(pattern, Pattern::Bottom { .. }))
                    .expect("matched owise disjunct contains bottom")
                    .clone();
                **argument = bottom;
                rewritten += 1;
            }
        }
    }
    (removed, rewritten)
}

/// The sorts `S` of every `subsort{S, SortKItem}` axiom: the sorts whose values are K items.
fn kitem_subsorts(definition: &Definition) -> BTreeSet<Sort> {
    definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            Sentence::Axiom { attributes, .. } => attributes.0.iter().find_map(|attribute| {
                let Pattern::Application { symbol, arguments } = attribute else {
                    return None;
                };
                (symbol.name == "subsort"
                    && arguments.is_empty()
                    && symbol.sort_parameters.len() == 2
                    && symbol.sort_parameters[1] == kore_sort("SortKItem"))
                .then(|| symbol.sort_parameters[0].clone())
            }),
            _ => None,
        })
        .collect()
}

fn kore_sort(name: &str) -> Sort {
    Sort::Application {
        name: name.into(),
        arguments: vec![],
    }
}

fn sort_predicate_equation<'a>(
    pattern: &'a Pattern,
    value: &str,
) -> Option<(&'a str, &'a Variable, &'a Pattern)> {
    let Pattern::Implies { sort, left, right } = pattern else {
        return None;
    };
    if *sort != Sort::Variable("R".into()) {
        return None;
    }
    let Pattern::Equals {
        operand_sort,
        result_sort,
        left: result_left,
        right: result_right,
    } = right.as_ref()
    else {
        return None;
    };
    if **operand_sort != kore_sort("SortBool") || *result_sort != Sort::Variable("R".into()) {
        return None;
    }
    let Pattern::Application { symbol, arguments } = result_left.as_ref() else {
        return None;
    };
    let [Pattern::Variable(variable)] = arguments.as_slice() else {
        return None;
    };
    let Pattern::And {
        sort: result_sort,
        arguments: result,
    } = result_right.as_ref()
    else {
        return None;
    };
    let [
        Pattern::DomainValue { sort, value: token },
        Pattern::Top { sort: top_sort },
    ] = result.as_slice()
    else {
        return None;
    };
    (variable.sort == kore_sort("SortK")
        && *sort == kore_sort("SortBool")
        && *result_sort == kore_sort("SortBool")
        && *top_sort == kore_sort("SortBool")
        && token == value
        && symbol.sort_parameters.is_empty()
        && symbol.name.starts_with("Lblis"))
    .then_some((&symbol.name, variable, left.as_ref()))
}

fn single_predicate_match<'a>(pattern: &'a Pattern, argument: &Variable) -> Option<&'a Pattern> {
    match pattern {
        Pattern::Top { sort } if *sort == Sort::Variable("R".into()) => None,
        Pattern::And { sort, arguments } if *sort == Sort::Variable("R".into()) => {
            let mut found = None;
            for child in arguments {
                if matches!(child, Pattern::Top { sort } if *sort == Sort::Variable("R".into())) {
                    continue;
                }
                let next = single_predicate_match(child, argument)?;
                if found.replace(next).is_some() {
                    return None;
                }
            }
            found
        }
        Pattern::In {
            operand_sort,
            result_sort,
            left,
            right,
        } if **operand_sort == kore_sort("SortK")
            && *result_sort == Sort::Variable("R".into())
            && matches!(left.as_ref(), Pattern::Variable(variable) if variable == argument) =>
        {
            Some(right.as_ref())
        }
        _ => None,
    }
}

fn injected_predicate_argument(pattern: &Pattern) -> Option<(Sort, Sort, &Variable)> {
    let (injection, target_sort) = match pattern {
        Pattern::Application { symbol, arguments }
            if symbol.name == "kseq"
                && symbol.sort_parameters.is_empty()
                && matches!(arguments.as_slice(), [_, Pattern::Application { symbol: dotk, arguments: empty }] if dotk.name == "dotk" && empty.is_empty()) =>
        {
            (&arguments[0], kore_sort("SortKItem"))
        }
        other => (other, kore_sort("SortK")),
    };
    let Pattern::Application { symbol, arguments } = injection else {
        return None;
    };
    let [source, target] = symbol.sort_parameters.as_slice() else {
        return None;
    };
    let [Pattern::Variable(variable)] = arguments.as_slice() else {
        return None;
    };
    (symbol.name == "inj"
        && *target == target_sort
        && *source != kore_sort("SortK")
        && variable.sort == *source)
        .then(|| (source.clone(), target.clone(), variable))
}

fn unsupported_sort_predicate_axiom(
    sentence: &Sentence,
    supported: &BTreeSet<Sort>,
) -> Option<(String, Sort, Sort)> {
    let Sentence::Axiom {
        pattern,
        attributes,
        ..
    } = sentence
    else {
        return None;
    };
    if attributes.0.iter().any(|attribute| {
        matches!(attribute, Pattern::Application { symbol, .. } if symbol.name == "owise")
    }) {
        return None;
    }
    let (predicate, argument, condition) = sort_predicate_equation(pattern, "true")?;
    let (source, target, _) =
        injected_predicate_argument(single_predicate_match(condition, argument)?)?;
    let sort_name = match &source {
        Sort::Application { name, arguments } if arguments.is_empty() => {
            name.strip_prefix("Sort")?
        }
        _ => return None,
    };
    (predicate == format!("Lblis{sort_name}") && !supported.contains(&source))
        .then(|| (predicate.to_owned(), source, target))
}

fn owise_unsupported_disjunct(sentence: &Sentence) -> Option<(String, Sort, Sort)> {
    let Sentence::Axiom {
        pattern,
        attributes,
        ..
    } = sentence
    else {
        return None;
    };
    if !attributes.0.iter().any(|attribute| {
        matches!(attribute, Pattern::Application { symbol, .. } if symbol.name == "owise")
    }) {
        return None;
    }
    let (predicate, argument, condition) = sort_predicate_equation(pattern, "false")?;
    let Pattern::And { arguments, .. } = condition else {
        return None;
    };
    let [
        Pattern::Not {
            argument: negated, ..
        },
        rest,
    ] = arguments.as_slice()
    else {
        return None;
    };
    single_predicate_match(rest, argument)?;
    let Pattern::Or { arguments, .. } = negated.as_ref() else {
        return None;
    };
    let [first, second] = arguments.as_slice() else {
        return None;
    };
    let exists = match (first, second) {
        (Pattern::Exists { .. }, Pattern::Bottom { .. }) => first,
        (Pattern::Bottom { .. }, Pattern::Exists { .. }) => second,
        _ => return None,
    };
    let Pattern::Exists { variable, body, .. } = exists else {
        return None;
    };
    let (source, target, injected) =
        injected_predicate_argument(single_predicate_match(body, argument)?)?;
    (**variable == *injected).then(|| (predicate.to_owned(), source, target))
}

#[test]
fn sort_predicate_normalizer_requires_a_missing_subsort_axiom() {
    let definition = |with_subsort| {
        let subsort = if with_subsort {
            r"axiom{R} \exists{R}(Val:SortKItem{}, \equals{SortKItem{}, R}(Val:SortKItem{}, inj{SortFoo{}, SortKItem{}}(From:SortFoo{}))) [subsort{SortFoo{}, SortKItem{}}()]"
        } else {
            ""
        };
        parse_definition(&[
            r"[] module TEST
              sort SortFoo{} []
              sort SortKItem{} []
              sort SortK{} []
              sort SortBool{} []
              symbol LblisFoo{}(SortK{}) : SortBool{} []",
            subsort,
            r#"axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(
                    \in{SortK{}, R}(X0:SortK{}, kseq{}(inj{SortFoo{}, SortKItem{}}(VarFoo:SortFoo{}), dotk{}())),
                    \top{R}())),
                \equals{SortBool{}, R}(LblisFoo{}(X0:SortK{}), \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}()))) []
              axiom{R} \implies{R}(
                \and{R}(\not{R}(\or{R}(
                    \exists{R}(Gen:SortFoo{}, \and{R}(\top{R}(), \and{R}(
                        \in{SortK{}, R}(X0:SortK{}, kseq{}(inj{SortFoo{}, SortKItem{}}(Gen:SortFoo{}), dotk{}())),
                        \top{R}()))),
                    \bottom{R}())),
                    \and{R}(\top{R}(), \and{R}(\in{SortK{}, R}(X0:SortK{}, VarK:SortK{}), \top{R}()))),
                \equals{SortBool{}, R}(LblisFoo{}(X0:SortK{}), \and{SortBool{}}(\dv{SortBool{}}("false"), \top{SortBool{}}()))) [owise{}()]
            endmodule []"#,
        ]
        .join("\n"))
        .unwrap()
    };

    let mut supported = definition(true);
    let original = supported.clone();
    assert_eq!(
        normalize_unsupported_sort_predicates(&mut supported),
        (0, 0)
    );
    assert_eq!(
        supported, original,
        "a declared embedding must keep both equations"
    );

    let mut unsupported = definition(false);
    assert_eq!(
        normalize_unsupported_sort_predicates(&mut unsupported),
        (1, 1)
    );
    let axioms = unsupported.modules[0]
        .sentences
        .iter()
        .filter(|sentence| matches!(sentence, Sentence::Axiom { .. }))
        .collect::<Vec<_>>();
    assert_eq!(axioms.len(), 1);
    let Sentence::Axiom { pattern, .. } = axioms[0] else {
        unreachable!()
    };
    let (predicate, _, condition) = sort_predicate_equation(pattern, "false").unwrap();
    assert_eq!(predicate, "LblisFoo");
    assert!(matches!(condition, Pattern::And { arguments, .. }
        if matches!(arguments.first(), Some(Pattern::Not { argument, .. })
            if matches!(argument.as_ref(), Pattern::Bottom { .. }))));

    let at_k = parse_pattern("inj{SortFoo{}, SortK{}}(VarFoo:SortFoo{})").unwrap();
    assert_eq!(
        injected_predicate_argument(&at_k).map(|(sort, _, _)| sort),
        Some(kore_sort("SortFoo"))
    );
}

/// N35: on the reference side, drop the sort predicate `isS` of a sort `S` without K terms, only
/// when the port declares no symbol of that name and the reference defines it as constantly false
/// and mentions it nowhere else. Returns the number of predicates dropped.
///
/// `isS(T)` tests whether the K term `T` is a term of `S`. Without a `subsort{S, SortKItem}`
/// axiom no K item is a value of `S`, so the predicate is false on every argument: N32 has already
/// removed its ill-sorted true equation and the matching owise disjunct, which leaves the
/// unconditional owise equation `isS(X:SortK) = false`. A total function symbol that only its
/// declaration, its functional axiom and that equation mention constrains nothing else in the
/// theory, so removing all three changes the meaning of no pattern that does not mention it. The
/// port generates sort predicates only for sorts of K terms
/// (docs/compatibility.md#sorts-of-compiled-terms). A port that declares the symbol, a reference
/// that embeds `S` in `KItem`, a remaining true equation, any other owise condition, and any other
/// mention of the symbol leave the reference untouched, so a predicate the port declares, or one
/// the reference uses, stays compared.
fn normalize_withheld_sort_predicates(reference: &mut Definition, actual: &Definition) -> usize {
    let port_symbols = actual
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            Sentence::SymbolDeclaration { symbol, .. } => Some(symbol.name.as_str()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let sentences = || {
        reference
            .modules
            .iter()
            .flat_map(|module| &module.sentences)
    };
    let declared_sorts = sentences()
        .filter_map(|sentence| match sentence {
            Sentence::SortDeclaration {
                name, parameters, ..
            } if parameters.is_empty() => Some(kore_sort(name)),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let embedded = kitem_subsorts(reference);
    let mut withheld = sentences()
        .filter_map(sort_predicate_declaration)
        .filter(|(name, sort)| {
            !port_symbols.contains(name)
                && declared_sorts.contains(sort)
                && !embedded.contains(sort)
        })
        .map(|(name, _)| name.to_owned())
        .collect::<BTreeSet<_>>();
    for sentence in sentences() {
        withheld.retain(|name| {
            !sentence_mentions_symbol(sentence, name)
                || constant_false_predicate_sentence(sentence, name)
        });
    }
    for module in &mut reference.modules {
        module.sentences.retain(|sentence| {
            !withheld
                .iter()
                .any(|name| sentence_mentions_symbol(sentence, name))
        });
    }
    withheld.len()
}

/// N35: the name of a sort-predicate declaration `LblisS{}(SortK{}) : SortBool{}` and the sort
/// `SortS{}` its name tests.
fn sort_predicate_declaration(sentence: &Sentence) -> Option<(&str, Sort)> {
    let Sentence::SymbolDeclaration {
        symbol,
        argument_sorts,
        result_sort,
        ..
    } = sentence
    else {
        return None;
    };
    let sort_name = symbol.name.strip_prefix("Lblis")?;
    (symbol.sort_parameters.is_empty()
        && argument_sorts.as_slice() == [kore_sort("SortK")]
        && *result_sort == kore_sort("SortBool"))
    .then(|| (symbol.name.as_str(), kore_sort(&format!("Sort{sort_name}"))))
}

/// N35: whether the sentence declares, applies, or names in an attribute the symbol `name`.
fn sentence_mentions_symbol(sentence: &Sentence, name: &str) -> bool {
    let symbols = BTreeSet::from([name.to_owned()]);
    let mentions = |pattern: &Pattern| pattern_mentions_any_symbol(pattern, &symbols);
    let (patterns, attributes): (Vec<&Pattern>, &Attributes) = match sentence {
        Sentence::Import { attributes, .. } | Sentence::SortDeclaration { attributes, .. } => {
            (Vec::new(), attributes)
        }
        Sentence::SymbolDeclaration {
            symbol, attributes, ..
        } => {
            if symbol.name == name {
                return true;
            }
            (Vec::new(), attributes)
        }
        Sentence::AliasDeclaration {
            alias,
            left,
            right,
            attributes,
            ..
        } => {
            if alias.name == name {
                return true;
            }
            (vec![left.as_ref(), right.as_ref()], attributes)
        }
        Sentence::Axiom {
            pattern,
            attributes,
            ..
        }
        | Sentence::Claim {
            pattern,
            attributes,
            ..
        } => (vec![pattern.as_ref()], attributes),
    };
    patterns.into_iter().any(mentions) || attributes.0.iter().any(mentions)
}

/// N35: whether the sentence is one of the three sentences of a constantly false sort predicate
/// `name`: its declaration, its functional axiom `\exists V. V = name(K0:SortK)`, or its owise
/// equation `name(X:SortK) = false` whose only condition is the unconstrained match of `X` (the
/// negated applicability disjunction is `\bottom`, as N32 leaves it once no true equation remains).
fn constant_false_predicate_sentence(sentence: &Sentence, name: &str) -> bool {
    let has = |attributes: &Attributes, attribute: &str| {
        attributes.0.iter().any(|candidate| {
            matches!(candidate, Pattern::Application { symbol, arguments }
                if symbol.name == attribute && arguments.is_empty())
        })
    };
    let (pattern, attributes) = match sentence {
        Sentence::SymbolDeclaration { .. } => {
            return sort_predicate_declaration(sentence).is_some_and(|(symbol, _)| symbol == name);
        }
        Sentence::Axiom {
            pattern,
            attributes,
            ..
        } => (pattern.as_ref(), attributes),
        _ => return false,
    };
    if has(attributes, "functional") {
        let Pattern::Exists { variable, body, .. } = pattern else {
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
        let Pattern::Application { symbol, arguments } = right.as_ref() else {
            return false;
        };
        return **operand_sort == kore_sort("SortBool")
            && variable.sort == kore_sort("SortBool")
            && matches!(left.as_ref(), Pattern::Variable(value) if value == variable.as_ref())
            && symbol.name == name
            && symbol.sort_parameters.is_empty()
            && matches!(arguments.as_slice(), [Pattern::Variable(argument)]
                if argument.sort == kore_sort("SortK"));
    }
    if !has(attributes, "owise") {
        return false;
    }
    let Some((predicate, argument, condition)) = sort_predicate_equation(pattern, "false") else {
        return false;
    };
    let Pattern::And { arguments, .. } = condition else {
        return false;
    };
    let [
        Pattern::Not {
            argument: negated, ..
        },
        rest,
    ] = arguments.as_slice()
    else {
        return false;
    };
    predicate == name
        && matches!(negated.as_ref(), Pattern::Bottom { .. })
        && matches!(single_predicate_match(rest, argument), Some(Pattern::Variable(any))
            if any.sort == kore_sort("SortK"))
}

#[test]
fn withheld_sort_predicate_normalizer_drops_only_unused_constantly_false_predicates() {
    // `#Layout` has no `subsort{Sort'Hash'Layout{}, SortKItem{}}` axiom unless `extra` adds one;
    // `Foo` is a sort of K items with an ordinary predicate.
    let definition = |layout_predicate: bool, extra: &str| {
        let layout = if layout_predicate {
            r#"symbol Lblis'Hash'Layout{}(SortK{}) : SortBool{} [function{}(), functional{}(), total{}()]
              axiom{R} \exists{R}(Val:SortBool{}, \equals{SortBool{}, R}(Val:SortBool{}, Lblis'Hash'Layout{}(K0:SortK{}))) [functional{}()]
              axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(
                    \in{SortK{}, R}(X0:SortK{}, kseq{}(inj{Sort'Hash'Layout{}, SortKItem{}}(VarL:Sort'Hash'Layout{}), dotk{}())),
                    \top{R}())),
                \equals{SortBool{}, R}(Lblis'Hash'Layout{}(X0:SortK{}), \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}()))) []
              axiom{R} \implies{R}(
                \and{R}(\not{R}(\or{R}(
                    \exists{R}(Gen:Sort'Hash'Layout{}, \and{R}(\top{R}(), \and{R}(
                        \in{SortK{}, R}(X0:SortK{}, kseq{}(inj{Sort'Hash'Layout{}, SortKItem{}}(Gen:Sort'Hash'Layout{}), dotk{}())),
                        \top{R}()))),
                    \bottom{R}())),
                    \and{R}(\top{R}(), \and{R}(\in{SortK{}, R}(X0:SortK{}, VarK:SortK{}), \top{R}()))),
                \equals{SortBool{}, R}(Lblis'Hash'Layout{}(X0:SortK{}), \and{SortBool{}}(\dv{SortBool{}}("false"), \top{SortBool{}}()))) [owise{}()]"#
        } else {
            ""
        };
        parse_definition(&format!(
            r"[] module TEST
              sort SortK{{}} []
              sort SortKItem{{}} []
              sort SortBool{{}} []
              sort Sort'Hash'Layout{{}} []
              sort SortFoo{{}} []
              symbol LblisFoo{{}}(SortK{{}}) : SortBool{{}} [function{{}}(), functional{{}}(), total{{}}()]
              axiom{{R}} \exists{{R}}(Val:SortBool{{}}, \equals{{SortBool{{}}, R}}(Val:SortBool{{}}, LblisFoo{{}}(K0:SortK{{}}))) [functional{{}}()]
              axiom{{R}} \exists{{R}}(Val:SortKItem{{}}, \equals{{SortKItem{{}}, R}}(Val:SortKItem{{}}, inj{{SortFoo{{}}, SortKItem{{}}}}(From:SortFoo{{}}))) [subsort{{SortFoo{{}}, SortKItem{{}}}}()]
              {layout}
              {extra}
            endmodule []"
        ))
        .unwrap()
    };
    // The comparison applies N32 first, which leaves the owise equation unconditional.
    let normalized = |reference: &mut Definition, port: &Definition| {
        normalize_unsupported_sort_predicates(reference);
        normalize_withheld_sort_predicates(reference, port)
    };

    let port = definition(false, "");
    let mut reference = definition(true, "");
    assert_eq!(normalized(&mut reference, &port), 1);
    assert_eq!(
        reference, port,
        "the declaration, the functional axiom and the owise equation go; isFoo stays"
    );

    // A syntax definition declares the predicate without axioms.
    let syntax = |layout_predicate: bool| {
        parse_definition(&format!(
            r"[] module TEST
              sort SortK{{}} []
              sort SortBool{{}} []
              sort Sort'Hash'Layout{{}} []
              {}
            endmodule []",
            if layout_predicate {
                r"symbol Lblis'Hash'Layout{}(SortK{}) : SortBool{} [function{}()]"
            } else {
                ""
            }
        ))
        .unwrap()
    };
    let mut reference = syntax(true);
    assert_eq!(
        normalize_withheld_sort_predicates(&mut reference, &syntax(false)),
        1
    );
    assert_eq!(reference, syntax(false));

    // Every control leaves the reference as N32 left it.
    let embedding = r"axiom{R} \exists{R}(Val:SortKItem{}, \equals{SortKItem{}, R}(Val:SortKItem{}, inj{Sort'Hash'Layout{}, SortKItem{}}(From:Sort'Hash'Layout{}))) [subsort{Sort'Hash'Layout{}, SortKItem{}}()]";
    let used = r#"axiom{R} \equals{SortBool{}, R}(Lblis'Hash'Layout{}(X:SortK{}), \dv{SortBool{}}("false")) []"#;
    for (port, extra, control) in [
        (definition(true, ""), "", "the port declares the predicate"),
        (
            definition(false, embedding),
            embedding,
            "the reference embeds #Layout in KItem",
        ),
        (
            definition(false, used),
            used,
            "another axiom uses the predicate",
        ),
    ] {
        let mut reference = definition(true, extra);
        normalize_unsupported_sort_predicates(&mut reference);
        let original = reference.clone();
        assert_eq!(
            normalize_withheld_sort_predicates(&mut reference, &port),
            0,
            "{control}"
        );
        assert_eq!(reference, original, "{control}");
    }
}

#[test]
#[ignore = "requires K_REFERENCE_KORE and K_RUST_KORE outputs"]
fn emitted_macro_kore_matches_the_reference_frontend() {
    let reference_path = env::var("K_REFERENCE_KORE").expect("K_REFERENCE_KORE is required");
    let actual_path = env::var("K_RUST_KORE").expect("K_RUST_KORE is required");
    let reference_source = fs::read_to_string(&reference_path).unwrap();
    let actual_source = fs::read_to_string(&actual_path).unwrap();
    let reference = parse_macro_sentences(&reference_source);
    let actual = parse_macro_sentences(&actual_source);
    compare_definitions(reference, actual);
}

#[test]
#[ignore = "requires K_REFERENCE_KAST and K_RUST_KAST outputs"]
fn parsed_kast_matches_the_reference_frontend() {
    let reference_path = env::var("K_REFERENCE_KAST").expect("K_REFERENCE_KAST is required");
    let actual_path = env::var("K_RUST_KAST").expect("K_RUST_KAST is required");
    let reference_source = fs::read_to_string(&reference_path).unwrap();
    let actual_source = fs::read_to_string(&actual_path).unwrap();
    let reference = kast_json::from_str(&reference_source).unwrap();
    let actual = if let Ok(case) = env::var("K_RUST_KAST_CASE") {
        let batch: serde_json::Value = serde_json::from_str(&actual_source).unwrap();
        let encoded = serde_json::to_string(
            batch
                .get(&case)
                .unwrap_or_else(|| panic!("KAST batch output has no case {case:?}")),
        )
        .unwrap();
        kast_json::from_str(&encoded).unwrap()
    } else {
        kast_json::from_str(&actual_source).unwrap()
    };

    assert_eq!(reference, actual);
}

fn first_json_difference(
    path: &str,
    reference: &serde_json::Value,
    actual: &serde_json::Value,
) -> String {
    match (reference, actual) {
        (serde_json::Value::Object(reference), serde_json::Value::Object(actual)) => {
            let keys = reference
                .keys()
                .chain(actual.keys())
                .collect::<BTreeSet<_>>();
            for key in keys {
                match (reference.get(key), actual.get(key)) {
                    (Some(reference), Some(actual)) if reference != actual => {
                        return first_json_difference(&format!("{path}.{key}"), reference, actual);
                    }
                    (Some(_), None) => return format!("{path}.{key}: missing from actual"),
                    (None, Some(_)) => return format!("{path}.{key}: extra in actual"),
                    _ => {}
                }
            }
        }
        (serde_json::Value::Array(reference), serde_json::Value::Array(actual)) => {
            if reference.len() != actual.len() {
                return format!(
                    "{path}: array lengths differ: reference={} (first: {}), actual={} (first: {})",
                    reference.len(),
                    reference
                        .first()
                        .map(json_summary)
                        .unwrap_or_else(|| "<empty>".into()),
                    actual.len(),
                    actual
                        .first()
                        .map(json_summary)
                        .unwrap_or_else(|| "<empty>".into()),
                );
            }
            for (index, (reference, actual)) in reference.iter().zip(actual).enumerate() {
                if reference != actual {
                    return first_json_difference(&format!("{path}[{index}]"), reference, actual);
                }
            }
        }
        _ => {
            return format!("{path}: reference={reference:?}, actual={actual:?}");
        }
    }
    format!("{path}: values differ")
}

#[test]
#[ignore = "requires K_REFERENCE_DEFINITION and K_RUST_DEFINITION outputs"]
fn parsed_definition_matches_the_reference_frontend() {
    let reference_path =
        env::var("K_REFERENCE_DEFINITION").expect("K_REFERENCE_DEFINITION is required");
    let actual_path = env::var("K_RUST_DEFINITION").expect("K_RUST_DEFINITION is required");
    let reference_source = fs::read_to_string(reference_path).unwrap();
    let actual_source = fs::read_to_string(&actual_path).unwrap();
    // A context alias has no KAST v4 form, so both writers leave a bodiless `badsentence` in its
    // place. Normalization reorders and deduplicates sentences, so compare how many each module
    // lost rather than their positions.
    let omitted_per_module = |source: &str| {
        let (_, omitted) = definition_json::from_str_omitting_unrepresentable(source).unwrap();
        omitted
            .into_iter()
            .fold(BTreeMap::<String, usize>::new(), |mut counts, omitted| {
                *counts.entry(omitted.module).or_default() += 1;
                counts
            })
    };
    assert_eq!(
        omitted_per_module(&actual_source),
        omitted_per_module(&reference_source),
        "modules differ in how many sentences have no KAST v4 form"
    );
    let mut reference: serde_json::Value = serde_json::from_str(&reference_source).unwrap();
    let mut actual: serde_json::Value = serde_json::from_str(&actual_source).unwrap();
    normalize_definition_json(&mut reference);
    normalize_definition_json(&mut actual);
    let transport = normalize_configuration_transport_json(&reference, &mut actual)
        .expect("N37 requires a reference without configuration-value transport");
    println!("parsed configuration-value transport normalized (N37): {transport} rewrites");
    let compiled_path = Path::new(&actual_path).with_file_name("definition.kore");
    let compiled_source = fs::read_to_string(&compiled_path)
        .unwrap_or_else(|error| panic!("{}: {error}", compiled_path.display()));
    let compiled = parse_definition(&compiled_source).unwrap();
    let totality = normalize_configuration_deferred_totality_json(
        &mut reference,
        &actual,
        &compiled,
    )
    .expect(
        "N39 requires deferred parsed totality and total compiled configuration-generated symbols",
    );
    println!("parsed configuration-generated totality normalized (N39): {totality} rewrites");

    if reference != actual {
        if let Some(directory) = env::var_os("K_DIFFERENTIAL_NORMALIZED_DIRECTORY") {
            fs::create_dir_all(&directory).unwrap();
            fs::write(
                std::path::Path::new(&directory).join("reference.json"),
                serde_json::to_string_pretty(&reference).unwrap(),
            )
            .unwrap();
            fs::write(
                std::path::Path::new(&directory).join("actual.json"),
                serde_json::to_string_pretty(&actual).unwrap(),
            )
            .unwrap();
        }
        panic!(
            "normalized parsed definitions differ at {}",
            first_json_difference("$", &reference, &actual)
        );
    }
}

/// Parsed configuration expansion precedes the compilation judgements for generated totality.
/// Recognize projections through their cell map and nullary initializers through the cell
/// that generates them; retain every final compiled claim in the semantic comparison.
fn normalize_configuration_deferred_totality_json(
    reference: &mut serde_json::Value,
    actual: &serde_json::Value,
    compiled: &Definition,
) -> Result<usize, String> {
    let mut count = 0;
    let modules = reference["term"]["modules"]
        .as_array_mut()
        .ok_or("reference definition has no modules")?;
    for module in modules {
        let sentences = module["localSentences"]
            .as_array()
            .ok_or("reference module has no sentences")?;
        let mut projections = BTreeMap::new();
        let mut initializers = BTreeMap::new();
        for cell in sentences {
            let attributes = &cell["att"]["att"];
            let Some(cell_name) = attributes["cellName"].as_str() else {
                continue;
            };
            let cell_label = format!("<{cell_name}>");
            let Some(items) = cell["productionItems"].as_array() else {
                continue;
            };
            if cell["node"] != "KProduction"
                || attributes.get("cell").is_none()
                || cell["sort"]["params"] != serde_json::json!([])
                || cell["klabel"]["name"] != cell_label
                || items
                    .first()
                    .is_none_or(|item| item["node"] != "KTerminal" || item["value"] != cell_label)
                || items.last().is_none_or(|item| {
                    item["node"] != "KTerminal" || item["value"] != format!("</{cell_name}>")
                })
            {
                continue;
            }
            let cell_sort = cell["sort"]["name"]
                .as_str()
                .ok_or_else(|| format!("{cell_label}: reference cell sort has no name"))?;
            // The reference sort names the initializer; the cell name only checks consistency.
            let expected_cell_sort = cell_name
                .split('-')
                .map(|part| {
                    let mut characters = part.chars();
                    characters.next().map_or_else(String::new, |first| {
                        first.to_uppercase().chain(characters).collect()
                    })
                })
                .collect::<String>()
                + "Cell";
            if cell_sort != expected_cell_sort {
                return Err(format!(
                    "{cell_label}: reference cell sort {cell_sort} disagrees with cellName {cell_name} (expected {expected_cell_sort})"
                ));
            }
            let mut result_sort = cell["sort"].clone();
            match attributes["multiplicity"].as_str() {
                None | Some("1" | "?") => {}
                Some("*") => {
                    let collection_type = attributes["type"].as_str().unwrap_or("Bag");
                    let hook = match collection_type {
                        "Bag" => "BAG.concat",
                        "Map" => "MAP.concat",
                        "Set" => "SET.concat",
                        "List" => "LIST.concat",
                        _ => continue,
                    };
                    result_sort["name"] = format!("{cell_sort}{collection_type}").into();
                    if !sentences.iter().any(|collection| {
                        collection["node"] == "KProduction"
                            && collection["sort"] == result_sort
                            && collection["att"]["att"].get("cellCollection").is_some()
                            && collection["att"]["att"]["wrapElement"] == cell_label
                            && collection["att"]["att"]["hook"] == hook
                    }) {
                        continue;
                    }
                }
                _ => continue,
            }
            initializers.insert(format!("init{cell_sort}"), result_sort);
        }
        for collection in sentences {
            let attributes = &collection["att"]["att"];
            if collection["node"] != "KProduction"
                || attributes.get("cellCollection").is_none()
                || attributes["hook"] != "MAP.concat"
                || collection["sort"]["params"] != serde_json::json!([])
            {
                continue;
            }
            let Some(map_sort) = collection["sort"]["name"].as_str() else {
                continue;
            };
            let Some(cell_label) = attributes["wrapElement"].as_str() else {
                continue;
            };
            let cells = sentences
                .iter()
                .filter(|sentence| {
                    sentence["node"] == "KProduction"
                        && sentence["klabel"]["name"] == cell_label
                        && sentence["att"]["att"].get("cell").is_some()
                })
                .collect::<Vec<_>>();
            let [cell] = cells.as_slice() else {
                continue;
            };
            let Some(key) = cell["productionItems"]
                .as_array()
                .and_then(|items| items.iter().find(|item| item["node"] == "KNonTerminal"))
            else {
                continue;
            };
            projections.insert(
                format!("{map_sort}Key"),
                (cell["sort"].clone(), key["sort"].clone()),
            );
        }
        let actual_module = actual["term"]["modules"].as_array().and_then(|modules| {
            modules
                .iter()
                .find(|candidate| candidate["name"] == module["name"])
        });
        let module_name = module["name"].clone();
        let sentences = module["localSentences"].as_array_mut().unwrap();
        for production in sentences.iter_mut() {
            let Some(label) = production["klabel"]["name"].as_str() else {
                continue;
            };
            let (argument_sorts, result_sort, expected_items) =
                if let Some((cell_sort, key_sort)) = projections.get(label) {
                    (
                        vec![cell_sort.clone()],
                        key_sort.clone(),
                        serde_json::json!([
                            {"node": "KTerminal", "value": label},
                            {"node": "KTerminal", "value": "("},
                            {"node": "KNonTerminal", "sort": cell_sort},
                            {"node": "KTerminal", "value": ")"}
                        ]),
                    )
                } else if let Some(cell_sort) = initializers.get(label)
                    && production["att"]["att"].get("initializer").is_some()
                {
                    (
                        vec![],
                        cell_sort.clone(),
                        serde_json::json!([{"node": "KTerminal", "value": label}]),
                    )
                } else {
                    continue;
                };
            if production["node"] != "KProduction"
                || production["params"] != serde_json::json!([])
                || production["klabel"]["params"] != serde_json::json!([])
                || production["productionItems"] != expected_items
                || production["sort"] != result_sort
                || production["att"]["att"].get("function").is_none()
                || production["att"]["att"]["total"] != ""
                || argument_sorts
                    .iter()
                    .chain(std::iter::once(&result_sort))
                    .any(|sort| sort["params"] != serde_json::json!([]))
            {
                continue;
            }
            let counterpart = actual_module
                .and_then(|module| module["localSentences"].as_array())
                .and_then(|sentences| {
                    sentences.iter().find(|sentence| {
                        sentence["node"] == "KProduction"
                            && sentence["klabel"] == production["klabel"]
                    })
                })
                .ok_or_else(|| {
                    format!("{module_name}: missing parsed generated production {label}")
                })?;
            if counterpart["att"]["att"].get("total").is_some() {
                return Err(if initializers.contains_key(label) {
                    format!(
                        "{label}: parsed initializer already carries total; it may be source-written, or N39 is obsolete for initializers"
                    )
                } else {
                    format!(
                        "{label}: parsed generated production already carries total; remove N39"
                    )
                });
            }
            let mut deferred = production.clone();
            deferred["att"]["att"]
                .as_object_mut()
                .unwrap()
                .remove("total");
            if deferred != *counterpart {
                return Err(format!(
                    "{label}: parsed generated productions differ beyond deferred totality"
                ));
            }
            let symbol = k_rust::kompile::encode_kore_label(&k_rust::kast::Label::new(label));
            let encode_sort = |sort: &serde_json::Value| {
                sort["name"]
                    .as_str()
                    .map(|name| k_rust::kompile::encode_kore_sort(&k_rust::kast::Sort::new(name)))
                    .ok_or_else(|| format!("{label}: generated signature sort has no name"))
            };
            let arguments = argument_sorts
                .iter()
                .map(encode_sort)
                .collect::<Result<Vec<_>, _>>()?;
            let result = encode_sort(&result_sort)?;
            let declarations = compiled
                .modules
                .iter()
                .flat_map(|module| &module.sentences)
                .filter_map(|sentence| match sentence {
                    Sentence::SymbolDeclaration {
                        symbol: declared,
                        argument_sorts,
                        result_sort,
                        attributes,
                        ..
                    } if *declared == symbol => Some((argument_sorts, result_sort, attributes)),
                    _ => None,
                })
                .collect::<Vec<_>>();
            let [(declared_arguments, declared_result, attributes)] = declarations.as_slice()
            else {
                return Err(format!(
                    "{label}: expected one compiled generated symbol declaration"
                ));
            };
            if **declared_arguments != arguments
                || **declared_result != result
                || !has_kore_attribute(attributes, "total")
            {
                return Err(format!(
                    "{label}: compiled generated symbol must declare total{{}}() with its generated signature"
                ));
            }
            *production = deferred;
            count += 1;
        }
        // Removing an attribute changes the sentence's key in the existing set comparison.
        sentences.sort_by_key(json_sort_key);
        sentences.dedup();
    }
    Ok(count)
}

fn cell_map_key_totality_fixture() -> (serde_json::Value, serde_json::Value, Definition) {
    let sort = |name: &str| serde_json::json!({"node": "KSort", "name": name, "params": []});
    let projection = serde_json::json!({
        "node": "KProduction", "klabel": {"node": "KLabel", "name": "EntryCellMapKey", "params": []},
        "sort": sort("IdCell"), "params": [],
        "productionItems": [
            {"node": "KTerminal", "value": "EntryCellMapKey"},
            {"node": "KTerminal", "value": "("},
            {"node": "KNonTerminal", "sort": sort("EntryCell")},
            {"node": "KTerminal", "value": ")"}
        ],
        "att": {"node": "KAtt", "att": {"function": "", "total": ""}}
    });
    let mut unrelated = projection.clone();
    unrelated["klabel"]["name"] = "OtherCellMapKey".into();
    unrelated["productionItems"][0]["value"] = "OtherCellMapKey".into();
    let reference = serde_json::json!({"term": {"modules": [{
        "node": "KFlatModule", "name": "TEST", "imports": [], "att": {"node": "KAtt", "att": {}},
        "localSentences": [projection, {
            "node": "KProduction", "klabel": {"node": "KLabel", "name": "_EntryCellMap_", "params": []},
            "sort": sort("EntryCellMap"), "params": [], "productionItems": [],
            "att": {"node": "KAtt", "att": {"cellCollection": "", "hook": "MAP.concat", "wrapElement": "<entry>"}}
        }, {
            "node": "KProduction", "klabel": {"node": "KLabel", "name": "<entry>", "params": []},
            "sort": sort("EntryCell"), "params": [],
            "productionItems": [{"node": "KNonTerminal", "sort": sort("IdCell")}],
            "att": {"node": "KAtt", "att": {"cell": ""}}
        }, unrelated]
    }]}});
    let mut actual = reference.clone();
    actual["term"]["modules"][0]["localSentences"][0]["att"]["att"]
        .as_object_mut()
        .unwrap()
        .remove("total");
    let compiled = parse_definition("[] module TEST symbol LblEntryCellMapKey{}(SortEntryCell{}) : SortIdCell{} [function{}(), total{}()] endmodule []").unwrap();
    (reference, actual, compiled)
}

#[test]
fn cell_map_key_totality_json_normalizer_deduplicates_after_removing_total() {
    let (mut reference, mut actual, compiled) = cell_map_key_totality_fixture();
    let deferred = actual["term"]["modules"][0]["localSentences"][0].clone();
    reference["term"]["modules"][0]["localSentences"]
        .as_array_mut()
        .unwrap()
        .push(deferred);
    normalize_definition_json(&mut reference);
    normalize_definition_json(&mut actual);
    assert_eq!(
        normalize_configuration_deferred_totality_json(&mut reference, &actual, &compiled),
        Ok(1)
    );
    let projections = reference["term"]["modules"][0]["localSentences"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|sentence| sentence["klabel"]["name"] == "EntryCellMapKey")
        .count();
    assert_eq!(projections, 1, "normalized projection must have one copy");
    assert_eq!(reference, actual);
}

#[test]
fn cell_map_key_totality_json_normalizer_removes_only_the_deferred_claim() {
    let (mut reference, mut actual, compiled) = cell_map_key_totality_fixture();
    assert_eq!(
        normalize_configuration_deferred_totality_json(&mut reference, &actual, &compiled),
        Ok(1)
    );
    normalize_definition_json(&mut actual);
    normalize_definition_json(&mut reference);
    assert_eq!(reference, actual);
    assert!(
        reference["term"]["modules"][0]["localSentences"]
            .as_array()
            .unwrap()
            .iter()
            .any(|sentence| sentence["klabel"]["name"] == "OtherCellMapKey"
                && sentence["att"]["att"]["total"] == "")
    );
}

#[test]
fn cell_map_key_totality_json_normalizer_requires_collection_cell_and_signature() {
    for (path, replacement) in [
        (vec!["att", "att", "hook"], serde_json::json!("LIST.concat")),
        (
            vec!["att", "att", "wrapElement"],
            serde_json::json!("<other>"),
        ),
        (
            vec!["sort", "params"],
            serde_json::json!([{"node": "KSort", "name": "K", "params": []}]),
        ),
    ] {
        let (mut reference, actual, compiled) = cell_map_key_totality_fixture();
        let mut value = &mut reference["term"]["modules"][0]["localSentences"][1];
        for field in path {
            value = &mut value[field];
        }
        *value = replacement;
        let unchanged = reference.clone();
        assert_eq!(
            normalize_configuration_deferred_totality_json(&mut reference, &actual, &compiled),
            Ok(0)
        );
        normalize_definition_json(&mut reference);
        let mut unchanged = unchanged;
        normalize_definition_json(&mut unchanged);
        assert_eq!(reference, unchanged);
    }
    for (index, path, replacement) in [
        (0, "/sort/name", serde_json::json!("Wrong")),
        (2, "/sort/name", serde_json::json!("Wrong")),
        (0, "/att/att", serde_json::json!({"total": ""})),
        (0, "/productionItems/1/value", serde_json::json!("[")),
    ] {
        let (mut reference, actual, compiled) = cell_map_key_totality_fixture();
        *reference["term"]["modules"][0]["localSentences"][index]
            .pointer_mut(path)
            .unwrap() = replacement;
        assert_eq!(
            normalize_configuration_deferred_totality_json(&mut reference, &actual, &compiled),
            Ok(0)
        );
        assert!(
            reference["term"]["modules"][0]["localSentences"]
                .as_array()
                .unwrap()
                .iter()
                .any(|sentence| sentence["klabel"]["name"] == "EntryCellMapKey"
                    && sentence["att"]["att"]["total"] == "")
        );
    }
}

#[test]
fn cell_map_key_totality_json_normalizer_refuses_missing_final_totality() {
    for declaration in [
        "symbol LblEntryCellMapKey{}(SortEntryCell{}) : SortIdCell{} [function{}()]",
        "symbol LblOtherCellMapKey{}(SortEntryCell{}) : SortIdCell{} [total{}()]",
        "symbol LblEntryCellMapKey{}(SortOtherCell{}) : SortIdCell{} [total{}()]",
        "symbol LblEntryCellMapKey{}(SortEntryCell{}) : SortOtherCell{} [total{}()]",
        "symbol LblEntryCellMapKey{}(SortEntryCell{}) : SortIdCell{} [total{}(x{}())]",
    ] {
        let (mut reference, actual, _) = cell_map_key_totality_fixture();
        let compiled =
            parse_definition(&format!("[] module TEST {declaration} endmodule []")).unwrap();
        assert!(
            normalize_configuration_deferred_totality_json(&mut reference, &actual, &compiled)
                .is_err(),
            "{declaration}"
        );
    }
}

#[test]
fn cell_map_key_totality_json_normalizer_refuses_stale_or_changed_parsed_projection() {
    let (reference, actual, compiled) = cell_map_key_totality_fixture();
    for (attribute, value, message) in [
        ("total", "", "remove N39"),
        ("symbol", "changed", "differ beyond deferred totality"),
    ] {
        let mut reference = reference.clone();
        let mut actual = actual.clone();
        actual["term"]["modules"][0]["localSentences"][0]["att"]["att"][attribute] = value.into();
        let error =
            normalize_configuration_deferred_totality_json(&mut reference, &actual, &compiled)
                .unwrap_err();
        assert!(error.contains(message), "{error}");
    }
}

fn nullary_initializer_totality_fixture() -> (serde_json::Value, serde_json::Value, Definition) {
    let sort = |name: &str| serde_json::json!({"node": "KSort", "name": name, "params": []});
    // The expanded cell determines its initializer label and result sort.
    let initializer = serde_json::json!({
        "node": "KProduction", "klabel": {"node": "KLabel", "name": "initNCell", "params": []},
        "sort": sort("NCell"), "params": [],
        "productionItems": [{"node": "KTerminal", "value": "initNCell"}],
        "att": {"node": "KAtt", "att": {"initializer": "", "function": "", "total": ""}}
    });
    let mut unrelated = initializer.clone();
    unrelated["sort"] = sort("OtherCell");
    unrelated["klabel"]["name"] = "initOtherCell".into();
    unrelated["productionItems"][0]["value"] = "initOtherCell".into();
    unrelated["att"]["att"]
        .as_object_mut()
        .unwrap()
        .remove("initializer");
    let mut with_map = initializer.clone();
    with_map["sort"] = sort("MappedCell");
    with_map["klabel"]["name"] = "initMappedCell".into();
    with_map["productionItems"] = serde_json::json!([
        {"node": "KTerminal", "value": "initMappedCell"},
        {"node": "KTerminal", "value": "("},
        {"node": "KNonTerminal", "sort": sort("Map")},
        {"node": "KTerminal", "value": ")"}
    ]);
    let cell = |name: &str, cell_sort: &str| {
        serde_json::json!({
            "node": "KProduction", "klabel": {"node": "KLabel", "name": format!("<{name}>"), "params": []},
            "sort": sort(cell_sort), "params": [],
            "productionItems": [
                {"node": "KTerminal", "value": format!("<{name}>")},
                {"node": "KNonTerminal", "sort": sort("Int")},
                {"node": "KTerminal", "value": format!("</{name}>")}
            ],
            "att": {"node": "KAtt", "att": {"cell": "", "cellName": name, "multiplicity": "1"}}
        })
    };
    let reference = serde_json::json!({"term": {"modules": [{
        "node": "KFlatModule", "name": "TEST", "imports": [], "att": {"node": "KAtt", "att": {}},
        "localSentences": [
            initializer, unrelated, with_map,
            cell("n", "NCell"), cell("other", "OtherCell"), cell("mapped", "MappedCell")
        ]
    }]}});
    let mut actual = reference.clone();
    actual["term"]["modules"][0]["localSentences"][0]["att"]["att"]
        .as_object_mut()
        .unwrap()
        .remove("total");
    let compiled = parse_definition(
        "[] module TEST symbol LblinitNCell{}() : SortNCell{} [function{}(), total{}()] endmodule []",
    )
    .unwrap();
    (reference, actual, compiled)
}

#[test]
fn nullary_initializer_totality_json_normalizer_requires_the_generating_cell() {
    for (path, replacement) in [
        ("/att/att", serde_json::json!({"cellName": "n"})),
        ("/att/att", serde_json::json!({"cell": ""})),
        ("/att/att/cellName", serde_json::json!("other")),
        ("/klabel/name", serde_json::json!("<other>")),
        ("/productionItems/0/value", serde_json::json!("<other>")),
        ("/productionItems/2/value", serde_json::json!("</other>")),
        ("/att/att/multiplicity", serde_json::json!("*")),
    ] {
        let (mut reference, actual, compiled) = nullary_initializer_totality_fixture();
        *reference["term"]["modules"][0]["localSentences"][3]
            .pointer_mut(path)
            .unwrap() = replacement;
        normalize_definition_json(&mut reference);
        let unchanged = reference.clone();
        assert_eq!(
            normalize_configuration_deferred_totality_json(&mut reference, &actual, &compiled),
            Ok(0),
            "{path}"
        );
        assert_eq!(reference, unchanged);
    }
}

#[test]
fn nullary_initializer_totality_json_normalizer_refuses_inconsistent_cell_sort() {
    for (path, replacement, message) in [
        (
            "/sort/name",
            serde_json::json!("OtherCell"),
            "<n>: reference cell sort OtherCell disagrees with cellName n (expected NCell)",
        ),
        (
            "/att/att/cellName",
            serde_json::json!("other"),
            "<other>: reference cell sort NCell disagrees with cellName other (expected OtherCell)",
        ),
    ] {
        let (mut reference, actual, compiled) = nullary_initializer_totality_fixture();
        let cell = &mut reference["term"]["modules"][0]["localSentences"][3];
        *cell.pointer_mut(path).unwrap() = replacement;
        if path == "/att/att/cellName" {
            cell["klabel"]["name"] = "<other>".into();
            cell["productionItems"][0]["value"] = "<other>".into();
            cell["productionItems"][2]["value"] = "</other>".into();
        }
        normalize_definition_json(&mut reference);
        let unchanged = reference.clone();
        assert_eq!(
            normalize_configuration_deferred_totality_json(&mut reference, &actual, &compiled),
            Err(message.into()),
            "{path}"
        );
        assert_eq!(reference, unchanged);
    }
}

#[test]
fn nullary_initializer_totality_json_normalizer_recognizes_collection_result_sorts() {
    for (collection_type, hook) in [
        ("Bag", "BAG.concat"),
        ("Map", "MAP.concat"),
        ("Set", "SET.concat"),
        ("List", "LIST.concat"),
    ] {
        let (mut reference, _, _) = nullary_initializer_totality_fixture();
        let sentences = reference["term"]["modules"][0]["localSentences"]
            .as_array_mut()
            .unwrap();
        sentences[3]["att"]["att"]["multiplicity"] = "*".into();
        // Bag is the default collection type when the cell has no explicit type property.
        if collection_type != "Bag" {
            sentences[3]["att"]["att"]["type"] = collection_type.into();
        }
        let result_sort = format!("NCell{collection_type}");
        sentences[0]["sort"]["name"] = result_sort.clone().into();
        sentences.push(serde_json::json!({
            "node": "KProduction", "sort": sentences[0]["sort"],
            "att": {"node": "KAtt", "att": {
                "cellCollection": "", "hook": hook, "wrapElement": "<n>"
            }}
        }));
        let mut actual = reference.clone();
        actual["term"]["modules"][0]["localSentences"][0]["att"]["att"]
            .as_object_mut()
            .unwrap()
            .remove("total");
        normalize_definition_json(&mut reference);
        normalize_definition_json(&mut actual);
        let compiled = parse_definition(&format!(
            "[] module TEST symbol LblinitNCell{{}}() : Sort{result_sort}{{}} [function{{}}(), total{{}}()] endmodule []"
        ))
        .unwrap();
        let mut wrong_result_sort = reference.clone();
        let initializer = wrong_result_sort["term"]["modules"][0]["localSentences"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|sentence| sentence["klabel"]["name"] == "initNCell")
            .unwrap();
        initializer["sort"]["name"] = "NCell".into();
        normalize_definition_json(&mut wrong_result_sort);
        let unchanged = wrong_result_sort.clone();
        assert_eq!(
            normalize_configuration_deferred_totality_json(
                &mut wrong_result_sort,
                &actual,
                &compiled
            ),
            Ok(0),
            "{collection_type}: the element sort is not the initializer's collection result sort"
        );
        assert_eq!(wrong_result_sort, unchanged);
        assert_eq!(
            normalize_configuration_deferred_totality_json(&mut reference, &actual, &compiled),
            Ok(1),
            "{collection_type}"
        );
        assert_eq!(reference, actual);
    }
}

#[test]
fn nullary_initializer_totality_json_normalizer_preserves_source_written_production() {
    let (mut reference, _, compiled) = nullary_initializer_totality_fixture();
    let source = &mut reference["term"]["modules"][0]["localSentences"][0];
    source["klabel"]["name"] = "sourceInitializer".into();
    source["productionItems"][0]["value"] = "sourceInitializer".into();
    normalize_definition_json(&mut reference);
    let actual = reference.clone();
    assert_eq!(
        normalize_configuration_deferred_totality_json(&mut reference, &actual, &compiled),
        Ok(0),
        "a source-written initializer must pass through without refusal"
    );
    assert_eq!(reference, actual);
}

#[test]
fn nullary_initializer_totality_json_normalizer_requires_cell_marker_and_nullary_signature() {
    let (mut reference, mut actual, compiled) = nullary_initializer_totality_fixture();
    assert_eq!(
        normalize_configuration_deferred_totality_json(&mut reference, &actual, &compiled),
        Ok(1)
    );
    normalize_definition_json(&mut reference);
    normalize_definition_json(&mut actual);
    assert_eq!(reference, actual);
    for label in ["initOtherCell", "initMappedCell"] {
        assert!(
            reference["term"]["modules"][0]["localSentences"]
                .as_array()
                .unwrap()
                .iter()
                .any(|sentence| sentence["klabel"]["name"] == label
                    && sentence["att"]["att"]["total"] == "")
        );
    }
    for (path, replacement) in [
        ("/att/att", serde_json::json!({"function": "", "total": ""})),
        ("/productionItems/0/value", serde_json::json!("different")),
        (
            "/params",
            serde_json::json!([{"node": "KSort", "name": "S", "params": []}]),
        ),
        (
            "/sort/params",
            serde_json::json!([{"node": "KSort", "name": "S", "params": []}]),
        ),
        ("/sort/name", serde_json::json!("OtherCell")),
    ] {
        let (mut reference, actual, compiled) = nullary_initializer_totality_fixture();
        *reference["term"]["modules"][0]["localSentences"][0]
            .pointer_mut(path)
            .unwrap() = replacement;
        normalize_definition_json(&mut reference);
        let unchanged = reference.clone();
        assert_eq!(
            normalize_configuration_deferred_totality_json(&mut reference, &actual, &compiled),
            Ok(0),
            "{path}"
        );
        assert_eq!(reference, unchanged);
    }
}

#[test]
fn nullary_initializer_totality_json_normalizer_refuses_missing_or_changed_final_claim() {
    for declaration in [
        "symbol LblinitNCell{}() : SortNCell{} [function{}()]",
        "symbol Lblother{}() : SortNCell{} [total{}()]",
        "symbol LblinitNCell{}(SortMap{}) : SortNCell{} [total{}()]",
        "symbol LblinitNCell{}() : SortOtherCell{} [total{}()]",
        "symbol LblinitNCell{}() : SortNCell{} [total{}(x{}())]",
        "symbol LblinitNCell{}() : SortNCell{} [total{}()] symbol LblinitNCell{}() : SortNCell{} [total{}()]",
    ] {
        let (mut reference, actual, _) = nullary_initializer_totality_fixture();
        let compiled =
            parse_definition(&format!("[] module TEST {declaration} endmodule []")).unwrap();
        assert!(
            normalize_configuration_deferred_totality_json(&mut reference, &actual, &compiled)
                .is_err(),
            "{declaration}"
        );
    }
}

#[test]
fn nullary_initializer_totality_json_normalizer_refuses_stale_or_changed_parsed_claim() {
    for (attribute, value, message) in [
        (
            "total",
            "",
            "may be source-written, or N39 is obsolete for initializers",
        ),
        ("symbol", "changed", "differ beyond deferred totality"),
    ] {
        let (mut reference, mut actual, compiled) = nullary_initializer_totality_fixture();
        actual["term"]["modules"][0]["localSentences"][0]["att"]["att"][attribute] = value.into();
        let error =
            normalize_configuration_deferred_totality_json(&mut reference, &actual, &compiled)
                .unwrap_err();
        assert!(error.contains(message), "{error}");
    }
}

#[test]
fn configuration_deferred_totality_json_normalizer_counts_each_generated_symbol() {
    let (mut reference, mut actual, mut compiled) = cell_map_key_totality_fixture();
    let (initializers, actual_initializers, compiled_initializers) =
        nullary_initializer_totality_fixture();
    reference["term"]["modules"][0]["localSentences"]
        .as_array_mut()
        .unwrap()
        .extend(
            initializers["term"]["modules"][0]["localSentences"]
                .as_array()
                .unwrap()
                .iter()
                .cloned(),
        );
    actual["term"]["modules"][0]["localSentences"]
        .as_array_mut()
        .unwrap()
        .extend(
            actual_initializers["term"]["modules"][0]["localSentences"]
                .as_array()
                .unwrap()
                .iter()
                .cloned(),
        );
    compiled.modules[0]
        .sentences
        .extend(compiled_initializers.modules[0].sentences.clone());
    assert_eq!(
        normalize_configuration_deferred_totality_json(&mut reference, &actual, &compiled),
        Ok(2)
    );
    normalize_definition_json(&mut reference);
    normalize_definition_json(&mut actual);
    assert_eq!(reference, actual);
}

fn parsed_transport_module() -> serde_json::Value {
    let sort = |name: &str| serde_json::json!({"node": "KSort", "name": name, "params": []});
    let production = |label: &str, result: &str, argument: &str, function: bool| {
        let mut attributes = serde_json::json!({"symbol": label});
        if function {
            attributes["function"] = "".into();
        }
        serde_json::json!({
            "node": "KProduction", "klabel": {"node": "KLabel", "name": label, "params": []},
            "params": [], "sort": sort(result),
            "productionItems": [
                {"node": "KTerminal", "value": label}, {"node": "KTerminal", "value": "("},
                {"node": "KNonTerminal", "sort": sort(argument)},
                {"node": "KTerminal", "value": ")"}
            ], "att": {"node": "KAtt", "att": attributes}
        })
    };
    let payload = serde_json::json!({"node": "KVariable", "name": "KS", "sort": sort("K")});
    let truth = serde_json::json!({"node": "KToken", "sort": sort("Bool"), "token": "true"});
    let mut sentences = vec![
        production("#KConfigValue", "KItem", "K", false),
        production("#unboxKConfigValue", "K", "KItem", true),
        serde_json::json!({
            "node": "KRule", "body": parsed_rewrite(
                parsed_application("#unboxKConfigValue", serde_json::json!([]), vec![
                    parsed_application("#KConfigValue", serde_json::json!([]), vec![payload.clone()])
                ]), payload
            ), "requires": truth, "ensures": truth, "att": {"node": "KAtt", "att": {}}
        }),
    ];
    sentences.sort_by_key(json_sort_key);
    serde_json::json!({
        "node": "KFlatModule", "name": "K-RUST-CONFIGURATION-VALUES", "imports": [],
        "localSentences": sentences, "att": {"node": "KAtt", "att": {}}
    })
}

/// The parsed artifact carries the same private module and initializer reads before injection.
/// Require the exact protocol; any altered declaration or inverse equation stays compared.
fn normalize_configuration_transport_json(
    reference: &serde_json::Value,
    actual: &mut serde_json::Value,
) -> Result<usize, String> {
    fn mentions_transport(value: &serde_json::Value) -> bool {
        match value {
            serde_json::Value::String(name) => matches!(
                name.as_str(),
                "#KConfigValue" | "#unboxKConfigValue" | "K-RUST-CONFIGURATION-VALUES"
            ),
            serde_json::Value::Array(values) => values.iter().any(mentions_transport),
            serde_json::Value::Object(object) => object.values().any(mentions_transport),
            _ => false,
        }
    }
    if mentions_transport(reference) {
        return Err("reference names private configuration-value transport".into());
    }
    let Some(modules) = actual["term"]["modules"].as_array_mut() else {
        return Ok(0);
    };
    let expected = parsed_transport_module();
    let Some(index) = modules.iter().position(|module| *module == expected) else {
        return Ok(0);
    };
    modules.remove(index);
    let mut count = 4; // The module and its two declarations and inverse equation.
    for module in modules {
        if let Some(imports) = module["imports"].as_array_mut() {
            let before = imports.len();
            imports.retain(|import| {
                *import != serde_json::json!({"node": "KImport", "name": "K-RUST-CONFIGURATION-VALUES", "isPublic": true})
            });
            count += before - imports.len();
        }
        let sentences = module["localSentences"]
            .as_array_mut()
            .expect("normalized module has a sentence array");
        for sentence in sentences.iter_mut() {
            let lhs = &sentence["body"]["lhs"];
            if sentence["node"] == "KRule"
                && sentence["att"]["att"].get("initializer").is_some()
                && sentence["body"]["node"] == "KRewrite"
                && lhs["node"] == "KApply"
                && lhs["label"]["name"]
                    .as_str()
                    .is_some_and(|label| label.starts_with("init") && label.ends_with("Cell"))
                && lhs["args"].as_array().is_some_and(|args| {
                    args.len() == 1
                        && args[0]["node"] == "KVariable"
                        && args[0]["sort"]
                            == serde_json::json!({"node": "KSort", "name": "Map", "params": []})
                })
            {
                normalize_parsed_configuration_read(&mut sentence["body"]["rhs"], &mut count);
            }
        }
        // Translating a body changes its key in the existing sentence-set comparison.
        sentences.sort_by_key(json_sort_key);
    }
    Ok(count)
}

fn normalize_parsed_configuration_read(value: &mut serde_json::Value, count: &mut usize) {
    let unary = |value: &serde_json::Value, label: &str| {
        value["node"] == "KApply"
            && value["label"]["name"] == label
            && value["label"]["params"] == serde_json::json!([])
            && value["arity"] == 1
            && value["args"].as_array().is_some_and(|args| args.len() == 1)
    };
    if value["node"] == "KApply"
        && value["label"]["name"]
            .as_str()
            .is_some_and(|label| label.starts_with("project:"))
        && value["label"]["params"] == serde_json::json!([])
        && value["arity"] == 1
        && value["args"].as_array().is_some_and(|args| args.len() == 1)
        && unary(&value["args"][0], "#unboxKConfigValue")
    {
        let lookup = &value["args"][0]["args"][0];
        if lookup["node"] == "KApply"
            && lookup["label"]["name"] == "Map:lookup"
            && lookup["label"]["params"] == serde_json::json!([])
            && lookup["arity"] == 2
            && lookup["args"].as_array().is_some_and(|args| {
                args.len() == 2
                    && args[0]["node"] == "KVariable"
                    && args[0]["sort"]
                        == serde_json::json!({"node": "KSort", "name": "Map", "params": []})
                    && args[1]["node"] == "KToken"
                    && args[1]["sort"]
                        == serde_json::json!({"node": "KSort", "name": "KConfigVar", "params": []})
            })
        {
            value["args"][0] = lookup.clone();
            *count += 1;
            if value["label"]["name"] == "project:K" {
                value["label"]["name"] = "project:KItem".into();
                *count += 1;
            }
            return;
        }
    }
    match value {
        serde_json::Value::Array(values) => {
            for value in values {
                normalize_parsed_configuration_read(value, count);
            }
        }
        serde_json::Value::Object(object) => {
            for value in object.values_mut() {
                normalize_parsed_configuration_read(value, count);
            }
        }
        _ => {}
    }
}

#[test]
fn configuration_transport_json_normalizer_preserves_everything_outside_the_protocol() {
    let sort = |name: &str| serde_json::json!({"node": "KSort", "name": name, "params": []});
    let lookup = parsed_application(
        "Map:lookup",
        serde_json::json!([]),
        vec![
            serde_json::json!({"node": "KVariable", "name": "Init", "sort": sort("Map")}),
            serde_json::json!({"node": "KToken", "token": "$PGM", "sort": sort("KConfigVar")}),
        ],
    );
    let read = |boxed: bool| {
        parsed_application(
            if boxed { "project:K" } else { "project:KItem" },
            serde_json::json!([]),
            vec![if boxed {
                parsed_application(
                    "#unboxKConfigValue",
                    serde_json::json!([]),
                    vec![lookup.clone()],
                )
            } else {
                lookup.clone()
            }],
        )
    };
    let definition = |boxed: bool| {
        let mut modules = vec![serde_json::json!({
            "node": "KFlatModule", "name": "TEST", "att": {"node": "KAtt", "att": {}},
            "imports": if boxed { vec![serde_json::json!({"node": "KImport", "name": "K-RUST-CONFIGURATION-VALUES", "isPublic": true})] } else { vec![] },
            "localSentences": [{
                "node": "KRule", "att": {"node": "KAtt", "att": {"initializer": ""}},
                "body": parsed_rewrite(parsed_application("initKCell", serde_json::json!([]), vec![
                    serde_json::json!({"node": "KVariable", "name": "Init", "sort": sort("Map")})
                ]), read(boxed)),
            }]
        })];
        if boxed {
            modules.push(parsed_transport_module());
        }
        serde_json::json!({"term": {"modules": modules}})
    };
    let reference = definition(false);
    let mut actual = definition(true);
    assert_eq!(
        normalize_configuration_transport_json(&reference, &mut actual),
        Ok(7)
    );
    assert_eq!(actual, reference);
    assert_eq!(
        normalize_configuration_transport_json(&reference, &mut actual),
        Ok(0)
    );

    let boxed_reference = definition(true);
    let mut unchanged = boxed_reference.clone();
    assert!(normalize_configuration_transport_json(&boxed_reference, &mut unchanged).is_err());
    assert_eq!(unchanged, boxed_reference);

    let mut changed_protocol = definition(true);
    changed_protocol["term"]["modules"][1]["localSentences"][0]["att"]["att"]["total"] = "".into();
    let before = changed_protocol.clone();
    assert_eq!(
        normalize_configuration_transport_json(&reference, &mut changed_protocol),
        Ok(0)
    );
    assert_eq!(changed_protocol, before);

    let mut source_rule = definition(true);
    source_rule["term"]["modules"][0]["localSentences"][0]["att"]["att"] = serde_json::json!({});
    normalize_configuration_transport_json(&reference, &mut source_rule).unwrap();
    assert_eq!(
        source_rule["term"]["modules"][0]["localSentences"][0]["body"]["rhs"],
        read(true)
    );

    for path in [
        "/label/params",
        "/args/0/label/params",
        "/args/0/args/0/label/params",
    ] {
        let mut parameterized = read(true);
        *parameterized.pointer_mut(path).unwrap() = serde_json::json!([sort("K")]);
        let before = parameterized.clone();
        let mut count = 0;
        normalize_parsed_configuration_read(&mut parameterized, &mut count);
        assert_eq!(count, 0, "{path}");
        assert_eq!(parameterized, before, "{path}");
    }

    let mut changed_lookup = read(true);
    changed_lookup["args"][0]["args"][0]["args"][1]["sort"] = sort("String");
    let before = changed_lookup.clone();
    let mut count = 0;
    normalize_parsed_configuration_read(&mut changed_lookup, &mut count);
    assert_eq!(count, 0);
    assert_eq!(changed_lookup, before);
}

fn json_summary(value: &serde_json::Value) -> String {
    let text = json_sort_key(value);
    let mut summary = text.chars().take(400).collect::<String>();
    if summary.len() < text.len() {
        summary.push('…');
    }
    summary
}

fn normalize_definition_json(value: &mut serde_json::Value) {
    let associative_units = associative_units(value);
    normalize_definition_value(value, &associative_units);
    let modules = value["term"]["modules"]
        .as_array_mut()
        .expect("definition modules must be an array");
    for module in modules.iter_mut() {
        module["imports"]
            .as_array_mut()
            .expect("module imports must be an array")
            .sort_by_key(json_sort_key);
        let sentences = module["localSentences"]
            .as_array_mut()
            .expect("local sentences must be an array");
        let cell_sorts = sentences
            .iter()
            .filter(|sentence| {
                sentence["node"] == "KProduction" && sentence["att"]["att"].get("cell").is_some()
            })
            .filter_map(|sentence| sentence["sort"]["name"].as_str().map(str::to_owned))
            .collect::<BTreeSet<_>>();
        let mut normalized = Vec::new();
        for sentence in std::mem::take(sentences) {
            // Rust can retain an empty generated sort declaration alongside the cell production
            // that already declares that sort; Java's sentence set deduplicates it.
            let redundant_cell_sort = sentence["node"] == "KSyntaxSort"
                && sentence["att"]["att"]
                    .as_object()
                    .is_some_and(serde_json::Map::is_empty)
                && sentence["sort"]["name"]
                    .as_str()
                    .is_some_and(|sort| cell_sorts.contains(sort));
            if redundant_cell_sort {
                continue;
            } else if sentence["node"] == "KSyntaxAssociativity" {
                let tags = sentence["tags"]
                    .as_array()
                    .expect("associativity tags must be an array");
                for tag in tags {
                    let mut singleton = sentence.clone();
                    singleton["tags"] = serde_json::Value::Array(vec![tag.clone()]);
                    normalized.push(singleton);
                }
            } else {
                normalized.push(sentence);
            }
        }
        normalized.sort_by_key(json_sort_key);
        normalized.dedup();
        *sentences = normalized;
    }
    modules.sort_by_key(|module| module["name"].as_str().unwrap_or_default().to_owned());
}

fn associative_units(value: &serde_json::Value) -> BTreeMap<String, String> {
    fn collect(value: &serde_json::Value, result: &mut BTreeMap<String, String>) {
        match value {
            serde_json::Value::Array(values) => {
                for value in values {
                    collect(value, result);
                }
            }
            serde_json::Value::Object(object) => {
                if object.get("node").and_then(serde_json::Value::as_str) == Some("KProduction")
                    && object["att"]["att"].get("assoc").is_some()
                    && let (Some(label), Some(unit)) = (
                        object["klabel"]["name"].as_str(),
                        object["att"]["att"]["unit"].as_str(),
                    )
                {
                    result.insert(label.into(), unit.into());
                }
                if object.get("node").and_then(serde_json::Value::as_str) == Some("KProduction")
                    && object["att"]["att"].get("userList").is_some()
                    && object["productionItems"]
                        .as_array()
                        .is_some_and(|items| items.len() > 1)
                    && let (Some(label), Some(sort)) = (
                        object["klabel"]["name"].as_str(),
                        object["sort"]["name"].as_str(),
                    )
                {
                    result.insert(label.into(), format!(r#".List{{"{label}"}}_{sort}"#));
                }
                for value in object.values() {
                    collect(value, result);
                }
            }
            _ => {}
        }
    }

    let mut result = BTreeMap::new();
    collect(value, &mut result);
    result
}

fn normalize_definition_value(
    value: &mut serde_json::Value,
    associative_units: &BTreeMap<String, String>,
) {
    match value {
        serde_json::Value::Array(values) => {
            for value in values {
                normalize_definition_value(value, associative_units);
            }
        }
        serde_json::Value::Object(object) => {
            // These fields are frontend provenance or generated parser bookkeeping rather than
            // the parsed definition's semantic structure.
            for key in [
                "digest",
                "org.kframework.attributes.Source",
                "org.kframework.attributes.SourceId",
                "org.krust.provenance.Origin",
                "org.krust.provenance.SentenceStartOffset",
                "org.krust.provenance.SentenceEndOffset",
                "org.kframework.attributes.Location",
                "org.kframework.definition.Production",
                "contentStartColumn",
                "contentStartLine",
                "contentStartOffset",
                "temporary-cell-sort-decl",
            ] {
                object.remove(key);
            }
            if let Some(serde_json::Value::Object(label)) = object.get("bracketLabel")
                && let Some(name) = label.get("name").and_then(serde_json::Value::as_str)
            {
                object.insert("bracketLabel".into(), name.into());
            }
            for value in object.values_mut() {
                normalize_definition_value(value, associative_units);
            }
            match object.get("node").and_then(serde_json::Value::as_str) {
                Some("KVariable") => {
                    let Some(name) = object["name"].as_str() else {
                        return;
                    };
                    if name.starts_with('_') {
                        // Java HashSet traversal and deterministic Rust traversal allocate suffixes
                        // in different orders for generated anonymous variables.
                        let stem =
                            name.trim_end_matches(|character: char| character.is_ascii_digit());
                        if stem.len() != name.len() {
                            object.insert("name".into(), stem.into());
                        }
                    }
                }
                Some("KLabel") => {
                    // Java's parsed JSON omits inferred concrete label parameters; declarations
                    // still retain their separate `params` field, and KAST has its own exact gate.
                    object.insert("params".into(), serde_json::Value::Array(Vec::new()));
                }
                Some("KRegexTerminal") => {
                    let source = object["regex"].as_str().expect("regex must be a string");
                    let parsed = regex::parse(source).unwrap_or_else(|error| {
                        panic!("failed to normalize regex {source:?}: {error}")
                    });
                    object.insert(
                        "regex".into(),
                        canonical_regex(&parsed.body, parsed.start_line, parsed.end_line).into(),
                    );
                }
                Some("KSyntaxAssociativity") => {
                    object["tags"]
                        .as_array_mut()
                        .expect("associativity tags must be an array")
                        .sort_by_key(json_sort_key);
                }
                Some("KSyntaxPriority") => {
                    for group in object["priorities"]
                        .as_array_mut()
                        .expect("priority groups must be an array")
                    {
                        group
                            .as_array_mut()
                            .expect("priority group must be an array")
                            .sort_by_key(json_sort_key);
                    }
                }
                Some("KApply") => {
                    canonicalize_local_function(object);
                    let Some(label) = object["label"]["name"].as_str() else {
                        return;
                    };
                    let Some(unit) = associative_units.get(label) else {
                        return;
                    };
                    let label = label.to_owned();
                    let arguments = object["args"]
                        .as_array_mut()
                        .expect("application arguments must be an array");
                    let mut flattened = Vec::new();
                    // User lists and associative productions can differ only in nesting and
                    // explicit unit insertion before both frontends lower them to identical KORE.
                    for argument in std::mem::take(arguments) {
                        let nested_label = argument["label"]["name"].as_str();
                        let nested_arguments = argument["args"].as_array();
                        if nested_label == Some(label.as_str()) {
                            flattened.extend(nested_arguments.unwrap().iter().cloned());
                        } else if nested_label == Some(unit.as_str())
                            && nested_arguments.is_some_and(Vec::is_empty)
                        {
                        } else {
                            flattened.push(argument);
                        }
                    }
                    if flattened.len() == 1
                        && let serde_json::Value::Object(singleton) = flattened.pop().unwrap()
                    {
                        *object = singleton;
                        return;
                    }
                    object.insert("arity".into(), flattened.len().into());
                    object.insert("args".into(), flattened.into());
                }
                _ => {}
            }
        }
        _ => {}
    }
}

/// Rewrites a parsed `#fun3(L, R, A)` into `#fun2(L => R, A)`.
///
/// Both labels are local-function applications that kompile lowers through one path
/// (`resolve_fun.rs`, `resolve_application`): `#fun3(L, R, A)` becomes the body `L => R`
/// applied to `A`, and `#fun2(B, A)` becomes the body `B` applied to `A`. The lambda it builds
/// depends only on that `(body, argument)` pair and never reads the label's sort parameters,
/// which `normalize_definition_value` already erases on every label. So the two parse trees
/// denote the same definition and differ only in which of two equivalent productions the
/// parser chose. A `#fun2` over a non-rewrite body, `#let`, any other label, and a `#fun3`
/// without exactly three arguments are left unchanged; a difference in `L`, `R` or `A` stays
/// visible after the rewrite.
fn canonicalize_local_function(object: &mut serde_json::Map<String, serde_json::Value>) {
    if object["label"]["name"].as_str() != Some("#fun3") {
        return;
    }
    let Some(serde_json::Value::Array(arguments)) = object.get_mut("args") else {
        return;
    };
    let [left, right, argument] = arguments.as_mut_slice() else {
        return;
    };
    let body = serde_json::json!({
        "node": "KRewrite",
        "lhs": std::mem::take(left),
        "rhs": std::mem::take(right),
    });
    let argument = std::mem::take(argument);
    object.insert("args".into(), serde_json::json!([body, argument]));
    object.insert("arity".into(), 2.into());
    object["label"]["name"] = "#fun2".into();
}

fn json_sort_key(value: &serde_json::Value) -> String {
    match value {
        serde_json::Value::Array(values) => format!(
            "[{}]",
            values
                .iter()
                .map(json_sort_key)
                .collect::<Vec<_>>()
                .join(",")
        ),
        serde_json::Value::Object(object) => {
            let mut fields = object
                .iter()
                .map(|(key, value)| {
                    format!(
                        "{}:{}",
                        serde_json::to_string(key).unwrap(),
                        json_sort_key(value)
                    )
                })
                .collect::<Vec<_>>();
            fields.sort();
            format!("{{{}}}", fields.join(","))
        }
        value => serde_json::to_string(value).unwrap(),
    }
}

fn canonical_regex(body: &RegexBody, start_line: bool, end_line: bool) -> String {
    format!(
        "{}{}{}",
        if start_line { "^" } else { "" },
        canonical_regex_body(body),
        if end_line { "$" } else { "" },
    )
}

fn canonical_regex_body(body: &RegexBody) -> String {
    match body {
        RegexBody::Char(character) => format!("char:{character:?}"),
        RegexBody::AnyChar => "any".into(),
        RegexBody::Named(name) => format!("named:{name}"),
        RegexBody::CharClass { negated, members } => {
            let mut members = members
                .iter()
                .map(|member| match member {
                    CharClass::Char(character) => format!("char:{character:?}"),
                    CharClass::Range { start, end } => format!("range:{start:?}:{end:?}"),
                })
                .collect::<Vec<_>>();
            members.sort();
            members.dedup();
            format!("class:{negated}:[{}]", members.join(","))
        }
        RegexBody::Union { .. } => {
            fn flatten(body: &RegexBody, members: &mut Vec<String>) {
                if let RegexBody::Union { left, right } = body {
                    flatten(left, members);
                    flatten(right, members);
                } else {
                    members.push(canonical_regex_body(body));
                }
            }
            let mut members = Vec::new();
            flatten(body, &mut members);
            members.sort();
            members.dedup();
            format!("union:[{}]", members.join(","))
        }
        RegexBody::Concat(members) => format!(
            "concat:[{}]",
            members
                .iter()
                .map(canonical_regex_body)
                .collect::<Vec<_>>()
                .join(",")
        ),
        RegexBody::ZeroOrMore(body) => format!("star:{}", canonical_regex_body(body)),
        RegexBody::ZeroOrOne(body) => format!("optional:{}", canonical_regex_body(body)),
        RegexBody::OneOrMore(body) => format!("plus:{}", canonical_regex_body(body)),
        RegexBody::Exactly { body, count } => {
            format!("exactly:{count}:{}", canonical_regex_body(body))
        }
        RegexBody::AtLeast { body, count } => {
            format!("at-least:{count}:{}", canonical_regex_body(body))
        }
        RegexBody::Range {
            body,
            at_least,
            at_most,
        } => format!("range:{at_least}:{at_most}:{}", canonical_regex_body(body)),
    }
}

#[test]
fn definition_normalizer_compares_regex_languages() {
    let left = regex::parse("[A-Za-z_]").unwrap();
    let right = regex::parse(r"[A-Za-z\_]").unwrap();

    assert_eq!(
        canonical_regex(&left.body, left.start_line, left.end_line),
        canonical_regex(&right.body, right.start_line, right.end_line),
    );
}

#[test]
fn definition_normalizer_flattens_user_lists_and_generated_variables() {
    let mut reference = serde_json::json!({
        "node": "KApply",
        "label": { "node": "KLabel", "name": "cons", "params": [{ "name": "Items" }] },
        "arity": 2,
        "args": [
            {
                "node": "KApply",
                "label": { "node": "KLabel", "name": "cast", "params": [] },
                "arity": 1,
                "args": [{ "node": "KVariable", "name": "_item1" }]
            },
            {
                "node": "KApply",
                "label": { "node": "KLabel", "name": ".Items", "params": [] },
                "arity": 0,
                "args": []
            }
        ]
    });
    let mut actual = serde_json::json!({
        "node": "KApply",
        "label": { "node": "KLabel", "name": "cast", "params": [{ "name": "Items" }] },
        "arity": 1,
        "args": [{ "node": "KVariable", "name": "_item7" }]
    });
    let units = BTreeMap::from([("cons".into(), ".Items".into())]);

    normalize_definition_value(&mut reference, &units);
    normalize_definition_value(&mut actual, &units);

    assert_eq!(reference, actual);
}

fn parsed_variable(name: &str) -> serde_json::Value {
    serde_json::json!({ "node": "KVariable", "name": name })
}

fn parsed_application(
    label: &str,
    params: serde_json::Value,
    args: Vec<serde_json::Value>,
) -> serde_json::Value {
    serde_json::json!({
        "node": "KApply",
        "label": { "node": "KLabel", "name": label, "params": params },
        "arity": args.len(),
        "args": args,
    })
}

fn parsed_rewrite(lhs: serde_json::Value, rhs: serde_json::Value) -> serde_json::Value {
    serde_json::json!({ "node": "KRewrite", "lhs": lhs, "rhs": rhs })
}

fn normalized_parsed_term(mut value: serde_json::Value) -> serde_json::Value {
    normalize_definition_value(&mut value, &BTreeMap::new());
    value
}

fn fun3(left: &str, right: &str, argument: &str) -> serde_json::Value {
    parsed_application(
        "#fun3",
        serde_json::json!([{ "name": "Map" }, { "name": "Type" }]),
        vec![
            parsed_variable(left),
            parsed_variable(right),
            parsed_variable(argument),
        ],
    )
}

fn fun2_over_rewrite(left: &str, right: &str, argument: &str) -> serde_json::Value {
    parsed_application(
        "#fun2",
        serde_json::json!([{ "name": "KItem" }]),
        vec![
            parsed_rewrite(parsed_variable(left), parsed_variable(right)),
            parsed_variable(argument),
        ],
    )
}

#[test]
fn definition_normalizer_identifies_fun3_with_fun2_over_a_rewrite() {
    let reference = normalized_parsed_term(fun3("L", "R", "A"));
    let actual = normalized_parsed_term(fun2_over_rewrite("L", "R", "A"));
    assert_eq!(reference, actual);

    // Nested under another application, including inside the rewritten #fun3 itself.
    let nested = |inner: serde_json::Value| {
        parsed_application(
            "#fun3",
            serde_json::json!([]),
            vec![parsed_variable("X"), inner, parsed_variable("Y")],
        )
    };
    assert_eq!(
        normalized_parsed_term(nested(fun3("L", "R", "A"))),
        normalized_parsed_term(parsed_application(
            "#fun2",
            serde_json::json!([]),
            vec![
                parsed_rewrite(parsed_variable("X"), fun2_over_rewrite("L", "R", "A")),
                parsed_variable("Y"),
            ],
        )),
    );
}

#[test]
fn definition_normalizer_keeps_differences_inside_local_functions() {
    let reference = normalized_parsed_term(fun3("L", "R", "A"));
    for actual in [
        fun2_over_rewrite("M", "R", "A"),
        fun2_over_rewrite("L", "S", "A"),
        fun2_over_rewrite("L", "R", "B"),
        fun3("L", "R", "B"),
    ] {
        assert_ne!(reference, normalized_parsed_term(actual));
    }
}

#[test]
fn definition_normalizer_leaves_other_local_function_shapes_unchanged() {
    let unchanged = [
        // #fun2 over a body that is not a rewrite.
        parsed_application(
            "#fun2",
            serde_json::json!([]),
            vec![parsed_variable("B"), parsed_variable("A")],
        ),
        // #let(L, A, R) keeps its own argument order.
        parsed_application(
            "#let",
            serde_json::json!([]),
            vec![
                parsed_variable("L"),
                parsed_variable("A"),
                parsed_variable("R"),
            ],
        ),
        // A #fun3 without three arguments is not a local-function application.
        parsed_application(
            "#fun3",
            serde_json::json!([]),
            vec![parsed_variable("L"), parsed_variable("R")],
        ),
        // Any other three-argument label.
        parsed_application(
            "ite",
            serde_json::json!([]),
            vec![
                parsed_variable("C"),
                parsed_variable("T"),
                parsed_variable("E"),
            ],
        ),
    ];
    for term in unchanged {
        assert_eq!(normalized_parsed_term(term.clone()), term);
    }
    // #fun3(L, R, A) and #let(L, A, R) stay distinct.
    assert_ne!(
        normalized_parsed_term(fun3("L", "R", "A")),
        normalized_parsed_term(parsed_application(
            "#let",
            serde_json::json!([]),
            vec![
                parsed_variable("L"),
                parsed_variable("A"),
                parsed_variable("R"),
            ],
        )),
    );
}

#[test]
fn definition_normalizer_canonicalizes_set_valued_outer_syntax() {
    let associativity = |tags: serde_json::Value| {
        serde_json::json!({
            "node": "KSyntaxAssociativity",
            "assoc": "Left",
            "tags": tags,
            "att": { "node": "KAtt", "att": {} }
        })
    };
    let priority = |first: serde_json::Value| {
        serde_json::json!({
            "node": "KSyntaxPriority",
            "priorities": [first, ["low"]],
            "att": { "node": "KAtt", "att": {} }
        })
    };
    let module = |imports: serde_json::Value, sentences: serde_json::Value| {
        serde_json::json!({
            "node": "KFlatModule",
            "name": "A",
            "imports": imports,
            "localSentences": sentences,
            "att": { "node": "KAtt", "att": {} }
        })
    };
    let empty_module = serde_json::json!({
        "node": "KFlatModule",
        "name": "B",
        "imports": [],
        "localSentences": [],
        "att": { "node": "KAtt", "att": {} }
    });
    let import_y = serde_json::json!({ "node": "KImport", "name": "Y", "isPublic": true });
    let import_z = serde_json::json!({ "node": "KImport", "name": "Z", "isPublic": true });
    let mut reference = serde_json::json!({
        "term": {
            "modules": [
                empty_module.clone(),
                module(
                    serde_json::json!([import_z.clone(), import_y.clone()]),
                    serde_json::json!([
                        associativity(serde_json::json!(["right", "left"])),
                        priority(serde_json::json!(["right", "left"]))
                    ])
                )
            ]
        }
    });
    let mut actual = serde_json::json!({
        "term": {
            "modules": [
                module(
                    serde_json::json!([import_y, import_z]),
                    serde_json::json!([
                        priority(serde_json::json!(["left", "right"])),
                        associativity(serde_json::json!(["left"])),
                        associativity(serde_json::json!(["right"]))
                    ])
                ),
                empty_module
            ]
        }
    });

    normalize_definition_json(&mut reference);
    normalize_definition_json(&mut actual);

    assert_eq!(reference, actual);
}

#[test]
#[ignore = "requires K_REFERENCE_EXECUTION and K_RUST_EXECUTION outputs"]
fn executed_kore_matches_the_reference_backend() {
    let reference_path =
        env::var("K_REFERENCE_EXECUTION").expect("K_REFERENCE_EXECUTION is required");
    let actual_path = env::var("K_RUST_EXECUTION").expect("K_RUST_EXECUTION is required");
    // N4: with the initial pattern at hand every result variable that is not free in it carries an
    // engine-chosen name (rule variables the reference leaves free, AC remainders, the port's
    // externalized fresh names); without it only the generated name shapes are canonicalized.
    let initial = env::var_os("K_DIFFERENTIAL_INITIAL_PATTERN").map(|path| {
        let source = fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("read {}: {error}", Path::new(&path).display()));
        parse_pattern(&source).unwrap()
    });
    // N4: without an initial pattern, `K_DIFFERENTIAL_PATTERN_EXISTENTIALS` lists the search
    // pattern's `?` variables (K names without `?`, whitespace-separated); when it is set, every
    // other `?` variable of a result is a rule existential.
    let pattern_existentials = env::var("K_DIFFERENTIAL_PATTERN_EXISTENTIALS")
        .ok()
        .map(|names| names.split_whitespace().map(str::to_owned).collect());
    let names = match (&initial, pattern_existentials) {
        (Some(initial), _) => GeneratedNames::fixing(initial),
        (None, Some(pattern)) => GeneratedNames::shapes_with_pattern_existentials(pattern),
        (None, None) => GeneratedNames::shapes(),
    };
    let reference =
        normalize_execution_pattern_with(read_execution_result(&reference_path), &names);
    let actual = normalize_execution_pattern_with(read_execution_result(&actual_path), &names);

    let definition = env::var_os("K_DIFFERENTIAL_DEFINITION");
    let module = env::var("K_DIFFERENTIAL_MODULE").unwrap_or_else(|_| "MAIN".into());
    let definition = definition.as_deref().map(Path::new);
    let krust = implication_krust();
    let oracle = definition.map(|definition| ImplicationOracle {
        krust: &krust,
        definition,
    });
    // N26: an any-strategy port result is compared as a member of the reference all-strategy
    // result set; the exclusions are about reference leaves, which membership already tolerates.
    let strategy = env::var("K_DIFFERENTIAL_STRATEGY");
    let exclusion = env::var("K_DIFFERENTIAL_ORACLE_EXCLUSION");
    let result = match (strategy.as_deref(), exclusion.as_deref()) {
        (Ok("any"), Ok(_)) => Err(
            "K_DIFFERENTIAL_STRATEGY=any cannot be combined with K_DIFFERENTIAL_ORACLE_EXCLUSION"
                .into(),
        ),
        (Ok("any"), Err(_)) => {
            compare_execution_any_membership(&reference, &actual, oracle, &module).map(|unpaired| {
                let total = execution_disjuncts(&reference).len();
                println!(
                    "any-strategy: {} of {total} reference leaves reached",
                    total - unpaired
                );
            })
        }
        (Ok("all") | Err(_), Ok("gotstuck")) => {
            let stop_path = env::var("K_DIFFERENTIAL_STOP_LEAVES")
                .expect("K_DIFFERENTIAL_STOP_LEAVES is required for the gotstuck exclusion");
            let stop_source = fs::read_to_string(stop_path).unwrap();
            let stop_leaves = normalize_execution_pattern(parse_pattern(&stop_source).unwrap());
            compare_execution_modulo_gotstuck(&reference, &actual, &stop_leaves, oracle, &module)
        }
        (Ok("all") | Err(_), Ok(exclusion)) => {
            Err(format!("unknown oracle exclusion: {exclusion}"))
        }
        (Ok("all") | Err(_), Err(_)) => {
            compare_execution_modulo_implication(&reference, &actual, oracle, &module)
        }
        (Ok(strategy), _) => Err(format!("unknown differential strategy: {strategy}")),
    };
    result.unwrap_or_else(|error| panic!("{error}"));
}

/// An execution result file: KORE text, or the KORE JSON envelope (`format`, `version`, `term`)
/// when the path ends in `.json`, the form of the `state` of an RPC response, so a result an RPC
/// server returned is compared without a conversion step.
fn read_execution_result(path: &str) -> Pattern {
    let source = fs::read_to_string(path).unwrap_or_else(|error| panic!("read {path}: {error}"));
    if path.ends_with(".json") {
        k_rust::kore::json::from_str(&source)
            .unwrap_or_else(|error| panic!("{path} is not a KORE JSON pattern: {error}"))
    } else {
        parse_pattern(&source)
            .unwrap_or_else(|error| panic!("{path} is not a KORE pattern: {error}"))
    }
}

/// The execution comparator entry point reads a reference result in KORE JSON when its path ends
/// in `.json`: the same pattern in JSON and in text compares equal to a port result, and a JSON
/// reference that differs still fails. Runs this test binary's ignored comparator.
#[test]
fn execution_comparator_reads_a_kore_json_reference_result() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = env::temp_dir().join(format!(
        "k-rust-execution-json-{}-{nonce}",
        std::process::id()
    ));
    fs::create_dir(&directory).unwrap();
    let write = |name: &str, text: &str| {
        let path = directory.join(name);
        fs::write(&path, text).unwrap();
        path
    };
    let pattern = r#"\or{S{}}(t{}(\dv{SortInt{}}("1")), t{}(\dv{SortInt{}}("2")))"#;
    let json =
        |pattern: &str| k_rust::kore::json::to_string(&parse_pattern(pattern).unwrap()).unwrap();
    let port = write("port.kore", pattern);
    let reference = write("reference.json", &json(pattern));
    let differing = write(
        "differing.json",
        &json(r#"\or{S{}}(t{}(\dv{SortInt{}}("1")), t{}(\dv{SortInt{}}("3")))"#),
    );
    let bottom = write("bottom.json", &json(r"\bottom{S{}}()"));
    let port_bottom = write("port-bottom.kore", r"\bottom{S{}}()");
    let compare = |reference: &Path, actual: &Path| {
        Command::new(env::current_exe().unwrap())
            .args([
                "--quiet",
                "--ignored",
                "--exact",
                "executed_kore_matches_the_reference_backend",
            ])
            .env("K_REFERENCE_EXECUTION", reference)
            .env("K_RUST_EXECUTION", actual)
            .env_remove("K_DIFFERENTIAL_DEFINITION")
            .env_remove("K_DIFFERENTIAL_INITIAL_PATTERN")
            .env_remove("K_DIFFERENTIAL_PATTERN_EXISTENTIALS")
            .env_remove("K_DIFFERENTIAL_STRATEGY")
            .env_remove("K_DIFFERENTIAL_ORACLE_EXCLUSION")
            .output()
            .unwrap()
    };
    for (reference, actual, equal) in [
        (&reference, &port, true),
        (&differing, &port, false),
        (&bottom, &port_bottom, true),
        (&bottom, &port, false),
    ] {
        let output = compare(reference, actual);
        assert_eq!(
            output.status.success(),
            equal,
            "{} against {}: {}{}",
            reference.display(),
            actual.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    fs::remove_dir_all(directory).unwrap();
}

/// N10: the execution gate refuses an oracle exception whose committed k-rust expectation the
/// comparator accepts against the recorded reference result, because then the exception excuses
/// nothing. Both are committed files, so this is checked on every push, not only when the gate runs
/// the reference. The gate compares them as `executed_kore_matches_the_reference_backend` does
/// without an initial pattern; here no definition is at hand, so the implication oracle (N15) is
/// unavailable. A term that pairs with no disjunct of the other side is a difference with or
/// without it, but two results that pair only through it cannot be told apart here and fail.
#[test]
fn committed_execution_oracle_exceptions_are_not_equivalent() {
    let manifest = include_str!("../../../scripts/reference-differential.toml")
        .parse::<toml::Value>()
        .expect("valid differential TOML");
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let read = |value: &toml::Value| {
        let value = value.as_str().expect("oracle exception file");
        let relative = value
            .strip_prefix("${workspace}/")
            .unwrap_or_else(|| panic!("{value} is not a workspace file"));
        let path = workspace.join(relative);
        let source = fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        normalize_execution_pattern_with(
            parse_pattern(&source).unwrap_or_else(|error| panic!("{relative}: {error:?}")),
            &GeneratedNames::shapes(),
        )
    };
    let mut checked = 0;
    for entry in manifest["execution"].as_array().expect("execution cases") {
        let name = entry["name"].as_str().expect("execution case name");
        let module = entry["main-module"]
            .as_str()
            .expect("execution main module");
        for exception in entry
            .get("oracle-exception")
            .and_then(toml::Value::as_array)
            .into_iter()
            .flatten()
        {
            let program = exception["program"].as_str().expect("exception program");
            let reference = read(&exception["reference"]);
            let expected = read(&exception["expected"]);
            match compare_execution_modulo_implication(&reference, &expected, None, module) {
                Ok(()) => panic!(
                    "committed oracle exception expectations for {name}:{program} are equivalent"
                ),
                Err(error) if error.contains("K_DIFFERENTIAL_DEFINITION is not set") => panic!(
                    "committed oracle exception expectations for {name}:{program} differ only in \
                     constraints the implication oracle must decide: {error}"
                ),
                Err(_) => checked += 1,
            }
        }
    }
    assert!(checked > 0, "no execution oracle exception was checked");
}

#[derive(Debug, Eq, PartialEq, Serialize)]
struct StdoutLeaf {
    constraints: Vec<String>,
    buffers: Vec<Vec<u8>>,
}

#[derive(Debug, Eq, PartialEq, Serialize)]
struct StdoutBufferReport {
    leaves: Vec<StdoutLeaf>,
}

/// C9 reports stdout buffers and residual constraints from a krust execution result.
///
/// The conformance driver owns the comparison with the checked-in `.out`; this helper owns only
/// structural KORE parsing.  Keeping that boundary here prevents the driver from recognizing a
/// pretty-printed substring as a configuration cell.
#[test]
#[ignore = "requires K_RUST_EXECUTION"]
fn conformance_stdout_stream_buffers() {
    let path = env::var("K_RUST_EXECUTION").expect("K_RUST_EXECUTION is required");
    let source = fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", Path::new(&path).display()));
    let pattern = parse_pattern(&source).unwrap_or_else(|error| {
        panic!("krust execution is not one complete KORE pattern: {error}")
    });
    println!(
        "c9-stdout-report = {}",
        serde_json::to_string(&stdout_buffer_report(&pattern)).unwrap()
    );
}

fn stdout_buffer_report(pattern: &Pattern) -> StdoutBufferReport {
    let leaves = execution_disjuncts_recursive(pattern)
        .into_iter()
        .map(|leaf| {
            let leaf = unwrap_exists(leaf);
            let (term, constraints) = split_constrained(leaf);
            StdoutLeaf {
                constraints: constraints
                    .iter()
                    .map(|constraint| bounded_text(&Printer::compact().print_pattern(constraint)))
                    .collect(),
                buffers: stdout_buffers(term),
            }
        })
        .collect();
    StdoutBufferReport { leaves }
}

fn execution_disjuncts_recursive(pattern: &Pattern) -> Vec<&Pattern> {
    let mut work = vec![pattern];
    let mut leaves = Vec::new();
    while let Some(pattern) = work.pop() {
        if let Pattern::Or { arguments, .. } = pattern {
            work.extend(arguments.iter().rev());
        } else {
            leaves.push(pattern);
        }
    }
    leaves
}

fn unwrap_exists(mut pattern: &Pattern) -> &Pattern {
    while let Pattern::Exists { body, .. } = pattern {
        pattern = body;
    }
    pattern
}

fn stdout_buffers(term: &Pattern) -> Vec<Vec<u8>> {
    let mut work = vec![term];
    let mut buffers = Vec::new();
    while let Some(pattern) = work.pop() {
        if let Pattern::Application { symbol, arguments } = pattern
            && symbol.name.starts_with("Lbl'-LT-'output'-GT-'")
            && arguments.len() == 1
            && let Some(items) = stream_list_items(&arguments[0])
            && let [descriptor, mode, buffer] = items.as_slice()
            && is_stream_descriptor(descriptor, "Lbl'Hash'ostream", "SortInt", "1")
            && domain_value(unwrap_injections(mode), "SortString") == Some("off")
            && let Some(value) = stream_buffer(buffer)
        {
            buffers.push(value);
        }
        work.extend(pattern_children(pattern).into_iter().rev());
    }
    buffers
}

fn stream_list_items(pattern: &Pattern) -> Option<Vec<&Pattern>> {
    fn append<'a>(pattern: &'a Pattern, items: &mut Vec<&'a Pattern>) -> bool {
        let pattern = unwrap_injections(pattern);
        let Pattern::Application { symbol, arguments } = pattern else {
            return false;
        };
        if symbol.name == "Lbl'Unds'List'Unds'" && arguments.len() == 2 {
            append(&arguments[0], items) && append(&arguments[1], items)
        } else if symbol.name == "LblListItem" && arguments.len() == 1 {
            items.push(&arguments[0]);
            true
        } else {
            false
        }
    }

    let mut items = Vec::new();
    append(pattern, &mut items).then_some(items)
}

fn unwrap_injections(mut pattern: &Pattern) -> &Pattern {
    while let Pattern::Application { symbol, arguments } = pattern
        && symbol.name == "inj"
        && arguments.len() == 1
    {
        pattern = &arguments[0];
    }
    pattern
}

fn domain_value<'a>(pattern: &'a Pattern, sort_name: &str) -> Option<&'a str> {
    let Pattern::DomainValue { sort, value } = pattern else {
        return None;
    };
    matches!(sort, k_rust::kore::ast::Sort::Application { name, arguments }
        if name == sort_name && arguments.is_empty())
    .then(|| value.as_utf8().ok())
    .flatten()
}

fn is_stream_descriptor(
    pattern: &Pattern,
    symbol_prefix: &str,
    sort_name: &str,
    value: &str,
) -> bool {
    let Pattern::Application { symbol, arguments } = unwrap_injections(pattern) else {
        return false;
    };
    symbol.name.starts_with(symbol_prefix)
        && arguments.len() == 1
        && domain_value(unwrap_injections(&arguments[0]), sort_name) == Some(value)
}

fn stream_buffer(pattern: &Pattern) -> Option<Vec<u8>> {
    let Pattern::Application { symbol, arguments } = unwrap_injections(pattern) else {
        return None;
    };
    if !symbol.name.starts_with("Lbl'Hash'buffer") || arguments.len() != 1 {
        return None;
    }
    let Pattern::Application {
        symbol: sequence,
        arguments: sequence_arguments,
    } = unwrap_injections(&arguments[0])
    else {
        return None;
    };
    if sequence.name != "kseq" || sequence_arguments.len() != 2 {
        return None;
    }
    let Pattern::Application {
        symbol: terminator,
        arguments: terminator_arguments,
    } = &sequence_arguments[1]
    else {
        return None;
    };
    if terminator.name != "dotk" || !terminator_arguments.is_empty() {
        return None;
    }
    domain_value_bytes(unwrap_injections(&sequence_arguments[0]), "SortString")
}

/// The console bytes of a `String` buffer: each character is one byte, its code point.
fn domain_value_bytes(pattern: &Pattern, sort_name: &str) -> Option<Vec<u8>> {
    let Pattern::DomainValue { sort, value } = pattern else {
        return None;
    };
    if !matches!(sort, k_rust::kore::ast::Sort::Application { name, arguments }
        if name == sort_name && arguments.is_empty())
    {
        return None;
    }
    value
        .as_utf8()
        .ok()?
        .chars()
        .map(|character| u8::try_from(u32::from(character)).ok())
        .collect()
}

#[test]
fn stdout_stream_buffer_report_requires_a_structural_stdout_cell() {
    let stdout = r#"Lbl'Unds'List'Unds'{}(
        LblListItem{}(inj{SortStream{}, SortKItem{}}(
            Lbl'Hash'ostream'LParUndsRParUnds'K-IO'Unds'Stream'Unds'Int{}(\dv{SortInt{}}("1")))),
        Lbl'Unds'List'Unds'{}(
            LblListItem{}(inj{SortString{}, SortKItem{}}(\dv{SortString{}}("off"))),
            LblListItem{}(inj{SortStream{}, SortKItem{}}(
                Lbl'Hash'buffer'LParUndsRParUnds'K-IO'Unds'Stream'Unds'K{}(
                    kseq{}(inj{SortString{}, SortKItem{}}(\dv{SortString{}}("hello\n")), dotk{}()))))))"#;
    let terminal = parse_pattern(&format!("cfg{{}}(Lbl'-LT-'output'-GT-'{{}}({stdout}))")).unwrap();
    assert_eq!(
        stdout_buffer_report(&terminal),
        StdoutBufferReport {
            leaves: vec![StdoutLeaf {
                constraints: vec![],
                buffers: vec![b"hello\n".to_vec()],
            }],
        }
    );

    let residual = parse_pattern(&format!(
        r#"\or{{S{{}}}}(cfg{{}}(Lbl'-LT-'output'-GT-'{{}}({stdout})), \and{{S{{}}}}(cfg{{}}(Lbl'-LT-'output'-GT-'{{}}({stdout})), \not{{B{{}}}}(\top{{B{{}}}}())))"#
    ))
    .unwrap();
    let report = stdout_buffer_report(&residual);
    assert_eq!(report.leaves.len(), 2);
    assert_eq!(report.leaves[0].buffers, [b"hello\n".to_vec()]);
    assert!(report.leaves[0].constraints.is_empty());
    assert_eq!(report.leaves[1].buffers, [b"hello\n".to_vec()]);
    assert_eq!(report.leaves[1].constraints.len(), 1);

    let impostor = parse_pattern(
        r#"cfg{}(LblListItem{}(\dv{SortString{}}("Lbl#ostream(1) off #buffer(hello)")))"#,
    )
    .unwrap();
    assert!(stdout_buffer_report(&impostor).leaves[0].buffers.is_empty());
}

#[cfg(feature = "cli")]
fn output_with_stdin(command: &mut Command, input: &[u8]) -> std::process::Output {
    use std::{io::Write, process::Stdio};
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(input).unwrap();
    child.wait_with_output().unwrap()
}

// It runs the `krust` binary, which cargo builds only with the `cli` feature.
#[cfg(feature = "cli")]
#[test]
fn c9_captured_and_live_console_paths_agree_on_arbitrary_bytes() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root = env::temp_dir().join(format!(
        "k-rust-three-console-paths-{}-{nonce}",
        std::process::id()
    ));
    let compiled = root.join("compiled");
    fs::create_dir_all(&root).unwrap();
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/live-io/test.k");
    let compile = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "kcompile",
            fixture.to_str().unwrap(),
            "--main-module",
            "LIVE-IO",
            "--output-directory",
        ])
        .arg(&compiled)
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let input = [0xff, 0x80, 0x00, b'A', b'\n'];
    let expected = &input[..4];
    let command = |output: &str| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_krust"));
        command.args([
            "krun",
            "--definition",
            compiled.to_str().unwrap(),
            "--sort",
            "Pgm",
            "--expression",
            "three-path-bytes",
            "--output",
            output,
        ]);
        command
    };

    let mut c9_command = command("kore");
    c9_command.args(["--io", "off"]);
    let c9 = output_with_stdin(&mut c9_command, &input);
    assert!(
        c9.status.success(),
        "{}",
        String::from_utf8_lossy(&c9.stderr)
    );
    let c9_pattern = parse_pattern(std::str::from_utf8(&c9.stdout).unwrap()).unwrap();
    let report = stdout_buffer_report(&c9_pattern);
    assert_eq!(report.leaves.len(), 1, "{report:?}");
    assert!(report.leaves[0].constraints.is_empty(), "{report:?}");
    assert_eq!(report.leaves[0].buffers, [expected.to_vec()]);

    let captured = output_with_stdin(&mut command("captured"), &input);
    assert!(
        captured.status.success(),
        "{}",
        String::from_utf8_lossy(&captured.stderr)
    );
    assert_eq!(captured.stdout, expected);

    let mut live_command = command("none");
    live_command.args(["--io", "on"]);
    let live = output_with_stdin(&mut live_command, &input);
    assert!(
        live.status.success(),
        "{}",
        String::from_utf8_lossy(&live.stderr)
    );
    assert_eq!(live.stdout, expected);

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn execution_normalizer_treats_search_disjunctions_as_result_sets() {
    let left = parse_pattern(r"\or{S{}}(\or{S{}}(a{}(), b{}()), c{}())").unwrap();
    let right = parse_pattern(r"\or{S{}}(\or{S{}}(c{}(), a{}()), b{}())").unwrap();
    assert_eq!(
        normalize_execution_pattern(left),
        normalize_execution_pattern(right)
    );
}

#[test]
fn execution_normalizer_reassociates_map_concatenation() {
    let left =
        parse_pattern(r"Lbl'Unds'Map'Unds'{}(Lbl'Unds'Map'Unds'{}(a{}(), b{}()), c{}())").unwrap();
    let right =
        parse_pattern(r"Lbl'Unds'Map'Unds'{}(c{}(), Lbl'Unds'Map'Unds'{}(b{}(), a{}()))").unwrap();

    assert_eq!(
        normalize_execution_pattern(left),
        normalize_execution_pattern(right)
    );
}

#[test]
fn execution_normalizer_alpha_normalizes_each_bound_scope() {
    let initial = parse_pattern("t{}()").unwrap();
    let reference = parse_pattern(
        r"\and{S{}}(
            t{}(),
            \not{S{}}(\exists{S{}}(VarX:T{}, \equals{T{}, S{}}(VarX:T{}, a{}()))),
            \not{S{}}(\exists{S{}}(VarX:T{}, \equals{T{}, S{}}(VarX:T{}, b{}())))
        )",
    )
    .unwrap();
    let actual = parse_pattern(
        r"\and{S{}}(
            t{}(),
            \not{S{}}(\exists{S{}}(VarY:T{}, \equals{T{}, S{}}(VarY:T{}, a{}()))),
            \not{S{}}(\exists{S{}}(VarZ:T{}, \equals{T{}, S{}}(VarZ:T{}, b{}())))
        )",
    )
    .unwrap();

    assert_eq!(
        normalize_execution_pattern_fixing(reference, &initial),
        normalize_execution_pattern_fixing(actual, &initial)
    );
}

#[test]
fn execution_normalizer_commutes_existential_binder_chains() {
    let initial = parse_pattern("t{}()").unwrap();
    let reference = parse_pattern(
        r"\and{S{}}(t{}(), \exists{S{}}(VarX:T{}, \exists{S{}}(VarY:U{}, f{}(VarX:T{}, VarY:U{}))))",
    )
    .unwrap();
    let actual = parse_pattern(
        r"\and{S{}}(t{}(), \exists{S{}}(VarY:U{}, \exists{S{}}(VarX:T{}, f{}(VarX:T{}, VarY:U{}))))",
    )
    .unwrap();

    assert_eq!(
        normalize_execution_pattern_fixing(reference, &initial),
        normalize_execution_pattern_fixing(actual, &initial)
    );
}

#[test]
fn compile_normalizer_commutes_no_confusion_pairs() {
    let canonical = |source: &str| {
        let mut pattern = parse_pattern(source).unwrap();
        canonicalize_pattern(&mut pattern);
        pattern
    };
    let reference = canonical(r"\not{S{}}(\and{S{}}(Lblpair{}(X0:S{}, X1:T{}), Lblzero{}()))");
    let swapped = canonical(r"\not{S{}}(\and{S{}}(Lblzero{}(), Lblpair{}(Y0:S{}, Y1:T{})))");
    assert_eq!(reference, swapped);

    let other_constructor =
        canonical(r"\not{S{}}(\and{S{}}(Lblone{}(), Lblpair{}(Y0:S{}, Y1:T{})))");
    assert_ne!(reference, other_constructor);
    let other_sort = canonical(r"\not{S{}}(\and{S{}}(Lblpair{}(Y0:T{}, Y1:T{}), Lblzero{}()))");
    assert_ne!(reference, other_sort);

    let not_a_pair = r"\not{S{}}(\and{S{}}(Lblpair{}(X0:S{}, f{}(X1:T{})), Lblzero{}()))";
    assert_eq!(canonical(not_a_pair), parse_pattern(not_a_pair).unwrap());
}

#[test]
fn execution_normalizer_commutes_same_sort_binders_while_preserving_their_roles() {
    let initial = parse_pattern("t{}()").unwrap();
    let reference = parse_pattern(
        r"\and{S{}}(
            t{}(),
            \exists{S{}}(VarFirst:T{}, \exists{S{}}(VarSecond:T{},
                \and{S{}}(
                    \equals{T{}, S{}}(k{}(), op{}(VarFirst:T{}, VarSecond:T{})),
                    q{}(VarSecond:T{})
                )
            ))
        )",
    )
    .unwrap();
    let actual = parse_pattern(
        r"\and{S{}}(
            t{}(),
            \exists{S{}}(VarTested:T{}, \exists{S{}}(VarOther:T{},
                \and{S{}}(
                    q{}(VarTested:T{}),
                    \equals{T{}, S{}}(op{}(VarOther:T{}, VarTested:T{}), k{}())
                )
            ))
        )",
    )
    .unwrap();

    assert_eq!(
        normalize_execution_pattern_fixing(reference, &initial),
        normalize_execution_pattern_fixing(actual, &initial)
    );
}

#[test]
fn execution_normalizer_does_not_exchange_bound_variable_roles() {
    let initial = parse_pattern("t{}()").unwrap();
    let reference = parse_pattern(
        r"\and{S{}}(
            t{}(),
            \exists{S{}}(VarFirst:T{}, \exists{S{}}(VarSecond:T{},
                \and{S{}}(
                    \equals{T{}, S{}}(k{}(), op{}(VarFirst:T{}, VarSecond:T{})),
                    q{}(VarSecond:T{})
                )
            ))
        )",
    )
    .unwrap();
    let changed_role = parse_pattern(
        r"\and{S{}}(
            t{}(),
            \exists{S{}}(VarFirst:T{}, \exists{S{}}(VarSecond:T{},
                \and{S{}}(
                    \equals{T{}, S{}}(k{}(), op{}(VarFirst:T{}, VarSecond:T{})),
                    q{}(VarFirst:T{})
                )
            ))
        )",
    )
    .unwrap();

    assert_ne!(
        normalize_execution_pattern_fixing(reference, &initial),
        normalize_execution_pattern_fixing(changed_role, &initial)
    );
}

#[test]
fn execution_normalizer_canonicalizes_equalities_and_boolean_false() {
    let reference = parse_pattern(
        r#"\and{S{}}(
            t{}(),
            \equals{T{}, S{}}(b{}(), a{}()),
            \equals{SortBool{}, S{}}(\dv{SortBool{}}("false"), LblisKResult{}(x{}()))
        )"#,
    )
    .unwrap();
    let actual = parse_pattern(
        r#"\and{S{}}(
            t{}(),
            \equals{T{}, S{}}(a{}(), b{}()),
            \not{S{}}(\equals{SortBool{}, S{}}(LblisKResult{}(x{}()), \dv{SortBool{}}("true")))
        )"#,
    )
    .unwrap();

    assert_eq!(
        normalize_execution_pattern(reference),
        normalize_execution_pattern(actual)
    );
}

#[test]
fn execution_normalizer_preserves_partial_and_unrecognized_boolean_equalities() {
    let false_bottom = parse_pattern(
        r#"\equals{SortBool{}, S{}}(\dv{SortBool{}}("false"), \bottom{SortBool{}}())"#,
    )
    .unwrap();
    let not_true_bottom = parse_pattern(
        r#"\not{S{}}(\equals{SortBool{}, S{}}(\dv{SortBool{}}("true"), \bottom{SortBool{}}()))"#,
    )
    .unwrap();
    assert_ne!(
        normalize_execution_pattern(false_bottom),
        normalize_execution_pattern(not_true_bottom),
        "a partial Boolean pattern does not satisfy two-valued complementation"
    );

    let false_unknown =
        parse_pattern(r#"\equals{SortBool{}, S{}}(\dv{SortBool{}}("false"), p{}())"#).unwrap();
    let not_true_unknown =
        parse_pattern(r#"\not{S{}}(\equals{SortBool{}, S{}}(\dv{SortBool{}}("true"), p{}()))"#)
            .unwrap();
    assert_ne!(
        normalize_execution_pattern(false_unknown),
        normalize_execution_pattern(not_true_unknown),
        "the comparator cannot infer totality from a SortBool result alone"
    );
}

#[test]
fn execution_normalizer_keeps_different_sort_disjunctions_nested() {
    let nested = parse_pattern(r"\or{S{}}(\or{T{}}(a{}(), b{}()), c{}())").unwrap();
    let flattened = parse_pattern(r"\or{S{}}(a{}(), \or{T{}}(b{}(), c{}()))").unwrap();

    assert_ne!(
        normalize_execution_pattern(nested),
        normalize_execution_pattern(flattened)
    );
}

#[test]
fn execution_normalizer_preserves_disjunction_multiplicity() {
    let repeated = parse_pattern(r"\or{S{}}(a{}(), a{}(), b{}())").unwrap();
    let unique = parse_pattern(r"\or{S{}}(a{}(), b{}())").unwrap();

    assert_ne!(
        normalize_execution_pattern(repeated),
        normalize_execution_pattern(unique)
    );
}

#[test]
fn execution_normalizer_drops_the_outer_existential_prefix() {
    let quantified =
        parse_pattern(r"\exists{S{}}(Var'Unds'AC1:S{}, \and{S{}}(a{}(), Var'Unds'AC1:S{}))")
            .unwrap();
    let body = parse_pattern(r"\and{S{}}(a{}(), Var'Unds'AC7:S{})").unwrap();

    assert_eq!(
        normalize_execution_pattern(quantified),
        normalize_execution_pattern(body)
    );
}

#[test]
fn execution_normalizer_drops_an_outer_binder_of_a_variable_not_in_the_initial_pattern() {
    let initial = parse_pattern(r"f{}(VarX:S{})").unwrap();
    let quantified = parse_pattern(
        r"\exists{S{}}(VarY:S{}, \and{S{}}(f{}(VarX:S{}), \equals{S{}, S{}}(VarY:S{}, VarX:S{})))",
    )
    .unwrap();
    let body =
        parse_pattern(r"\and{S{}}(f{}(VarX:S{}), \equals{S{}, S{}}(VarZ:S{}, VarX:S{}))").unwrap();

    assert_eq!(
        normalize_execution_pattern_fixing(quantified, &initial),
        normalize_execution_pattern_fixing(body, &initial)
    );
}

#[test]
fn execution_normalizer_keeps_an_outer_binder_of_an_initial_pattern_variable() {
    let initial = parse_pattern(r"f{}(VarX:S{})").unwrap();
    let quantified =
        parse_pattern(r"\exists{S{}}(VarX:S{}, \and{S{}}(a{}(), f{}(VarX:S{})))").unwrap();
    let body = parse_pattern(r"\and{S{}}(a{}(), f{}(VarX:S{}))").unwrap();

    assert_ne!(
        normalize_execution_pattern_fixing(quantified, &initial),
        normalize_execution_pattern_fixing(body, &initial)
    );
}

#[test]
fn execution_normalizer_keeps_an_outer_binder_of_a_non_generated_shape_without_an_initial_pattern()
{
    let quantified =
        parse_pattern(r"\exists{S{}}(VarX:S{}, \and{S{}}(a{}(), f{}(VarX:S{})))").unwrap();
    let body = parse_pattern(r"\and{S{}}(a{}(), f{}(VarX:S{}))").unwrap();

    assert_ne!(
        normalize_execution_pattern(quantified),
        normalize_execution_pattern(body)
    );
}

#[test]
fn execution_normalizer_emits_reparseable_generated_variable_names() {
    let pattern = parse_pattern(
        r"\and{S{}}(f{}(Var'Unds'X1:S{}, Var'Unds'X2:S{}), \equals{S{}, S{}}(Var'Unds'X1:S{}, Var'Unds'X2:S{}))",
    )
    .unwrap();
    let normalized = normalize_execution_pattern(pattern);
    let rendered = normalized.to_string();

    parse_pattern(&rendered)
        .unwrap_or_else(|error| panic!("normalized KORE must reparse ({error}): {rendered}"));
}

#[test]
fn execution_comparator_pairs_disjuncts_by_term_and_reports_unpaired() {
    let reference =
        normalize_execution_pattern(parse_pattern(r"\and{S{}}(a{}(), \top{S{}}())").unwrap());
    let different_constraints =
        normalize_execution_pattern(parse_pattern(r"\and{S{}}(a{}(), \bottom{S{}}())").unwrap());
    let error =
        compare_execution_modulo_implication(&reference, &different_constraints, None, "TEST")
            .expect_err("different constraints need an implication definition");
    assert!(error.contains("constraints differ"), "{error}");

    let different_term = normalize_execution_pattern(parse_pattern("b{}()").unwrap());
    let error = compare_execution_modulo_implication(&reference, &different_term, None, "TEST")
        .expect_err("different terms cannot be paired");
    assert!(error.contains("unpaired disjunct"), "{error}");
}

#[test]
fn execution_comparator_allows_only_marked_gotstuck_stop_leaves() {
    let reference = normalize_execution_pattern(parse_pattern("a{}()").unwrap());
    let actual = normalize_execution_pattern(parse_pattern(r"\or{S{}}(a{}(), b{}())").unwrap());
    let stop_leaves = normalize_execution_pattern(parse_pattern("b{}()").unwrap());
    compare_execution_modulo_gotstuck(&reference, &actual, &stop_leaves, None, "TEST")
        .expect("the one extra actual leaf is marked as depth-bounded");

    let wrong_stop = normalize_execution_pattern(parse_pattern("c{}()").unwrap());
    let error = compare_execution_modulo_gotstuck(&reference, &actual, &wrong_stop, None, "TEST")
        .expect_err("an unmarked actual leaf must still fail");
    assert!(error.contains("unpaired disjunct"), "{error}");
}

#[test]
fn execution_comparator_accepts_an_any_result_that_is_a_member_of_the_all_set() {
    // N26: a concrete any-strategy run reaches one leaf of the all-strategy set.
    let reference = normalize_execution_pattern(
        parse_pattern(r"\or{S{}}(\and{S{}}(a{}(), \top{S{}}()), b{}())").unwrap(),
    );
    for member in [r"\and{S{}}(a{}(), \top{S{}}())", "b{}()"] {
        let actual = normalize_execution_pattern(parse_pattern(member).unwrap());
        assert_eq!(
            compare_execution_any_membership(&reference, &actual, None, "TEST"),
            Ok(1),
            "{member} is a member of the reference set"
        );
    }
    // A symbolic any-strategy run may reach several leaves; the whole set is a member of itself.
    assert_eq!(
        compare_execution_any_membership(&reference, &reference, None, "TEST"),
        Ok(0)
    );
}

#[test]
fn execution_comparator_rejects_an_any_result_outside_the_all_set() {
    let reference = normalize_execution_pattern(parse_pattern(r"\or{S{}}(a{}(), b{}())").unwrap());
    let other_term = normalize_execution_pattern(parse_pattern("c{}()").unwrap());
    let error = compare_execution_any_membership(&reference, &other_term, None, "TEST")
        .expect_err("a leaf outside the reference set cannot be paired");
    assert!(error.contains("unpaired port disjunct: c{}()"), "{error}");

    let reference =
        normalize_execution_pattern(parse_pattern(r"\and{S{}}(a{}(), \top{S{}}())").unwrap());
    let other_constraints =
        normalize_execution_pattern(parse_pattern(r"\and{S{}}(a{}(), \bottom{S{}}())").unwrap());
    let error = compare_execution_any_membership(&reference, &other_constraints, None, "TEST")
        .expect_err("different constraints need an implication definition");
    assert!(error.contains("constraints differ"), "{error}");
}

#[test]
fn execution_comparator_rejects_an_empty_any_result() {
    let reference = normalize_execution_pattern(parse_pattern(r"\or{S{}}(a{}(), b{}())").unwrap());
    let Pattern::Or { sort, .. } = &reference else {
        panic!("normalized disjunction");
    };
    let empty = Pattern::Or {
        sort: sort.clone(),
        arguments: Vec::new(),
    };
    assert!(is_empty_disjunction(&empty));
    let error = compare_execution_any_membership(&reference, &empty, None, "TEST")
        .expect_err("an any-strategy run must reach a leaf");
    assert!(error.contains("empty"), "{error}");
}

#[test]
fn execution_comparator_keeps_any_multiplicity() {
    let reference = normalize_execution_pattern(parse_pattern(r"\or{S{}}(a{}(), b{}())").unwrap());
    let duplicated = normalize_execution_pattern(parse_pattern(r"\or{S{}}(a{}(), a{}())").unwrap());
    let error = compare_execution_any_membership(&reference, &duplicated, None, "TEST")
        .expect_err("a duplicated port leaf needs a second reference copy");
    assert!(error.contains("unpaired port disjunct: a{}()"), "{error}");

    let reference = normalize_execution_pattern(parse_pattern(r"\or{S{}}(a{}(), a{}())").unwrap());
    assert_eq!(
        compare_execution_any_membership(&reference, &duplicated, None, "TEST"),
        Ok(0)
    );
}

#[test]
fn execution_comparator_pairs_reference_remainders_with_port_remainders() {
    // Reference shape (kore-exec at --depth 2 on the symbolic collection-frame fixture): the rewritten branch
    // nests its term inside a second \and, the remainder carries \not(\exists ...) over the rule
    // variables with the NewUnifier's AC remainder VarAC1'Unds'1 left free, and conjunctions are
    // right-nested with a duplicated conjunct.
    let reference = parse_pattern(concat!(
        r"\or{S{}}(",
        r"\and{S{}}(\and{S{}}(top{}(done{}(), m{}(concat{}(entry{}(k1{}(), v2{}()), VarAC1'Unds'1:Map{}))), ",
        r#"\and{S{}}(\equals{Bool{}, S{}}(\dv{Bool{}}("false"), inkeys{}(Var'Unds'K:KI{}, VarAC1'Unds'1:Map{})), "#,
        r#"\and{S{}}(\equals{Bool{}, S{}}(\dv{Bool{}}("false"), inkeys{}(k1{}(), VarAC1'Unds'1:Map{})), "#,
        r"\not{S{}}(\equals{KI{}, S{}}(Var'Unds'K:KI{}, k1{}()))))), ",
        r"\equals{Map{}, S{}}(VarM:Map{}, concat{}(entry{}(Var'Unds'K:KI{}, Var'Unds'V:KI{}), VarAC1'Unds'1:Map{}))), ",
        r"\and{S{}}(top{}(go{}(), m{}(concat{}(entry{}(k1{}(), v2{}()), VarM:Map{}))), ",
        r#"\and{S{}}(\not{S{}}(\equals{Bool{}, S{}}(\dv{Bool{}}("false"), inkeys{}(k1{}(), VarM:Map{}))), "#,
        r"\not{S{}}(\exists{S{}}(Var'Unds'K:KI{}, \exists{S{}}(Var'Unds'V:KI{}, ",
        r#"\and{S{}}(\and{S{}}(\equals{Bool{}, S{}}(\dv{Bool{}}("false"), inkeys{}(Var'Unds'K:KI{}, VarAC1'Unds'1:Map{})), "#,
        r#"\and{S{}}(\equals{Bool{}, S{}}(\dv{Bool{}}("false"), inkeys{}(k1{}(), VarAC1'Unds'1:Map{})), "#,
        r"\not{S{}}(\equals{KI{}, S{}}(Var'Unds'K:KI{}, k1{}())))), ",
        r#"\and{S{}}(\equals{Bool{}, S{}}(\dv{Bool{}}("false"), inkeys{}(Var'Unds'K:KI{}, VarAC1'Unds'1:Map{})), "#,
        r"\equals{Map{}, S{}}(VarM:Map{}, concat{}(entry{}(Var'Unds'K:KI{}, Var'Unds'V:KI{}), VarAC1'Unds'1:Map{})))))))))",
        r")",
    ))
    .unwrap();
    // Port shape (krust kore-exec): flat conjunctions, the externalized fresh names Ex-hFrame-b0 and
    // Ex-hVar'Unds'K-b1, and the frame quantified inside the negated existential.
    let actual = parse_pattern(concat!(
        r"\or{S{}}(",
        r"\and{S{}}(top{}(go{}(), m{}(concat{}(entry{}(k1{}(), v2{}()), VarM:Map{}))), ",
        r#"\and{S{}}(\not{S{}}(\equals{Bool{}, S{}}(\dv{Bool{}}("false"), inkeys{}(k1{}(), VarM:Map{}))), "#,
        r"\not{S{}}(\exists{S{}}(Ex-hVar'Unds'K-b1:KI{}, \exists{S{}}(Ex-hVar'Unds'V-b2:KI{}, \exists{S{}}(Ex-hFrame-b0:Map{}, ",
        r"\and{S{}}(\not{S{}}(\equals{KI{}, S{}}(Ex-hVar'Unds'K-b1:KI{}, k1{}())), ",
        r#"\equals{Bool{}, S{}}(\dv{Bool{}}("false"), inkeys{}(Ex-hVar'Unds'K-b1:KI{}, Ex-hFrame-b0:Map{})), "#,
        r#"\equals{Bool{}, S{}}(\dv{Bool{}}("false"), inkeys{}(k1{}(), Ex-hFrame-b0:Map{})), "#,
        r"\equals{Map{}, S{}}(VarM:Map{}, concat{}(entry{}(Ex-hVar'Unds'K-b1:KI{}, Ex-hVar'Unds'V-b2:KI{}), Ex-hFrame-b0:Map{}))))))))), ",
        r"\and{S{}}(top{}(done{}(), m{}(concat{}(entry{}(k1{}(), v2{}()), Ex-hFrame-b0:Map{}))), ",
        r"\and{S{}}(\equals{Map{}, S{}}(VarM:Map{}, concat{}(entry{}(Ex-hVar'Unds'K-b1:KI{}, Ex-hVar'Unds'V-b2:KI{}), Ex-hFrame-b0:Map{})), ",
        r"\not{S{}}(\equals{KI{}, S{}}(Ex-hVar'Unds'K-b1:KI{}, k1{}())), ",
        r#"\equals{Bool{}, S{}}(\dv{Bool{}}("false"), inkeys{}(Ex-hVar'Unds'K-b1:KI{}, Ex-hFrame-b0:Map{})), "#,
        r#"\equals{Bool{}, S{}}(\dv{Bool{}}("false"), inkeys{}(k1{}(), Ex-hFrame-b0:Map{}))))"#,
        r")",
    ))
    .unwrap();
    let initial =
        parse_pattern(r"top{}(go{}(), m{}(concat{}(entry{}(k1{}(), v2{}()), VarM:Map{})))")
            .unwrap();
    let reference = normalize_execution_pattern_fixing(reference, &initial);
    let actual = normalize_execution_pattern_fixing(actual, &initial);
    let rendered = actual.to_string();
    parse_pattern(&rendered)
        .unwrap_or_else(|error| panic!("normalized KORE must reparse ({error}): {rendered}"));
    assert_eq!(
        reference, actual,
        "both branch sets must normalize to the same pattern"
    );
    compare_execution_modulo_implication(&reference, &actual, None, "TEST")
        .expect("the reference and port branch multisets pair structurally");

    // A port that drops the remainder is a genuine branch-set difference.
    let Pattern::Or { sort, arguments } = &actual else {
        panic!("normalized disjunction");
    };
    let rewritten_only = Pattern::Or {
        sort: sort.clone(),
        arguments: arguments
            .iter()
            .filter(|disjunct| !disjunct.to_string().contains("go{}()"))
            .cloned()
            .collect(),
    };
    assert_eq!(execution_disjuncts(&rewritten_only).len(), 1);
    let error = compare_execution_modulo_implication(&reference, &rewritten_only, None, "TEST")
        .expect_err("a missing remainder branch must still fail");
    assert!(error.contains("unpaired disjunct"), "{error}");
}

#[test]
fn execution_normalizer_canonicalizes_rule_variables_absent_from_the_initial_pattern() {
    // Injection-narrowing fixture: kore-exec leaves the rule variable I free (VarI), krust prints Ex-hVarI-b0.
    let reference = parse_pattern(concat!(
        r"\or{S{}}(",
        r"\and{S{}}(top{}(inj{Exp{}, KI{}}(bar{}(VarI:Int{}))), \equals{Exp{}, S{}}(VarE:Exp{}, inj{Int{}, Exp{}}(VarI:Int{}))), ",
        r"\and{S{}}(top{}(inj{Exp{}, KI{}}(VarE:Exp{})), \not{S{}}(\exists{S{}}(VarI:Int{}, \equals{Exp{}, S{}}(VarE:Exp{}, inj{Int{}, Exp{}}(VarI:Int{}))))))",
    ))
    .unwrap();
    let actual = parse_pattern(concat!(
        r"\or{S{}}(",
        r"\and{S{}}(top{}(inj{Exp{}, KI{}}(VarE:Exp{})), \not{S{}}(\exists{S{}}(Ex-hVarI-b0:Int{}, \equals{Exp{}, S{}}(VarE:Exp{}, inj{Int{}, Exp{}}(Ex-hVarI-b0:Int{}))))), ",
        r"\and{S{}}(top{}(inj{Exp{}, KI{}}(bar{}(Ex-hVarI-b0:Int{}))), \equals{Exp{}, S{}}(VarE:Exp{}, inj{Int{}, Exp{}}(Ex-hVarI-b0:Int{}))))",
    ))
    .unwrap();
    let initial = parse_pattern(r"top{}(inj{Exp{}, KI{}}(VarE:Exp{}))").unwrap();

    // Without the initial pattern only the generated shapes are renamed: VarI is a user name, so
    // the rewritten branch stays unpaired and the remainder's constraints differ.
    let error = compare_execution_modulo_implication(
        &normalize_execution_pattern(reference.clone()),
        &normalize_execution_pattern(actual.clone()),
        None,
        "TEST",
    )
    .expect_err("VarI is not a generated shape");
    assert!(
        error.contains("unpaired disjunct") || error.contains("constraints differ"),
        "{error}"
    );

    let reference = normalize_execution_pattern_fixing(reference, &initial);
    let actual = normalize_execution_pattern_fixing(actual, &initial);
    assert_eq!(reference, actual);
    // The initial pattern's own variable keeps its name and sort.
    assert!(reference.to_string().contains("VarE:Exp{}"), "{reference}");
    assert!(!reference.to_string().contains("VarI:"), "{reference}");
}

#[test]
fn execution_normalizer_preserves_sorts_and_distinctness_of_generated_variables() {
    let reference = parse_pattern(
        r"\and{S{}}(f{}(VarAC1'Unds'1:Map{}, VarAC2'Unds'1:Set{}), \equals{Map{}, S{}}(VarAC1'Unds'1:Map{}, g{}(VarAC2'Unds'1:Set{})))",
    )
    .unwrap();
    let actual = parse_pattern(
        r"\and{S{}}(f{}(Ex-hFrame-b0:Map{}, Ex-hFrame-b1:Set{}), \equals{Map{}, S{}}(Ex-hFrame-b0:Map{}, g{}(Ex-hFrame-b1:Set{})))",
    )
    .unwrap();
    assert_eq!(
        normalize_execution_pattern(reference),
        normalize_execution_pattern(actual)
    );

    let collapsed = parse_pattern(
        r"\and{S{}}(f{}(Ex-hFrame-b0:Map{}, Ex-hFrame-b0:Set{}), \equals{Map{}, S{}}(Ex-hFrame-b0:Map{}, g{}(Ex-hFrame-b0:Set{})))",
    )
    .unwrap();
    let distinct = parse_pattern(
        r"\and{S{}}(f{}(Ex-hFrame-b0:Map{}, Ex-hFrame-b1:Set{}), \equals{Map{}, S{}}(Ex-hFrame-b0:Map{}, g{}(Ex-hFrame-b1:Set{})))",
    )
    .unwrap();
    assert_ne!(
        normalize_execution_pattern(collapsed),
        normalize_execution_pattern(distinct),
        "two generated names of different sorts stay distinct from one name"
    );
}

#[test]
fn execution_normalizer_renames_instantiated_rule_existentials_in_shapes_mode() {
    // LAMBDA type inferencer (pl-tutorial/1_k/5_types/lesson_6), composition.lambda, searched
    // with the free VarT:SortType{}: the engines keep different fresh counters and unification
    // representatives for the rules' `?T` existentials but the same sharing structure.
    let reference = parse_pattern(concat!(
        r"\equals{SortType{}, SortGeneratedTopCell{}}(VarT:SortType{}, ",
        r"arrow{}(arrow{}(Var'Ques'T3:SortType{}, Var'Ques'Te1:SortType{}), ",
        r"arrow{}(arrow{}(Var'Ques'Tx1:SortType{}, Var'Ques'T3:SortType{}), ",
        r"arrow{}(Var'Ques'Tx1:SortType{}, Var'Ques'Te1:SortType{}))))",
    ))
    .unwrap();
    let actual = parse_pattern(concat!(
        r"\equals{SortType{}, SortGeneratedTopCell{}}(VarT:SortType{}, ",
        r"arrow{}(arrow{}(Var'Ques'T2:SortType{}, Var'Ques'Te1:SortType{}), ",
        r"arrow{}(arrow{}(Var'Ques'T3:SortType{}, Var'Ques'T2:SortType{}), ",
        r"arrow{}(Var'Ques'T3:SortType{}, Var'Ques'Te1:SortType{}))))",
    ))
    .unwrap();
    let normalized = normalize_execution_pattern(reference);
    assert_eq!(normalized, normalize_execution_pattern(actual));
    // The search pattern's own variable keeps its name; every `?` instance is renamed.
    let rendered = normalized.to_string();
    assert!(rendered.contains("VarT:SortType{}"), "{rendered}");
    assert!(!rendered.contains("Var'Ques'"), "{rendered}");
    assert!(
        rendered.contains("Var'Hash'KDiff2:SortType{}"),
        "{rendered}"
    );
}

#[test]
fn execution_normalizer_keeps_lost_sharing_between_rule_existentials() {
    let shared = parse_pattern(r"arrow{}(Var'Ques'A1:S{}, Var'Ques'A1:S{})").unwrap();
    let distinct = parse_pattern(r"arrow{}(Var'Ques'A1:S{}, Var'Ques'B1:S{})").unwrap();
    assert_ne!(
        normalize_execution_pattern(shared),
        normalize_execution_pattern(distinct)
    );
}

#[test]
fn execution_normalizer_keeps_uncounted_existentials_and_pattern_variables_fixed() {
    assert!(existential_generated_name("Var'Ques'X0"));
    assert!(existential_generated_name("Var'Ques'Tx1"));
    assert!(!existential_generated_name("Var'Ques'X"));
    assert!(!existential_generated_name("Var'Ques'1"));
    assert!(!existential_generated_name("Var'Ques'X'Hash'KDiff0"));
    assert!(!execution_generated_name("Var'Ques'X"));
    assert!(!execution_generated_name("VarT"));
    assert!(!execution_generated_name("VarT1"));
    assert!(execution_generated_name("Ex-hFrame-b0"));
    assert!(execution_generated_name("Rule-hX"));
    assert!(execution_generated_name("Var'Ques'X-b3"));
    assert!(!execution_generated_name("ExVarI0"));
    assert!(!execution_generated_name("a-x"));
    // Definitions keep their Var'Unds' stem semantics: a `?` variable has no stem there.
    assert_eq!(generated_stem("Var'Unds'X1"), Some("X"));
    assert_eq!(generated_stem("Var'Ques'X1"), None);

    let bare = parse_pattern(r"arrow{}(Var'Ques'X:S{}, VarT:S{})").unwrap();
    let normalized = normalize_execution_pattern(bare.clone());
    assert_eq!(normalized, bare);
    let counted = parse_pattern(r"arrow{}(Var'Ques'X1:S{}, VarT:S{})").unwrap();
    assert_ne!(normalize_execution_pattern(counted), normalized);
}

#[test]
fn execution_normalizer_given_the_pattern_renames_every_other_rule_existential() {
    let pattern = BTreeSet::from(["P".to_owned()]);
    let names = GeneratedNames::shapes_with_pattern_existentials(pattern.clone());
    assert!(rule_existential_name("Var'QuesUnds'X", &pattern));
    assert!(rule_existential_name("Var'Ques'X", &pattern));
    assert!(!rule_existential_name("Var'Ques'P", &pattern));
    assert!(!rule_existential_name("VarX", &pattern));
    assert!(!rule_existential_name("@Var'Ques'X", &pattern));
    // The reference keeps the rule's name and the port mints one: one variable up to its name.
    let reference =
        parse_pattern(r"arrow{}(Var'QuesUnds'X:S{}, arrow{}(Var'QuesUnds'X:S{}, Var'Ques'P:S{}))")
            .unwrap();
    let actual = parse_pattern(
        r"arrow{}(Ex-hVar'QuesUnds'X-b0:S{}, arrow{}(Ex-hVar'QuesUnds'X-b0:S{}, Var'Ques'P:S{}))",
    )
    .unwrap();
    assert_eq!(
        normalize_execution_pattern_with(reference.clone(), &names),
        normalize_execution_pattern_with(actual, &names)
    );
    // Sharing still counts, and the pattern's own variable stays fixed.
    let unshared =
        parse_pattern(r"arrow{}(Var'QuesUnds'X:S{}, arrow{}(Var'QuesUnds'Y:S{}, Var'Ques'P:S{}))")
            .unwrap();
    assert_ne!(
        normalize_execution_pattern_with(reference.clone(), &names),
        normalize_execution_pattern_with(unshared, &names)
    );
    let renamed_pattern =
        parse_pattern(r"arrow{}(Var'QuesUnds'X:S{}, arrow{}(Var'QuesUnds'X:S{}, Var'Ques'Q:S{}))")
            .unwrap();
    assert_ne!(
        normalize_execution_pattern_with(reference, &names),
        normalize_execution_pattern_with(renamed_pattern, &names)
    );
}

#[test]
fn execution_normalizer_preserves_sorts_of_rule_existentials() {
    let reference = parse_pattern(r"arrow{}(Var'Ques'A1:S{}, Var'Ques'B1:T{})").unwrap();
    let actual = parse_pattern(r"arrow{}(Var'Ques'A7:S{}, Var'Ques'B7:S{})").unwrap();
    assert_ne!(
        normalize_execution_pattern(reference),
        normalize_execution_pattern(actual)
    );
}

#[test]
fn execution_predicate_recognizer_matches_the_kore_predicate_constructors() {
    // haskell-backend Kore/Internal/Predicate.hs PredicateF: And, Bottom, Ceil, Equals, Exists,
    // Floor, Forall, Iff, Implies, In, Not, Or, Top.
    for source in [
        r"\not{S{}}(\exists{S{}}(VarX:T{}, \equals{T{}, S{}}(VarX:T{}, a{}())))",
        r"\forall{S{}}(VarX:T{}, \ceil{T{}, S{}}(f{}(VarX:T{})))",
        r"\implies{S{}}(\top{S{}}(), \floor{T{}, S{}}(a{}()))",
        r"\iff{S{}}(\in{T{}, S{}}(a{}(), b{}()), \bottom{S{}}())",
        r"\or{S{}}(\equals{T{}, S{}}(a{}(), b{}()), \and{S{}}(\top{S{}}(), \equals{T{}, S{}}(a{}(), b{}())))",
    ] {
        let pattern = parse_pattern(source).unwrap();
        assert!(is_predicate_pattern(&pattern), "{source}");
    }
    for source in [
        r"\exists{S{}}(VarX:T{}, f{}(VarX:T{}))",
        r"\and{S{}}(a{}(), \top{S{}}())",
        r"\next{S{}}(\top{S{}}())",
    ] {
        let pattern = parse_pattern(source).unwrap();
        assert!(!is_predicate_pattern(&pattern), "{source}");
    }
    let disjunct = parse_pattern(
        r"\and{S{}}(t{}(), \not{S{}}(\exists{S{}}(VarX:T{}, \equals{T{}, S{}}(VarX:T{}, a{}()))))",
    )
    .unwrap();
    let (term, constraints) = split_constrained(&disjunct);
    assert_eq!(term.to_string(), "t{}()");
    assert_eq!(constraints.len(), 1);
}

#[test]
fn constraint_pairing_aligns_constraint_only_variables_onto_the_reference_names() {
    // The constraints are spelled differently (the reference's \ceil against the port's
    // \not(true = in(...))), so N4's first-occurrence indices diverge: the reference names its Map
    // variable first, the port its KItem variable. Pairing must try the bijection that maps the
    // port's free constraint-only variables onto the reference's names per sort.
    let reference = normalize_execution_pattern(
        parse_pattern(concat!(
            r"\and{S{}}(t{}(), \ceil{Map{}, S{}}(g{}(Var'Unds'B1:Map{})), ",
            r#"\equals{Bool{}, S{}}(\dv{Bool{}}("false"), q{}(Var'Unds'A1:KI{})))"#,
        ))
        .unwrap(),
    );
    let actual = normalize_execution_pattern(
        parse_pattern(concat!(
            r#"\and{S{}}(t{}(), \equals{Bool{}, S{}}(\dv{Bool{}}("false"), q{}(Ex-hA-b0:KI{})), "#,
            r#"\not{S{}}(\equals{Bool{}, S{}}(\dv{Bool{}}("true"), in{}(Ex-hB-b0:Map{}))))"#,
        ))
        .unwrap(),
    );
    let aligned_variable = r"Var'Hash'KDiff0:Map{}";
    assert!(
        reference.to_string().contains(aligned_variable),
        "{reference}"
    );
    assert!(!actual.to_string().contains(aligned_variable), "{actual}");

    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = env::temp_dir().join(format!(
        "k-rust-alignment-fake-{}-{nonce}",
        std::process::id()
    ));
    fs::create_dir(&directory).unwrap();
    let calls = directory.join("calls");
    let needle = directory.join("needle");
    fs::write(&needle, aligned_variable).unwrap();
    let oracle = directory.join("aligned-only-krust");
    // Valid only when both sides carry the reference's Map variable name.
    fs::write(
        &oracle,
        format!(
            "#!/usr/bin/env bash\nprintf '%s\\n' \"$*\" >>{calls}\nwhile (($#)); do case $1 in --antecedent) a=$2;; --consequent) c=$2;; esac; shift; done\nif grep -qFf {needle} \"$a\" && grep -qFf {needle} \"$c\"; then printf '{{\"status\":\"valid\"}}\\n'; else printf '{{\"status\":\"invalid\"}}\\n'; fi\n",
            calls = calls.display(),
            needle = needle.display(),
        ),
    )
    .unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut permissions = fs::metadata(&oracle).unwrap().permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&oracle, permissions).unwrap();
    }
    let definition = directory.join("definition.kore");
    fs::write(&definition, "[]").unwrap();
    let result = compare_execution_modulo_implication(
        &reference,
        &actual,
        Some(ImplicationOracle {
            krust: &oracle,
            definition: &definition,
        }),
        "TEST",
    );
    result.expect("the aligned bijection pairs the remainders");
    let calls = fs::read_to_string(&calls).unwrap();
    assert!(
        calls.lines().count() >= 3,
        "the identity candidate fails before the aligned one succeeds: {calls}"
    );
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn implication_fallback_checks_both_directions_and_requires_valid() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = env::temp_dir().join(format!(
        "k-rust-implication-fake-{}-{nonce}",
        std::process::id()
    ));
    fs::create_dir(&directory).unwrap();
    let calls = directory.join("calls");
    let valid = directory.join("valid-krust");
    let invalid = directory.join("invalid-krust");
    fs::write(
        &valid,
        format!(
            "#!/usr/bin/env bash\nprintf '%s\\n' \"$*\" >>{}\nprintf '{{\"status\":\"valid\"}}\\n'\n",
            calls.display()
        ),
    )
    .unwrap();
    fs::write(
        &invalid,
        "#!/usr/bin/env bash\nprintf '{\"status\":\"indeterminate\"}\\n'\n",
    )
    .unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        for path in [&valid, &invalid] {
            let mut permissions = fs::metadata(path).unwrap().permissions();
            permissions.set_mode(0o755);
            fs::set_permissions(path, permissions).unwrap();
        }
    }
    let reference = normalize_execution_pattern(
        parse_pattern(r"\and{S{}}(f{}(Var'Unds'X1:S{}), \top{S{}}())").unwrap(),
    );
    let actual = normalize_execution_pattern(
        parse_pattern(
            r"\and{S{}}(f{}(Var'Unds'X9:S{}), \equals{S{}, S{}}(Var'Unds'X9:S{}, Var'Unds'X9:S{}))",
        )
        .unwrap(),
    );
    let definition = directory.join("definition.kore");
    fs::write(&definition, "[]").unwrap();

    prove_implication_both_ways_with(&valid, &reference, &actual, &definition, "TEST")
        .expect("both valid directions");
    let calls = fs::read_to_string(&calls).unwrap();
    assert_eq!(calls.lines().count(), 2, "both implication directions");
    assert!(calls.lines().all(|line| line.contains("--module TEST")));
    assert!(
        calls
            .lines()
            .all(|line| line.contains(definition.to_str().unwrap()))
    );

    let error =
        prove_implication_both_ways_with(&invalid, &reference, &actual, &definition, "TEST")
            .expect_err("an indeterminate answer cannot certify equivalence");
    assert!(error.contains("not valid"), "{error}");
    fs::remove_dir_all(directory).unwrap();
}

/// The exact execution comparison never lets the port's simplifier remove a disjunct of either
/// side: the simplifier is code under test and shares its constructor-domain checks and SMT layer
/// with the executor, so a defect that loses a feasible branch in the port's execution could
/// otherwise remove the reference's copy of that branch and turn the difference into a pass. Here a
/// fake `krust kore-simplify` reduces every pattern to `\bottom` (a defect of that kind); a port
/// result missing a reference branch, or holding an extra one, still fails, and the comparison
/// never asks for a simplification. Reference results that only the reference's own simplifier
/// reduces are handled per case by the execution gate (N41).
#[test]
fn execution_comparator_never_asks_the_port_simplifier_to_drop_disjuncts() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = env::temp_dir().join(format!(
        "k-rust-execution-no-simplify-{}-{nonce}",
        std::process::id()
    ));
    fs::create_dir(&directory).unwrap();
    let calls = directory.join("calls");
    let krust = directory.join("krust");
    fs::write(
        &krust,
        format!(
            "#!/usr/bin/env bash\nprintf '%s\\n' \"$*\" >>{calls}\n[[ $1 == kore-simplify ]] || exit 3\nprintf '\\\\bottom{{S{{}}}}()\\n'\n",
            calls = calls.display(),
        ),
    )
    .unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut permissions = fs::metadata(&krust).unwrap().permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&krust, permissions).unwrap();
    }
    let definition = directory.join("definition.kore");
    fs::write(&definition, "[]").unwrap();
    let oracle = ImplicationOracle {
        krust: &krust,
        definition: &definition,
    };
    let pattern = |text: &str| normalize_execution_pattern(parse_pattern(text).unwrap());

    let reference = pattern(r#"\or{S{}}(t{}(\dv{Int{}}("1")), t{}(\dv{Int{}}("2")))"#);
    let error = compare_execution_modulo_implication(
        &reference,
        &pattern(r#"t{}(\dv{Int{}}("1"))"#),
        Some(oracle),
        "TEST",
    )
    .expect_err("a reference branch the port lost fails");
    assert!(error.contains("unpaired"), "{error}");
    let error = compare_execution_modulo_implication(
        &pattern(r#"t{}(\dv{Int{}}("1"))"#),
        &pattern(r#"\or{S{}}(t{}(\dv{Int{}}("1")), t{}(\dv{Int{}}("3")))"#),
        Some(oracle),
        "TEST",
    )
    .expect_err("a port branch the reference lacks fails");
    assert!(
        error.contains(r#"unpaired disjunct: t{}(\dv{Int{}}("3"))"#),
        "{error}"
    );
    let error = compare_execution_modulo_implication(
        &reference,
        &pattern(r"\bottom{S{}}()"),
        Some(oracle),
        "TEST",
    )
    .expect_err("a reference the port's simplifier calls \\bottom is still compared as it is");
    assert!(error.contains("unpaired"), "{error}");
    let calls = fs::read_to_string(&calls).unwrap_or_default();
    assert!(
        !calls.contains("kore-simplify"),
        "the comparison asked the port's simplifier: {calls}"
    );
    fs::remove_dir_all(directory).unwrap();
}

fn normalize_execution_pattern(pattern: Pattern) -> Pattern {
    normalize_execution_pattern_with(pattern, &GeneratedNames::shapes())
}

/// Normalize a result whose fixed variable names are the free variables of `initial`.
fn normalize_execution_pattern_fixing(pattern: Pattern, initial: &Pattern) -> Pattern {
    normalize_execution_pattern_with(pattern, &GeneratedNames::fixing(initial))
}

fn normalize_execution_pattern_with(pattern: Pattern, names: &GeneratedNames) -> Pattern {
    let pattern = normalize_execution_structure(pattern);
    match &pattern {
        Pattern::Or { sort, arguments } => {
            // Disjunction order is semantically empty, so execution
            // gates compare a sorted multiset and retain multiplicity:
            // duplicate final configurations are a backend defect, not a gate normalization.
            let mut arguments = arguments
                .iter()
                .cloned()
                .map(|disjunct| normalize_execution_disjunct(disjunct, names))
                .collect::<Vec<_>>();
            arguments.sort();
            Pattern::Or {
                sort: sort.clone(),
                arguments,
            }
        }
        _ => normalize_execution_disjunct(pattern, names),
    }
}

fn normalize_execution_disjunct(mut pattern: Pattern, names: &GeneratedNames) -> Pattern {
    // N16: a variable not free in the initial pattern is existentially quantified over its
    // disjunct (docs/compatibility.md#execution-results), so an outer binder of a generated
    // variable denotes the same disjunct as its body. A binder of an initial-pattern variable
    // cuts the result's link to the query's valuation of it, so stripping stops there and the
    // rest of the prefix is compared as printed.
    while let Pattern::Exists { variable, body, .. } = &mut pattern
        && names.is_generated(variable)
    {
        pattern = std::mem::replace(body.as_mut(), Pattern::String(String::new().into()));
    }
    normalize_conjunctions(&mut pattern);
    canonicalize_remainder_existentials(&mut pattern, names);
    normalize_execution_equalities(&mut pattern);
    canonicalize_commuting_quantifier_chains(&mut pattern);
    alpha_normalize_bound_variables(&mut pattern);
    rename_execution_variables(&mut pattern, names);
    pattern
}

type KoreVariable = k_rust::kore::ast::Variable;

/// N4 for execution results: which result variables carry an engine-chosen name.
///
/// Kore prints a rule variable that survives into a result under its rule name (`VarI`,
/// `Var'Unds'K`), the NewUnifier's AC remainder as `VarAC<n>'Unds'<counter>`
/// (NewUnifier.hs:1302, externalizeFreshVariableName) and the port prints the same variables
/// with encoded `Ex#`/`Eq#`/`Rule#` markers or `!` counters. Both print
/// an instantiated rule existential as `Var'Ques'<stem><counter>` with their own counters
/// (`existential_generated_name`). Only the free variables of the initial pattern are fixed names
/// shared by both engines.
struct GeneratedNames {
    fixed: Option<BTreeSet<String>>,
    /// Without an initial pattern: when given, the K names (without `?`) of the search
    /// pattern's `?` variables, and every other `?` variable of a result is an instance of a
    /// rule existential, whatever its name (`rule_existential_name`).
    pattern_existentials: Option<BTreeSet<String>>,
}

impl GeneratedNames {
    /// Recognize generated names by their shape only (no initial pattern available).
    fn shapes() -> Self {
        Self {
            fixed: None,
            pattern_existentials: None,
        }
    }

    /// Recognize generated names by their shape, and every `?` variable other than the
    /// search pattern's `pattern_existentials` as a rule existential.
    fn shapes_with_pattern_existentials(pattern_existentials: BTreeSet<String>) -> Self {
        Self {
            fixed: None,
            pattern_existentials: Some(pattern_existentials),
        }
    }

    /// Every variable that is not free in `initial` is generated.
    fn fixing(initial: &Pattern) -> Self {
        Self {
            fixed: Some(
                initial
                    .free_variables()
                    .into_iter()
                    .map(|variable| variable.name)
                    .collect(),
            ),
            pattern_existentials: None,
        }
    }

    fn is_generated(&self, variable: &KoreVariable) -> bool {
        if variable.name.contains(CANONICAL_NAME) {
            return false;
        }
        match &self.fixed {
            Some(fixed) => !fixed.contains(&variable.name),
            None => {
                execution_generated_name(&variable.name)
                    || self
                        .pattern_existentials
                        .as_ref()
                        .is_some_and(|pattern| rule_existential_name(&variable.name, pattern))
            }
        }
    }
}

/// N4 given the search pattern's `?` variables: whether `name` is a K `?` variable
/// (`Var'Ques'X` for `?X`) that the search pattern does not declare.
///
/// A `?` variable of a rule's right-hand side is existentially quantified over the rule's
/// result, so an instance of it in an execution result is quantified over its disjunct
/// (docs/compatibility.md#result-variables) whatever name an engine prints it under: under its
/// rule name `Var'Ques'X` when that name is free, with a counter, or with the port's marker.
/// The only other `?` variables a result can hold are the search pattern's, which the request
/// names, so a caller that lists them separates the two.
fn rule_existential_name(name: &str, pattern_existentials: &BTreeSet<String>) -> bool {
    match k_rust::kast::identifier::decode_variable(name) {
        (k_rust::kore::ast::VariableKind::Element, Ok(decoded)) => decoded
            .strip_prefix('?')
            .is_some_and(|declared| !pattern_existentials.contains(declared)),
        _ => false,
    }
}

const CANONICAL_NAME: &str = "Var'Hash'KDiff";

fn is_canonical_free_name(name: &str) -> bool {
    name.strip_prefix(CANONICAL_NAME).is_some_and(|suffix| {
        !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
    })
}

fn execution_generated_name(name: &str) -> bool {
    if let Ok(decoded) = k_rust_backend::term::names::decode_variable_name(name)
        && (decoded.contains('!')
            || k_rust_backend::term::names::split_marker(
                &decoded,
                &k_rust_backend::term::names::VariableProvenance::ALL,
            )
            .0
            .is_some())
    {
        return true;
    }
    if generated_stem(name).is_some() || existential_generated_name(name) {
        return true;
    }
    // Kore/Unification/NewUnifier.hs:1302: generatedId "VarAC<n>'Unds'" plus the fresh counter.
    if let Some((index, counter)) = name
        .strip_prefix("VarAC")
        .and_then(|rest| rest.split_once("'Unds'"))
    {
        let digits =
            |text: &str| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit());
        if digits(index) && digits(counter) {
            return true;
        }
    }
    false
}

/// N4: a reference engine's instantiated rule existential, `Var'Ques'<stem><digits>`.
///
/// K compiles a rule's `?X` to the KORE variable `Var'Ques'X`. When the rule applies, Kore
/// refreshes it with a fresh counter and prints the instance by appending the counter's digits to
/// the base. The port encodes its `Var'Ques'X!3` as `Var'Ques'X-b3`; that spelling is recognized
/// by `execution_generated_name`. The counters and the unification representative each keeps
/// are engine-chosen. A bare `Var'Ques'X` (no counter) is a rule or
/// search-pattern variable printed under its own name and stays fixed in shapes mode.
fn existential_generated_name(name: &str) -> bool {
    counted_stem("Var'Ques'", name).is_some()
}

/// N21: flatten nested same-sort conjunctions and drop duplicated conjuncts.
///
/// Kore prints a rewritten branch as `\and(\and(term, predicate), substitution)` with
/// right-nested predicate conjunctions that may repeat a conjunct (the remainder repeats the
/// `in_keys` condition of the AC solution), while the port prints one flat conjunction.
fn normalize_conjunctions(pattern: &mut Pattern) {
    match pattern {
        Pattern::And { sort, arguments } => {
            let mut flattened = Vec::new();
            for mut argument in std::mem::take(arguments) {
                normalize_conjunctions(&mut argument);
                let nested = match &mut argument {
                    Pattern::And {
                        sort: nested_sort,
                        arguments: nested,
                    } if *nested_sort == *sort => Some(std::mem::take(nested)),
                    _ => None,
                };
                if let Some(mut nested) = nested {
                    flattened.append(&mut nested);
                } else {
                    flattened.push(argument);
                }
            }
            let mut deduplicated: Vec<Pattern> = Vec::with_capacity(flattened.len());
            for argument in flattened {
                if !deduplicated.contains(&argument) {
                    deduplicated.push(argument);
                }
            }
            deduplicated.sort();
            *arguments = deduplicated;
        }
        Pattern::Application { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => {
            for argument in arguments {
                normalize_conjunctions(argument);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => normalize_conjunctions(argument),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            normalize_conjunctions(left);
            normalize_conjunctions(right);
        }
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => normalize_conjunctions(body),
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }
}

/// N24: use one orientation for symmetric equalities and for false Boolean predicates.
fn normalize_execution_equalities(pattern: &mut Pattern) {
    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => {
            for argument in arguments {
                normalize_execution_equalities(argument);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => normalize_execution_equalities(argument),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::In { left, right, .. } => {
            normalize_execution_equalities(left);
            normalize_execution_equalities(right);
        }
        Pattern::Equals { left, right, .. } => {
            normalize_execution_equalities(left);
            normalize_execution_equalities(right);
        }
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => normalize_execution_equalities(body),
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }

    let Pattern::Equals {
        operand_sort,
        result_sort,
        left,
        right,
    } = pattern
    else {
        return;
    };
    let boolean_sort = matches!(
        &**operand_sort,
        k_rust::kore::ast::Sort::Application { name, arguments }
            if name == "SortBool" && arguments.is_empty()
    );
    let literal = |candidate: &Pattern, value: &str| {
        matches!(
            candidate,
            Pattern::DomainValue { sort, value: actual }
                if *sort == **operand_sort && actual == value
        )
    };
    let false_complement = if literal(left, "false") {
        Some(&**right)
    } else if literal(right, "false") {
        Some(&**left)
    } else {
        None
    };
    let is_k_result = |candidate: &Pattern| {
        matches!(
            candidate,
            Pattern::Application { symbol, .. } if symbol.name == "LblisKResult"
        )
    };
    if boolean_sort && false_complement.is_some_and(is_k_result) {
        let term = false_complement.expect("checked above").clone();
        *pattern = Pattern::Not {
            sort: result_sort.clone(),
            argument: Box::new(Pattern::Equals {
                operand_sort: operand_sort.clone(),
                result_sort: result_sort.clone(),
                left: Box::new(Pattern::DomainValue {
                    sort: operand_sort.as_ref().clone(),
                    value: "true".into(),
                }),
                right: Box::new(term),
            }),
        };
    } else if (boolean_sort && literal(right, "true"))
        || (!(boolean_sort && literal(left, "true")) && **right < **left)
    {
        std::mem::swap(left, right);
    }
}

/// N22: quantify a generated variable that is local to a negated existential.
///
/// Kore's remainder `\not(\exists rule variables. solution)` quantifies only the rule variables
/// (Kore/Rewrite/Remainder.hs existentiallyQuantifyRuleVariables) and leaves the fresh AC
/// remainder of the unification solution free although it occurs nowhere else in the disjunct;
/// the port quantifies that variable inside the negation, which is the reading under which the
/// remainder excludes every instance of the rule.
fn canonicalize_remainder_existentials(pattern: &mut Pattern, names: &GeneratedNames) {
    let conjuncts: Vec<&Pattern> = match &*pattern {
        Pattern::And { arguments, .. } => arguments.iter().collect(),
        single => vec![single],
    };
    let free_of = Pattern::free_variables;
    let free_per_conjunct = conjuncts
        .iter()
        .map(|conjunct| free_of(conjunct))
        .collect::<Vec<_>>();
    let mut additions = Vec::new();
    for (index, conjunct) in conjuncts.iter().enumerate() {
        let Pattern::Not { argument, .. } = conjunct else {
            continue;
        };
        if !matches!(**argument, Pattern::Exists { .. }) {
            continue;
        }
        let local = free_per_conjunct[index]
            .iter()
            .filter(|variable| names.is_generated(variable))
            .filter(|variable| {
                free_per_conjunct
                    .iter()
                    .enumerate()
                    .all(|(other, free)| other == index || !free.contains(*variable))
            })
            .cloned()
            .collect::<Vec<_>>();
        if !local.is_empty() {
            additions.push((index, local));
        }
    }
    if additions.is_empty() {
        return;
    }
    let conjuncts: Vec<&mut Pattern> = match pattern {
        Pattern::And { arguments, .. } => arguments.iter_mut().collect(),
        pattern => vec![pattern],
    };
    for (conjunct, (_, local)) in
        conjuncts
            .into_iter()
            .enumerate()
            .filter_map(|(index, conjunct)| {
                additions
                    .iter()
                    .find(|(added, _)| *added == index)
                    .map(|addition| (conjunct, addition))
            })
    {
        let Pattern::Not { argument, .. } = conjunct else {
            unreachable!("recorded above");
        };
        let mut innermost: &mut Pattern = argument;
        let mut sort = None;
        while let Pattern::Exists {
            sort: chain_sort,
            body,
            ..
        } = innermost
        {
            sort = Some(chain_sort.clone());
            innermost = body;
        }
        let sort = sort.expect("recorded as an existential");
        let body = std::mem::replace(innermost, Pattern::String(String::new().into()));
        *innermost = local
            .iter()
            .rev()
            .fold(body, |body, variable| Pattern::Exists {
                sort: sort.clone(),
                variable: Box::new(variable.clone()),
                body: Box::new(body),
            });
    }
}

/// N4 for execution results: rename generated variables by first occurrence in a canonical
/// traversal (term before constraints, conjuncts ordered by their name-erased rendering,
/// quantifier chains ordered by the renamed binder), preserving each variable's sort.
fn rename_execution_variables(pattern: &mut Pattern, names: &GeneratedNames) {
    fn erased_key(pattern: &Pattern, names: &GeneratedNames) -> String {
        fn erase(pattern: &mut Pattern, names: &GeneratedNames) {
            match pattern {
                Pattern::Application { arguments, .. }
                | Pattern::And { arguments, .. }
                | Pattern::Or { arguments, .. }
                | Pattern::AssociativeApplication { arguments, .. } => {
                    for argument in arguments {
                        erase(argument, names);
                    }
                }
                Pattern::Not { argument, .. }
                | Pattern::Next { argument, .. }
                | Pattern::Ceil { argument, .. }
                | Pattern::Floor { argument, .. } => erase(argument, names),
                Pattern::Implies { left, right, .. }
                | Pattern::Iff { left, right, .. }
                | Pattern::Rewrites { left, right, .. }
                | Pattern::Equals { left, right, .. }
                | Pattern::In { left, right, .. } => {
                    erase(left, names);
                    erase(right, names);
                }
                Pattern::Exists { variable, body, .. }
                | Pattern::Forall { variable, body, .. }
                | Pattern::Mu { variable, body }
                | Pattern::Nu { variable, body } => {
                    if names.is_generated(variable) {
                        variable.name = CANONICAL_NAME.to_owned();
                    }
                    erase(body, names);
                }
                Pattern::Variable(variable) => {
                    if names.is_generated(variable) {
                        variable.name = CANONICAL_NAME.to_owned();
                    }
                }
                Pattern::String(_)
                | Pattern::Top { .. }
                | Pattern::Bottom { .. }
                | Pattern::DomainValue { .. } => {}
            }
        }
        let mut erased = pattern.clone();
        erase(&mut erased, names);
        erased.to_string()
    }

    fn order_conjuncts(pattern: &mut Pattern, names: &GeneratedNames) {
        match pattern {
            Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => {
                for argument in arguments.iter_mut() {
                    order_conjuncts(argument, names);
                }
                // The term of a constrained pattern leads so that its variables take the
                // first indices on both sides; constraints follow in name-erased order.
                arguments.sort_by_cached_key(|argument| {
                    (is_predicate_pattern(argument), erased_key(argument, names))
                });
            }
            Pattern::Application { arguments, .. }
            | Pattern::AssociativeApplication { arguments, .. } => {
                for argument in arguments {
                    order_conjuncts(argument, names);
                }
            }
            Pattern::Not { argument, .. }
            | Pattern::Next { argument, .. }
            | Pattern::Ceil { argument, .. }
            | Pattern::Floor { argument, .. } => order_conjuncts(argument, names),
            Pattern::Implies { left, right, .. }
            | Pattern::Iff { left, right, .. }
            | Pattern::Rewrites { left, right, .. }
            | Pattern::Equals { left, right, .. }
            | Pattern::In { left, right, .. } => {
                order_conjuncts(left, names);
                order_conjuncts(right, names);
            }
            Pattern::Exists { body, .. }
            | Pattern::Forall { body, .. }
            | Pattern::Mu { body, .. }
            | Pattern::Nu { body, .. } => order_conjuncts(body, names),
            Pattern::String(_)
            | Pattern::Variable(_)
            | Pattern::Top { .. }
            | Pattern::Bottom { .. }
            | Pattern::DomainValue { .. } => {}
        }
    }

    fn rename(
        variable: &mut KoreVariable,
        names: &GeneratedNames,
        indices: &mut BTreeMap<String, usize>,
    ) {
        if !names.is_generated(variable) {
            return;
        }
        let next = indices.len();
        let index = *indices.entry(variable.name.clone()).or_insert(next);
        variable.name = format!("{CANONICAL_NAME}{index}");
    }

    #[derive(Clone, Copy, PartialEq)]
    enum Quantifier {
        Exists,
        Forall,
    }

    fn assign(
        pattern: &mut Pattern,
        names: &GeneratedNames,
        indices: &mut BTreeMap<String, usize>,
    ) {
        match pattern {
            Pattern::Application { arguments, .. }
            | Pattern::And { arguments, .. }
            | Pattern::Or { arguments, .. }
            | Pattern::AssociativeApplication { arguments, .. } => {
                for argument in arguments {
                    assign(argument, names, indices);
                }
            }
            Pattern::Not { argument, .. }
            | Pattern::Next { argument, .. }
            | Pattern::Ceil { argument, .. }
            | Pattern::Floor { argument, .. } => assign(argument, names, indices),
            Pattern::Implies { left, right, .. }
            | Pattern::Iff { left, right, .. }
            | Pattern::Rewrites { left, right, .. }
            | Pattern::Equals { left, right, .. }
            | Pattern::In { left, right, .. } => {
                assign(left, names, indices);
                assign(right, names, indices);
            }
            Pattern::Exists { .. } | Pattern::Forall { .. } => {
                let quantifier = if matches!(pattern, Pattern::Exists { .. }) {
                    Quantifier::Exists
                } else {
                    Quantifier::Forall
                };
                let mut current = std::mem::replace(pattern, Pattern::String(String::new().into()));
                let mut binders = Vec::new();
                loop {
                    let fields = match (quantifier, &mut current) {
                        (
                            Quantifier::Exists,
                            Pattern::Exists {
                                sort,
                                variable,
                                body,
                            },
                        )
                        | (
                            Quantifier::Forall,
                            Pattern::Forall {
                                sort,
                                variable,
                                body,
                            },
                        ) => Some((
                            sort.clone(),
                            variable.clone(),
                            std::mem::replace(body.as_mut(), Pattern::String(String::new().into())),
                        )),
                        _ => None,
                    };
                    let Some((sort, variable, body)) = fields else {
                        break;
                    };
                    binders.push((sort, variable));
                    current = body;
                }
                // Binders take their index from the body so that the chain order, which the
                // engines choose differently, does not influence the canonical names.
                assign(&mut current, names, indices);
                for (_, variable) in &mut binders {
                    rename(variable, names, indices);
                }
                binders.sort_by(|(_, left), (_, right)| left.cmp(right));
                *pattern = binders
                    .into_iter()
                    .rev()
                    .fold(current, |body, (sort, variable)| match quantifier {
                        Quantifier::Exists => Pattern::Exists {
                            sort,
                            variable,
                            body: Box::new(body),
                        },
                        Quantifier::Forall => Pattern::Forall {
                            sort,
                            variable,
                            body: Box::new(body),
                        },
                    });
            }
            Pattern::Mu { variable, body } | Pattern::Nu { variable, body } => {
                rename(variable, names, indices);
                assign(body, names, indices);
            }
            Pattern::Variable(variable) => rename(variable, names, indices),
            Pattern::String(_)
            | Pattern::Top { .. }
            | Pattern::Bottom { .. }
            | Pattern::DomainValue { .. } => {}
        }
    }

    order_conjuncts(pattern, names);
    assign(pattern, names, &mut BTreeMap::new());
}

fn normalize_execution_structure(pattern: Pattern) -> Pattern {
    match &pattern {
        Pattern::Application { symbol, arguments } => {
            let arguments = arguments
                .iter()
                .cloned()
                .map(normalize_execution_structure)
                .collect::<Vec<_>>();
            if matches!(
                symbol.name.as_str(),
                "Lbl'Unds'Map'Unds'" | "Lbl'Unds'Set'Unds'"
            ) {
                let mut flattened = Vec::new();
                for argument in arguments {
                    flatten_collection(symbol, argument, &mut flattened);
                }
                flattened.sort();
                let mut flattened = flattened.into_iter().rev();
                let mut result = flattened
                    .next()
                    .expect("collection concatenation is binary");
                for argument in flattened {
                    result = Pattern::Application {
                        symbol: symbol.clone(),
                        arguments: vec![argument, result],
                    };
                }
                result
            } else {
                Pattern::Application {
                    symbol: symbol.clone(),
                    arguments,
                }
            }
        }
        Pattern::And { sort, arguments } => Pattern::And {
            sort: sort.clone(),
            arguments: arguments
                .iter()
                .cloned()
                .map(normalize_execution_structure)
                .collect(),
        },
        Pattern::Or { sort, arguments } => {
            let mut flattened = Vec::new();
            for mut argument in arguments.iter().cloned().map(normalize_execution_structure) {
                let nested = match &mut argument {
                    Pattern::Or {
                        sort: nested_sort,
                        arguments,
                    } if nested_sort == sort => Some(std::mem::take(arguments)),
                    _ => None,
                };
                if let Some(mut nested) = nested {
                    flattened.append(&mut nested);
                } else {
                    flattened.push(argument);
                }
            }
            flattened.sort();
            Pattern::Or {
                sort: sort.clone(),
                arguments: flattened,
            }
        }
        Pattern::Not { sort, argument } => Pattern::Not {
            sort: sort.clone(),
            argument: Box::new(normalize_execution_structure((**argument).clone())),
        },
        Pattern::Next { sort, argument } => Pattern::Next {
            sort: sort.clone(),
            argument: Box::new(normalize_execution_structure((**argument).clone())),
        },
        Pattern::Implies { sort, left, right } => Pattern::Implies {
            sort: sort.clone(),
            left: Box::new(normalize_execution_structure((**left).clone())),
            right: Box::new(normalize_execution_structure((**right).clone())),
        },
        Pattern::Iff { sort, left, right } => Pattern::Iff {
            sort: sort.clone(),
            left: Box::new(normalize_execution_structure((**left).clone())),
            right: Box::new(normalize_execution_structure((**right).clone())),
        },
        Pattern::Rewrites { sort, left, right } => Pattern::Rewrites {
            sort: sort.clone(),
            left: Box::new(normalize_execution_structure((**left).clone())),
            right: Box::new(normalize_execution_structure((**right).clone())),
        },
        Pattern::Exists {
            sort,
            variable,
            body,
        } => Pattern::Exists {
            sort: sort.clone(),
            variable: variable.clone(),
            body: Box::new(normalize_execution_structure((**body).clone())),
        },
        Pattern::Forall {
            sort,
            variable,
            body,
        } => Pattern::Forall {
            sort: sort.clone(),
            variable: variable.clone(),
            body: Box::new(normalize_execution_structure((**body).clone())),
        },
        Pattern::Mu { variable, body } => Pattern::Mu {
            variable: variable.clone(),
            body: Box::new(normalize_execution_structure((**body).clone())),
        },
        Pattern::Nu { variable, body } => Pattern::Nu {
            variable: variable.clone(),
            body: Box::new(normalize_execution_structure((**body).clone())),
        },
        Pattern::Ceil {
            operand_sort,
            result_sort,
            argument,
        } => Pattern::Ceil {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            argument: Box::new(normalize_execution_structure((**argument).clone())),
        },
        Pattern::Floor {
            operand_sort,
            result_sort,
            argument,
        } => Pattern::Floor {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            argument: Box::new(normalize_execution_structure((**argument).clone())),
        },
        Pattern::Equals {
            operand_sort,
            result_sort,
            left,
            right,
        } => Pattern::Equals {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            left: Box::new(normalize_execution_structure((**left).clone())),
            right: Box::new(normalize_execution_structure((**right).clone())),
        },
        Pattern::In {
            operand_sort,
            result_sort,
            left,
            right,
        } => Pattern::In {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            left: Box::new(normalize_execution_structure((**left).clone())),
            right: Box::new(normalize_execution_structure((**right).clone())),
        },
        Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } => Pattern::AssociativeApplication {
            associativity: *associativity,
            symbol: symbol.clone(),
            arguments: arguments
                .iter()
                .cloned()
                .map(normalize_execution_structure)
                .collect(),
        },
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => pattern,
    }
}

fn flatten_collection(symbol: &Symbol, mut pattern: Pattern, output: &mut Vec<Pattern>) {
    let nested_arguments = match &mut pattern {
        Pattern::Application {
            symbol: nested,
            arguments,
        } if *nested == *symbol => Some(std::mem::take(arguments)),
        _ => None,
    };
    if let Some(arguments) = nested_arguments {
        for argument in arguments {
            flatten_collection(symbol, argument, output);
        }
    } else {
        output.push(pattern);
    }
}

fn compare_execution_modulo_implication(
    reference: &Pattern,
    actual: &Pattern,
    oracle: Option<ImplicationOracle>,
    module: &str,
) -> Result<(), String> {
    compare_execution_disjuncts(reference, actual, oracle, module, None)
}

fn compare_execution_modulo_gotstuck(
    reference: &Pattern,
    actual: &Pattern,
    stop_leaves: &Pattern,
    oracle: Option<ImplicationOracle>,
    module: &str,
) -> Result<(), String> {
    compare_execution_disjuncts(reference, actual, oracle, module, Some(stop_leaves))
}

fn compare_execution_disjuncts(
    reference: &Pattern,
    actual: &Pattern,
    oracle: Option<ImplicationOracle>,
    module: &str,
    expected_unpaired_actual: Option<&Pattern>,
) -> Result<(), String> {
    if reference == actual {
        return match expected_unpaired_actual {
            Some(stop_leaves) if !is_empty_disjunction(stop_leaves) => Err(
                "oracle exception no longer needed: no GotStuck leaves are missing from the reference"
                    .into(),
            ),
            _ => Ok(()),
        };
    }

    let reference_disjuncts = execution_disjuncts(reference);
    let actual_disjuncts = execution_disjuncts(actual);
    let paired_actual = pair_disjuncts(
        &reference_disjuncts,
        &actual_disjuncts,
        PairingDriver::Reference,
        oracle,
        module,
    )?;
    let unpaired_actual = paired_actual
        .iter()
        .enumerate()
        .filter(|(_, paired)| !**paired)
        .map(|(index, _)| actual_disjuncts[index])
        .collect::<Vec<_>>();
    if let Some(expected) = expected_unpaired_actual {
        let mut expected = execution_disjuncts(expected)
            .into_iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        let mut unpaired = unpaired_actual
            .iter()
            .map(|pattern| pattern.to_string())
            .collect::<Vec<_>>();
        expected.sort();
        unpaired.sort();
        if unpaired != expected {
            let term = unpaired_actual
                .first()
                .map(|pattern| split_constrained(pattern).0.to_string())
                .unwrap_or_else(|| "<none>".into());
            return Err(format!(
                "unpaired disjunct: {term}; GotStuck stop leaves differ (expected {expected:?}, actual {unpaired:?})"
            ));
        }
    } else if let Some(disjunct) = unpaired_actual.first() {
        let (term, _) = split_constrained(disjunct);
        return Err(format!("unpaired disjunct: {term}"));
    }
    Ok(())
}

/// N26: every port disjunct pairs with a distinct reference disjunct (term equal, constraints
/// equal under N4/N15); reference disjuncts may stay unpaired. Used for any-strategy runs, whose
/// result is one member (a concrete run) or a sub-multiset (a symbolic run, where successive
/// remainders can apply further rules) of the reference all-strategy result set. Returns the
/// number of reference disjuncts left unpaired.
fn compare_execution_any_membership(
    reference: &Pattern,
    actual: &Pattern,
    oracle: Option<ImplicationOracle>,
    module: &str,
) -> Result<usize, String> {
    let reference_disjuncts = execution_disjuncts(reference);
    let actual_disjuncts = execution_disjuncts(actual);
    if actual_disjuncts.is_empty() {
        return Err("any-strategy result is empty".into());
    }
    let paired_reference = pair_disjuncts(
        &actual_disjuncts,
        &reference_disjuncts,
        PairingDriver::Actual,
        oracle,
        module,
    )?;
    Ok(paired_reference.iter().filter(|paired| !**paired).count())
}

/// Which side drives a pairing: every driving disjunct needs a partner in the other side's pool.
#[derive(Clone, Copy)]
enum PairingDriver {
    Reference,
    Actual,
}

/// Pair every driving disjunct with a distinct pool disjunct whose term is equal and whose
/// constraints compare equal under `compare_paired_constraints` (N4, N15), in driving order,
/// taking the first unpaired pool candidate. Returns which pool disjuncts were paired; the first
/// driving disjunct without a partner fails.
fn pair_disjuncts(
    driving: &[&Pattern],
    pool: &[&Pattern],
    driver: PairingDriver,
    oracle: Option<ImplicationOracle>,
    module: &str,
) -> Result<Vec<bool>, String> {
    let mut paired = vec![false; pool.len()];
    for driving_disjunct in driving {
        let (driving_term, _) = split_constrained(driving_disjunct);
        let Some((pool_index, pool_disjunct)) =
            pool.iter().enumerate().find(|(index, pool_disjunct)| {
                !paired[*index] && split_constrained(pool_disjunct).0 == driving_term
            })
        else {
            return Err(match driver {
                PairingDriver::Reference => format!("unpaired disjunct: {driving_term}"),
                PairingDriver::Actual => format!("unpaired port disjunct: {driving_term}"),
            });
        };
        paired[pool_index] = true;
        let (reference_disjunct, actual_disjunct) = match driver {
            PairingDriver::Reference => (*driving_disjunct, *pool_disjunct),
            PairingDriver::Actual => (*pool_disjunct, *driving_disjunct),
        };
        let (_, mut reference_constraints) = split_constrained(reference_disjunct);
        reference_constraints.sort();
        compare_paired_constraints(
            reference_disjunct,
            &reference_constraints,
            actual_disjunct,
            oracle,
            module,
        )?;
    }
    Ok(paired)
}

/// Compare the constraints of two disjuncts whose terms paired.
///
/// N4 names generated variables by first occurrence, which the term anchors for every variable
/// it mentions; a variable that occurs only in the constraints (the rule variables and the AC
/// remainder of a negated existential) takes its index from the conjunct order, and the two
/// engines spell the same conjunct differently (`false = t` against `\not(true = t)`, `\ceil`
/// of a set concatenation against `\not(true = in(...))`). So the constraint sets are compared
/// modulo a bijection of those variables within each sort: structurally first, then through the
/// implication oracle (N15), identity first. The search is bounded; a larger group reports the
/// identity failure.
fn compare_paired_constraints(
    reference_disjunct: &Pattern,
    reference_constraints: &[Pattern],
    actual_disjunct: &Pattern,
    oracle: Option<ImplicationOracle>,
    module: &str,
) -> Result<(), String> {
    let (actual_term, _) = split_constrained(actual_disjunct);
    let mut candidates = vec![actual_disjunct.clone()];
    for renaming in constraint_variable_renamings(reference_disjunct, actual_disjunct, actual_term)
    {
        if renaming.is_empty() {
            continue;
        }
        let mut candidate = actual_disjunct.clone();
        apply_variable_renaming(&mut candidate, &renaming);
        canonicalize_quantifier_chains(&mut candidate);
        if !candidates.contains(&candidate) {
            candidates.push(candidate);
        }
    }
    for candidate in &candidates {
        let (_, mut candidate_constraints) = split_constrained(candidate);
        candidate_constraints.sort();
        if reference_constraints == candidate_constraints.as_slice() {
            return Ok(());
        }
    }
    let Some(oracle) = oracle else {
        return Err(format!(
            "constraints differ for paired disjunct {}; K_DIFFERENTIAL_DEFINITION is not set",
            split_constrained(reference_disjunct).0
        ));
    };
    let mut last_error = None;
    for candidate in &candidates {
        match prove_implication_both_ways(oracle, reference_disjunct, candidate, module) {
            Ok(()) => return Ok(()),
            Err(error) => last_error = Some(error),
        }
    }
    Err(last_error.expect("the identity candidate is always tried"))
}

const CONSTRAINT_RENAMING_LIMIT: usize = 24;

/// Every bijection from the canonical generated variables that occur in the actual disjunct
/// but not in its term onto the reference's such variables of the same kind and sort; none
/// when the groups differ in size or the search would exceed `CONSTRAINT_RENAMING_LIMIT`
/// candidates. The caller tries the identity first.
fn constraint_variable_renamings(
    reference_disjunct: &Pattern,
    actual_disjunct: &Pattern,
    actual_term: &Pattern,
) -> Vec<BTreeMap<KoreVariable, String>> {
    fn collect(pattern: &Pattern, output: &mut BTreeSet<KoreVariable>) {
        match pattern {
            Pattern::Application { arguments, .. }
            | Pattern::And { arguments, .. }
            | Pattern::Or { arguments, .. }
            | Pattern::AssociativeApplication { arguments, .. } => {
                for argument in arguments {
                    collect(argument, output);
                }
            }
            Pattern::Not { argument, .. }
            | Pattern::Next { argument, .. }
            | Pattern::Ceil { argument, .. }
            | Pattern::Floor { argument, .. } => collect(argument, output),
            Pattern::Implies { left, right, .. }
            | Pattern::Iff { left, right, .. }
            | Pattern::Rewrites { left, right, .. }
            | Pattern::Equals { left, right, .. }
            | Pattern::In { left, right, .. } => {
                collect(left, output);
                collect(right, output);
            }
            Pattern::Exists { variable, body, .. }
            | Pattern::Forall { variable, body, .. }
            | Pattern::Mu { variable, body }
            | Pattern::Nu { variable, body } => {
                if is_canonical_free_name(&variable.name) {
                    output.insert(variable.as_ref().clone());
                }
                collect(body, output);
            }
            Pattern::Variable(variable) => {
                if is_canonical_free_name(&variable.name) {
                    output.insert(variable.clone());
                }
            }
            Pattern::String(_)
            | Pattern::Top { .. }
            | Pattern::Bottom { .. }
            | Pattern::DomainValue { .. } => {}
        }
    }
    let no_candidates = Vec::new();
    let mut in_term = BTreeSet::new();
    collect(actual_term, &mut in_term);
    let mut actual_variables = BTreeSet::new();
    collect(actual_disjunct, &mut actual_variables);
    let mut reference_variables = BTreeSet::new();
    collect(reference_disjunct, &mut reference_variables);
    let group = |variables: &BTreeSet<KoreVariable>| {
        let mut groups: BTreeMap<_, Vec<KoreVariable>> = BTreeMap::new();
        for variable in variables.difference(&in_term) {
            groups
                .entry((variable.kind, variable.sort.clone()))
                .or_default()
                .push(variable.clone());
        }
        groups
    };
    let actual_groups = group(&actual_variables);
    let reference_groups = group(&reference_variables);
    let mut renamings = vec![BTreeMap::new()];
    for (key, sources) in actual_groups {
        let Some(targets) = reference_groups.get(&key) else {
            return no_candidates;
        };
        if targets.len() != sources.len() {
            return no_candidates;
        }
        let permutations = permutations(targets);
        if renamings.len() * permutations.len() > CONSTRAINT_RENAMING_LIMIT {
            return no_candidates;
        }
        let mut extended = Vec::with_capacity(renamings.len() * permutations.len());
        for base in &renamings {
            for permutation in &permutations {
                let mut renaming = base.clone();
                for (from, to) in sources.iter().zip(permutation) {
                    if from.name != to.name {
                        renaming.insert(from.clone(), to.name.clone());
                    }
                }
                extended.push(renaming);
            }
        }
        renamings = extended;
    }
    renamings
}

/// All orderings of `items`, the given order first.
fn permutations<T: Clone>(items: &[T]) -> Vec<Vec<T>> {
    if items.len() <= 1 {
        return vec![items.to_vec()];
    }
    let mut output = Vec::new();
    for (index, head) in items.iter().enumerate() {
        let mut rest = items.to_vec();
        rest.remove(index);
        for mut tail in permutations(&rest) {
            tail.insert(0, head.clone());
            output.push(tail);
        }
    }
    output
}

/// Order every chain of same-kind quantifiers by its (renamed) binder, as N4's renaming does.
fn canonicalize_quantifier_chains(pattern: &mut Pattern) {
    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => {
            for argument in arguments {
                canonicalize_quantifier_chains(argument);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => canonicalize_quantifier_chains(argument),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            canonicalize_quantifier_chains(left);
            canonicalize_quantifier_chains(right);
        }
        Pattern::Mu { body, .. } | Pattern::Nu { body, .. } => canonicalize_quantifier_chains(body),
        Pattern::Exists { .. } | Pattern::Forall { .. } => {
            let exists = matches!(pattern, Pattern::Exists { .. });
            let mut current = std::mem::replace(pattern, Pattern::String(String::new().into()));
            let mut binders = Vec::new();
            loop {
                let fields = match (exists, &mut current) {
                    (
                        true,
                        Pattern::Exists {
                            sort,
                            variable,
                            body,
                        },
                    )
                    | (
                        false,
                        Pattern::Forall {
                            sort,
                            variable,
                            body,
                        },
                    ) => Some((
                        sort.clone(),
                        variable.clone(),
                        std::mem::replace(body.as_mut(), Pattern::String(String::new().into())),
                    )),
                    _ => None,
                };
                let Some((sort, variable, body)) = fields else {
                    break;
                };
                binders.push((sort, variable));
                current = body;
            }
            canonicalize_quantifier_chains(&mut current);
            binders.sort_by(|(_, left), (_, right)| left.cmp(right));
            *pattern = binders
                .into_iter()
                .rev()
                .fold(current, |body, (sort, variable)| {
                    if exists {
                        Pattern::Exists {
                            sort,
                            variable,
                            body: Box::new(body),
                        }
                    } else {
                        Pattern::Forall {
                            sort,
                            variable,
                            body: Box::new(body),
                        }
                    }
                });
        }
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }
}

fn apply_variable_renaming(pattern: &mut Pattern, renaming: &BTreeMap<KoreVariable, String>) {
    let rename = |variable: &mut KoreVariable| {
        if let Some(name) = renaming.get(variable) {
            variable.name.clone_from(name);
        }
    };
    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => {
            for argument in arguments {
                apply_variable_renaming(argument, renaming);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => apply_variable_renaming(argument, renaming),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            apply_variable_renaming(left, renaming);
            apply_variable_renaming(right, renaming);
        }
        Pattern::Exists { variable, body, .. }
        | Pattern::Forall { variable, body, .. }
        | Pattern::Mu { variable, body }
        | Pattern::Nu { variable, body } => {
            rename(variable);
            apply_variable_renaming(body, renaming);
        }
        Pattern::Variable(variable) => rename(variable),
        Pattern::String(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }
}

fn is_empty_disjunction(pattern: &Pattern) -> bool {
    matches!(pattern, Pattern::Or { arguments, .. } if arguments.is_empty())
}

fn execution_disjuncts(pattern: &Pattern) -> Vec<&Pattern> {
    match pattern {
        Pattern::Or { arguments, .. } => arguments.iter().collect(),
        pattern => vec![pattern],
    }
}

fn split_constrained(pattern: &Pattern) -> (&Pattern, Vec<Pattern>) {
    let Pattern::And { arguments, .. } = pattern else {
        return (pattern, Vec::new());
    };
    let terms = arguments
        .iter()
        .enumerate()
        .filter(|(_, argument)| !is_predicate_pattern(argument))
        .collect::<Vec<_>>();
    let [(term_index, term)] = terms.as_slice() else {
        return (pattern, Vec::new());
    };
    let constraints = arguments
        .iter()
        .enumerate()
        .filter(|(index, _)| index != term_index)
        .map(|(_, argument)| argument.clone())
        .collect();
    (term, constraints)
}

/// The predicate shapes of Kore/Internal/Predicate.hs (PredicateF): top, bottom, ceil, floor,
/// equals, in, and the connectives and quantifiers over predicates. A remainder branch
/// constrains its term with `\not(\exists rule variables. solution)`.
fn is_predicate_pattern(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::Ceil { .. }
        | Pattern::Floor { .. }
        | Pattern::Equals { .. }
        | Pattern::In { .. } => true,
        Pattern::Not { argument, .. } => is_predicate_pattern(argument),
        Pattern::Exists { body, .. } | Pattern::Forall { body, .. } => is_predicate_pattern(body),
        Pattern::Implies { left, right, .. } | Pattern::Iff { left, right, .. } => {
            is_predicate_pattern(left) && is_predicate_pattern(right)
        }
        Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => {
            arguments.iter().all(is_predicate_pattern)
        }
        _ => false,
    }
}

/// What the implication fallback (N15) runs: the `krust` executable that proves the claims, and
/// the definition it proves them in. Both are explicit so a test can substitute a fake `krust`
/// without touching the process environment, which every concurrently running test reads.
#[derive(Clone, Copy)]
struct ImplicationOracle<'a> {
    krust: &'a Path,
    definition: &'a Path,
}

/// The `krust` executable the execution comparison proves implications with: `K_RUST_KRUST`,
/// else the one Cargo built for this test, else `target/release/krust`.
fn implication_krust() -> std::path::PathBuf {
    env::var_os("K_RUST_KRUST")
        .map(std::path::PathBuf::from)
        .or_else(|| option_env!("CARGO_BIN_EXE_krust").map(std::path::PathBuf::from))
        .unwrap_or_else(|| std::path::PathBuf::from("target/release/krust"))
}

fn prove_implication_both_ways(
    oracle: ImplicationOracle,
    reference: &Pattern,
    actual: &Pattern,
    module: &str,
) -> Result<(), String> {
    prove_implication_both_ways_with(oracle.krust, reference, actual, oracle.definition, module)
}

fn prove_implication_both_ways_with(
    krust: &Path,
    reference: &Pattern,
    actual: &Pattern,
    definition: &Path,
    module: &str,
) -> Result<(), String> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|error| format!("system clock before Unix epoch: {error}"))?
        .as_nanos();
    let directory = env::temp_dir().join(format!(
        "k-rust-execution-implication-{}-{nonce}",
        std::process::id()
    ));
    fs::create_dir(&directory).map_err(|error| format!("create implication fixture: {error}"))?;
    let reference_path = directory.join("reference.kore");
    let actual_path = directory.join("actual.kore");
    fs::write(&reference_path, reference.to_string())
        .map_err(|error| format!("write reference implication pattern: {error}"))?;
    fs::write(&actual_path, actual.to_string())
        .map_err(|error| format!("write actual implication pattern: {error}"))?;

    let result = (|| {
        prove_implication(
            krust,
            &reference_path,
            &actual_path,
            definition,
            module,
            "reference => actual",
        )?;
        prove_implication(
            krust,
            &actual_path,
            &reference_path,
            definition,
            module,
            "actual => reference",
        )
    })();
    let _ = fs::remove_dir_all(directory);
    result
}

fn prove_implication(
    krust: &Path,
    antecedent: &Path,
    consequent: &Path,
    definition: &Path,
    module: &str,
    direction: &str,
) -> Result<(), String> {
    let output = Command::new(krust)
        .arg("kore-implies")
        .arg(definition)
        .arg("--module")
        .arg(module)
        .arg("--antecedent")
        .arg(antecedent)
        .arg("--consequent")
        .arg(consequent)
        .output()
        .map_err(|error| format!("run {} for {direction}: {error}", krust.display()))?;
    if !output.status.success() {
        return Err(format!(
            "constraint implication {direction} failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let response: serde_json::Value = serde_json::from_slice(&output.stdout).map_err(|error| {
        format!(
            "constraint implication {direction} returned invalid JSON ({error}): {}",
            String::from_utf8_lossy(&output.stdout)
        )
    })?;
    if response["status"] != "valid" {
        let antecedent = fs::read_to_string(antecedent).unwrap_or_default();
        let consequent = fs::read_to_string(consequent).unwrap_or_default();
        return Err(format!(
            "constraint implication {direction} is not valid (status {}):\n  antecedent: {antecedent}\n  consequent: {consequent}",
            response["status"]
        ));
    }
    Ok(())
}

fn parse_macro_sentences(source: &str) -> Definition {
    parse_definition(&format!("[]\nmodule MACROS\n{source}\nendmodule []\n"))
        .expect("macro sentence list should parse")
}

#[test]
fn comparator_ignores_generated_variable_suffixes() {
    let reference = differential_definition("axiom{} Var'Unds'Gen7:S{} []");
    let actual = differential_definition("axiom{} Var'Unds'Gen9:S{} []");

    compare_definitions(reference, actual);
}

#[test]
fn comparator_detects_unique_id_differences_by_default() {
    let reference = differential_definition(r#"axiom{} a{}() [UNIQUE'Unds'ID{}("reference-id")]"#);
    let actual = differential_definition(r#"axiom{} a{}() [UNIQUE'Unds'ID{}("actual-id")]"#);

    assert!(
        std::panic::catch_unwind(|| compare_definitions(reference, actual)).is_err(),
        "UNIQUE_ID must participate in the default differential comparison"
    );
}

#[test]
fn comparator_skips_ids_of_multi_alias_freezer_axioms() {
    let definition = |first_id: &str, second_id: &str| {
        parse_definition(&format!(
            r#"[]
            module TEST
              sort S{{}} []
              symbol Lbl'Hash'freezerfoo'Unds'0{{}}() : S{{}} []
              symbol Lbl'Hash'freezerfoo'Unds'1{{}}() : S{{}} []
              axiom{{}} Lbl'Hash'freezerfoo'Unds'0{{}}() [UNIQUE'Unds'ID{{}}("{first_id}")]
              axiom{{}} Lbl'Hash'freezerfoo'Unds'1{{}}() [UNIQUE'Unds'ID{{}}("{second_id}")]
            endmodule []"#,
        ))
        .unwrap()
    };

    compare_definitions(
        definition("reference-zero", "reference-one"),
        definition("actual-zero", "actual-one"),
    );
}

#[test]
fn comparator_ignores_which_multi_alias_freezer_suffix_each_context_receives() {
    // ResolveContexts.getUniqueFreezerLabel names the first freezer of a hint `_` and the
    // second `_2`, and meets the contexts of a multi-alias group in Scala HashSet order
    // (N3; docs/compatibility.md#comparison-contract). The suffix a context receives is not
    // portable: the heat rules of the two aliases swap freezer symbols between the
    // reference and the port while everything else is equal.
    let definition = |first: &str, second: &str| {
        parse_definition(&format!(
            r#"[]
            module TEST
              sort S{{}} []
              symbol Lbla{{}}() : S{{}} []
              symbol Lblb{{}}() : S{{}} []
              symbol Lbl'Hash'freezerfoo'Unds'0'Unds'{{}}() : S{{}} []
              symbol Lbl'Hash'freezerfoo'Unds'0'Unds'2{{}}() : S{{}} []
              axiom{{}} \equals{{S{{}}, S{{}}}}(Lbla{{}}(), {first}{{}}()) [UNIQUE'Unds'ID{{}}("{first}")]
              axiom{{}} \equals{{S{{}}, S{{}}}}(Lblb{{}}(), {second}{{}}()) [UNIQUE'Unds'ID{{}}("{second}")]
            endmodule []"#,
        ))
        .unwrap()
    };
    let unsuffixed = "Lbl'Hash'freezerfoo'Unds'0'Unds'";
    let second = "Lbl'Hash'freezerfoo'Unds'0'Unds'2";

    let report = compare_definitions_with(
        definition(unsuffixed, second),
        definition(second, unsuffixed),
        CompareOptions::default(),
    );
    assert_eq!(report.verdict, CompareVerdict::Equal);
    assert_eq!(report.multi_alias_axioms, 2);

    // A hint with a single freezer is not a multi-alias group: its symbol keeps its
    // identity and a swapped use stays a difference.
    let single = |target: &str| {
        parse_definition(&format!(
            r#"[]
            module TEST
              sort S{{}} []
              symbol Lbla{{}}() : S{{}} []
              symbol Lblb{{}}() : S{{}} []
              symbol Lbl'Hash'freezerfoo'Unds'0'Unds'{{}}() : S{{}} []
              axiom{{}} \equals{{S{{}}, S{{}}}}({target}{{}}(), Lbl'Hash'freezerfoo'Unds'0'Unds'{{}}()) []
            endmodule []"#,
        ))
        .unwrap()
    };
    let report =
        compare_definitions_with(single("Lbla"), single("Lblb"), CompareOptions::default());
    assert!(
        matches!(report.verdict, CompareVerdict::Differs(_)),
        "a single freezer must keep its identity"
    );
    assert_eq!(report.multi_alias_axioms, 0);
}

#[test]
fn comparator_ignores_which_lambda_suffix_each_local_function_receives() {
    // ResolveFun.getUniqueLambdaLabel names the first `#fun`/`#let`/`:=K` of a name hint
    // `#lambda<h1>_<h2>_` and the following ones `_2`, `_3`, ... in the order the module's
    // sentences are met, which is Scala HashSet order in the reference (N23;
    // docs/compatibility.md#comparison-contract): the same definition compiled from
    // two directories assigns the suffixes differently. The port numbers in declaration
    // order. Collapse every lambda of a multi-suffix family onto the unsuffixed name and
    // drop the UNIQUE_IDs derived from it, so that the bodies and signatures still compare.
    let definition = |first: &str, second: &str| {
        parse_definition(&format!(
            r#"[]
            module TEST
              sort S{{}} []
              sort T{{}} []
              symbol Lbla{{}}() : S{{}} []
              symbol Lblb{{}}() : T{{}} []
              symbol {first}{{}}(S{{}}) : S{{}} [function{{}}()]
              symbol {second}{{}}(S{{}}, T{{}}) : T{{}} [function{{}}()]
              axiom{{}} \equals{{S{{}}, S{{}}}}({first}{{}}(Lbla{{}}()), Lbla{{}}()) [UNIQUE'Unds'ID{{}}("{first}")]
              axiom{{}} \equals{{T{{}}, T{{}}}}({second}{{}}(Lbla{{}}(), Lblb{{}}()), Lblb{{}}()) [UNIQUE'Unds'ID{{}}("{second}")]
            endmodule []"#,
        ))
        .unwrap()
    };
    let unsuffixed = "Lbl'Hash'lambda'UndsUnds'";
    let second = "Lbl'Hash'lambda'UndsUnds'2";

    let report = compare_definitions_with(
        definition(unsuffixed, second),
        definition(second, unsuffixed),
        CompareOptions::default(),
    );
    assert_eq!(report.verdict, CompareVerdict::Equal);
    assert_eq!(report.multi_suffix_lambda_axioms, 2);
    assert_eq!(report.multi_alias_axioms, 0);

    // The family key is the name without its trailing suffix digits: a hint ending in a
    // digit (`#lambdaF2__`) or carrying encoded punctuation (`#lambdaF_test(_,_,_)_..._`)
    // is one family with its `_2` twin.
    let record = "Lbl'Hash'lambdaF'Unds'test'LParUndsCommUndsCommUndsRParUnds'TEST'Unds'Foo'Unds'";
    let report = compare_definitions_with(
        definition(record, &format!("{record}2")),
        definition(&format!("{record}2"), record),
        CompareOptions::default(),
    );
    assert_eq!(report.verdict, CompareVerdict::Equal);
    assert_eq!(report.multi_suffix_lambda_axioms, 2);

    // A hint with a single lambda is not a family: its symbol keeps its identity, a
    // swapped use stays a difference, and a hint ending in a digit is not a suffix.
    let single = |target: &str| {
        parse_definition(&format!(
            r#"[]
            module TEST
              sort S{{}} []
              symbol Lbla{{}}() : S{{}} []
              symbol Lblb{{}}() : S{{}} []
              symbol Lbl'Hash'lambdaF2'UndsUnds'{{}}(S{{}}) : S{{}} [function{{}}()]
              axiom{{}} \equals{{S{{}}, S{{}}}}({target}{{}}(), Lbl'Hash'lambdaF2'UndsUnds'{{}}(Lbla{{}}())) []
            endmodule []"#,
        ))
        .unwrap()
    };
    let report =
        compare_definitions_with(single("Lbla"), single("Lblb"), CompareOptions::default());
    assert!(
        matches!(report.verdict, CompareVerdict::Differs(_)),
        "a single lambda must keep its identity"
    );
    assert_eq!(report.multi_suffix_lambda_axioms, 0);

    // The exclusion is opt-out: without it the swapped family is a difference.
    let report = compare_definitions_with(
        definition(unsuffixed, second),
        definition(second, unsuffixed),
        CompareOptions {
            skip_multi_suffix_lambda_ids: false,
            ..CompareOptions::default()
        },
    );
    assert!(matches!(report.verdict, CompareVerdict::Differs(_)));
}

#[test]
fn comparator_keeps_distinct_generated_variables_distinct() {
    let distinct =
        differential_definition(r"axiom{} \and{S{}}(Var'Unds'X1:S{}, Var'Unds'X2:S{}) []");
    let repeated =
        differential_definition(r"axiom{} \and{S{}}(Var'Unds'X1:S{}, Var'Unds'X1:S{}) []");

    assert!(
        std::panic::catch_unwind(|| compare_definitions(distinct, repeated)).is_err(),
        "two generated variables must not compare equal to one repeated variable"
    );

    let reference =
        differential_definition(r"axiom{} \and{S{}}(Var'Unds'X1:S{}, Var'Unds'X2:S{}) []");
    let actual = differential_definition(r"axiom{} \and{S{}}(Var'Unds'X7:S{}, Var'Unds'X9:S{}) []");
    compare_definitions(reference, actual);
}

#[test]
fn comparator_treats_same_sort_disjunction_order_as_equal() {
    let reference = differential_definition(r"axiom{} \or{S{}}(a{}(), b{}(), c{}()) []");
    let actual = differential_definition(r"axiom{} \or{S{}}(\or{S{}}(c{}(), a{}()), b{}()) []");

    compare_definitions(reference, actual);
}

#[test]
fn comparator_reorders_existential_binder_chains() {
    let reference = differential_definition(
        r"axiom{} \exists{S{}}(X:S{}, \exists{S{}}(Y:S{}, \and{S{}}(X:S{}, Y:S{}))) []",
    );
    let actual = differential_definition(
        r"axiom{} \exists{S{}}(Y:S{}, \exists{S{}}(X:S{}, \and{S{}}(X:S{}, Y:S{}))) []",
    );

    compare_definitions(reference, actual);
}

#[test]
fn comparator_reorders_generated_existential_binders_before_alpha_renaming() {
    let reference = differential_definition(
        r"axiom{} \exists{R{}}(Var'Unds'Gen2:Set{}, \exists{R{}}(Var'Unds'Gen3:Int{}, \and{R{}}(Var'Unds'Gen2:Set{}, Var'Unds'Gen3:Int{}))) []",
    );
    let actual = differential_definition(
        r"axiom{} \exists{R{}}(Var'Unds'Gen3:Int{}, \exists{R{}}(Var'Unds'Gen2:Set{}, \and{R{}}(Var'Unds'Gen2:Set{}, Var'Unds'Gen3:Int{}))) []",
    );

    compare_definitions(reference, actual);
}

#[test]
fn comparator_reorders_universal_binder_chains() {
    let reference = differential_definition(
        r"axiom{} \forall{S{}}(X:S{}, \forall{S{}}(Y:S{}, \and{S{}}(X:S{}, Y:S{}))) []",
    );
    let actual = differential_definition(
        r"axiom{} \forall{S{}}(Y:S{}, \forall{S{}}(X:S{}, \and{S{}}(X:S{}, Y:S{}))) []",
    );

    compare_definitions(reference, actual);
}

#[test]
fn comparator_alpha_normalizes_disjoint_bound_variable_names() {
    let reference = differential_definition(
        r"axiom{} \or{S{}}(
            \exists{S{}}(X:S{}, X:S{}),
            \exists{S{}}(X:T{}, X:T{})
        ) []",
    );
    let actual = differential_definition(
        r"axiom{} \or{S{}}(
            \exists{S{}}(X:S{}, X:S{}),
            \exists{S{}}(X0V2:T{}, X0V2:T{})
        ) []",
    );

    compare_definitions(reference, actual);
}

#[test]
fn comparator_detects_multiplicity_differences() {
    let reference = differential_definition("axiom{} a{}() []\naxiom{} a{}() []");
    let actual = differential_definition("axiom{} a{}() []");

    assert!(
        std::panic::catch_unwind(|| compare_definitions(reference, actual)).is_err(),
        "the comparator must retain sentence multiplicity"
    );
}

#[test]
fn comparator_reports_the_first_differing_sentence() {
    let reference = differential_definition(
        r#"axiom{} a{}() [UNIQUE'Unds'ID{}("common")]
           axiom{} b{}() [UNIQUE'Unds'ID{}("expected-second")]"#,
    );
    let actual = differential_definition(
        r#"axiom{} a{}() [UNIQUE'Unds'ID{}("common")]
           axiom{} c{}() [UNIQUE'Unds'ID{}("actual-second")]"#,
    );

    let panic = std::panic::catch_unwind(|| compare_definitions(reference, actual))
        .expect_err("different sentences must fail comparison");
    let message = panic_message(panic);
    assert!(message.contains("first differing sentence=5"), "{message}");
    assert!(message.contains("expected-second"), "{message}");
    assert!(message.contains("actual-second"), "{message}");
}

fn differential_definition(sentences: &str) -> Definition {
    parse_definition(&format!(
        r#"[]
        module TEST
          sort S{{}} []
          symbol a{{}}() : S{{}} []
          symbol b{{}}() : S{{}} []
          symbol c{{}}() : S{{}} []
          {sentences}
        endmodule []"#
    ))
    .expect("differential test definition should parse")
}

fn panic_message(panic: Box<dyn std::any::Any + Send>) -> String {
    match panic.downcast::<String>() {
        Ok(message) => *message,
        Err(panic) => panic
            .downcast::<&'static str>()
            .map(|message| (*message).to_owned())
            .unwrap_or_else(|_| "non-string panic".into()),
    }
}

#[derive(Clone, Copy, Debug)]
struct CompareOptions {
    skip_multi_alias_ids: bool,
    skip_multi_suffix_lambda_ids: bool,
}

impl Default for CompareOptions {
    fn default() -> Self {
        Self {
            // N3: freezer suffixes for multi-alias context groups
            // follow Scala HashSet iteration in the oracle. Keep the port's declaration
            // order and exclude only those derived identifiers permanently.
            skip_multi_alias_ids: true,
            // N23 covers the `#lambda` suffixes ResolveFun assigns in the same HashSet
            // order; see docs/compatibility.md#comparison-contract for both policies.
            skip_multi_suffix_lambda_ids: true,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum CompareVerdict {
    Equal,
    Differs(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CompareReport {
    verdict: CompareVerdict,
    multi_alias_axioms: usize,
    multi_suffix_lambda_axioms: usize,
}

fn compare_definitions(reference: Definition, actual: Definition) {
    let report = compare_definitions_with(reference, actual, CompareOptions::default());
    println!("multi-alias freezer axioms: {}", report.multi_alias_axioms);
    println!(
        "multi-suffix lambda axioms: {}",
        report.multi_suffix_lambda_axioms
    );
    println!(
        "no-confusion pairs canonicalised (N30, both sides): {}",
        NO_CONFUSION_PAIRS.swap(0, std::sync::atomic::Ordering::Relaxed)
    );
    if let CompareVerdict::Differs(message) = report.verdict {
        panic!("{message}");
    }
}

fn compare_definitions_with(
    mut reference: Definition,
    mut actual: Definition,
    options: CompareOptions,
) -> CompareReport {
    let raw_reference = reference.clone();
    let raw_actual = actual.clone();
    strip_source_metadata(&mut reference);
    strip_source_metadata(&mut actual);
    let multi_alias_axioms = if options.skip_multi_alias_ids {
        let reference_count = strip_multi_alias_freezer_ids(&mut reference);
        let actual_count = strip_multi_alias_freezer_ids(&mut actual);
        reference_count.max(actual_count)
    } else {
        0
    };
    let multi_suffix_lambda_axioms = if options.skip_multi_suffix_lambda_ids {
        let reference_count = strip_multi_suffix_lambda_ids(&mut reference);
        let actual_count = strip_multi_suffix_lambda_ids(&mut actual);
        reference_count.max(actual_count)
    } else {
        0
    };
    let verdict = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        compare_stripped_definitions(reference, actual, &raw_reference, &raw_actual)
    })) {
        Ok(()) => CompareVerdict::Equal,
        Err(panic) => CompareVerdict::Differs(panic_message(panic)),
    };
    CompareReport {
        verdict,
        multi_alias_axioms,
        multi_suffix_lambda_axioms,
    }
}

fn compare_stripped_definitions(
    reference: Definition,
    actual: Definition,
    raw_reference: &Definition,
    raw_actual: &Definition,
) {
    assert_eq!(
        reference.attributes, actual.attributes,
        "definition attributes"
    );
    assert_eq!(
        reference.modules.len(),
        actual.modules.len(),
        "module count"
    );
    for (module_index, (reference, actual)) in
        reference.modules.iter().zip(&actual.modules).enumerate()
    {
        assert_eq!(reference.name, actual.name, "module name");
        assert_eq!(
            reference.attributes, actual.attributes,
            "{} attributes",
            reference.name
        );
        let reference_canonical = reference
            .sentences
            .iter()
            .map(canonical_sentence)
            .collect::<Vec<_>>();
        let actual_canonical = actual
            .sentences
            .iter()
            .map(canonical_sentence)
            .collect::<Vec<_>>();
        let reference_sentences = multiset(reference_canonical.clone());
        let actual_sentences = multiset(actual_canonical.clone());
        if reference_sentences != actual_sentences {
            let missing = count_differences(&reference_sentences, &actual_sentences);
            let extra = count_differences(&actual_sentences, &reference_sentences);
            let reference_side = ReportSide::new(
                &reference_canonical,
                &reference.sentences,
                &raw_reference.modules[module_index].sentences,
            );
            let actual_side = ReportSide::new(
                &actual_canonical,
                &actual.sentences,
                &raw_actual.modules[module_index].sentences,
            );
            let missing_ids = difference_ids(&missing, &reference_side);
            let extra_ids = difference_ids(&extra, &actual_side);
            panic!(
                "{} sentence multiset differs: reference={}, actual={} ({}); missing={} {:?}, extra={} {:?}\n{}\n{}\nmissing summaries:\n{}\nextra summaries:\n{}",
                reference.name,
                sentence_counts(&reference.sentences),
                sentence_counts(&actual.sentences),
                first_sentence_difference(&reference.sentences, &actual.sentences),
                missing.len(),
                missing_ids,
                extra.len(),
                extra_ids,
                difference_context(
                    missing.first().map(String::as_str),
                    extra.first().map(String::as_str)
                ),
                paired_difference_context(&missing, &extra, &reference_side, &actual_side),
                difference_summaries(&missing, &reference_side),
                difference_summaries(&extra, &actual_side),
            );
        }
    }
}

/// One side of a module's sentence comparison, as the mismatch report reads it.
///
/// Each sentence is canonicalised once, and a difference finds its sentence by lookup: scanning
/// and canonicalising every sentence again for each difference made the report quadratic in the
/// module size.
struct ReportSide<'a> {
    /// `canonical[index]` is `canonical_sentence(&stripped[index])`.
    canonical: &'a [String],
    /// The first index of each canonical form, which is the index a linear scan finds.
    positions: HashMap<&'a str, usize>,
    stripped: &'a [Sentence],
    raw: &'a [Sentence],
}

impl<'a> ReportSide<'a> {
    fn new(canonical: &'a [String], stripped: &'a [Sentence], raw: &'a [Sentence]) -> Self {
        let mut positions = HashMap::with_capacity(canonical.len());
        for (index, sentence) in canonical.iter().enumerate() {
            positions.entry(sentence.as_str()).or_insert(index);
        }
        Self {
            canonical,
            positions,
            stripped,
            raw,
        }
    }

    /// The index of the first sentence whose canonical form is `canonical`.
    fn position(&self, canonical: &str) -> Option<usize> {
        self.positions.get(canonical).copied()
    }
}

fn difference_summaries(differences: &[String], side: &ReportSide) -> String {
    let (stripped, raw) = (side.stripped, side.raw);
    differences
        .iter()
        .enumerate()
        .filter_map(|(difference_index, difference)| {
            let sentence_index = side.position(difference)?;
            let identity =
                sentence_identity(&raw[sentence_index]).unwrap_or_else(|| "<generated>".into());
            let kind = match &stripped[sentence_index] {
                Sentence::Import { .. } => "import",
                Sentence::SortDeclaration { .. } => "sort",
                Sentence::SymbolDeclaration { .. } => "symbol",
                Sentence::AliasDeclaration { .. } => "alias",
                Sentence::Axiom { .. } => "axiom",
                Sentence::Claim { .. } => "claim",
            };
            let excerpt = difference.chars().take(900).collect::<String>();
            Some(format!(
                "{}. {kind} {identity} (sentence {sentence_index}): {excerpt}",
                difference_index + 1
            ))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn paired_difference_context(
    missing: &[String],
    extra: &[String],
    reference: &ReportSide,
    actual: &ReportSide,
) -> String {
    let (stripped_reference, raw_reference) = (reference.stripped, reference.raw);
    let (stripped_actual, raw_actual) = (actual.stripped, actual.raw);
    let extra = extra.iter().map(String::as_str).collect::<HashSet<_>>();
    for missing_sentence in missing {
        let Some(reference_index) = reference.position(missing_sentence) else {
            continue;
        };
        let Some(identity) = sentence_identity(&raw_reference[reference_index]) else {
            continue;
        };
        if identity == "<generated>" {
            continue;
        }
        let actual_index = raw_actual
            .iter()
            .position(|sentence| sentence_identity(sentence).as_deref() == Some(&identity))
            .or_else(|| {
                let label = sentence_attribute(&raw_reference[reference_index], "label")?;
                raw_actual.iter().position(|sentence| {
                    sentence_attribute(sentence, "label").as_deref() == Some(&label)
                })
            });
        let Some(actual_index) = actual_index else {
            continue;
        };
        let actual_sentence = &actual.canonical[actual_index];
        if extra.contains(actual_sentence.as_str()) {
            let reference_value = canonicalized_sentence(&stripped_reference[reference_index]);
            let actual_value = canonicalized_sentence(&stripped_actual[actual_index]);
            let competitor_context = match (
                owise_competitors(&reference_value),
                owise_competitors(&actual_value),
            ) {
                (Some(reference), Some(actual)) => {
                    let reference = multiset(
                        reference
                            .iter()
                            .map(|pattern| format!("{pattern:?}"))
                            .collect(),
                    );
                    let actual = multiset(
                        actual
                            .iter()
                            .map(|pattern| format!("{pattern:?}"))
                            .collect(),
                    );
                    let missing = count_differences(&reference, &actual);
                    let extra = count_differences(&actual, &reference);
                    format!(
                        "\ncompetitors: reference={}, actual={}, missing={}, extra={}\n{}",
                        reference.values().sum::<usize>(),
                        actual.values().sum::<usize>(),
                        missing.len(),
                        extra.len(),
                        difference_context(
                            missing.first().map(String::as_str),
                            extra.first().map(String::as_str),
                        )
                    )
                }
                _ => String::new(),
            };
            return format!(
                "paired difference for {identity}:\n{}{}",
                difference_context(Some(missing_sentence), Some(actual_sentence)),
                competitor_context,
            );
        }
    }
    "no source-identified missing/extra pair".into()
}

fn sentence_attribute(sentence: &Sentence, name: &str) -> Option<String> {
    let attributes = match sentence {
        Sentence::Import { attributes, .. }
        | Sentence::SortDeclaration { attributes, .. }
        | Sentence::SymbolDeclaration { attributes, .. }
        | Sentence::AliasDeclaration { attributes, .. }
        | Sentence::Axiom { attributes, .. }
        | Sentence::Claim { attributes, .. } => attributes,
    };
    attributes.0.iter().find_map(|attribute| match attribute {
        Pattern::Application { symbol, arguments } if symbol.name == name => {
            arguments.first().and_then(|argument| match argument {
                Pattern::String(value) => Some(value.as_utf8().unwrap().to_owned()),
                _ => None,
            })
        }
        _ => None,
    })
}

fn owise_competitors(sentence: &Sentence) -> Option<&[Pattern]> {
    let Sentence::Axiom { pattern, .. } = sentence else {
        return None;
    };
    let Pattern::Implies { left, .. } = pattern.as_ref() else {
        return None;
    };
    let Pattern::And { arguments, .. } = left.as_ref() else {
        return None;
    };
    arguments.iter().find_map(|argument| {
        let Pattern::Not { argument, .. } = argument else {
            return None;
        };
        let Pattern::Or { arguments, .. } = argument.as_ref() else {
            return None;
        };
        Some(arguments.as_slice())
    })
}

fn difference_ids(differences: &[String], side: &ReportSide) -> Vec<String> {
    differences
        .iter()
        .map(|difference| {
            side.position(difference)
                .and_then(|index| sentence_identity(&side.raw[index]))
                .unwrap_or_else(|| "<generated>".into())
        })
        .collect()
}

fn sentence_identity(sentence: &Sentence) -> Option<String> {
    let attributes = match sentence {
        Sentence::Import { attributes, .. }
        | Sentence::SortDeclaration { attributes, .. }
        | Sentence::SymbolDeclaration { attributes, .. }
        | Sentence::AliasDeclaration { attributes, .. }
        | Sentence::Axiom { attributes, .. }
        | Sentence::Claim { attributes, .. } => attributes,
    };
    attributes.0.iter().find_map(|attribute| match attribute {
        Pattern::Application { symbol, arguments }
            if symbol.name == "UNIQUE'Unds'ID"
                || symbol.name == "org'Stop'kframework'Stop'attributes'Stop'Source" =>
        {
            arguments.first().and_then(|argument| match argument {
                Pattern::String(value) => Some(value.as_utf8().unwrap().to_owned()),
                _ => None,
            })
        }
        _ => None,
    })
}

fn canonical_sentence(sentence: &Sentence) -> String {
    format!("{:?}", canonicalized_sentence(sentence))
}

fn canonicalized_sentence(sentence: &Sentence) -> Sentence {
    let mut sentence = sentence.clone();
    match &mut sentence {
        Sentence::AliasDeclaration {
            left,
            right,
            attributes,
            ..
        } => {
            canonicalize_pattern(left);
            canonicalize_pattern(right);
            canonicalize_attributes(attributes);
        }
        Sentence::Axiom {
            pattern,
            attributes,
            ..
        }
        | Sentence::Claim {
            pattern,
            attributes,
            ..
        } => {
            canonicalize_pattern(pattern);
            canonicalize_attributes(attributes);
        }
        Sentence::Import { attributes, .. }
        | Sentence::SortDeclaration { attributes, .. }
        | Sentence::SymbolDeclaration { attributes, .. } => {
            canonicalize_attributes(attributes);
        }
    }
    sentence
}

fn canonicalize_attributes(attributes: &mut Attributes) {
    for attribute in &mut attributes.0 {
        canonicalize_pattern(attribute);
    }
}

fn canonicalize_pattern(pattern: &mut Pattern) {
    canonicalize_no_confusion_pairs(pattern);
    // N5/N6: stabilize set-derived binders, alpha-normalize each scope, and only then sort
    // disjunctions. This makes N4's free-variable first-occurrence traversal independent of the
    // reference's binder and competitor set order.
    canonicalize_existentials(pattern);
    alpha_normalize_bound_variables(pattern);
    canonicalize_existentials(pattern);
    rename_generated_variables(pattern);
}

/// N30: pairs canonicalised so far in this comparison (reference and port sides together).
static NO_CONFUSION_PAIRS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// N30: a no-confusion axiom `\not(\and(P(X0..), Q(Y0..)))` compares with its two constructor
/// applications ordered by symbol and argument sorts and their free variables renamed by
/// position.
///
/// K emits one such axiom per unordered pair of distinct constructors of a sort and picks the
/// `X` side by `Production.ord` (ModuleToKORE.java, "no confusion different constructors"); the
/// port picks it by declaration order. `\and` is commutative and the free `X*`/`Y*` names are
/// alpha-equivalent under the axiom's closure, so the canonical form hides nothing semantic. The
/// shape (top-level negated binary conjunction of two applications over variables) identifies the
/// family; no other emitted axiom has it.
fn canonicalize_no_confusion_pairs(pattern: &mut Pattern) {
    let Pattern::Not { argument, .. } = pattern else {
        return;
    };
    let Pattern::And { arguments, .. } = argument.as_mut() else {
        return;
    };
    if arguments.len() != 2 || !arguments.iter().all(is_application_over_variables) {
        return;
    }
    arguments.sort_by_cached_key(no_confusion_conjunct_key);
    for (side, conjunct) in arguments.iter_mut().enumerate() {
        let Pattern::Application { arguments, .. } = conjunct else {
            unreachable!("checked above");
        };
        for (position, argument) in arguments.iter_mut().enumerate() {
            let Pattern::Variable(variable) = argument else {
                unreachable!("checked above");
            };
            variable.name = format!("{CANONICAL_NAME}Pair{side}Arg{position}");
        }
    }
    NO_CONFUSION_PAIRS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}

fn is_application_over_variables(pattern: &Pattern) -> bool {
    matches!(
        pattern,
        Pattern::Application { arguments, .. }
            if arguments.iter().all(|argument| matches!(argument, Pattern::Variable(_)))
    )
}

fn no_confusion_conjunct_key(pattern: &Pattern) -> (Symbol, Vec<k_rust::kore::ast::Sort>) {
    let Pattern::Application { symbol, arguments } = pattern else {
        unreachable!("only applications over variables are keyed");
    };
    let sorts = arguments
        .iter()
        .map(|argument| match argument {
            Pattern::Variable(variable) => variable.sort.clone(),
            _ => unreachable!("only applications over variables are keyed"),
        })
        .collect();
    (symbol.clone(), sorts)
}

fn alpha_normalize_bound_variables(pattern: &mut Pattern) {
    fn visit(pattern: &mut Pattern, scopes: &mut Vec<(k_rust::kore::ast::Variable, String)>) {
        match pattern {
            Pattern::Application { arguments, .. }
            | Pattern::And { arguments, .. }
            | Pattern::Or { arguments, .. }
            | Pattern::AssociativeApplication { arguments, .. } => {
                for argument in arguments {
                    visit(argument, scopes);
                }
            }
            Pattern::Not { argument, .. }
            | Pattern::Next { argument, .. }
            | Pattern::Ceil { argument, .. }
            | Pattern::Floor { argument, .. } => visit(argument, scopes),
            Pattern::Implies { left, right, .. }
            | Pattern::Iff { left, right, .. }
            | Pattern::Rewrites { left, right, .. }
            | Pattern::Equals { left, right, .. }
            | Pattern::In { left, right, .. } => {
                visit(left, scopes);
                visit(right, scopes);
            }
            Pattern::Exists { variable, body, .. }
            | Pattern::Forall { variable, body, .. }
            | Pattern::Mu { variable, body }
            | Pattern::Nu { variable, body } => {
                let original = variable.as_ref().clone();
                let canonical = format!("{CANONICAL_NAME}Bound{}", scopes.len());
                variable.name.clone_from(&canonical);
                scopes.push((original, canonical));
                visit(body, scopes);
                scopes.pop();
            }
            Pattern::Variable(variable) => {
                if let Some((_, canonical)) = scopes.iter().rev().find(|(bound, _)| {
                    bound.kind == variable.kind
                        && bound.name == variable.name
                        && bound.sort == variable.sort
                }) {
                    variable.name.clone_from(canonical);
                }
            }
            Pattern::String(_)
            | Pattern::Top { .. }
            | Pattern::Bottom { .. }
            | Pattern::DomainValue { .. } => {}
        }
    }

    visit(pattern, &mut Vec::new());
}

/// N5 for execution results: choose one alpha-normalized representative for each bounded block
/// of adjacent existential or universal binders. Same-kind binders commute, including binders of
/// the same sort whose variables occupy different roles in the body. Enumerating the block keeps
/// those binding relationships intact while avoiding a name- or traversal-order heuristic.
fn canonicalize_commuting_quantifier_chains(pattern: &mut Pattern) {
    #[derive(Clone, Copy)]
    enum Quantifier {
        Exists,
        Forall,
    }

    fn rebuild(
        quantifier: Quantifier,
        binders: Vec<(k_rust::kore::ast::Sort, KoreVariable)>,
        body: Pattern,
    ) -> Pattern {
        binders
            .into_iter()
            .rev()
            .fold(body, |body, (sort, variable)| match quantifier {
                Quantifier::Exists => Pattern::Exists {
                    sort,
                    variable: Box::new(variable),
                    body: Box::new(body),
                },
                Quantifier::Forall => Pattern::Forall {
                    sort,
                    variable: Box::new(variable),
                    body: Box::new(body),
                },
            })
    }

    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => {
            for argument in arguments {
                canonicalize_commuting_quantifier_chains(argument);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => canonicalize_commuting_quantifier_chains(argument),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            canonicalize_commuting_quantifier_chains(left);
            canonicalize_commuting_quantifier_chains(right);
        }
        Pattern::Mu { body, .. } | Pattern::Nu { body, .. } => {
            canonicalize_commuting_quantifier_chains(body);
        }
        Pattern::Exists { .. } | Pattern::Forall { .. } => {
            let quantifier = if matches!(pattern, Pattern::Exists { .. }) {
                Quantifier::Exists
            } else {
                Quantifier::Forall
            };
            let mut current = std::mem::replace(pattern, Pattern::String(String::new().into()));
            let mut binders = Vec::new();
            loop {
                let fields = match (quantifier, &mut current) {
                    (
                        Quantifier::Exists,
                        Pattern::Exists {
                            sort,
                            variable,
                            body,
                        },
                    )
                    | (
                        Quantifier::Forall,
                        Pattern::Forall {
                            sort,
                            variable,
                            body,
                        },
                    ) => Some((
                        sort.clone(),
                        variable.as_ref().clone(),
                        std::mem::replace(body.as_mut(), Pattern::String(String::new().into())),
                    )),
                    _ => None,
                };
                let Some((sort, variable, body)) = fields else {
                    break;
                };
                binders.push((sort, variable));
                current = body;
            }
            canonicalize_commuting_quantifier_chains(&mut current);

            let within_limit = (1..=binders.len())
                .try_fold(1usize, |count, factor| count.checked_mul(factor))
                .is_some_and(|count| count <= CONSTRAINT_RENAMING_LIMIT);
            if within_limit {
                let mut candidates = permutations(&binders).into_iter().map(|permutation| {
                    let mut candidate = rebuild(quantifier, permutation, current.clone());
                    alpha_normalize_bound_variables(&mut candidate);
                    normalize_conjunctions(&mut candidate);
                    candidate
                });
                *pattern = candidates
                    .next()
                    .map(|first| candidates.fold(first, std::cmp::min))
                    .expect("a quantifier chain contains at least one binder");
            } else {
                // Retaining the original order can only cause a conservative comparator failure.
                // It avoids factorial work for a definition with an unexpectedly large block.
                *pattern = rebuild(quantifier, binders, current);
            }
        }
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }
}

fn canonicalize_existentials(pattern: &mut Pattern) {
    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => {
            for argument in arguments {
                canonicalize_existentials(argument);
            }
        }
        Pattern::Or { sort, arguments } => {
            for argument in arguments.iter_mut() {
                canonicalize_existentials(argument);
            }
            let mut flattened = Vec::new();
            for mut argument in std::mem::take(arguments) {
                let nested = match &mut argument {
                    Pattern::Or {
                        sort: nested_sort,
                        arguments: nested,
                    } if *nested_sort == *sort => Some(std::mem::take(nested)),
                    _ => None,
                };
                if let Some(mut nested) = nested {
                    flattened.append(&mut nested);
                } else {
                    flattened.push(argument);
                }
            }
            flattened.sort();
            *arguments = flattened;
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => canonicalize_existentials(argument),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            canonicalize_existentials(left);
            canonicalize_existentials(right);
        }
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => {
            canonicalize_existentials(body);
        }
        Pattern::String(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
        Pattern::Variable(_) => {}
    }

    #[derive(Clone, Copy)]
    enum Quantifier {
        Exists,
        Forall,
    }
    let quantifier = match pattern {
        Pattern::Exists { .. } => Quantifier::Exists,
        Pattern::Forall { .. } => Quantifier::Forall,
        _ => return,
    };
    let mut current = std::mem::replace(pattern, Pattern::String(String::new().into()));
    let mut binders = Vec::new();
    loop {
        let fields = match (quantifier, &mut current) {
            (
                Quantifier::Exists,
                Pattern::Exists {
                    sort,
                    variable,
                    body,
                },
            )
            | (
                Quantifier::Forall,
                Pattern::Forall {
                    sort,
                    variable,
                    body,
                },
            ) => Some((
                sort.clone(),
                variable.clone(),
                std::mem::replace(body.as_mut(), Pattern::String(String::new().into())),
            )),
            _ => None,
        };
        let Some((sort, variable, body)) = fields else {
            break;
        };
        binders.push((sort, variable));
        current = body;
    }
    let chain_variables = binders
        .iter()
        .map(|(_, variable)| variable.as_ref().clone())
        .collect::<BTreeSet<_>>();
    let mut first_occurrences = BTreeMap::new();
    fn record_first_occurrences(
        pattern: &Pattern,
        chain_variables: &BTreeSet<k_rust::kore::ast::Variable>,
        shadowed: &mut Vec<k_rust::kore::ast::Variable>,
        first_occurrences: &mut BTreeMap<k_rust::kore::ast::Variable, usize>,
    ) {
        match pattern {
            Pattern::Application { arguments, .. }
            | Pattern::And { arguments, .. }
            | Pattern::Or { arguments, .. }
            | Pattern::AssociativeApplication { arguments, .. } => {
                for argument in arguments {
                    record_first_occurrences(
                        argument,
                        chain_variables,
                        shadowed,
                        first_occurrences,
                    );
                }
            }
            Pattern::Not { argument, .. }
            | Pattern::Next { argument, .. }
            | Pattern::Ceil { argument, .. }
            | Pattern::Floor { argument, .. } => {
                record_first_occurrences(argument, chain_variables, shadowed, first_occurrences)
            }
            Pattern::Implies { left, right, .. }
            | Pattern::Iff { left, right, .. }
            | Pattern::Rewrites { left, right, .. }
            | Pattern::Equals { left, right, .. }
            | Pattern::In { left, right, .. } => {
                record_first_occurrences(left, chain_variables, shadowed, first_occurrences);
                record_first_occurrences(right, chain_variables, shadowed, first_occurrences);
            }
            Pattern::Exists { variable, body, .. }
            | Pattern::Forall { variable, body, .. }
            | Pattern::Mu { variable, body }
            | Pattern::Nu { variable, body } => {
                let shadows_chain = chain_variables.contains(variable.as_ref());
                if shadows_chain {
                    shadowed.push(variable.as_ref().clone());
                }
                record_first_occurrences(body, chain_variables, shadowed, first_occurrences);
                if shadows_chain {
                    shadowed.pop();
                }
            }
            Pattern::Variable(variable)
                if chain_variables.contains(variable) && !shadowed.contains(variable) =>
            {
                let next = first_occurrences.len();
                first_occurrences.entry(variable.clone()).or_insert(next);
            }
            Pattern::Variable(_)
            | Pattern::String(_)
            | Pattern::Top { .. }
            | Pattern::Bottom { .. }
            | Pattern::DomainValue { .. } => {}
        }
    }
    record_first_occurrences(
        &current,
        &chain_variables,
        &mut Vec::new(),
        &mut first_occurrences,
    );
    binders.sort_by(|left, right| {
        let key = |(_, variable): &(_, Box<k_rust::kore::ast::Variable>)| {
            (
                first_occurrences
                    .get(variable.as_ref())
                    .copied()
                    .unwrap_or(usize::MAX),
                variable.sort.clone(),
                variable.kind,
                variable.name.clone(),
            )
        };
        key(left).cmp(&key(right))
    });
    for (sort, variable) in binders.into_iter().rev() {
        current = match quantifier {
            Quantifier::Exists => Pattern::Exists {
                sort,
                variable,
                body: Box::new(current),
            },
            Quantifier::Forall => Pattern::Forall {
                sort,
                variable,
                body: Box::new(current),
            },
        };
    }
    *pattern = current;
}

/// N4: the frontend's `Var'Unds'<stem>N` names, whose stem definitions keep when renaming.
fn generated_stem(name: &str) -> Option<&str> {
    counted_stem("Var'Unds'", name)
}

/// N4: the stem of a `<prefix><stem><digits>` name (stem non-empty, at least one trailing
/// digit), `None` for any name that already carries the canonical `'Hash'KDiff` marker.
fn counted_stem<'name>(prefix: &str, name: &'name str) -> Option<&'name str> {
    let suffix = name.strip_prefix(prefix)?;
    if suffix.contains("'Hash'KDiff") {
        return None;
    }
    let stem = suffix.trim_end_matches(|character: char| character.is_ascii_digit());
    (!stem.is_empty() && stem.len() != suffix.len()).then_some(stem)
}

fn rename_generated_variables(pattern: &mut Pattern) {
    fn rename(variable: &mut k_rust::kore::ast::Variable, indices: &mut BTreeMap<String, usize>) {
        let Some(stem) = generated_stem(&variable.name) else {
            return;
        };
        let stem = stem.to_owned();
        let next = indices.len();
        let index = *indices.entry(variable.name.clone()).or_insert(next);
        // KORE identifiers encode punctuation in apostrophe-delimited
        // words. A raw `#` would make N15's serialized implication inputs
        // unparsable by both kore-parser and krust.
        variable.name = format!("Var'Unds'{stem}'Hash'KDiff{index}");
    }

    fn visit(pattern: &mut Pattern, indices: &mut BTreeMap<String, usize>) {
        match pattern {
            Pattern::Application { arguments, .. }
            | Pattern::And { arguments, .. }
            | Pattern::Or { arguments, .. }
            | Pattern::AssociativeApplication { arguments, .. } => {
                for argument in arguments {
                    visit(argument, indices);
                }
            }
            Pattern::Not { argument, .. }
            | Pattern::Next { argument, .. }
            | Pattern::Ceil { argument, .. }
            | Pattern::Floor { argument, .. } => visit(argument, indices),
            Pattern::Implies { left, right, .. }
            | Pattern::Iff { left, right, .. }
            | Pattern::Rewrites { left, right, .. }
            | Pattern::Equals { left, right, .. }
            | Pattern::In { left, right, .. } => {
                visit(left, indices);
                visit(right, indices);
            }
            Pattern::Exists { variable, body, .. }
            | Pattern::Forall { variable, body, .. }
            | Pattern::Mu { variable, body }
            | Pattern::Nu { variable, body } => {
                rename(variable, indices);
                visit(body, indices);
            }
            Pattern::Variable(variable) => rename(variable, indices),
            Pattern::String(_)
            | Pattern::Top { .. }
            | Pattern::Bottom { .. }
            | Pattern::DomainValue { .. } => {}
        }
    }

    visit(pattern, &mut BTreeMap::new());
}

fn strip_source_metadata(definition: &mut Definition) {
    strip_attributes(&mut definition.attributes);
    for module in &mut definition.modules {
        strip_attributes(&mut module.attributes);
        for sentence in &mut module.sentences {
            let attributes = match sentence {
                Sentence::Import { attributes, .. }
                | Sentence::SortDeclaration { attributes, .. }
                | Sentence::SymbolDeclaration { attributes, .. }
                | Sentence::AliasDeclaration { attributes, .. }
                | Sentence::Axiom { attributes, .. }
                | Sentence::Claim { attributes, .. } => attributes,
            };
            strip_attributes(attributes);
        }
    }
}

/// N3: the freezers of a multi-alias context group are named `_`, `_2`, ... in
/// the order `ResolveContexts` meets the aliases, which is Scala HashSet order in the
/// reference and declaration order in the port. Collapse every freezer of such a group onto
/// the group's unsuffixed name (declarations and uses alike) and drop the UNIQUE_ID of the
/// axioms that mention them, so that only the derived identifiers leave the comparison.
/// Returns the number of axioms touched.
fn strip_multi_alias_freezer_ids(definition: &mut Definition) -> usize {
    strip_symbol_family_ids(definition, multi_alias_freezer)
}

/// `ResolveFun.getUniqueLambdaLabel` names the first `#fun`/`#let`/`:=K`/`:/=K` of a name hint
/// `#lambda<h1>_<h2>_` and the following ones `_2`, `_3`, ... in the order
/// `stream(m.localSentences())` meets the sentences, which is Scala HashSet order over hashes
/// that include the Source attribute: the pinned reference assigns the suffixes differently
/// from two checkout paths. N23 (docs/compatibility.md#comparison-contract) covers these families:
/// collapse every lambda of a multi-suffix family onto the unsuffixed name, in declarations and
/// uses alike, and drop the UNIQUE_IDs derived from those names. Returns the number of axioms
/// touched.
fn strip_multi_suffix_lambda_ids(definition: &mut Definition) -> usize {
    strip_symbol_family_ids(definition, multi_suffix_lambda)
}

/// Collapse the symbol families `families` reports for each module (member name to canonical
/// name) in declarations and patterns, dropping the UNIQUE_ID of every axiom or claim that
/// mentions a member. Returns the number of axioms touched.
fn strip_symbol_family_ids(
    definition: &mut Definition,
    families: fn(&k_rust::kore::ast::Module) -> BTreeMap<String, String>,
) -> usize {
    let mut stripped = 0;
    for module in &mut definition.modules {
        let renames = families(module);
        if renames.is_empty() {
            continue;
        }
        let freezers = renames.keys().cloned().collect::<BTreeSet<_>>();
        for sentence in &mut module.sentences {
            match sentence {
                Sentence::SymbolDeclaration { symbol, .. } => {
                    if let Some(canonical) = renames.get(&symbol.name) {
                        symbol.name = canonical.clone();
                    }
                }
                Sentence::Axiom {
                    pattern,
                    attributes,
                    ..
                }
                | Sentence::Claim {
                    pattern,
                    attributes,
                    ..
                } => {
                    if pattern_mentions_any_symbol(pattern, &freezers) {
                        rename_symbols(pattern, &renames);
                        strip_unique_id_attributes(attributes);
                        stripped += 1;
                    }
                }
                Sentence::Import { .. }
                | Sentence::SortDeclaration { .. }
                | Sentence::AliasDeclaration { .. } => {}
            }
        }
    }
    stripped
}

/// Every freezer symbol of a multi-alias group mapped to the group's canonical name.
fn multi_alias_freezer(module: &k_rust::kore::ast::Module) -> BTreeMap<String, String> {
    let mut by_hint = BTreeMap::<String, Vec<String>>::new();
    for sentence in &module.sentences {
        let Sentence::SymbolDeclaration { symbol, .. } = sentence else {
            continue;
        };
        let Some(hint) = multi_alias_freezer_hint(&symbol.name) else {
            continue;
        };
        by_hint
            .entry(hint.into())
            .or_default()
            .push(symbol.name.clone());
    }
    by_hint
        .into_iter()
        .filter(|(_, names)| names.len() > 1)
        .flat_map(|(hint, names)| {
            let canonical = format!("Lbl'Hash'freezer{hint}'Unds'");
            names.into_iter().map(move |name| (name, canonical.clone()))
        })
        .collect()
}

/// `ResolveContexts.getUniqueFreezerLabel`: `#freezer<hint>_` for the first context of a
/// hint, `#freezer<hint>_<n>` (n >= 2) for the following ones.
fn multi_alias_freezer_hint(name: &str) -> Option<&str> {
    let suffix = name.strip_prefix("Lbl'Hash'freezer")?;
    let (hint, number) = suffix.rsplit_once("'Unds'")?;
    (!hint.is_empty() && number.bytes().all(|byte| byte.is_ascii_digit())).then_some(hint)
}

/// Every `#lambda` symbol of a multi-suffix family mapped to the family's unsuffixed name.
fn multi_suffix_lambda(module: &k_rust::kore::ast::Module) -> BTreeMap<String, String> {
    let mut by_family = BTreeMap::<String, Vec<String>>::new();
    for sentence in &module.sentences {
        let Sentence::SymbolDeclaration { symbol, .. } = sentence else {
            continue;
        };
        let Some(family) = multi_suffix_lambda_family(&symbol.name) else {
            continue;
        };
        by_family
            .entry(family.into())
            .or_default()
            .push(symbol.name.clone());
    }
    by_family
        .into_iter()
        .filter(|(_, names)| names.len() > 1)
        .flat_map(|(family, names)| names.into_iter().map(move |name| (name, family.clone())))
        .collect()
}

/// `ResolveFun.getUniqueLambdaLabel`: `#lambda<h1>_<h2>_` for the first lambda of a hint pair,
/// `#lambda<h1>_<h2>_<n>` (n >= 2) for the following ones. The KORE encoding folds the trailing
/// `_` into the last quoted run (`'Unds'`, `'UndsUnds'`, `'LParUndsRParUnds'`), so the family
/// is the name without its trailing suffix digits, and that name ends in `Unds'`; a hint ending
/// in a digit (`#lambdaF2__`) keeps its digit inside the quoted run.
fn multi_suffix_lambda_family(name: &str) -> Option<&str> {
    name.strip_prefix("Lbl'Hash'lambda")?;
    let family = name.trim_end_matches(|character: char| character.is_ascii_digit());
    family.ends_with("Unds'").then_some(family)
}

fn rename_symbols(pattern: &mut Pattern, renames: &BTreeMap<String, String>) {
    match pattern {
        Pattern::Application { symbol, arguments }
        | Pattern::AssociativeApplication {
            symbol, arguments, ..
        } => {
            if let Some(canonical) = renames.get(&symbol.name) {
                symbol.name = canonical.clone();
            }
            for argument in arguments {
                rename_symbols(argument, renames);
            }
        }
        Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => {
            for argument in arguments {
                rename_symbols(argument, renames);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => rename_symbols(argument, renames),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            rename_symbols(left, renames);
            rename_symbols(right, renames);
        }
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => rename_symbols(body, renames),
        Pattern::Variable(_)
        | Pattern::String(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }
}

fn pattern_mentions_any_symbol(pattern: &Pattern, symbols: &BTreeSet<String>) -> bool {
    match pattern {
        Pattern::Application { symbol, arguments }
        | Pattern::AssociativeApplication {
            symbol, arguments, ..
        } => {
            symbols.contains(&symbol.name)
                || arguments
                    .iter()
                    .any(|argument| pattern_mentions_any_symbol(argument, symbols))
        }
        Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => arguments
            .iter()
            .any(|argument| pattern_mentions_any_symbol(argument, symbols)),
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => pattern_mentions_any_symbol(argument, symbols),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            pattern_mentions_any_symbol(left, symbols)
                || pattern_mentions_any_symbol(right, symbols)
        }
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => pattern_mentions_any_symbol(body, symbols),
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => false,
    }
}

fn strip_unique_id_attributes(attributes: &mut Attributes) {
    attributes.0.retain(|attribute| {
        !matches!(
            attribute,
            Pattern::Application { symbol, .. } if symbol.name == "UNIQUE'Unds'ID"
        )
    });
}

fn strip_attributes(attributes: &mut Attributes) {
    attributes.0.retain(|attribute| {
        !matches!(
            attribute,
            Pattern::Application { symbol, .. }
                if symbol.name == "org'Stop'kframework'Stop'attributes'Stop'Location"
                    || symbol.name == "org'Stop'kframework'Stop'attributes'Stop'Source"
        )
    });
}

fn multiset(values: Vec<String>) -> BTreeMap<String, usize> {
    let mut counts = BTreeMap::new();
    for value in values {
        *counts.entry(value).or_default() += 1;
    }
    counts
}

fn count_differences(
    left: &BTreeMap<String, usize>,
    right: &BTreeMap<String, usize>,
) -> Vec<String> {
    left.iter()
        .flat_map(|(sentence, left_count)| {
            let difference =
                left_count.saturating_sub(right.get(sentence).copied().unwrap_or_default());
            std::iter::repeat_n(sentence.clone(), difference)
        })
        .collect()
}

fn difference_context(reference: Option<&str>, actual: Option<&str>) -> String {
    let (Some(reference), Some(actual)) = (reference, actual) else {
        return format!(
            "missing: {}\nextra: {}",
            reference.unwrap_or("none"),
            actual.unwrap_or("none")
        );
    };
    let reference = reference.chars().collect::<Vec<_>>();
    let actual = actual.chars().collect::<Vec<_>>();
    let index = reference
        .iter()
        .zip(&actual)
        .position(|(reference, actual)| reference != actual)
        .unwrap_or_else(|| reference.len().min(actual.len()));
    let start = index.saturating_sub(250);
    let end = (index + 1800).min(reference.len().max(actual.len()));
    let excerpt = |value: &[char]| {
        value[start.min(value.len())..end.min(value.len())]
            .iter()
            .collect::<String>()
    };
    format!(
        "first difference at character {index}\nreference: …{}…\nactual:    …{}…",
        excerpt(&reference),
        excerpt(&actual)
    )
}

fn sentence_counts(sentences: &[Sentence]) -> String {
    let mut counts = [0; 6];
    for sentence in sentences {
        counts[match sentence {
            Sentence::Import { .. } => 0,
            Sentence::SortDeclaration { .. } => 1,
            Sentence::SymbolDeclaration { .. } => 2,
            Sentence::AliasDeclaration { .. } => 3,
            Sentence::Axiom { .. } => 4,
            Sentence::Claim { .. } => 5,
        }] += 1;
    }
    format!(
        "imports={}, sorts={}, symbols={}, aliases={}, axioms={}, claims={}",
        counts[0], counts[1], counts[2], counts[3], counts[4], counts[5]
    )
}

fn first_sentence_difference(reference: &[Sentence], actual: &[Sentence]) -> String {
    reference
        .iter()
        .zip(actual)
        .position(|(reference, actual)| reference != actual)
        .map_or_else(
            || "common prefix is identical".into(),
            |index| format!("first differing sentence={index}"),
        )
}
