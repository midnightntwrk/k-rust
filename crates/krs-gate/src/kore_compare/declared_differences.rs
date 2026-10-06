//! Declared k-rust/Java K differences that the comparator removes before comparing.
//!
//! Each normalization ports one entry of k-rust's `scripts/reference-normalisations.toml` at the pinned commit.
//! Each acts only on the exact generated shapes that entry names and fails closed otherwise.

use std::collections::BTreeSet;

use k_rust::kore::ast::{Module, Pattern, Sentence, Sort, Symbol};
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
}
