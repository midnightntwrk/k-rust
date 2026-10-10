//! A map frame of an equation's left-hand side that nothing else in the equation reads
//! (`rule::unread_map_frames`) is not built by the match when the subject map is `ceil_free`
//! (`matching::match_equation_in_definition`): the instance is the same whatever the frame is
//! bound to, so the rest of the subject is not copied to bind it.

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_equation_in_definition, match_terms_in_definition},
    rule::{RewriteRule, TermIndex},
    simplify::{SimplificationOptions, simplify},
    term::{Name, Sort, Term},
};

const PRELUDE: &str = r#"
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortC{} [hook{}("MAP.Map"), unit{}(cUnit{}()), element{}(cItem{}()), concat{}(cConcat{}())]
    hooked-symbol cUnit{}() : SortC{} [function{}(), total{}(), hook{}("MAP.unit")]
    hooked-symbol cItem{}(SortInt{}, SortInt{}) : SortC{} [function{}(), total{}(), hook{}("MAP.element")]
    hooked-symbol cConcat{}(SortC{}, SortC{}) : SortC{}
        [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}(), unit{}(cUnit{}())]
    symbol lookup{}(SortC{}, SortInt{}) : SortInt{} [function{}()]
    symbol pinned{}(SortC{}, SortInt{}) : SortInt{} [function{}()]
    symbol rest{}(SortC{}, SortInt{}) : SortC{} [function{}()]
    symbol both{}(SortC{}, SortC{}) : SortInt{} [function{}()]
"#;

const ENTRY: &str = r"cConcat{}(cItem{}(VarK:SortInt{}, VarV:SortInt{}), VarM:SortC{})";

/// `head(ENTRY, second) = result`, an equation of two arguments.
fn equation(head: &str, second: &str, sort: &str, result: &str, attributes: &str) -> String {
    let second_sort = if second.ends_with("SortC{}") {
        "SortC"
    } else {
        "SortInt"
    };
    format!(
        r"axiom{{R}} \implies{{R}}(\and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortC{{}}, R}}(X0:SortC{{}}, {ENTRY}), \and{{R}}(\in{{{second_sort}{{}}, R}}(X1:{second_sort}{{}}, {second}), \top{{R}}()))), \equals{{{sort}{{}}, R}}({head}{{}}(X0:SortC{{}}, X1:{second_sort}{{}}), \and{{{sort}{{}}}}({result}, \top{{{sort}{{}}}}()))) [{attributes}]"
    )
}

fn load() -> BackendDefinition {
    let axioms = [
        equation("lookup", "VarK:SortInt{}", "SortInt", "VarV:SortInt{}", ""),
        equation(
            "pinned",
            "VarK:SortInt{}",
            "SortInt",
            "VarV:SortInt{}",
            "concrete{}(VarM:SortC{})",
        ),
        equation("rest", "VarK:SortInt{}", "SortC", "VarM:SortC{}", ""),
        equation("both", "VarM:SortC{}", "SortInt", "VarV:SortInt{}", ""),
    ];
    let source = format!(
        "[] module MAIN {PRELUDE} {} endmodule []",
        axioms.join("\n")
    );
    let syntax = parse_definition(&source).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).unwrap(), &[])
        .expect("the term internalizes")
}

fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// The map `{key |-> 10 * key, ...}` over the given keys, each written as a pattern.
fn map(keys: &[String]) -> String {
    keys.iter()
        .enumerate()
        .map(|(index, key)| format!(r"cItem{{}}({key}, {})", int(10 * (index as i64 + 1))))
        .reduce(|left, right| format!(r"cConcat{{}}({left}, {right})"))
        .expect("at least one entry")
}

fn only_equation<'d>(definition: &'d BackendDefinition, head: &str) -> &'d RewriteRule {
    let groups = &definition.function_theory()[&TermIndex::Symbol(Name::from(head))];
    let mut rules = groups.values().flatten();
    let rule = rules.next().expect("one equation");
    assert!(rules.next().is_none(), "{head} has one equation");
    rule
}

fn binds_a_map(result: &MatchResult) -> bool {
    let MatchResult::Success(substitution) = result else {
        panic!("the match succeeds: {result:?}");
    };
    substitution
        .keys()
        .any(|variable| variable.sort == Sort::simple("SortC"))
}

/// The frame of `lookup((K |-> V) M, K) = V` is read by nothing; the frame of `rest` is its
/// result, the frame of `both` is compared with a second argument, and the frame of `pinned`
/// is constrained by `concrete(M)`, so those three read it.
#[test]
fn only_a_frame_no_part_of_the_equation_reads_is_unread() {
    let definition = load();
    let frames = |head| {
        only_equation(&definition, head)
            .computed_attributes
            .unread_map_frames
            .clone()
    };
    let lookup = frames("lookup");
    assert_eq!(lookup.len(), 1);
    assert!(
        lookup
            .iter()
            .all(|variable| variable.sort == Sort::simple("SortC"))
    );
    for head in ["rest", "both", "pinned"] {
        assert!(frames(head).is_empty(), "{head}");
    }
}

/// Against a ground map the unread frame is left unbound, and the instance (`V`) is the one a
/// match that binds the frame finds; against a map with a symbolic key, which is not
/// `ceil_free`, the frame is bound as before. The equation evaluates to the same value.
#[test]
fn an_unread_frame_is_bound_only_where_the_subject_has_obligations() {
    let definition = load();
    let rule = only_equation(&definition, "lookup");
    let frames = &rule.computed_attributes.unread_map_frames;
    let key = int(2);

    let ground = term(
        &definition,
        &format!("lookup{{}}({}, {key})", map(&[int(1), int(2), int(3)])),
    );
    let elided = match_equation_in_definition(&definition, &rule.lhs, &ground, frames);
    let bound = match_terms_in_definition(MatchMode::Evaluate, &definition, &rule.lhs, &ground);
    assert!(!binds_a_map(&elided));
    assert!(binds_a_map(&bound));
    let (MatchResult::Success(elided), MatchResult::Success(mut bound)) = (elided, bound) else {
        unreachable!("checked above");
    };
    bound.retain(|variable, _| !frames.contains(variable));
    assert_eq!(elided, bound);
    assert_eq!(
        simplify(&definition, &ground, SimplificationOptions::default())
            .expect("no stop is armed")
            .expect("the simplification succeeds")
            .term,
        term(&definition, &int(20))
    );

    let symbolic = term(
        &definition,
        &format!(
            "lookup{{}}({}, {key})",
            map(&["VarX:SortInt{}".to_owned(), int(2)])
        ),
    );
    assert!(!symbolic.attributes().ceil_free());
    let kept = match_equation_in_definition(&definition, &rule.lhs, &symbolic, frames);
    assert!(binds_a_map(&kept));
}
