//! The classes of review 2 of the check (the design's "Revision after review 2"): self pairs of
//! left-hand sides that match one subject in several ways (R2.2), checked by probes and by a
//! brute-force enumeration of matchings (V3c), and `SortReach`'s collection edges (T-obs through
//! collection elements). Each class has a V7 switch that the tests show they see.

use std::collections::{BTreeMap, BTreeSet};

use k_rust_kore::kore::parser::parse_definition;

use crate::{
    confluence::{
        UnjoinedReason, UnresolvedShape,
        switches::{self, Switches},
        undetermined_variables,
    },
    definition::BackendDefinition,
    rule::TermIndex,
};

const PRELUDE: &str = r#"
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
    sort SortS{} []
    sort SortB{} []
    symbol mk{}(SortInt{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
    symbol wrapB{}(SortB{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
    symbol v{}(SortInt{}) : SortB{} [anywhere{}(), value-production{}()]
"#;

/// A hooked collection sort `SortC` of kind `kind` (`map`, `list` or `set`) over the sorts
/// `parts` (key and value for a map, the element otherwise), with its unit `cUnit`, element
/// `cItem`, concatenation `cConcat` and size `cSize`.
fn collection(kind: &str, parts: &[&str]) -> String {
    let (hook, axioms) = match kind {
        "map" => ("MAP", "assoc{}(), comm{}(), unit{}(cUnit{}())"),
        "list" => ("LIST", "assoc{}(), unit{}(cUnit{}())"),
        "set" => ("SET", "assoc{}(), comm{}(), idem{}(), unit{}(cUnit{}())"),
        _ => unreachable!("a collection kind"),
    };
    let sort_hook = match kind {
        "map" => "MAP.Map",
        "list" => "LIST.List",
        _ => "SET.Set",
    };
    let parts = parts.join(", ");
    format!(
        r#"
        hooked-sort SortC{{}} [hook{{}}("{sort_hook}"), unit{{}}(cUnit{{}}()), element{{}}(cItem{{}}()), concat{{}}(cConcat{{}}())]
        hooked-symbol cUnit{{}}() : SortC{{}} [function{{}}(), total{{}}(), hook{{}}("{hook}.unit")]
        hooked-symbol cItem{{}}({parts}) : SortC{{}} [function{{}}(), total{{}}(), hook{{}}("{hook}.element")]
        hooked-symbol cConcat{{}}(SortC{{}}, SortC{{}}) : SortC{{}} [function{{}}(), hook{{}}("{hook}.concat"), {axioms}]
        hooked-symbol cSize{{}}(SortC{{}}) : SortInt{{}} [function{{}}(), total{{}}(), hook{{}}("{hook}.size")]
        "#
    )
}

fn load(declarations: &str, axioms: &[String]) -> BackendDefinition {
    let source = format!(
        "[] module MAIN {PRELUDE} {declarations} {} endmodule []",
        axioms.join("\n")
    );
    let syntax = parse_definition(&source).expect("the probe parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the probe internalizes")
}

fn tainted(definition: &BackendDefinition, symbol: &str) -> bool {
    definition
        .value_claims()
        .tainted_symbols()
        .iter()
        .any(|name| name.as_ref() == symbol)
}

/// `head(X0, ..., Xn) = right requires requires`, each `Xi` bound to `patterns[i]` of sort
/// `sorts[i]`.
fn equation(
    head: &str,
    sorts: &[&str],
    result: &str,
    patterns: &[String],
    right: &str,
    requires: &str,
) -> String {
    let memberships = sorts.iter().zip(patterns).enumerate().rev().fold(
        r"\top{R}()".to_owned(),
        |rest, (index, (sort, pattern))| {
            format!(r"\and{{R}}(\in{{{sort}, R}}(X{index}:{sort}, {pattern}), {rest})")
        },
    );
    let parameters = sorts
        .iter()
        .enumerate()
        .map(|(index, sort)| format!("X{index}:{sort}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        r"axiom{{R}} \implies{{R}}(\and{{R}}({requires}, {memberships}), \equals{{{result}, R}}({head}{{}}({parameters}), \and{{{result}}}({right}, \top{{{result}}}()))) []"
    )
}

fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

fn int_equals(term: &str, value: i64) -> String {
    format!(
        r#"\equals{{SortBool{{}}, R}}(eqInt{{}}({term}, {}), \dv{{SortBool{{}}}}("true"))"#,
        int(value)
    )
}

fn without(switch: impl FnOnce(&mut Switches), run: impl FnOnce() -> bool) -> bool {
    let mut switches = Switches::default();
    switch(&mut switches);
    switches::with(switches, run)
}

/// Review 2, probe 1: `pick(K |-> V M) = mk(K)` over a map from `Int` to `B`, `B` built only by
/// `v`. On `{1 |-> b, 2 |-> b}` the two matchings give `mk(1) = mk(2)`, so every model has `B`
/// empty and `v(1)` undefined. The equation is a peak with itself.
fn pick() -> BackendDefinition {
    let declarations = format!(
        "{} symbol pick{{}}(SortC{{}}) : SortS{{}} [function{{}}()]",
        collection("map", &["SortInt{}", "SortB{}"])
    );
    load(
        &declarations,
        &[equation(
            "pick",
            &["SortC{}"],
            "SortS{}",
            &["cConcat{}(cItem{}(VarK:SortInt{}, VarV:SortB{}), VarM:SortC{})".into()],
            "mk{}(VarK:SortInt{})",
            r"\top{R}()",
        )],
    )
}

/// Review 2, probe 2: `pickW(SetItem(X) S) = wrapB(X)` over a set of `B`.
fn pick_set() -> BackendDefinition {
    let declarations = format!(
        "{} symbol pickW{{}}(SortC{{}}) : SortS{{}} [function{{}}()]",
        collection("set", &["SortB{}"])
    );
    load(
        &declarations,
        &[equation(
            "pickW",
            &["SortC{}"],
            "SortS{}",
            &["cConcat{}(cItem{}(VarX:SortB{}), VarS:SortC{})".into()],
            "wrapB{}(VarX:SortB{})",
            r"\top{R}()",
        )],
    )
}

#[test]
fn review_2_self_pairs_withdraw_v_and_are_seen_without_their_rule() {
    for (name, build) in [
        ("pick", pick as fn() -> BackendDefinition),
        ("pickW", pick_set),
    ] {
        let definition = build();
        let claims = definition.value_claims();
        assert!(
            claims.unjoined().iter().any(|pair| {
                pair.reason == UnjoinedReason::Unresolved(UnresolvedShape::SeveralMatches)
                    && pair.relevant()
            }),
            "{name}: {:?}",
            claims.unjoined()
        );
        assert_eq!(claims.counts().several_matches, 1, "{name}");
        assert!(tainted(&definition, "v"), "{name}");
        assert!(
            !without(|s| s.drop_several_matches = true, || tainted(&build(), "v")),
            "{name}: v is withdrawn without the self pairs"
        );
    }
}

/// The same shapes where the matchings cannot disagree: a key fixed by another argument (unitary
/// matching), and a right-hand side that reads no variable the matching chooses (a trivial
/// peak). Neither withdraws anything.
#[test]
fn a_fixed_key_or_a_result_independent_of_the_matching_withdraws_nothing() {
    let declarations = format!(
        "{} symbol look{{}}(SortC{{}}, SortInt{{}}) : SortS{{}} [function{{}}()]
        symbol nonEmpty{{}}(SortC{{}}) : SortS{{}} [function{{}}()]",
        collection("map", &["SortInt{}", "SortB{}"])
    );
    let definition = load(
        &declarations,
        &[
            equation(
                "look",
                &["SortC{}", "SortInt{}"],
                "SortS{}",
                &[
                    "cConcat{}(cItem{}(VarK:SortInt{}, VarV:SortB{}), VarM:SortC{})".into(),
                    "VarK:SortInt{}".into(),
                ],
                "wrapB{}(VarV:SortB{})",
                r"\top{R}()",
            ),
            equation(
                "nonEmpty",
                &["SortC{}"],
                "SortS{}",
                &["cConcat{}(cItem{}(VarK:SortInt{}, VarV:SortB{}), VarM:SortC{})".into()],
                &format!("mk{{}}({})", int(1)),
                r"\top{R}()",
            ),
        ],
    );
    let claims = definition.value_claims();
    assert!(claims.unjoined().is_empty(), "{:?}", claims.unjoined());
    assert_eq!(claims.counts().several_matches, 1);
    assert!(!tainted(&definition, "v"));
}

/// T-obs through each collection edge of `SortReach`: `g(C) = mk(1) requires size(C) ==Int 1`
/// beside `g(C) = mk(2)`, with `B`, built only by `v`, at the collection's `part`. Every model
/// has no singleton collection, so `B` is empty and `v(1)` undefined: `v` must be withdrawn, and
/// it is not when the collection edges are dropped.
#[test]
fn a_pair_withdraws_the_heads_its_collection_variables_hold() {
    for (kind, parts) in [
        ("map", ["SortB{}", "SortInt{}"].as_slice()),
        ("map", ["SortInt{}", "SortB{}"].as_slice()),
        ("list", ["SortB{}"].as_slice()),
        ("set", ["SortB{}"].as_slice()),
    ] {
        let build = || {
            let declarations = format!(
                "{} symbol g{{}}(SortC{{}}) : SortS{{}} [function{{}}()]",
                collection(kind, parts)
            );
            load(
                &declarations,
                &[
                    equation(
                        "g",
                        &["SortC{}"],
                        "SortS{}",
                        &["VarM:SortC{}".into()],
                        &format!("mk{{}}({})", int(1)),
                        &int_equals("cSize{}(VarM:SortC{})", 1),
                    ),
                    equation(
                        "g",
                        &["SortC{}"],
                        "SortS{}",
                        &["VarM:SortC{}".into()],
                        &format!("mk{{}}({})", int(2)),
                        r"\top{R}()",
                    ),
                ],
            )
        };
        let definition = build();
        assert!(
            definition
                .value_claims()
                .unjoined()
                .iter()
                .any(|pair| pair.reason == UnjoinedReason::ConditionOpen),
            "{kind} {parts:?}: {:?}",
            definition.value_claims().unjoined()
        );
        assert!(tainted(&definition, "v"), "{kind} {parts:?}");
        assert!(
            !without(
                |s| s.drop_collection_edges = true,
                || tainted(&build(), "v")
            ),
            "{kind} {parts:?}: v is withdrawn without the collection edges"
        );
    }
}

// ---- V3c: self pairs by brute force ----

/// A key, element or map value pattern of the generated language.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Slot {
    Literal(i64),
    Variable(&'static str),
}

impl Slot {
    fn kore(self) -> String {
        match self {
            Self::Literal(value) => int(value),
            Self::Variable(name) => format!("Var{name}:SortInt{{}}"),
        }
    }
}

/// `f(C, J) = res(first, second, rest) [requires x ==Int n]`: `C` a map (`Int` keys and values)
/// or set (`Int` elements) pattern with `entries` (keys and, for a map, values) and an optional
/// rest `M`; `J` the variable `J` or the literal 1; `rest` in the result the rest `M` or the unit.
#[derive(Clone, Debug)]
struct Generated {
    set: bool,
    entries: Vec<(Slot, Slot)>,
    rest: bool,
    j_variable: bool,
    result: (Slot, Slot, bool),
    requires: Option<(&'static str, i64)>,
}

/// A value bound by a matching.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Value {
    Int(i64),
    Collection(Vec<(i64, i64)>),
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, bound: usize) -> usize {
        usize::try_from(self.next() % bound as u64).expect("a small bound")
    }
}

impl Generated {
    fn random(rng: &mut Rng) -> Self {
        let set = rng.below(2) == 0;
        let j_variable = rng.below(3) != 0;
        let mut keys = vec![
            Slot::Literal(0),
            Slot::Literal(1),
            Slot::Literal(2),
            Slot::Variable("K0"),
            Slot::Variable("K1"),
        ];
        if j_variable {
            keys.push(Slot::Variable("J"));
        }
        let values = [
            Slot::Literal(0),
            Slot::Literal(1),
            Slot::Variable("V0"),
            Slot::Variable("V1"),
            Slot::Variable("K0"),
        ];
        let mut entries = Vec::new();
        for _ in 0..rng.below(3) {
            let key = keys.remove(rng.below(keys.len()));
            let value = if set {
                Slot::Literal(0)
            } else {
                values[rng.below(values.len())]
            };
            entries.push((key, value));
        }
        let rest = rng.below(3) != 0;
        let mut variables = vec![];
        for (key, value) in &entries {
            for slot in [key, value] {
                if let Slot::Variable(name) = slot
                    && (!set || slot == key)
                    && !variables.contains(name)
                {
                    variables.push(*name);
                }
            }
        }
        if j_variable && !variables.contains(&"J") {
            variables.push("J");
        }
        let pick = |rng: &mut Rng| {
            if variables.is_empty() || rng.below(4) == 0 {
                Slot::Literal(i64::try_from(rng.below(2)).expect("small"))
            } else {
                Slot::Variable(variables[rng.below(variables.len())])
            }
        };
        let result = (pick(rng), pick(rng), rest && rng.below(2) == 0);
        let requires = (rng.below(3) == 0 && !variables.is_empty()).then(|| {
            (
                variables[rng.below(variables.len())],
                i64::try_from(rng.below(3)).expect("small"),
            )
        });
        Self {
            set,
            entries,
            rest,
            j_variable,
            result,
            requires,
        }
    }

    fn kore(&self) -> String {
        let declarations = format!(
            "{}
            symbol res{{}}(SortInt{{}}, SortInt{{}}, SortC{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol f{{}}(SortC{{}}, SortInt{{}}) : SortS{{}} [function{{}}()]",
            if self.set {
                collection("set", &["SortInt{}"])
            } else {
                collection("map", &["SortInt{}", "SortInt{}"])
            }
        );
        let mut parts = self
            .entries
            .iter()
            .map(|(key, value)| {
                if self.set {
                    format!("cItem{{}}({})", key.kore())
                } else {
                    format!("cItem{{}}({}, {})", key.kore(), value.kore())
                }
            })
            .collect::<Vec<_>>();
        if self.rest {
            parts.push("VarM:SortC{}".into());
        }
        let collection = parts
            .into_iter()
            .rev()
            .reduce(|right, left| format!("cConcat{{}}({left}, {right})"))
            .unwrap_or_else(|| "cUnit{}()".into());
        let j = if self.j_variable {
            "VarJ:SortInt{}".to_owned()
        } else {
            int(1)
        };
        let rest = if self.result.2 {
            "VarM:SortC{}"
        } else {
            "cUnit{}()"
        };
        let right = format!(
            "res{{}}({}, {}, {rest})",
            self.result.0.kore(),
            self.result.1.kore()
        );
        let requires = self.requires.map_or_else(
            || r"\top{R}()".to_owned(),
            |(variable, value)| int_equals(&format!("Var{variable}:SortInt{{}}"), value),
        );
        format!(
            "[] module MAIN {PRELUDE} {declarations} {} endmodule []",
            equation(
                "f",
                &["SortC{}", "SortInt{}"],
                "SortS{}",
                &[collection, j],
                &right,
                &requires,
            )
        )
    }

    /// Every matching of the left-hand side against `subject` (sorted entries; a set's values are
    /// 0) and `j`, by brute force: an injective assignment of the pattern's entries to the
    /// subject's, the remainder bound to the rest.
    fn matchings(&self, subject: &[(i64, i64)], j: i64) -> BTreeSet<BTreeMap<&'static str, Value>> {
        fn bind(slot: Slot, value: i64, binding: &mut BTreeMap<&'static str, Value>) -> bool {
            match slot {
                Slot::Literal(literal) => literal == value,
                Slot::Variable(name) => match binding.get(name) {
                    Some(bound) => *bound == Value::Int(value),
                    None => {
                        binding.insert(name, Value::Int(value));
                        true
                    }
                },
            }
        }
        fn assign(
            generated: &Generated,
            index: usize,
            used: &mut Vec<bool>,
            subject: &[(i64, i64)],
            binding: &BTreeMap<&'static str, Value>,
            into: &mut BTreeSet<BTreeMap<&'static str, Value>>,
        ) {
            if index == generated.entries.len() {
                let remainder = subject
                    .iter()
                    .zip(used.iter())
                    .filter(|(_, used)| !**used)
                    .map(|(entry, _)| *entry)
                    .collect::<Vec<_>>();
                let mut binding = binding.clone();
                if generated.rest {
                    binding.insert("M", Value::Collection(remainder));
                } else if !remainder.is_empty() {
                    return;
                }
                into.insert(binding);
                return;
            }
            let (key, value) = generated.entries[index];
            for (position, entry) in subject.iter().enumerate() {
                if used[position] {
                    continue;
                }
                let mut extended = binding.clone();
                if bind(key, entry.0, &mut extended)
                    && (generated.set || bind(value, entry.1, &mut extended))
                {
                    used[position] = true;
                    assign(generated, index + 1, used, subject, &extended, into);
                    used[position] = false;
                }
            }
        }
        let mut binding = BTreeMap::new();
        if self.j_variable {
            binding.insert("J", Value::Int(j));
        } else if j != 1 {
            return BTreeSet::new();
        }
        let mut matchings = BTreeSet::new();
        assign(
            self,
            0,
            &mut vec![false; subject.len()],
            subject,
            &binding,
            &mut matchings,
        );
        matchings
    }

    /// The right-hand side's instance under a matching, when its `requires` holds.
    fn reduct(&self, binding: &BTreeMap<&'static str, Value>) -> Option<(Value, Value, Value)> {
        let slot = |slot: Slot| match slot {
            Slot::Literal(value) => Value::Int(value),
            Slot::Variable(name) => binding[name].clone(),
        };
        if let Some((variable, value)) = self.requires
            && binding[variable] != Value::Int(value)
        {
            return None;
        }
        let rest = if self.result.2 {
            binding["M"].clone()
        } else {
            Value::Collection(Vec::new())
        };
        Some((slot(self.result.0), slot(self.result.1), rest))
    }

    /// Every subject the brute force tries: maps over keys `{0, 1, 2}` and values `{0, 1}`, or
    /// sets over `{0, 1, 2}` (values 0).
    fn subjects(&self) -> Vec<Vec<(i64, i64)>> {
        let choices: &[Option<i64>] = if self.set {
            &[None, Some(0)]
        } else {
            &[None, Some(0), Some(1)]
        };
        let mut subjects = vec![Vec::new()];
        for key in 0..3 {
            subjects = subjects
                .into_iter()
                .flat_map(|subject: Vec<(i64, i64)>| {
                    choices.iter().map(move |choice| {
                        let mut subject = subject.clone();
                        if let Some(value) = choice {
                            subject.push((key, *value));
                        }
                        subject
                    })
                })
                .collect();
        }
        subjects
    }
}

#[derive(Debug, Default)]
struct SelfPairs {
    definitions: usize,
    peaks: usize,
    unitary: usize,
    failures: Vec<String>,
}

fn check_self_pairs(cases: u64) -> SelfPairs {
    let mut result = SelfPairs::default();
    let mut rng = Rng(0x5eed_0002_u64);
    for case in 0..cases {
        let generated = Generated::random(&mut rng);
        let source = generated.kore();
        let syntax = parse_definition(&source).expect("the generated definition parses");
        let definition = match BackendDefinition::internalize(&syntax, "MAIN") {
            Ok(definition) => definition,
            Err(error) => {
                result
                    .failures
                    .push(format!("case {case}: {error:?}\n{generated:?}"));
                continue;
            }
        };
        result.definitions += 1;
        let rules = definition
            .function_theory()
            .get(&TermIndex::Symbol("f".into()))
            .map(|priorities| priorities.values().flatten().cloned().collect::<Vec<_>>())
            .unwrap_or_default();
        let [rule] = rules.as_slice() else {
            result.failures.push(format!(
                "case {case}: {} equations at f\n{generated:?}",
                rules.len()
            ));
            continue;
        };
        let unitary = undetermined_variables(&rule.lhs).is_empty();
        let reported =
            definition.value_claims().unjoined().iter().any(|pair| {
                pair.reason == UnjoinedReason::Unresolved(UnresolvedShape::SeveralMatches)
            });
        let mut peak = None;
        let mut several = None;
        for subject in generated.subjects() {
            for j in 0..3 {
                let matchings = generated.matchings(&subject, j);
                if matchings.len() > 1 {
                    several.get_or_insert((subject.clone(), j, matchings.len()));
                }
                let reducts = matchings
                    .iter()
                    .filter_map(|binding| generated.reduct(binding))
                    .collect::<BTreeSet<_>>();
                if reducts.len() > 1 {
                    peak.get_or_insert((subject.clone(), j, reducts));
                }
            }
        }
        if unitary {
            result.unitary += 1;
            if let Some((subject, j, count)) = several {
                result.failures.push(format!(
                    "case {case}: every variable is called determined, yet {count} matchings at {subject:?}, {j}\n{generated:?}"
                ));
            }
        }
        if let Some((subject, j, reducts)) = peak {
            result.peaks += 1;
            if !reported {
                result.failures.push(format!(
                    "case {case}: the matchings at {subject:?}, {j} give {reducts:?}, and no self pair is reported\n{generated:?}"
                ));
            }
        }
    }
    result
}

/// V3c: whenever two matchings of a left-hand side against one subject give different results,
/// the check reports the equation's self pair; and a left-hand side whose variables the check
/// calls determined matches every subject in at most one way. The ground truth is a brute-force
/// enumeration of matchings over every small map or set, sharing no code with the backend's
/// matcher or with the fixpoint of `undetermined_variables`.
#[test]
fn every_self_peak_of_small_collection_patterns_is_reported() {
    let result = check_self_pairs(600);
    eprintln!(
        "self pairs: {} definitions, {} with a peak, {} unitary, {} failures",
        result.definitions,
        result.peaks,
        result.unitary,
        result.failures.len()
    );
    assert!(result.failures.is_empty(), "{}", result.failures.join("\n"));
    assert!(result.peaks >= 60, "too few peaks: {}", result.peaks);
    assert!(result.unitary >= 60, "too few unitary: {}", result.unitary);
}

#[test]
fn the_self_pair_brute_force_sees_a_check_without_self_pairs() {
    let result = switches::with(
        Switches {
            drop_several_matches: true,
            ..Switches::default()
        },
        || check_self_pairs(200),
    );
    assert!(
        !result.failures.is_empty(),
        "no failure without the self pairs"
    );
}
