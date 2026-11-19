//! The parametric premise, checked (PJ-34, U34f; kink `trust.md`, "What a kill trusts"): claim
//! removal keeps the prelude's hooked and `concrete` equations when a patch inserts a fresh
//! constructor, on the premise that a prelude equation that names no symbol of the importing
//! definition stays true for any constructor the definition adds. That is
//! a fact about k-rust's hooks as well as about the prelude's text, so it is not taken on trust
//! alone for the equations the premise decides over a prelude-importing definition (the
//! unsupported claims U34f's probe found under the rule without it): K-EQUAL's `=/=K` equation and
//! its two `#if` equations, LIST's `pushList`, SET's `|Set` (`concrete`), and STRING's two
//! `findChar` equations, which reach `#if`.
//!
//! Over `testdata/k/insertion/premise.k` with a fresh constructor `fresh(Int)` inserted at the
//! user sort Val, each equation's left-hand side is simplified by k-rust's backend, which applies
//! a hook's builtin before any equation of its symbol, and compared with the simplified right-hand
//! side the equation gives on the same terms (its `requires` holding). `pushList` and `findChar`
//! have no builtin (k-rust-backend `builtin/evaluated.rs` `NOT_EVALUATED`), so their equations
//! are their meaning and the check is that they evaluate; it becomes a comparison the day a
//! builtin is added, which the dispatch pins below also flag. The prelude's equations and the
//! hook code they are checked against are pinned (`PREMISE_PASSAGES`): a change of either fails
//! here and must be read again.

#[path = "../../../testdata/k/support.rs"]
mod support;

#[path = "../../../testdata/k/passage.rs"]
mod passage;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::definition::{AttributeKey, Attributes, ProductionItem, Sentence};
use k_rust::k_rust_backend::definition::Admission;
use k_rust::kast::identifier::{encode, encode_label};
use k_rust::kast::{Label, Sort};
use k_rust::kompile::initial_configuration::{kore_application, kore_sort};
use k_rust::kore::ast::Pattern;
use kink_patch::{Baseline, ClaimSupport, Edit, InsertPosition, Patch, apply};
use std::path::Path;

const MAIN: &str = "PREMISE";

fn baseline() -> Baseline {
    support::load_path(&Path::new(support::DIR).join("insertion/premise.k"), MAIN)
}

/// The patch that inserts the fresh constructor `fresh(Int)` of sort Val.
fn fresh_constructor() -> Patch {
    Patch::new(vec![Edit::InsertSentence {
        position: InsertPosition::ModuleEnd(MAIN.to_owned()),
        ordinal: 0,
        sentence: Sentence::Production {
            label: Some(Label::new("fresh")),
            parameters: Vec::new(),
            sort: Sort::new("Val"),
            items: vec![
                ProductionItem::Terminal("fresh".to_owned()),
                ProductionItem::Terminal("(".to_owned()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("Int"),
                    name: None,
                },
                ProductionItem::Terminal(")".to_owned()),
            ],
            attributes: Attributes::default(),
        },
    }])
    .expect("patch")
}

/// KORE terms over the mutant: symbols are found by their hook, so that the check names the
/// prelude's symbols as the backend dispatches them.
struct Terms<'b> {
    baseline: &'b Baseline,
}

impl Terms<'_> {
    /// The KORE symbol of the one production hooked `hook`.
    fn hooked(&self, hook: &str) -> String {
        let mut labels = self
            .baseline
            .definition()
            .modules
            .iter()
            .flat_map(|module| &module.local_sentences)
            .filter_map(|sentence| match &**sentence {
                Sentence::Production {
                    label: Some(label),
                    attributes,
                    ..
                } if attributes.string(AttributeKey::Hook) == Some(hook) => {
                    Some(label.name.clone())
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        labels.dedup();
        let [label] = labels.as_slice() else {
            panic!("one production hooked {hook}: {labels:?}");
        };
        encode_label(label)
    }

    fn hook(&self, hook: &str, arguments: Vec<Pattern>) -> Pattern {
        kore_application(&self.hooked(hook), Vec::new(), arguments)
    }

    fn ite(sort: &str, condition: Pattern, then: Pattern, otherwise: Pattern) -> Pattern {
        kore_application(
            &encode_label("ite"),
            vec![kore_sort(sort)],
            vec![condition, then, otherwise],
        )
    }

    fn fresh(value: i64) -> Pattern {
        kore_application(
            &encode_label("fresh"),
            Vec::new(),
            vec![support::int(value)],
        )
    }

    fn z() -> Pattern {
        kore_application(&encode_label("z"), Vec::new(), Vec::new())
    }

    fn item(value: Pattern) -> Pattern {
        kore_application(
            "inj",
            vec![kore_sort("SortVal"), kore_sort("SortKItem")],
            vec![value],
        )
    }

    /// The one-item K sequence of a Val.
    fn k(value: Pattern) -> Pattern {
        kore_application(
            "kseq",
            Vec::new(),
            vec![
                Self::item(value),
                kore_application("dotk", Vec::new(), Vec::new()),
            ],
        )
    }

    fn boolean(value: bool) -> Pattern {
        Pattern::DomainValue {
            sort: kore_sort("SortBool"),
            value: value.to_string().into(),
        }
    }

    fn string(value: &str) -> Pattern {
        Pattern::DomainValue {
            sort: kore_sort("SortString"),
            value: value.into(),
        }
    }

    fn list(&self, values: &[i64]) -> Pattern {
        self.collection("LIST", values)
    }

    fn set(&self, values: &[i64]) -> Pattern {
        self.collection("SET", values)
    }

    /// The collection of the fresh values, as concatenated elements.
    fn collection(&self, namespace: &str, values: &[i64]) -> Pattern {
        let elements = values
            .iter()
            .map(|value| {
                self.hook(
                    &format!("{namespace}.element"),
                    vec![Self::item(Self::fresh(*value))],
                )
            })
            .collect::<Vec<_>>();
        elements
            .into_iter()
            .reduce(|left, right| self.hook(&format!("{namespace}.concat"), vec![left, right]))
            .expect("a nonempty collection")
    }

    /// `findChar(S1, S2, I)`'s right-hand side in domains.md, `S2 =/=String ""`.
    fn find_char_rhs(&self, s1: &str, s2: &str, i: i64) -> Pattern {
        let substr = |from: Pattern, to: Pattern| {
            self.hook("STRING.substr", vec![Self::string(s2), from, to])
        };
        let length = self.hook("STRING.length", vec![Self::string(s2)]);
        let find_string = || {
            self.hook(
                "STRING.find",
                vec![
                    Self::string(s1),
                    substr(support::int(0), support::int(1)),
                    support::int(i),
                ],
            )
        };
        let find_char = || {
            self.hook(
                "STRING.findChar",
                vec![
                    Self::string(s1),
                    substr(support::int(1), length.clone()),
                    support::int(i),
                ],
            )
        };
        let missing = |found: Pattern| self.hook("INT.eq", vec![found, support::int(-1)]);
        Self::ite(
            "SortInt",
            missing(find_string()),
            find_char(),
            Self::ite(
                "SortInt",
                missing(find_char()),
                find_string(),
                self.hook("INT.min", vec![find_string(), find_char()]),
            ),
        )
    }
}

fn simplify(backend: &mut Backend, pattern: &Pattern) -> Pattern {
    backend
        .simplify_kore(None, pattern, Admission::Unverified)
        .unwrap_or_else(|error| panic!("{pattern:?} simplifies: {error:?}"))
}

/// On terms built with the fresh constructor, each blocking prelude equation's left-hand side,
/// which the backend evaluates by its hook where it has a builtin, is the value the equation's
/// right-hand side gives, and that value is the one expected.
#[test]
fn the_prelude_equations_agree_with_the_hooks_on_a_fresh_constructor() {
    let baseline = baseline();
    let patch = fresh_constructor();
    let withdrawal = ClaimSupport::new(&baseline)
        .withdraw(&baseline, &patch)
        .expect("the patch applies");
    assert!(withdrawal.trusted(), "{:?}", withdrawal.unsupported);
    let mutant = apply(&baseline, &patch).expect("the patch applies");
    let compiled = support::compile(&mutant.to_loaded(&baseline).expect("the mutant relinks"))
        .expect("the mutant compiles");
    let mut backend = Backend::new(
        &compiled.definition_kore,
        encode(MAIN),
        BackendOptions::DEFAULT,
    )
    .expect("backend");
    let terms = Terms {
        baseline: &baseline,
    };
    for (name, left, right, expected) in cases(&terms) {
        let by_hook = simplify(&mut backend, &left);
        let by_equation = simplify(&mut backend, &right);
        let expected = simplify(&mut backend, &expected);
        assert_eq!(
            by_hook, by_equation,
            "{name}: the hook and the equation disagree on {left:?}"
        );
        assert_eq!(by_hook, expected, "{name}: {left:?}");
    }
}

/// Each checked equation's instances: its name, its left-hand side, its right-hand side on the
/// same terms, and the value expected of both.
fn cases(terms: &Terms) -> Vec<(&'static str, Pattern, Pattern, Pattern)> {
    let (f1, f2) = (Terms::fresh(1), Terms::fresh(2));
    let mut cases = Vec::new();

    // rule K1:K =/=K K2:K => notBool (K1 ==K K2)
    for (left, right, differ) in [
        (f1.clone(), f2.clone(), true),
        (f1.clone(), f1.clone(), false),
        (f1.clone(), Terms::z(), true),
    ] {
        let (left, right) = (Terms::k(left), Terms::k(right));
        cases.push((
            "=/=K",
            terms.hook("KEQUAL.ne", vec![left.clone(), right.clone()]),
            terms.hook("BOOL.not", vec![terms.hook("KEQUAL.eq", vec![left, right])]),
            Terms::boolean(differ),
        ));
    }
    // rule #if C:Bool #then B1::K #else _ #fi => B1 requires C, and its `notBool C` twin, at K
    // and at the user sort.
    for condition in [true, false] {
        let chosen = if condition { &f1 } else { &f2 };
        cases.push((
            "#if (K)",
            Terms::ite(
                "SortK",
                Terms::boolean(condition),
                Terms::k(f1.clone()),
                Terms::k(f2.clone()),
            ),
            Terms::k(chosen.clone()),
            Terms::k(chosen.clone()),
        ));
        cases.push((
            "#if (Val)",
            Terms::ite("SortVal", Terms::boolean(condition), f1.clone(), f2.clone()),
            chosen.clone(),
            chosen.clone(),
        ));
    }
    // rule pushList(K::KItem, L1::List) => ListItem(K) L1
    cases.push((
        "pushList",
        terms.hook(
            "LIST.push",
            vec![Terms::item(f1.clone()), terms.list(&[2, 3])],
        ),
        terms.hook(
            "LIST.concat",
            vec![
                terms.hook("LIST.element", vec![Terms::item(f1.clone())]),
                terms.list(&[2, 3]),
            ],
        ),
        terms.list(&[1, 2, 3]),
    ));
    // rule S1:Set |Set S2:Set => S1 (S2 -Set S1) [concrete]: both operands are ground.
    let (s1, s2) = (terms.set(&[1, 2]), terms.set(&[2, 3]));
    cases.push((
        "|Set",
        terms.hook("SET.union", vec![s1.clone(), s2.clone()]),
        terms.hook(
            "SET.concat",
            vec![s1.clone(), terms.hook("SET.difference", vec![s2, s1])],
        ),
        terms.set(&[1, 2, 3]),
    ));
    // rule findChar(S1:String, S2:String, I:Int) => #if ... #fi requires S2 =/=String "", and
    // rule findChar(_, "", _) => -1. Their arguments are strings, so no fresh value reaches them;
    // they rest on `#if`, checked above.
    cases.push((
        "findChar",
        terms.hook(
            "STRING.findChar",
            vec![Terms::string("abcb"), Terms::string("cb"), support::int(0)],
        ),
        terms.find_char_rhs("abcb", "cb", 0),
        support::int(1),
    ));
    cases.push((
        "findChar (empty)",
        terms.hook(
            "STRING.findChar",
            vec![Terms::string("abc"), Terms::string(""), support::int(0)],
        ),
        support::int(-1),
        support::int(-1),
    ));
    cases
}

/// The k-rust passages the check rests on: the prelude's equations as written, and the backend's
/// builtins of `==K`, `=/=K`, `#if` and `|Set` with their dispatch, and the LIST and STRING
/// dispatches, where `LIST.push` and `STRING.findChar` have no builtin.
#[test]
fn the_premise_passages_are_pinned() {
    passage::assert_pinned(&k_rust_tree(), &PREMISE_PASSAGES);
}

fn k_rust_tree() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..")
}

const DOMAINS: &str = "crates/k-rust/builtin/domains.md";
const BUILTIN: &str = "crates/k-rust-backend/src/builtin.rs";

const PREMISE_PASSAGES: [passage::Passage; 13] = [
    passage::Passage {
        file: DOMAINS,
        anchor: "### Implementation of Bytes",
        opening: "rule K1:K =/=K K2:K => notBool (K1 ==K K2)",
        lines: 1,
        digest: "59d5c1ca6c88b123bcc5a5751629855b0a6922794af5efb7aeb8c2a6b6e77d09",
    },
    passage::Passage {
        file: DOMAINS,
        anchor: "### Implementation of Bytes",
        opening: "rule #if C:Bool #then B1::K #else _ #fi => B1 requires C",
        lines: 2,
        digest: "ec040bdb655c8b62b4dc4b4b2f4a249dcea243855b98be563d18b5e0c1054bd5",
    },
    passage::Passage {
        file: DOMAINS,
        anchor: "### List prepend",
        opening: "rule pushList(K::KItem, L1::List) => ListItem(K) L1",
        lines: 1,
        digest: "5cf7feab3819cdf1e4081559808b315197ec4fb179535e177aee5e54469ae404",
    },
    passage::Passage {
        file: DOMAINS,
        anchor: "### Set union",
        opening: "rule S1:Set |Set S2:Set => S1 (S2 -Set S1) [concrete]",
        lines: 1,
        digest: "fb8ec919085d7d96d3354a768ebffc486ae5815ce22bec9311d4df5e5859af5e",
    },
    passage::Passage {
        file: DOMAINS,
        anchor: "### Implementation of Strings",
        opening: "rule findChar(S1:String, S2:String, I:Int)",
        lines: 2,
        digest: "e6b7a14f33486516d62c8c3f975f8301462087a0b1577a8556c3b3a45b6a1a3a",
    },
    passage::Passage {
        file: BUILTIN,
        anchor: "fn evaluate_hook_with_context(",
        opening: "\"KEQUAL.ite\" => kequal_ite(arguments),",
        lines: 3,
        digest: "a9e9078660f2e9b72771ea120bf09d678724c04f62440c79f9c1f24d81605950",
    },
    passage::Passage {
        file: BUILTIN,
        anchor: "fn kequal_ite(",
        opening: "fn kequal_ite(arguments",
        lines: 19,
        digest: "8a320e49f2ea377f2864ac0b8e54404a9dce48479b065f3e2ee0bdd2bdb58d0a",
    },
    passage::Passage {
        file: BUILTIN,
        anchor: "fn kequal(",
        opening: "fn kequal(",
        lines: 44,
        digest: "e9c36adc91268074fd0b8b820f5260d5eaf27d7a4ce8090c8df02781f10c3a02",
    },
    passage::Passage {
        file: BUILTIN,
        anchor: "fn evaluate_equality(",
        opening: "fn evaluate_equality(",
        lines: 11,
        digest: "5883762884f59f4f8a2be05efd6dd1dc81a14429da30f78cd623b4e918d55e4f",
    },
    passage::Passage {
        file: "crates/k-rust-backend/src/builtin/set.rs",
        anchor: "pub(super) fn evaluate(",
        opening: "\"SET.union\" => union(arguments, result),",
        lines: 1,
        digest: "545fa1f8f01ccaa5e8f99114e264e626356f1039aca7c923799669f551cd8f78",
    },
    passage::Passage {
        file: "crates/k-rust-backend/src/builtin/set.rs",
        anchor: "fn union(",
        opening: "fn union(arguments",
        lines: 32,
        digest: "738932b1ad69eac3631c666006c850674deb0cb2e5e578108c27d775f1311f16",
    },
    passage::Passage {
        file: "crates/k-rust-backend/src/builtin/list.rs",
        anchor: "pub(super) fn evaluate(",
        opening: "\"LIST.concat\" => concat(arguments, result),",
        lines: 15,
        digest: "6472d9e743f5b92c97437701a1aa3a225fc26ac68a675082392392714cdfd95d",
    },
    passage::Passage {
        file: "crates/k-rust-backend/src/builtin/string.rs",
        anchor: "pub(super) fn evaluate(",
        opening: "\"STRING.eq\" =>",
        lines: 24,
        digest: "aa27c27c20f6aa66b6eb04b631df142950dc4a0ac3fb9298ea2af763d40e8e00",
    },
];
