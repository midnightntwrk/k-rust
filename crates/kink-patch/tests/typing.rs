//! Typing is a generation aid and a diagnostic, never a verdict (decision 4; findings C-02,
//! C-03; packets L2-2 and L2-2-fix-1).
//!
//! A mutant is valid when it compiles. kink-patch reads compilation's typing view (one
//! `SentenceTyper::for_compilation` per resolved definition, with `typing_in` the declaring
//! module; k-rust docs/compatibility.md, the `SentenceTyper` paragraphs) for site sorts, falling
//! back to the declaring module's own view, and records an edited rule's errors there as
//! `Mutant::typing_diagnostics`. No typing error refuses a patch or excludes a rule: k-rust's
//! contract that a typing error implies compilation fails is false at 501f18b9 (the LUB fixtures
//! below, from review L2-2-review-1).

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::builtin;
use k_rust::definition::{ResolvedDefinition, Sentence};
use k_rust::kast::{Sort, Term};
use k_rust::kompile::{SentenceTyper, SentenceTypingError};
use k_rust::outer::ResolvedSource;
use kink_patch::{
    Baseline, CandidateDisposition, Discovery, DiscoveryTuple, Edit, Patch, SelectionPolicy,
    SentenceOrigin, Site, SiteSelector, TermRef, Universe, apply, derive_sites_in,
    resolve_universe, select,
};

fn load(module: &str, text: &str) -> Baseline {
    load_with_syntax(module, None, text)
}

fn load_with_syntax(module: &str, syntax: Option<&str>, text: &str) -> Baseline {
    let mut resolver = |_: &str, name: &str| {
        builtin::embedded(name).ok_or_else(|| format!("{name} is not embedded"))
    };
    Baseline::load(
        ResolvedSource::new("typing.k", text),
        module,
        syntax,
        &mut resolver,
        &support::options(),
    )
    .expect("inline fixture loads")
}

/// C-03 case (a): `B` imports only `INT-SYNTAX`, so its own module's view lacks the `K` sequence
/// order and `twice` does not type there; compilation types it with the main module's injector,
/// over a closure that has it, and compiles the definition.
const MODULE_VIEW: &str = r#"module MODVIEW
  imports B
  imports INT
  imports BOOL
endmodule

module B
  imports INT-SYNTAX
  syntax KItem ::= step(Int) | done(Int)
  rule [twice]: step(X) => done(X) ~> done(X)
endmodule
"#;

/// C-03 case (c): a local function whose equation has a variable in the body of a cell with
/// children; compilation accepts it, and the typer refuses it with `CellCompletion`, the
/// contract's stated exception (k-rust tests/sentence_typing.rs
/// a_cell_with_a_variable_in_a_local_functions_equation_is_refused).
const CELL_COMPLETION: &str = r#"module UNTYPEDCELL
  imports INT
  imports BOOL
  configuration <t>
    <k> $PGM:K </k>
    <accounts> <account multiplicity="*" type="Map"> <id> 0 </id> <bal> 0 </bal> </account> </accounts>
  </t>
  syntax KItem ::= "go" | "stop" | box(AccountsCell) | fooK(K)
  rule [completed]: <k> go => #fun(box(<accounts> B </accounts>) => fooK(B))(box(<accounts> A </accounts>)) ... </k> <accounts> A </accounts>
  rule [plain]: <k> stop => .K ... </k>
endmodule
"#;

/// A module the main module does not import.
const OUTSIDE: &str = r#"module OUTSIDE
  imports INT
  syntax KItem ::= start(Int) | finish(Int)
  rule [inside]: start(X) => finish(X)
endmodule

module OTHER
  imports INT
  syntax KItem ::= other(Int)
  rule [outside]: other(X) => other(X +Int 1)
endmodule
"#;

/// A syntax module the main module does not import: `load_for_compilation` keeps it, and its
/// closure, outside the main module's import closure (k-rust `select_modules` retains the main,
/// syntax and configuration modules, the well-known modules and every bubble-free module; review
/// L2-2-review-1 minor 1, probe synout3). Compilation never emits its rules.
const SYNTAX_OUTSIDE: &str = r#"module SYN3-CFG
  imports INT
  syntax Pgm ::= go(Int) [symbol(go)]
  syntax KItem ::= aux(Int) [symbol(aux)] | done(Int) [symbol(done)]
  syntax Int ::= sf(Int) [function, total, symbol(sf)]
  configuration <k> $PGM:Pgm </k>
  rule [sfr]: sf(X) => X +Int 10
endmodule

module SYN3-SYNTAX
  imports SYN3-CFG
  rule [srule]: <k> aux(X) => done(X +Int 100) ... </k>
  rule [sfr2]: sf(0) => 5
endmodule

module SYN3
  imports SYN3-CFG
  rule [go]: go(X) => aux(sf(X))
  rule [mrule]: aux(X) => done(X +Int 1) [owise]
endmodule
"#;

/// The counterexample to k-rust's one-directional contract (review L2-2-review-1, probe lubbase):
/// `LUBBB` declares `C ::= A | B` and the rule `a(X) => b(X)`, whose two sides need the least
/// upper bound of `A` and `B`; the main module adds a second common supersort `D`. Compilation's
/// view gives a `Sort` error (no unique least upper bound), the own module's view types the
/// rule, and compilation accepts the definition and runs it.
const LUB_IMPORTED: &str = r#"module LUBBASE-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
endmodule

module LUBBB
  imports INT-SYNTAX
  syntax A ::= a(Int) [symbol(a)]
  syntax B ::= b(Int) [symbol(b)]
  syntax C ::= A | B
  rule [ab]: a(X) => b(X)
endmodule

module LUBBASE
  imports LUBBASE-SYNTAX
  imports LUBBB
  imports INT
  syntax D ::= A | B
  configuration <k> $PGM:Pgm </k>
  rule [go]: go(X) => a(X)
endmodule
"#;

/// The same rule in the main module, whose own view is compilation's (probe lubmain): neither
/// view types it, and compilation accepts it.
const LUB_MAIN: &str = r#"module LUBM-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
endmodule

module LUBM
  imports LUBM-SYNTAX
  imports INT
  syntax A ::= a(Int) [symbol(a)]
  syntax B ::= b(Int) [symbol(b)]
  syntax C ::= A | B
  syntax D ::= A | B
  configuration <k> $PGM:Pgm </k>
  rule [go]: go(X) => a(X)
  rule [ab]: a(X) => b(X)
endmodule
"#;

fn rule_sentence<'a>(
    definition: &'a k_rust::definition::Definition,
    at: &kink_patch::SentenceRef,
) -> &'a Sentence {
    definition
        .modules
        .iter()
        .find(|module| module.name == at.module)
        .and_then(|module| module.local_sentences.get(at.index as usize))
        .expect("sentence")
}

/// Compilation's typing view of the sentence at `at`.
fn compilation_typing(
    definition: &k_rust::definition::Definition,
    at: &kink_patch::SentenceRef,
) -> Result<(), SentenceTypingError> {
    let resolved = ResolvedDefinition::resolve(definition).expect("resolves");
    SentenceTyper::for_compilation(&resolved)?
        .typing_in(rule_sentence(definition, at), &at.module)
        .map(|_| ())
}

/// The pre-L2-2 gate: the sentence typed in its own module's view.
fn own_module_typing(
    definition: &k_rust::definition::Definition,
    at: &kink_patch::SentenceRef,
) -> Result<(), SentenceTypingError> {
    let resolved = ResolvedDefinition::resolve(definition).expect("resolves");
    SentenceTyper::new(&resolved, &at.module)?
        .typing(rule_sentence(definition, at))
        .map(|_| ())
}

/// `twice` with the second item of its right-hand side, `done(X)`, replaced by its left-hand
/// side `step(X)`: the edited rule still holds `~>`, so its own module still does not type it.
fn second_item_steps(baseline: &Baseline) -> Patch {
    let at = support::rule(baseline, "B.twice");
    let term = |path: &[u32]| {
        baseline
            .term(&TermRef::new(at.clone(), path))
            .unwrap_or_else(|| panic!("{path:?}"))
            .clone()
    };
    assert!(matches!(term(&[0, 1]).unannotated(), Term::Sequence(_)));
    Patch::new(vec![Edit::ReplaceTerm {
        at: TermRef::new(at.clone(), [0, 1, 1]),
        expected: term(&[0, 1, 1]),
        replacement: term(&[0, 0]),
    }])
    .expect("one edit")
    .pinned(baseline)
    .expect("pins")
}

#[test]
fn a_rule_that_types_only_in_compilations_view_is_a_site_and_its_edit_compiles() {
    let baseline = load("MODVIEW", MODULE_VIEW);
    support::compile(baseline.loaded()).expect("the baseline compiles");
    let twice = support::rule(&baseline, "B.twice");
    // The sentence's own module does not type it; compilation's view does.
    assert!(matches!(
        own_module_typing(baseline.definition(), &twice),
        Err(SentenceTypingError::Sort { .. })
    ));
    let compilation = SentenceTyper::for_compilation(baseline.loaded().resolved()).expect("typer");
    compilation
        .typing_in(rule_sentence(baseline.definition(), &twice), "B")
        .expect("compilation's view types twice");

    // The universe: before L2-2 twice was excluded as Untyped.
    let universe = resolve_universe(&baseline, &Universe::v1());
    assert_eq!(universe.excluded(), &[]);
    assert!(universe.included().contains(&twice));
    // Its sites have sorts, so a sort-selected discovery over it is exhaustive.
    let discovery = derive_sites_in(
        &baseline,
        &universe,
        &[
            SiteSelector::RuleLabel("B.twice".to_owned()),
            SiteSelector::Sort(Sort::new("Int")),
        ],
    )
    .expect("sites");
    assert!(discovery.exhaustive());
    assert!(!discovery.tuples().is_empty());

    // The edit: before L2-2 apply refused it (locally-ill-formed, the own-module error).
    let patch = second_item_steps(&baseline);
    let mutant = apply(&baseline, &patch).expect("compilation's view types the edited rule");
    assert!(own_module_typing(mutant.definition(), &twice).is_err());
    assert_eq!(mutant.typing_diagnostics(), &[]);
    support::compile(&mutant.to_loaded(&baseline).expect("relinks")).expect("the mutant compiles");
}

#[test]
fn a_cell_completion_shape_is_left_to_compilation() {
    let baseline = load("UNTYPEDCELL", CELL_COMPLETION);
    support::compile(baseline.loaded()).expect("the baseline compiles");
    let completed = support::rule(&baseline, "UNTYPEDCELL.completed");
    // L2-2-fix-1: no view types it, and the universe includes it without site sorts (L2-2 and
    // before: excluded as Untyped).
    let universe = resolve_universe(&baseline, &Universe::v1());
    assert_eq!(universe.excluded(), &[]);
    assert!(universe.included().contains(&completed));
    assert_eq!(universe.unsorted(), std::slice::from_ref(&completed));
    // An edit of it applies (before L2-2: refused with the CellCompletion error) and compiles;
    // the error is a diagnostic.
    let requires = baseline
        .term(&TermRef::new(completed.clone(), [1]))
        .expect("requires")
        .clone();
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        at: TermRef::new(completed.clone(), [1]),
        expected: requires,
        replacement: Term::Token {
            token: "false".to_owned(),
            sort: Sort::new("Bool"),
        },
    }])
    .expect("one edit");
    let mutant = apply(&baseline, &patch).expect("CellCompletion is compilation's to decide");
    assert!(matches!(
        own_module_typing(mutant.definition(), &completed),
        Err(SentenceTypingError::CellCompletion { .. })
    ));
    let [diagnostic] = mutant.typing_diagnostics() else {
        panic!("{:?}", mutant.typing_diagnostics());
    };
    assert_eq!(
        diagnostic.origin,
        SentenceOrigin::Baseline(completed.clone())
    );
    assert!(
        diagnostic.message.contains("local function"),
        "{}",
        diagnostic.message
    );
    support::compile(&mutant.to_loaded(&baseline).expect("relinks")).expect("the mutant compiles");
}

/// A loaded baseline holds the modules its main module reaches, and also the syntax module's
/// closure and k-rust's other retained roots (review L2-2-review-1 minor 1; L2-2 stated the
/// first half only). A module nothing retains is not loaded.
#[test]
fn a_module_the_main_module_does_not_import_is_not_loaded() {
    let baseline = load("OUTSIDE", OUTSIDE);
    let names = baseline
        .definition()
        .modules
        .iter()
        .map(|module| module.name.as_str())
        .collect::<Vec<_>>();
    assert!(
        names.contains(&"OUTSIDE") && !names.contains(&"OTHER"),
        "{names:?}"
    );
    assert_eq!(resolve_universe(&baseline, &Universe::v1()).excluded(), &[]);
}

/// A syntax module outside the main closure is loaded with its rules. Compilation's view says
/// nothing about them; the own module's view gives their site sorts (as at 1ee9955; L2-2 excluded
/// them as Untyped), and an edit of one applies with no diagnostic and compiles. Compilation never
/// emits such a rule, so its mutants compile equal to the baseline (kink-flow tests/search.rs
/// a_syntax_module_rule_outside_the_main_closure_is_an_equivalent_mutation).
#[test]
fn a_syntax_module_outside_the_main_closure_is_loaded_and_typed_in_its_own_view() {
    let baseline = load_with_syntax("SYN3", Some("SYN3-SYNTAX"), SYNTAX_OUTSIDE);
    support::compile(baseline.loaded()).expect("the baseline compiles");
    let resolved = baseline.loaded().resolved();
    let main = resolved.main_module_id();
    let closure = resolved
        .transitive_imports(main)
        .into_iter()
        .chain([main])
        .map(|id| resolved.module(id).name.clone())
        .collect::<Vec<_>>();
    assert!(
        !closure.iter().any(|name| name == "SYN3-SYNTAX"),
        "{closure:?}"
    );
    let srule = support::rule(&baseline, "SYN3-SYNTAX.srule");
    let sfr2 = support::rule(&baseline, "SYN3-SYNTAX.sfr2");
    let universe = resolve_universe(&baseline, &Universe::v1());
    assert_eq!(universe.excluded(), &[]);
    assert!(universe.included().contains(&srule) && universe.included().contains(&sfr2));
    assert_eq!(universe.unsorted(), &[]);
    let discovery = derive_sites_in(
        &baseline,
        &universe,
        &[
            SiteSelector::RuleLabel("SYN3-SYNTAX.sfr2".to_owned()),
            SiteSelector::Sort(Sort::new("Int")),
        ],
    )
    .expect("sites");
    assert!(discovery.exhaustive());
    assert!(!discovery.tuples().is_empty());
    let at = TermRef::new(sfr2, [0, 1]);
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).expect("5").clone(),
        at,
        replacement: Term::Token {
            token: "6".to_owned(),
            sort: Sort::new("Int"),
        },
    }])
    .expect("one edit");
    let mutant = apply(&baseline, &patch).expect("applies");
    assert_eq!(mutant.typing_diagnostics(), &[]);
    support::compile(&mutant.to_loaded(&baseline).expect("relinks")).expect("the mutant compiles");
}

/// `X` of the right-hand side `b(X)` (path `[0, 1, 0]`) replaced by the literal 0.
fn right_argument_zero(baseline: &Baseline, label: &str) -> Patch {
    let at = TermRef::new(support::rule(baseline, label), [0, 1, 0]);
    Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).expect("X").clone(),
        at,
        replacement: Term::Token {
            token: "0".to_owned(),
            sort: Sort::new("Int"),
        },
    }])
    .expect("one edit")
    .pinned(baseline)
    .expect("pins")
}

/// L2-2-fix-1 regression (review L2-2-review-1, major defect; probes lubbase and lubmain): a
/// `Sort` error in compilation's view on a rule of a baseline that compiles refuses nothing. In
/// an imported module the own module's view gives the site sorts (L2-2: excluded as Untyped);
/// in the main module neither view types it, and it is included without site sorts (L2-2 and
/// 1ee9955: excluded as Untyped). An edit of it applies with the error as a diagnostic (L2-2 and,
/// for the main module, 1ee9955: refused locally-ill-formed) and compiles.
#[test]
fn a_sort_error_compilation_accepts_refuses_nothing() {
    for (main, syntax, text, label, unsorted) in [
        ("LUBBASE", "LUBBASE-SYNTAX", LUB_IMPORTED, "LUBBB.ab", false),
        ("LUBM", "LUBM-SYNTAX", LUB_MAIN, "LUBM.ab", true),
    ] {
        let baseline = load_with_syntax(main, Some(syntax), text);
        support::compile(baseline.loaded()).expect("the baseline compiles");
        let ab = support::rule(&baseline, label);
        let error = compilation_typing(baseline.definition(), &ab).expect_err(label);
        assert!(
            matches!(error, SentenceTypingError::Sort { .. })
                && error.to_string().contains("unique least upper bound"),
            "{label}: {error}"
        );
        assert_eq!(
            own_module_typing(baseline.definition(), &ab).is_err(),
            unsorted,
            "{label}"
        );
        let universe = resolve_universe(&baseline, &Universe::v1());
        assert_eq!(universe.excluded(), &[], "{label}");
        assert!(universe.included().contains(&ab), "{label}");
        assert_eq!(universe.unsorted().contains(&ab), unsorted, "{label}");
        let discovery = derive_sites_in(
            &baseline,
            &universe,
            &[
                SiteSelector::RuleLabel(label.to_owned()),
                SiteSelector::Sort(Sort::new("Int")),
            ],
        )
        .expect("sites");
        assert_eq!(discovery.exhaustive(), !unsorted, "{label}");
        assert_eq!(discovery.tuples().is_empty(), unsorted, "{label}");

        let patch = right_argument_zero(&baseline, label);
        let mutant = apply(&baseline, &patch).expect("a typing error refuses nothing");
        let [diagnostic] = mutant.typing_diagnostics() else {
            panic!("{label}: {:?}", mutant.typing_diagnostics());
        };
        assert_eq!(diagnostic.origin, SentenceOrigin::Baseline(ab.clone()));
        assert!(
            diagnostic.message.contains("unique least upper bound"),
            "{label}: {}",
            diagnostic.message
        );
        support::compile(&mutant.to_loaded(&baseline).expect("relinks"))
            .unwrap_or_else(|error| panic!("{label}: the mutant compiles: {error}"));
    }
}

/// A structurally built candidate with an ill-sorted replacement is a candidate (L2-2 and before:
/// Rejected locally-ill-formed), with its typing error as a diagnostic, and compilation refuses
/// it: the validator rejects it, so it is an invalid mutant, never a run.
#[test]
fn an_ill_sorted_structural_candidate_is_left_to_compilation() {
    let baseline = load("MODVIEW", MODULE_VIEW);
    let twice = support::rule(&baseline, "B.twice");
    let at = TermRef::new(twice.clone(), [0, 1, 0, 0]);
    let expected = baseline.term(&at).expect("X").clone();
    let discovery = Discovery::supplied(
        &baseline,
        vec![DiscoveryTuple {
            sites: vec![Site {
                role: "site".to_owned(),
                at: at.clone(),
            }],
            bindings: kink_patch::Bindings::default(),
        }],
        false,
        false,
    )
    .expect("a baseline position");
    let generation = select(&discovery, SelectionPolicy::Each, 1)
        .expect("selection")
        .fold("bool-in-int", |_| {
            Patch::new(vec![Edit::ReplaceTerm {
                at: at.clone(),
                expected: expected.clone(),
                replacement: Term::Token {
                    token: "true".to_owned(),
                    sort: Sort::new("Bool"),
                },
            }])
            .expect("one edit")
        })
        .expect("fold");
    let [CandidateDisposition::Mutant(0)] = generation.dispositions() else {
        panic!("{:?}", generation.dispositions());
    };
    let candidate = &generation.candidates()[0];
    let [diagnostic] = candidate.typing_diagnostics.as_slice() else {
        panic!("{:?}", candidate.typing_diagnostics);
    };
    assert_eq!(diagnostic.origin, SentenceOrigin::Baseline(twice));
    let mutant = apply(&baseline, &candidate.patch).expect("applies");
    assert_eq!(mutant.typing_diagnostics(), candidate.typing_diagnostics);
    assert!(
        support::compile(&mutant.to_loaded(&baseline).expect("relinks")).is_err(),
        "compilation refuses a Bool in an Int position"
    );
}

/// Re-pin L1-3-fix-2 (review L1-3-2 D1): `apply` types an edited rule on a stack sized from the
/// rule's deepest term, so a rule 5,000 terms deep gets on a 1 MiB thread the typing it gets on
/// a 256 MiB one, error included. k-rust's typing (`SentenceTyper::typing_in`) has no stack guard
/// and takes about 2 KiB per level: before the fix this thread overflowed and the process
/// aborted, as kink-flow's 256 MiB thread did near 230,000 levels.
#[test]
fn a_deep_rule_is_typed_alike_on_a_thread_too_small_for_its_typing() {
    const DEPTH: usize = 5_000;
    let text = format!(
        "module DEEP\n  imports INT\n  syntax Peano ::= \"z\" | s(Peano)\n  syntax Exp ::= \
         go(Int) | deep(Peano)\n  rule [big]: go(I:Int) => deep({}z{}) requires I >Int 100\n\
         endmodule\n",
        "s(".repeat(DEPTH),
        ")".repeat(DEPTH)
    );
    let typings = |stack: usize| {
        let text = text.clone();
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(move || {
                let baseline = load("DEEP", &text);
                let at = rule_ref(&baseline, "DEEP.big");
                let patches = ["true", "1"].map(|token| {
                    let mut replacement = baseline.sentence(&at).unwrap().clone();
                    let Sentence::Rule { requires, .. } = &mut replacement else {
                        panic!("a rule");
                    };
                    *requires = Term::Token {
                        token: token.into(),
                        sort: Sort::new(if token == "1" { "Int" } else { "Bool" }),
                    };
                    Patch::new(vec![Edit::ReplaceSentence {
                        at: at.clone(),
                        replacement,
                    }])
                    .unwrap()
                });
                std::thread::scope(|scope| {
                    std::thread::Builder::new()
                        .stack_size(stack)
                        .spawn_scoped(scope, || {
                            patches
                                .iter()
                                .map(|patch| {
                                    let mutant = apply(&baseline, patch).unwrap();
                                    mutant
                                        .typing_diagnostics()
                                        .iter()
                                        .map(|d| d.message.clone())
                                        .collect::<Vec<_>>()
                                })
                                .collect::<Vec<_>>()
                        })
                        .unwrap()
                        .join()
                        .unwrap()
                })
            })
            .unwrap()
            .join()
            .unwrap()
    };
    let large = typings(256 << 20);
    assert!(large[0].is_empty(), "{large:?}");
    assert_eq!(
        large[1].len(),
        1,
        "an Int requires is a typing error: {large:?}"
    );
    assert_eq!(typings(1 << 20), large);
}

/// Re-pin L1-3-tail (review L1-3-fix-2-1 D2): the typing of a rule through parametric
/// productions (`#if`, the ML connectives) touches about twice the stack per level that a unary
/// symbol's does (`stack::TYPING_STACK_PER_LEVEL` records the measurement). Rules 6,000 levels
/// deep of two such shapes, `#if` nested in an `#if` condition and `#Not` nested in an `ensures`,
/// get on a 1 MiB thread the typing they get on a 256 MiB one, with a `Bool` guard (typed in full)
/// and with an `Int` one (a typing error). Typed on the calling thread, they overflow it.
#[test]
fn deep_parametric_rules_are_typed_alike_on_a_thread_too_small_for_their_typing() {
    const DEPTH: usize = 6_000;
    let text = format!(
        "module DEEP\n  imports INT\n  imports BOOL\n  imports K-EQUAL\n  syntax Exp ::= go(Int) \
         | deep(K)\n  rule [cond]: go(I:Int) => deep(#if {}true{} #then 0 #else 1 #fi) requires \
         I >Int 100\n  rule [ml]: go(I:Int) => deep(0) requires I <Int 100 ensures {}#Top{}\n\
         endmodule\n",
        "#if ".repeat(DEPTH),
        " #then true #else false #fi".repeat(DEPTH),
        "#Not(".repeat(DEPTH),
        ")".repeat(DEPTH),
    );
    let typings = |stack: usize| {
        let text = text.clone();
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(move || {
                let baseline = load("DEEP", &text);
                let patches = [
                    ("DEEP.cond", "true"),
                    ("DEEP.cond", "1"),
                    ("DEEP.ml", "true"),
                    ("DEEP.ml", "1"),
                ]
                .map(|(label, token)| {
                    let at = rule_ref(&baseline, label);
                    let mut replacement = baseline.sentence(&at).unwrap().clone();
                    let Sentence::Rule { requires, .. } = &mut replacement else {
                        panic!("a rule");
                    };
                    *requires = Term::Token {
                        token: token.into(),
                        sort: Sort::new(if token == "1" { "Int" } else { "Bool" }),
                    };
                    Patch::new(vec![Edit::ReplaceSentence { at, replacement }]).unwrap()
                });
                std::thread::scope(|scope| {
                    std::thread::Builder::new()
                        .stack_size(stack)
                        .spawn_scoped(scope, || {
                            patches
                                .iter()
                                .map(|patch| {
                                    let mutant = apply(&baseline, patch).unwrap();
                                    mutant
                                        .typing_diagnostics()
                                        .iter()
                                        .map(|d| d.message.clone())
                                        .collect::<Vec<_>>()
                                })
                                .collect::<Vec<_>>()
                        })
                        .unwrap()
                        .join()
                        .unwrap()
                })
            })
            .unwrap()
            .join()
            .unwrap()
    };
    let large = typings(256 << 20);
    for (index, diagnostics) in large.iter().enumerate() {
        if index % 2 == 0 {
            assert!(diagnostics.is_empty(), "a Bool requires types: {large:?}");
        } else {
            assert_eq!(
                diagnostics.len(),
                1,
                "an Int requires is a typing error: {large:?}"
            );
            assert!(!diagnostics[0].starts_with("not typed"), "{large:?}");
        }
    }
    assert_eq!(typings(1 << 20), large);
}

/// The one authored sentence labelled `label`.
fn rule_ref(baseline: &Baseline, label: &str) -> kink_patch::SentenceRef {
    support::rule(baseline, label)
}
