//! The typing gate per compilation's contract (decision 4; findings C-02, C-03; packet L2-2).
//!
//! kink-patch types sentences in compilation's view only: one `SentenceTyper::for_compilation` per
//! resolved definition, with `typing_in` the declaring module (k-rust docs/compatibility.md, the
//! `SentenceTyper` paragraphs). `apply` refuses an edited rule only on a sort or semantic-cast
//! error, at which compilation stops too; every other answer is compilation's to decide.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::builtin;
use k_rust::definition::{ResolvedDefinition, Sentence};
use k_rust::kast::{Sort, Term};
use k_rust::kompile::{SentenceTyper, SentenceTypingError};
use k_rust::outer::ResolvedSource;
use kink_patch::{
    Baseline, CandidateDisposition, Discovery, DiscoveryTuple, Edit, ExclusionReason, Patch,
    PatchFailureKind, SelectionPolicy, Site, SiteSelector, TermRef, Universe, apply,
    derive_sites_in, resolve_universe, select,
};

fn load(module: &str, text: &str) -> Baseline {
    let mut resolver = |_: &str, name: &str| {
        builtin::embedded(name).ok_or_else(|| format!("{name} is not embedded"))
    };
    Baseline::load(
        ResolvedSource::new("typing.k", text),
        module,
        None,
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
    support::compile(&mutant.to_loaded(&baseline).expect("relinks")).expect("the mutant compiles");
}

#[test]
fn a_cell_completion_shape_is_left_to_compilation() {
    let baseline = load("UNTYPEDCELL", CELL_COMPLETION);
    let completed = support::rule(&baseline, "UNTYPEDCELL.completed");
    // The universe still excludes it: it has no typing, so no site sort.
    assert_eq!(
        resolve_universe(&baseline, &Universe::v1()).excluded(),
        &[(completed.clone(), ExclusionReason::Untyped)]
    );
    // An edit of it applies (before L2-2: refused with the CellCompletion error) and compiles.
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
    support::compile(&mutant.to_loaded(&baseline).expect("relinks")).expect("the mutant compiles");
}

/// A loaded baseline holds only the modules its main module reaches, so every authored rule is in
/// the main closure and has compilation's typing; kink-patch's closure check (a rule outside it is
/// `Untyped`, and its edit is left to compilation, which never emits it) is defensive.
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

#[test]
fn an_ill_sorted_structural_candidate_is_still_rejected() {
    let baseline = load("MODVIEW", MODULE_VIEW);
    let twice = support::rule(&baseline, "B.twice");
    let at = TermRef::new(twice, [0, 1, 0, 0]);
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
    let [CandidateDisposition::Rejected(failure)] = generation.dispositions() else {
        panic!("{:?}", generation.dispositions());
    };
    assert_eq!(
        failure.kind(),
        PatchFailureKind::LocallyIllFormed,
        "{failure}"
    );
}
