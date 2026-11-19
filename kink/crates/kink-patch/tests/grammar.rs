//! Grammar sentences as mutation sites (PJ-34) over `testdata/k/grammar.k`: what `apply`
//! admits, the program-parser gate, the generated forms, and the claims a grammar edit leaves.

#[path = "../../../testdata/k/support.rs"]
mod support;

#[path = "../../../testdata/k/passage.rs"]
mod passage;

use k_rust::definition::{AttributeKey, ProductionItem, Sentence};
use k_rust::kast::Sort;
use kink_patch::{
    Baseline, CandidateDisposition, ClaimSupport, Edit, GrammarForm, GrammarSelector, Patch,
    PatchFailureKind, SentenceRef, apply, generate_grammar, grammar_variants,
};
use serde_json::Value;

const SYNTAX: &str = "GRAMMAR-SYNTAX";

fn baseline() -> Baseline {
    support::load("grammar.k")
}

/// The one authored sentence `matches` picks, with its address.
fn find(baseline: &Baseline, matches: impl Fn(&Sentence) -> bool) -> (SentenceRef, Sentence) {
    let mut found = baseline
        .authored_sentences()
        .filter(|(_, sentence)| matches(sentence));
    let (at, sentence) = found.next().expect("a matching sentence");
    assert!(found.next().is_none(), "one matching sentence");
    (at, sentence.clone())
}

fn production(baseline: &Baseline, label: &str) -> (SentenceRef, Sentence) {
    find(
        baseline,
        |sentence| matches!(sentence, Sentence::Production { label: Some(l), .. } if l.name == label),
    )
}

fn token(baseline: &Baseline, sort: &str) -> (SentenceRef, Sentence) {
    find(baseline, |sentence| {
        matches!(sentence, Sentence::Production { sort: s, attributes, .. }
            if s.name == sort && attributes.has(AttributeKey::Token))
    })
}

fn with_regex(sentence: &Sentence, regex: &str) -> Sentence {
    let mut sentence = sentence.clone();
    let Sentence::Production { items, .. } = &mut sentence else {
        panic!("a token production");
    };
    items[0] = ProductionItem::RegexTerminal {
        regex: regex.to_owned(),
    };
    sentence
}

fn one(edit: Edit) -> Patch {
    Patch::new(vec![edit]).expect("patch")
}

/// k-rust's definitions hold no follow (or precede) restriction, so no grammar form edits one
/// (PJ-34 `resolved`, U34a Q1): a regex terminal holds its regex only, and the KAST JSON reader
/// refuses a document that states one. This pins both, so that the day k-rust gains a follow
/// restriction this fails and the kind is added as a mutation site. The pattern below names
/// `RegexTerminal`'s fields without `..`: a new field fails to compile here.
#[test]
fn a_follow_restriction_has_no_place_in_k_rust_definitions() {
    let item = ProductionItem::RegexTerminal {
        regex: "a".to_owned(),
    };
    let ProductionItem::RegexTerminal { regex } = &item else {
        panic!("a regex terminal");
    };
    assert_eq!(regex, "a");
    passage::assert_pinned(&k_rust_tree(), &GRAMMAR_PASSAGES);
}

/// The k-rust passages the grammar layer rests on: the absence of follow restrictions (above),
/// and what `ClaimSupport`'s parse-only rule reads (kink-patch `claims.rs` `parse_only`): a
/// production's text and its priority and associativity relations reach KORE only as
/// unparsing attributes of its symbol (the `priorities`, `left` and `right` of the declaration
/// made under its label), and a token's value is read from its sort and hook, not from its regex.
const GRAMMAR_PASSAGES: [passage::Passage; 4] = [
    passage::Passage {
        file: "docs/compatibility.md",
        anchor: "## Token precede and follow restrictions",
        opening: "No K source syntax writes such a restriction",
        lines: 1,
        digest: "56013aa737f7544f75c163a96960d8d5c762378f2c80514e6b2f169dbe9fca95",
    },
    passage::Passage {
        file: "crates/k-rust/src/definition/ast.rs",
        anchor: "pub enum ProductionItem {",
        opening: "/// A token regex. Its tokens are the matches of `regex`",
        lines: 4,
        digest: "476aec485a0e2530b7cfce935ba13e6ed9d9a86c9ed593fb487eb54f6df29646",
    },
    passage::Passage {
        file: "crates/k-rust/src/kompile/module_to_kore.rs",
        anchor: "enum SyntaxDeclaration<'a> {",
        opening: "/// Under the production's own label: priority and associativity groups",
        lines: 1,
        digest: "3530474963472a1bd5b0f1049bc3a0b0f7647178b705a1bebf15bff72834d8d5",
    },
    passage::Passage {
        file: "crates/k-rust/src/kompile/token_value.rs",
        anchor: "pub fn token_value(",
        opening: "/// The value the token `text` of `sort` denotes",
        lines: 4,
        digest: "fec9e93782ddebea5f42de20dca19530b08e501caabbb9e204625d62fc693453",
    },
];

fn k_rust_tree() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..")
}

/// A production, a token, a lexical, a priority and an associativity declaration are replaced
/// and inserted; each patch is encoded and decoded to itself. A sort declaration is still not.
#[test]
fn grammar_sentences_are_replaced_inserted_and_encoded() {
    let baseline = baseline();
    for form in GrammarForm::ALL {
        let variants = grammar_variants(&baseline, form, &[]);
        assert!(!variants.is_empty(), "{} has no variant", form.name());
        for (at, patch) in variants {
            apply(&baseline, &patch).unwrap_or_else(|e| panic!("{} {at:?}: {e}", form.name()));
            let pinned = patch.pinned(&baseline).expect("pinned");
            let text = pinned.canonical_json().expect("encoded");
            assert_eq!(
                Patch::from_canonical_json(&text).expect("decoded"),
                pinned,
                "{} {at:?}",
                form.name()
            );
        }
    }
    let (at, sort) = find(
        &baseline,
        |sentence| matches!(sentence, Sentence::SyntaxSort { sort, .. } if sort.name == "Note"),
    );
    let mut replacement = sort;
    replacement
        .attributes_mut()
        .set(AttributeKey::Prefer, Value::String(String::new()));
    let failure = apply(&baseline, &one(Edit::ReplaceSentence { at, replacement }))
        .expect_err("a sort declaration is not editable");
    assert_eq!(failure.kind(), PatchFailureKind::LocallyIllFormed);
}

/// What each form generates at the fixture, by name and variant path: the literals of
/// `print Exp ;`, a float's regex loosened and narrowed, the `$` of `Tag`, the priority block.
#[test]
fn the_forms_edit_literals_tokens_and_relations() {
    let baseline = baseline();
    let at = |form, selector: &[GrammarSelector]| {
        grammar_variants(&baseline, form, selector)
            .into_iter()
            .map(|(at, _)| at.path.0)
            .collect::<Vec<_>>()
    };
    let print = [GrammarSelector::Label("print".to_owned())];
    // `print` Exp `;`: either literal is dropped, each with an alternative that lacks it.
    assert_eq!(at(GrammarForm::DropTerminal, &print), [vec![0], vec![2]]);
    assert_eq!(
        at(GrammarForm::AlternativeWithoutTerminal, &print),
        [vec![0], vec![2]]
    );
    // Stmt's other literal is `tag`: each of print's literals may become it.
    assert_eq!(
        at(GrammarForm::ChangeTerminal, &print),
        [vec![0, 0], vec![2, 0]]
    );
    let (_, patch) = grammar_variants(&baseline, GrammarForm::ChangeTerminal, &print)
        .into_iter()
        .next()
        .expect("a change");
    let [Edit::ReplaceSentence { replacement, .. }] = patch.edits() else {
        panic!("one replacement");
    };
    let Sentence::Production { items, label, .. } = replacement else {
        panic!("a production");
    };
    assert_eq!(label.as_ref().map(|l| l.name.as_str()), Some("print"));
    assert_eq!(items[0], ProductionItem::Terminal("tag".to_owned()));

    // The float token `{Digit}+([.]{Digit}*)?` and the lexical `[0-9]`.
    let num = [GrammarSelector::Sort(Sort::new("Num"))];
    let regexes = |form| {
        grammar_variants(&baseline, form, &num)
            .into_iter()
            .map(|(_, patch)| match patch.edits() {
                [
                    Edit::ReplaceSentence {
                        replacement: Sentence::Production { items, .. },
                        ..
                    },
                ] => match items.as_slice() {
                    [ProductionItem::RegexTerminal { regex }] => regex.clone(),
                    other => panic!("{other:?}"),
                },
                other => panic!("{other:?}"),
            })
            .collect::<Vec<_>>()
    };
    let loosened = regexes(GrammarForm::LoosenRegex);
    let narrowed = regexes(GrammarForm::NarrowRegex);
    eprintln!("loosened {loosened:?}\nnarrowed {narrowed:?}");
    // The fraction's dot becomes any character; its digits become optional.
    assert!(
        loosened
            .iter()
            .any(|regex| !regex.contains("[.]") && regex.contains('.'))
    );
    // The fraction becomes required.
    assert!(narrowed.iter().any(|regex| !regex.ends_with('?')));
    // No loosening makes the token match the empty text.
    assert!(!loosened.contains(&"{Digit}*([.]{Digit}*)?".to_owned()));
    assert!(!grammar_variants(&baseline, GrammarForm::LoosenRegex, &[]).is_empty());

    // `#[a-z]+$` loses its `$`, its one anchor.
    let tag = [GrammarSelector::Sort(Sort::new("Tag"))];
    assert_eq!(at(GrammarForm::DropAnchor, &tag), [vec![1]]);
    assert!(at(GrammarForm::DropAnchor, &num).is_empty());

    // The block's three groups give two boundaries; `syntax priority mul > neg` one.
    let mul = [GrammarSelector::Label("mul".to_owned())];
    assert_eq!(
        at(GrammarForm::MergePriorityGroups, &mul).len(),
        3,
        "two in the block, one in `syntax priority`"
    );
    // `[left]` on mul and on add give one declaration each; each takes two others.
    assert_eq!(
        at(GrammarForm::ChangeAssociativity, &mul),
        [vec![1], vec![2]]
    );
}

/// A generated grammar mutant gives a program parser, or its origin is refused with k-rust's
/// reason: swapping the block's groups to `add neg > mul` contradicts `syntax priority mul >
/// neg`, a priority cycle no parser is built for.
#[test]
fn generated_grammar_mutants_give_a_program_parser() {
    let baseline = baseline();
    for form in GrammarForm::ALL {
        let generation =
            generate_grammar(&baseline, form, &[], SYNTAX, usize::MAX).expect("generation");
        let refused = generation
            .dispositions()
            .iter()
            .filter_map(|disposition| match disposition {
                CandidateDisposition::Rejected(failure) => Some(failure),
                CandidateDisposition::Mutant(_) => None,
            })
            .collect::<Vec<_>>();
        eprintln!(
            "{}: {} candidates, refused {refused:?}",
            form.name(),
            generation.candidates().len()
        );
        assert!(
            generation.scored(),
            "{} is complete and scored",
            form.name()
        );
        assert!(!generation.candidates().is_empty(), "{}", form.name());
        if form == GrammarForm::SwapPriorityGroups {
            assert!(
                refused
                    .iter()
                    .any(|failure| failure.kind() == PatchFailureKind::NoProgramParser),
                "the cycle is refused"
            );
        }
    }
    let generation =
        generate_grammar(&baseline, GrammarForm::DropTerminal, &[], SYNTAX, 1).expect("capped");
    assert!(!generation.scored(), "a cut generation is incomplete");
}

/// The gate is k-rust's: a regex k-rust's scanner refuses, a token two productions rank
/// differently, and a syntax module the definition does not have give no program parser.
#[test]
fn the_program_parser_gate_refuses_what_k_rust_builds_no_parser_for() {
    let baseline = baseline();
    let (num, num_sentence) = token(&baseline, "Num");
    let identity = apply(
        &baseline,
        &one(Edit::ReplaceSentence {
            at: num.clone(),
            replacement: with_regex(&num_sentence, "[0-9]+"),
        }),
    )
    .expect("applies");
    identity.program_parser(SYNTAX).expect("a parser");
    let refused = identity
        .program_parser("NO-SUCH-MODULE")
        .expect_err("no module");
    assert_eq!(refused.kind(), PatchFailureKind::NoProgramParser);

    let invalid = apply(
        &baseline,
        &one(Edit::ReplaceSentence {
            at: num.clone(),
            replacement: with_regex(&num_sentence, "[0-9"),
        }),
    )
    .expect("applies: a regex is checked by the parser it builds");
    let refused = invalid
        .program_parser(SYNTAX)
        .expect_err("an invalid regex");
    assert_eq!(refused.kind(), PatchFailureKind::NoProgramParser);
    eprintln!("invalid regex: {refused}");

    // Tag's regex becomes Num's, at another precedence: one lexeme, two ranks.
    let (tag, tag_sentence) = token(&baseline, "Tag");
    let Sentence::Production { items, .. } = &num_sentence else {
        panic!("a production");
    };
    let [ProductionItem::RegexTerminal { regex }] = items.as_slice() else {
        panic!("a regex token");
    };
    let mut ranked = with_regex(&tag_sentence, regex);
    ranked
        .attributes_mut()
        .set(AttributeKey::Prec, Value::String("3".to_owned()));
    let conflict = apply(
        &baseline,
        &one(Edit::ReplaceSentence {
            at: tag,
            replacement: ranked,
        }),
    )
    .expect("applies");
    let refused = conflict
        .program_parser(SYNTAX)
        .expect_err("a precedence conflict");
    assert_eq!(refused.kind(), PatchFailureKind::NoProgramParser);
    eprintln!("precedence conflict: {refused}");
}

/// An edit that changes only which text parses to which term redefines no symbol (kink-patch
/// `claims.rs` `parse_only`), so it withdraws no claim and is trusted, though the main module
/// imports INT (whose hooked and `concrete` equations make an edit of unknown effect
/// unsupported): every generated priority, associativity, lexical, regex and literal edit. A
/// deleted production, which changes its sort's values, still withdraws every claim and is
/// refused, and so is an inserted one, which adds values to its sort (a constructor no equation
/// of a function over it covers): the two insertion forms are refused over this definition.
#[test]
fn a_parse_only_edit_leaves_every_claim() {
    let baseline = baseline();
    let support = ClaimSupport::new(&baseline);
    for form in [
        GrammarForm::DropTerminal,
        GrammarForm::ChangeTerminal,
        GrammarForm::LoosenRegex,
        GrammarForm::NarrowRegex,
        GrammarForm::DropAnchor,
        GrammarForm::MergePriorityGroups,
        GrammarForm::SwapPriorityGroups,
        GrammarForm::ChangeAssociativity,
        GrammarForm::DeleteRelation,
    ] {
        for (at, patch) in grammar_variants(&baseline, form, &[]) {
            let withdrawal = support.withdraw(&baseline, &patch).expect("applies");
            assert!(
                withdrawal.trusted() && withdrawal.withdrawn.is_empty(),
                "{} {at:?}: {withdrawal:?}",
                form.name()
            );
        }
    }
    let (at, _) = production(&baseline, "neg");
    let withdrawal = support
        .withdraw(&baseline, &one(Edit::DeleteSentence { at }))
        .expect("applies");
    assert!(!withdrawal.trusted());
    for form in [
        GrammarForm::AlternativeWithoutTerminal,
        GrammarForm::MergeAlternative,
    ] {
        for (at, patch) in grammar_variants(&baseline, form, &[]) {
            let withdrawal = support.withdraw(&baseline, &patch).expect("applies");
            assert!(!withdrawal.trusted(), "{} {at:?}", form.name());
        }
    }
}
