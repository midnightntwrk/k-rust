//! Grammar sentences as mutation sites (PJ-34) over `testdata/k/grammar.k`: what `apply`
//! admits, the program-parser gate, the generated forms, and the claims a grammar edit leaves.

#[path = "../../../testdata/k/support.rs"]
mod support;

#[path = "../../../testdata/k/passage.rs"]
mod passage;

use k_rust::definition::{AttributeKey, ProductionItem, Sentence};
use k_rust::kast::Sort;
use kink_patch::{
    Baseline, CandidateDisposition, ClaimSupport, Edit, GrammarEffect, GrammarForm,
    GrammarSelector, Patch, PatchFailureKind, SentenceRef, apply, generate_default_grammar,
    generate_grammar, grammar_variants,
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

/// The k-rust passages a grammar kill's reparse rests on (kink/trust.md, "What a grammar kill
/// trusts", "Both parsers are k-rust's" and "An ambiguity is a rejection"; U34e Q1): the two
/// constructors kink builds each side's program parser with (`ProgramGrammar::new` of a
/// definition, `ProgramParser::from_resolved` at a module: kink-patch `Mutant::program_parser`,
/// kink-corpus `InputGrammar::prepare` and `with_program_grammar_of`); that a parse refuses a
/// text with several readings (`ParseError::Ambiguous`, and `CyclicDerivation` for infinitely
/// many) and every parse failure is a `ProgramParseError`; and that assembly wraps the program
/// text's failure as `ConfigurationError::Program` and a variable's as `ConfigurationError::Parse`,
/// the two kink-corpus `input_error` reads as `InputError::Parse`, a rejection. That last mapping
/// is kink's own code, held by kink-flow's drop-left test (`tests/check.rs`), not pinned here.
/// Last, that a disagreement of the checked inference's two engines
/// (`ParseError::InferenceEngineDisagreement`) is kept apart from a rejection, which kink-corpus
/// reads as `InputError::InferenceDisagreement`, never `InputError::Parse` (FX2).
const PARSER_PASSAGES: [passage::Passage; 12] = [
    passage::Passage {
        file: "crates/k-rust/src/inner/parser.rs",
        anchor: "pub enum ParseError {",
        opening: "/// The input has several readings, the distinct terms its parses lower to.",
        lines: 2,
        digest: "eba2e592d77a706b56ac51fb2912e671247be7d621a4e4931f75c3fa98d3e9be",
    },
    passage::Passage {
        file: "crates/k-rust/src/inner/parser.rs",
        anchor: "pub enum ParseError {",
        opening: "/// A sort derives itself over a text without consuming input.",
        lines: 2,
        digest: "7530c4b891056d27249fc8b5b99c5ecac88c487d74e36d5d559aaccc8cdc56e5",
    },
    passage::Passage {
        file: "crates/k-rust/src/inner/programs.rs",
        anchor: "impl ProgramParser {",
        opening: "pub fn from_resolved(",
        lines: 4,
        digest: "68048023432933521841d468d01a976451fb8f96ab9235a44c5298d124e059fa",
    },
    passage::Passage {
        file: "crates/k-rust/src/inner/programs.rs",
        anchor: "impl ProgramParser {",
        opening: "/// text was printed from asks with it whether that term is among the readings; a program,",
        lines: 2,
        digest: "55de89671891dbf39cf61011ad5f6a2343962c6ad2923fbf2cfe1609ee4bae4f",
    },
    passage::Passage {
        file: "crates/k-rust/src/inner/programs.rs",
        anchor: "fn parse_within(",
        opening: ".map_err(|error| self.parse_error(start_sort, source, error))",
        lines: 1,
        digest: "c56ba703fc28aab34ba247d590b3f1548f56885bc473bde01afa18e11826c383",
    },
    passage::Passage {
        file: "crates/k-rust/src/kompile/initial_configuration.rs",
        anchor: "impl ProgramGrammar {",
        opening: "pub fn new(frontend: &Definition) -> Result<Self, ConfigurationError> {",
        lines: 4,
        digest: "211e599669f3e16529e832e418ece19949759cca2add51b9984bacc500407ae0",
    },
    passage::Passage {
        file: "crates/k-rust/src/kompile/initial_configuration.rs",
        anchor: "pub enum ConfigurationError {",
        opening: "/// The program text does not parse at the requested start sort.",
        lines: 2,
        digest: "74d8766de1db67a0291b2135377f3741b8bff5cab23f4e685ac06f1d47609867",
    },
    passage::Passage {
        file: "crates/k-rust/src/kompile/initial_configuration.rs",
        anchor: "pub enum ConfigurationError {",
        opening: "/// A configuration value that does not parse at its declared sort.",
        lines: 10,
        digest: "b2a1849461890b480cc436344270fdf5843e3a70a7089abe67206c800d8a6aa6",
    },
    passage::Passage {
        file: "crates/k-rust/src/kompile/initial_configuration.rs",
        anchor: "pub fn program_file(",
        opening: "ProgramParser::from_resolved(self.grammar.resolved(), &self.syntax_module)?,",
        lines: 1,
        digest: "0f0ff160a5133d94aed1c2c37be63ecbbcea60a9a27c4d1c3ec28ff3c8899f46",
    },
    passage::Passage {
        file: "crates/k-rust/src/kompile/initial_configuration.rs",
        anchor: "pub fn program_file(",
        opening: ".parse_file(start_sort, text, file)",
        lines: 2,
        digest: "ebeffcedf31258b2edce0352fbad497a0253bfc40f63fc15de800b5190e6136b",
    },
    passage::Passage {
        file: "crates/k-rust/src/kompile/initial_configuration.rs",
        anchor: "pub fn bind(",
        opening: "let parsed = parsed.map_err(|error| ConfigurationError::Parse {",
        lines: 1,
        digest: "d5159eafe18605c283209d3e026143eb656d7c8c7b402b3f6b654fca4a8272a8",
    },
    passage::Passage {
        file: "crates/k-rust/src/inner/parser.rs",
        anchor: "pub enum ParseError {",
        opening: "/// Checked inference only (`KRUST_TYPE_INFERENCE_MODE=checked`): the portable and Z3",
        lines: 9,
        digest: "ffa3fb55801bdfbb4480a28cc45e8b4223b9eb92df865dc86cda9e3f08c5739f",
    },
];

/// An ambiguity is a rejection, and both sides' parsers are built by the same two k-rust
/// constructors: the passages that reading rests on are pinned ([`PARSER_PASSAGES`]), so a
/// change of any of them fails here and the reading is checked again.
#[test]
fn the_ambiguity_reading_and_the_parser_constructors_are_pinned() {
    passage::assert_pinned(&k_rust_tree(), &PARSER_PASSAGES);
}

/// The default set (PJ-34) is the forms whose effect at their site is a widening or a token-level
/// narrowing; every other form is off and generated by name. The off forms are listed, so that a
/// change of the set is a change of this test.
#[test]
fn the_default_set_is_the_widening_forms_and_token_level_narrowing() {
    let default = GrammarForm::ALL
        .into_iter()
        .filter(|form| {
            matches!(
                form.effect(),
                GrammarEffect::Widening | GrammarEffect::TokenNarrowing
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(default, GrammarForm::DEFAULT);
    let names = |forms: &[GrammarForm]| forms.iter().map(|f| f.name()).collect::<Vec<_>>();
    assert_eq!(
        names(&GrammarForm::DEFAULT),
        [
            "alternative-without-terminal",
            "merge-alternative",
            "loosen-regex",
            "narrow-regex",
            "drop-anchor"
        ]
    );
    let off = GrammarForm::ALL
        .into_iter()
        .filter(|form| !GrammarForm::DEFAULT.contains(form))
        .map(|form| (form.name(), form.effect()))
        .collect::<Vec<_>>();
    assert_eq!(
        off,
        [
            ("drop-terminal", GrammarEffect::LiteralMove),
            ("change-terminal", GrammarEffect::LiteralMove),
            ("delete-production", GrammarEffect::ProductionNarrowing),
            ("merge-priority-groups", GrammarEffect::Disambiguation),
            ("swap-priority-groups", GrammarEffect::Disambiguation),
            ("change-associativity", GrammarEffect::Disambiguation),
            ("delete-relation", GrammarEffect::Disambiguation),
        ]
    );

    // The generated default set is `generate_grammar` of each default form, in order, and over
    // grammar.k each gives at least one mutant with a program parser.
    let baseline = baseline();
    let generations =
        generate_default_grammar(&baseline, &[], SYNTAX, usize::MAX).expect("generations");
    assert_eq!(
        generations
            .iter()
            .map(|(form, _)| *form)
            .collect::<Vec<_>>(),
        GrammarForm::DEFAULT
    );
    for (form, generation) in &generations {
        let alone = generate_grammar(&baseline, *form, &[], SYNTAX, usize::MAX).expect("alone");
        assert_eq!(
            generation.dispositions(),
            alone.dispositions(),
            "{}",
            form.name()
        );
        assert!(generation.scored(), "{} is complete", form.name());
        assert!(
            generation
                .dispositions()
                .iter()
                .any(|disposition| matches!(disposition, CandidateDisposition::Mutant(_))),
            "{} gives a mutant over grammar.k",
            form.name()
        );
    }
}

/// Every candidate of the default set, supplied again as one patch (as kink-flow judges a
/// generated grammar row, U34h), is one admitted mutant with that patch: an insertion anchored
/// after its production (`alternative-without-terminal`, `merge-alternative`) is authorized by
/// its anchor, which `supplied_grammar` makes a site.
#[test]
fn each_default_candidate_is_admitted_again_as_a_supplied_patch() {
    let baseline = baseline();
    let generations =
        generate_default_grammar(&baseline, &[], SYNTAX, usize::MAX).expect("generations");
    let mut inserted = 0;
    for (form, generation) in &generations {
        for candidate in generation.candidates() {
            inserted += usize::from(
                candidate
                    .patch
                    .edits()
                    .iter()
                    .any(|edit| matches!(edit, Edit::InsertSentence { .. })),
            );
            let supplied =
                kink_patch::supplied_grammar(&baseline, "supplied", &candidate.patch, SYNTAX)
                    .expect("supplied");
            assert_eq!(
                supplied.dispositions(),
                [CandidateDisposition::Mutant(0)],
                "{}: {:?}",
                form.name(),
                candidate.patch
            );
            assert_eq!(supplied.candidates()[0].patch, candidate.patch);
        }
    }
    assert!(inserted > 0, "the default set inserts alternatives");
}

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
/// refused. An inserted one adds values to its sort and to the sorts that hold them, which only
/// the symbols taking a value of one see (U34f): grammar.k has no claim of its own, and the
/// prelude's rest on the parametric premise (kink `trust.md`), so the two insertion forms are
/// trusted and withdraw nothing.
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
        let variants = grammar_variants(&baseline, form, &[]);
        assert!(!variants.is_empty(), "{}", form.name());
        for (at, patch) in variants {
            let withdrawal = support.withdraw(&baseline, &patch).expect("applies");
            assert!(
                withdrawal.trusted() && withdrawal.withdrawn.is_empty(),
                "{} {at:?}: {withdrawal:?}",
                form.name()
            );
        }
    }
}

/// Every production identity a term of `definition` carries in its metadata.
fn named_productions(term: &k_rust::kast::Term, named: &mut Vec<k_rust::kast::ProductionIdentity>) {
    use k_rust::kast::Term;
    if let Some(identity) = term.metadata().and_then(|metadata| metadata.production) {
        named.push(identity);
    }
    match term.unannotated() {
        Term::Rewrite { left, right } => {
            named_productions(left, named);
            named_productions(right, named);
        }
        Term::As { pattern, alias } => {
            named_productions(pattern, named);
            named_productions(alias, named);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                named_productions(item, named);
            }
        }
        _ => {}
    }
}

/// A production a rule applies is not deleted by `delete-production` (FX2): its mutant would keep
/// an application of a production it does not declare, which compilation refuses. `print` is
/// applied by `run`'s left-hand side: no variant deletes it, every variant that is generated
/// leaves no dangling application, and a deletion of `print` written by hand is named as one
/// (`Mutant::dangling_applications`, which kink-flow's grammar search refuses before anything
/// compiles the mutant).
#[test]
fn a_production_a_rule_applies_is_not_deleted() {
    let baseline = baseline();
    let (at, _) = production(&baseline, "print");
    let variants = grammar_variants(&baseline, GrammarForm::DeleteProduction, &[]);
    assert!(!variants.is_empty());
    for (site, patch) in &variants {
        assert_ne!(site.sentence, at, "{site:?}");
        let mutant = apply(&baseline, patch).expect("applies");
        assert_eq!(
            mutant.dangling_applications(),
            Vec::<String>::new(),
            "{site:?}"
        );
    }
    let mutant = apply(&baseline, &one(Edit::DeleteSentence { at })).expect("applies");
    assert_eq!(
        mutant.dangling_applications(),
        ["print in GRAMMAR".to_owned()]
    );
}

/// The source reading of an inserted alternative over grammar.k (FX2, U34h Q1): the affected
/// labels include `initStdinCell` and `initStdoutCell`, whose equations reach the redefined
/// `#unboxKConfigValue`, and which only the prelude's `STDIN-STREAM` and `STDOUT-STREAM` declare;
/// GRAMMAR does not import them, so they are `unimported` (kink-native leaves such a label out of
/// the checked heads where the compiled definition has no symbol for it). The withdrawal is not
/// read from it and is unchanged: nothing is withdrawn.
#[test]
fn an_inserted_alternatives_affected_labels_outside_the_main_module_are_unimported() {
    let baseline = baseline();
    let support = ClaimSupport::new(&baseline);
    let (_, patch) = grammar_variants(&baseline, GrammarForm::AlternativeWithoutTerminal, &[])
        .into_iter()
        .next()
        .expect("an alternative");
    let effect = support.effect(&baseline, &patch).expect("applies");
    let affected = effect.affected.expect("known symbol by symbol");
    let unimported = ["initStdinCell", "initStdoutCell"].map(str::to_owned);
    assert!(
        unimported.iter().all(|label| affected.contains(label)),
        "{affected:?}"
    );
    assert!(affected.contains("#unboxKConfigValue"), "{affected:?}");
    assert_eq!(effect.unimported, unimported.into_iter().collect());
    let withdrawal = support.withdraw(&baseline, &patch).expect("applies");
    assert!(
        withdrawal.trusted() && withdrawal.withdrawn.is_empty(),
        "{withdrawal:?}"
    );
}

/// A grammar edit keeps the rules' terms (PJ-34): a rule's application of a production whose
/// literal an edit changes or drops is an application of the same constructor, so its metadata
/// names the production the mutant declares in its place, never the replaced one (compilation
/// finds no production for a dangling identity). `print _E ;` is the rule `run`'s left-hand side.
#[test]
fn a_rule_built_with_a_replaced_production_names_its_replacement() {
    let baseline = baseline();
    let (at, before) = production(&baseline, "print");
    let old = k_rust::definition::production_identity(&before).expect("a production");
    let named_in_baseline = |definition: &k_rust::definition::Definition| {
        let mut named = Vec::new();
        for module in &definition.modules {
            for sentence in &module.local_sentences {
                for (_, term) in sentence.terms() {
                    named_productions(term, &mut named);
                }
            }
        }
        named
    };
    assert!(named_in_baseline(baseline.definition()).contains(&old));
    let mut edited = 0;
    for form in [GrammarForm::ChangeTerminal, GrammarForm::DropTerminal] {
        for (site, patch) in grammar_variants(&baseline, form, &[]) {
            if site.sentence != at {
                continue;
            }
            let mutant = apply(&baseline, &patch).expect("applies");
            let declared = mutant
                .definition()
                .modules
                .iter()
                .flat_map(|module| &module.local_sentences)
                .filter_map(|sentence| k_rust::definition::production_identity(sentence))
                .collect::<std::collections::BTreeSet<_>>();
            let named = named_in_baseline(mutant.definition());
            assert!(!named.contains(&old), "{} {site:?}", form.name());
            assert!(
                named.iter().all(|identity| declared.contains(identity)),
                "{} {site:?}: a term names a production the mutant does not declare",
                form.name()
            );
            edited += 1;
        }
    }
    assert!(edited > 1, "the forms edit `print`'s literals");
}
