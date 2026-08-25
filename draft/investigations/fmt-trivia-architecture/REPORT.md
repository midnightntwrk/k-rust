# Investigation: trivia architecture for `krs fmt` (decision F7 evidence)

**Date**: 2026-08-23. **Question**: how should `krs-syntax` represent
comments/whitespace (trivia) for the formatter — the proposed "lossless
source/trivia facade over the existing semantic parsers" vs a
rowan-style lossless-CST rewrite — and does the facade have real-world
precedent, or does it become two drifting parsers?

**Method**: two independent deep-dives over real formatter codebases
(cloned and read, not recalled): (1) verusfmt + cedar-policy-formatter
comment mechanics and documented failures; (2) precedent survey for
"one grammar, two views" — rust-analyzer, Slint, Roslyn/Biome,
Go/gofmt, Zig, ruff/black/parso/LibCST, rustfmt, ocamlformat, Prettier,
swc, Topiary. Extends doc 16's survey with source-level and
issue-tracker evidence.

## Verdict

**The facade is the right call, in one narrow form**: keep `syn` and
every grammar production bit-for-bit unchanged; replace the anonymous
`str -> TokenStream` step in the existing `parse_*_source` entry points
with `str -> (TokenStream, TriviaTable)`, where trivia is recovered by
classifying the byte **gaps** between proc-macro2's tokens. This adds
**zero grammar productions** — and duplicated productions, not
duplicated entry points, are what caused drift in every precedent that
drifted (black's blib2to3, verusfmt's 44 KB pest grammar, LibCST's
3,690-line grammar transliteration, parso's nine grammar files).
Projects with one rule set and multiple token sources (rust-analyzer
internally, Slint, Zig, Go, rustfmt, ruff, ocamlformat) have no
grammar-drift problem. A rowan rewrite stays as a named escape hatch
(trigger below), not the plan.

## Load-bearing findings

1. **rust-analyzer is the facade already shipping, inverted.** Its
   `parser` crate is token-representation-agnostic ("Token independence
   allows us to parse out both text-based source code and `tt`-based
   macro input"); `LexedStr::to_input()` drops trivia before the
   grammar runs, `intersperse_trivia()` re-attaches it afterwards from
   the same lexed record. The grammar never sees a comment. KRS's
   existing `parse_rule_block` / `parse_rule_block_source` pair is
   structurally the same design (`crates/krs-syntax/src/rule.rs`
   ~1810–1846); the `str -> TokenStream` step is exactly where trivia
   is dropped today.

2. **KRS has an advantage no surveyed tool had**: proc-macro2 (already
   built with `span-locations`; `Span::byte_range()` is documented
   accurate outside proc-macro context and was empirically confirmed
   in-tree) hands back a byte-exact token partition of the source. The
   trivia scanner therefore never decides token boundaries — it only
   classifies the *complement* of the token set, where the only legal
   content is whitespace, `//`, and nested `/* */`. That classifier is
   ~50 lines and **provably total**: assert
   `⋃ token_ranges ∪ ⋃ trivia_ranges == 0..len`. Divergence between
   the classifier and the lexer is a coverage-check failure, never
   silent — the drift worry, discharged by an oracle.
   *Hazard found empirically*: doc-comment desugaring (`///` →
   `# [doc = "…"]`) makes the five synthesized tokens share one byte
   range — union token ranges before complementing.

3. **verusfmt is the cautionary tale, not the model.** Comments enter
   pest's tree as untagged siblings; inline-vs-own-line is recovered by
   a regex pre-pass over rendered *line geometry* plus sentinel strings
   (`FORMATTER_FIXUP`…) patched out by a regex post-pass. The
   classifier's input is the formatter's own output → structurally
   non-idempotent (issue #22; ships an `idempotency-test` mode because
   of it). Its worst documented failure (#181, first entry) is
   literally KRS's table-row case: an own-line comment above a clause
   in a clause list gets dedented to column 0 and gains a spurious
   blank line. README lists "handle comments perfectly" as
   **Non-Future Work**; seven releases of comment fixes, #181 still
   open. Its other tax — the 44 KB grammar is a second Verus parser,
   ~80% of the changelog is catch-up — is what the facade avoids.

4. **cedar-policy-formatter is the attachment model to copy.**
   `WrappedToken { token, span, comment: { leading: Vec<&str>,
   trailing: &str } }`; the leading/trailing rule is one exact line —
   gap text up to the first `\n` trails the left token, the rest leads
   the right token — decided from *original* source geometry, so
   idempotent by construction. Its weakness: comment emission is
   hand-plumbed per syntactic position and a forgotten position
   silently drops the comment (issue #459, the `is` position). Cedar's
   compensations: a fuzz oracle injecting UUID comments at every token
   and asserting all appear **in order** (dropped vs reordered are
   distinct panics), plus consume-once semantics (clone-then-clear).
   Cedar deliberately deletes interior blank lines (#265 WONTFIX) —
   KRS keeps blank lines, so it must carry them explicitly.

5. **Attach trivia to tokens, not AST nodes** (Roslyn's rule: a token
   owns trivia after it on the same line up to the next token; later
   trivia belongs to the following token — total, no per-construct
   table). Node-attached models need a handler wherever the AST lacks
   a node for a token: ruff documents this exactly ("Because
   RustPython doesn't create a Node for the `/` argument, it is
   impossible to associate any comments with it") and pays 2,458
   lines / 38 handlers of placement heuristics; Prettier pays 37.
   KRS's `=>`, `;`, `:`, `where` are the same holes. Rowan does not
   buy attachment either — losslessness and attachment are orthogonal
   (black, on its lossless CST: "comments don't 'belong' anywhere…
   we simply don't know what the correct parent should be").

6. **The real hazard of recover-from-source is N approximations of
   the lexical rule.** Zig's renderer contains five independent
   `indexOf(source, "//")` scans, none the tokenizer's definition —
   and a long tail of zig-fmt comment-loss bugs (#3686, #12617,
   #20108, #25267…) at exactly the positions a scan forgot. One
   authority function, and nothing else ever scans for `//`.

7. **Every mature tool backstops attachment with mechanical oracles**,
   not trust: rustfmt's `recover_comment_removed` (on any lost comment
   payload, keep the author's original bytes), ocamlformat (AST
   equality up to normalization + comment-set equality up to
   location), ruff (`assert_all_formatted` per-comment consumed flag +
   `ComparableMod` + `--stability-check`), cedar (UUID fuzz walk).
   Comment-placement *quality* is the one thing no oracle can check
   (ruff: 209 placement issues; the only accepted Black divergence) —
   irreducible, paid by rowan-based tools too.

## Adopted design (decision F7)

1. **One lexical authority**: `krs_syntax::trivia::lex_gaps(source,
   &token_ranges) -> Vec<Trivia>` (`Whitespace{newlines}`,
   `LineComment`, `BlockComment`). Nothing else in krs-syntax or
   `krs fmt` may scan for `//` — enforced by a grep test.
2. **Totality asserted**: tokens ∪ trivia cover every byte exactly
   once (debug assert + release check in `--check`); union token
   ranges first (doc-comment hazard).
3. **API**: `parse_*_source_with_trivia(&str) -> Result<(Ast,
   TriviaTable), SyntaxError>` alongside the untouched existing entry
   points; trivia keyed by byte offset, **not** a trivia-carrying AST.
   Macro path and collector unaffected.
4. **Attachment**: cedar's first-`\n` split / Roslyn's same-line rule,
   anchored to tokens `(preceding_token_end, following_token_start)`,
   with formatter traversal reaching those token attachments via the
   existing `TokenRange` walk; ownership remains token-only.
5. **Placement table small by construction**: a rules table has few
   positions (before table, before clause, end of clause line, header,
   inside `k![…]`/`cells!`/`map!`). Budget 5–10 handlers;
   **>~15 handlers is the tripwire to re-open the rowan option**
   (reference designs: Slint, Biome; R1's versioned rust-analyzer
   syntax crate as outer CST).
6. **Blank lines**: blank-before trivia captured from source and
   preserved verbatim between clauses (never synthesize a run) —
   carried as data, never grammar (verusfmt's `MULTI_NEWLINE`
   grammatical scoping caused three of four #181 failures) and never
   inferred from rendered geometry.
7. **Doc comments stay structural** (already are:
   `ProductionDocumentation` via `#[doc]`) — never routed through
   trivia (verusfmt #102 learned this the hard way).
8. **Three in-binary oracles, on by default**: (a) trivia
   preservation — re-run `lex_gaps` on output, comment-payload
   multiset equal, on failure keep original bytes rustfmt-style;
   (b) AST equality modulo spans — re-parse output with the same
   entry point, compare span-blind (`ComparableRuleBlock`); this
   discharges the semantic-payload part of F6, while the formatter test
   ladder separately checks identity/topology-preserving re-anchoring;
   (c) idempotence (already F1). Plus cedar's UUID-injection fuzz target
   (inject marker comments at every token, assert all present **in
   order**, distinct dropped/reordered failures) and an
   all-consumed residue assertion cedar lacks.

## Layout consequences feeding F5

- **Decided (2026-08-23, folded into F7): DSL-body comments are line
  comments only.** Non-doc `/* */` inside `k::rules!`/`cells!`/`map!`
  bodies is a hard error at `krs fmt`/collector time (proc macros
  cannot see comments, so enforcement lives in the source-path tools;
  `fmt --check` is the blocking gate). This makes trailing comments
  provably newline-free (cedar's split rule holds exactly and
  idempotently), and deletes the inline-between-tokens, multi-line
  reindentation, and nesting failure classes. Precedent: Zig removed
  multiline comments language-wide for tooling; Python/TOML/Hare have
  none; cedar's clean model exists because it only has `//`. Zero
  `/* */` in the KRS corpus at decision time; the gap classifier
  still lexes them (good error spans), so relaxing later is purely
  additive. Consequence: a comment interior to a clause can only be a
  `//` on an author-broken line — the formatter normalizes it to
  leading position above the clause.
- **Still open (F5 fixture territory)**: whether trailing clause
  comments in a whole-table-aligned block form their own aligned
  **comment column** (recommended; no surveyed tool ships it — fixed
  2-space gutters everywhere) or sit at a fixed gutter.

## Known limits / unverified

- swc comment-loss issue numbers and ocamlformat's `parser_extended`
  rationale were not independently confirmed.
- proc-macro2's fallback lexer is itself a second Rust lexer vs
  rustc's — a pre-existing dependency of every `_source` entry point
  and `collect.rs`, out of scope here; one risk-register line.
- No oracle can verify a comment landed where the author *meant* —
  only that none were lost, reordered, or semantics-changing.
