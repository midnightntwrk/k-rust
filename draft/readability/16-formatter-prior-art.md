# 16: Formatter prior art — enforced layout for `k::rules!` bodies

Runs the survey pinned in [15-formatter-pin](15-formatter-pin.md).
Method: two parallel deep-research passes on 2026-08-21 — one over the
dedicated macro-DSL formatter ecosystem, one over the rustfmt /
rust-analyzer / pretty-printer substrate — verified against live repos,
issues, and local runs of `rustfmt 1.9.0-stable` / `1.10.0-nightly`
(claims below cite repo paths and issue numbers; empirical claims were
reproduced, not recalled). This doc answers pin questions 1, 2, and 4;
questions 3 (canonical layout design) and 5 (provenance/span safety) are
internal design work and stay open (§I).

## Verdict (2026-08-21, decided): build `krs fmt` after verusfmt

**Decision: KRS ships `krs fmt`, modeled on verusfmt.** The doc-15 bet
pays — candidate A's enforced-layout condition is satisfiable, and the
model to copy is settled. Four independent projects ship a dedicated
formatter for a Rust macro DSL — **verusfmt** (`verus!{}`),
**leptosfmt** (`view!`), **dioxus `dx fmt`** (`rsx!`), **Slint**
(`slint!`) — and verusfmt is a near-exact structural match to KRS: a
verification DSL inside one brace-delimited macro, built for the
identical "rustfmt won't format our macro body" reason, **enforced as a
blocking `--check` job in Verus's upstream CI** with a vendored
fixed-point corpus and an idempotency harness. The doc-14 fallback to
C/D is released: not needed on formatter grounds.

**Adopted from verusfmt wholesale** (§A for each):

- Standalone formatter binary that owns the DSL layout; layout engine
  is a Wadler/Oppen pretty-printing library (`pretty` crate), never
  hand-rolled; formatter kept stateless.
- Comments as first-class trivia in the parse (not `syn`-scraped).
- The **elide-and-splice** rustfmt coexistence: rustfmt runs over the
  file with `k::rules!` bodies collapsed to `k::rules!{}` placeholders,
  bodies spliced back after — rustfmt physically never sees DSL text,
  immune to rustfmt macro-handling changes (PR #7031, §D). The §D
  fixpoint (body anchored at block indent) is kept as a *tested
  invariant on top*, not as the mechanism.
- The project's `rustfmt.toml` discovered and forwarded so one style
  config governs both halves of the file.
- `--check` with unified diff + exit 1; four test layers
  (differential-vs-rustfmt, `insta` DSL snapshots, fixed-point corpus
  of real KRS files, idempotency mode); a scheduled corpus-refresh job;
  a skip attribute as the deep-nesting escape hatch (§H).
- CI enforcement as a blocking job other jobs `needs:` (§F).

**Deliberate deviations — each fixes a documented verusfmt gap:**

1. **krs-syntax is the parser** (verusfmt: a second 44 KB pest grammar,
   and grammar drift is its dominant lifetime cost, ~80% of its
   CHANGELOG; maud#479 is the same wound). One grammar, formatter as a
   krs-syntax consumer — the ungrammar lesson (07 §8) already decided
   this posture. Constraint: krs-syntax must expose a public parse API
   with comment/whitespace trivia (§C, §I).
2. **`--stdin` from day one** (verusfmt's missing stdin mode is why it
   has *no* editor integration, §A). Delivery via a checked-in
   `rust-analyzer.toml` `[rustfmt] overrideCommand = ["krs", "fmt",
   "--stdin"]` — one hook covers VSCode, Neovim, and Zed (§E).
3. **Workspace member, not a separate repo** (Verus fights formatter
   version skew with a minimum-version pin and a monthly corpus cron;
   in-workspace, `Cargo.lock` pins it and a grammar change plus its
   formatter change land in one reviewed commit, §F).
4. **Idempotence checked in-binary by default** with Topiary's two
   error variants (verusfmt hides it in an unstable dev subcommand,
   §G) — the right posture for a machine-checkable-oracle workspace.
5. **cargo-metadata file discovery**, `--check` failing on parse
   errors, aggregate-all-files reporting (the leptosfmt/verusfmt CI
   paper cuts, §B, §F).

Two findings sharpen the design beyond "copy verusfmt":

1. **Stable rustfmt can be made a *provable no-op* on the formatted
   body** (§D): rustfmt's only transform on braced macro bodies is an
   indent shift that is the identity iff the least-indented body line —
   including the closing `}` — sits at the macro's block indent. Emit at
   block indent and coexistence with `cargo fmt` needs no nightly
   options, no skip config, and no convention.
2. **Comment handling should pick the architecture** (§C): every
   `syn`-based formatter loses or scrapes comments forever; the two
   structurally sound options are a grammar with comments as first-class
   trivia (verusfmt's pest; krs-syntax can do this) or a lossless
   `rowan` CST (Slint).

Dead ends, confirmed so we never revisit: a rustfmt plugin/extension
point (explicitly refused by maintainers, §D), rustfmt-as-a-library
(maintainer: "In short, don't", §D), prettyplease as the DSL substrate
(private modules, comments won't-fix, §C), dprint (routes by file
extension only, §C), genemichaels (formats macro bodies by token
guesswork, no `--check`, §B), Topiary today (injection machinery
unreleased, Rust tier experimental — reference design only, §C).

---

## A. verusfmt — the headline precedent, examined

[verus-lang/verusfmt](https://github.com/verus-lang/verusfmt). Alive
(commit 2026-08-20, v0.7.2 2026-06-10). Mechanism: a 44 KB **pest**
grammar for the DSL plus a 2.5 KB *minimal* grammar that only
distinguishes DSL-macro spans from everything else; layout via the
**`pretty` crate** (Wadler); deliberately stateless. No `syn` anywhere.

- **The elide-and-splice trick** (`src/rustfmt.rs`): stash each
  `verus!{…}` body, replace it with the literal `verus!{}`, run the real
  `rustfmt` binary over the collapsed file on stdin, re-parse, splice
  the DSL-formatted bodies back. rustfmt is *physically unable* to see
  the DSL — a guarantee independent of rustfmt's macro handling ever
  changing. It also discovers the project's `rustfmt.toml` in rustfmt's
  own precedence order and forwards it, so one style config governs both
  halves of the file.
- **Enforced upstream as a blocking gate**: Verus CI's `fmt` job runs
  `cargo fmt -- --check` plus `find ./vstd -name '*.rs' -exec verusfmt
  --check {} +`, and downstream jobs declare `needs: [fmt, …]`.
  CONTRIBUTING requires conformance; their build tool pins
  `MINIMUM_VERUSFMT_VERSION` to fight version skew.
- **Four test layers** (the model to copy): differential-vs-rustfmt for
  plain-Rust constructs; `insta` snapshots for DSL syntax; **fixed-point
  tests over vendored real-world corpora** (`formatted == original` on
  IronFleet, node-replication, mimalloc, a vstd snapshot); an
  idempotency subcommand — plus a **monthly cron** that re-pulls
  upstream sources and auto-opens a PR when the corpus drifts, which is
  how syntax additions that outran the formatter get caught.
- **Its recurring failure mode is grammar drift**: the CHANGELOG is
  ~80% "add support for <syntax> (see verus#NNNN)" — every upstream
  syntax PR needs a matching formatter PR, forever. The same tax
  motivated maud#479 ("the ast parser is private and unusable… I'd have
  to keep it in sync"). **KRS is the only project in this survey
  positioned to not pay it**: krs-syntax already owns the real
  `cells!`/`map!`/rule grammar (15 §established; the ungrammar lesson,
  07 §8). This is an API decision to make *now* — the formatter must be
  able to depend on krs-syntax as a library.
- **Its one real gap: no stdin mode**, so it cannot be wired as a
  rust-analyzer formatter override at all — verus-analyzer contains
  zero references to it, and verus-mode.el still carries a "disable
  format-on-save" FIXME. verusfmt is a CLI/CI tool, not format-on-save
  (a `--stdin` PR, verusfmt#216, is open). KRS ships `--stdin` day one.
- **Comments are its declared non-goal** ("Handle comments perfectly —
  they're surprisingly hard!"; standing umbrella issue #181, maintainer:
  "Handling comments is Hard™️"). §C for why KRS can do better
  structurally.
- **Depth is real**: exponential blowup on ~27 nested variants (#106 —
  the maintainer's answer was the skip attribute; rustfmt itself also
  times out ~30), tests need an 8 MiB grown stack (`stacker`). A
  formatter over recursive rule terms needs an explicit stack-depth
  story and an escape hatch.

## B. The rest of the field, compressed

- **leptosfmt** (`view!`): the best *integration* story — `--stdin
  --rustfmt` wired as RA's `rustfmt.overrideCommand` is its documented
  install path — but the project is **stalled** (last release
  2025-01-30, 19 months) while still heavily used, and a known
  mangles-generic-tags bug sat fixed-but-unreleased for those 19 months
  (jaunder ADR-0118 pins a past git revision and notes the pinned
  binary is indistinguishable by `--version`). Its `syn` + forked
  prettyplease stack cannot represent non-doc comments in code blocks
  (README-documented), scrapes `//` comments from span gaps, walks
  `target/` because it globs instead of asking cargo (11.8 s vs `cargo
  fmt`'s 0.23 s, #158), and its `--check` **does not fail on parse
  errors** (unparseable files pass CI silently) — each a listed
  anti-lesson. Also the ordering cautionary tale: running itself
  *before* rustfmt caused oscillation that broke CI (#54).
- **dioxus `dx fmt`** (`rsx!`): alive and the best IDE story (VSCode
  extension with a real three-state format-on-save setting that
  *coexists* with rustfmt instead of replacing it; `--file -` stdin
  mode; honors `#[rustfmt::skip]` instead of inventing an attribute).
  Its hand-rolled 48 KB writer forces the README disclaimer "output is
  not guaranteed to be stable between minor versions" — which is fatal
  to a CI `--check` gate across upgrades, and the argument for using a
  layout library instead. Two transferable items: `FormattedBlock
  {formatted, start, end}` byte-range edits as the output type, and
  learning indentation/edition by shelling `cargo fmt -- --print-config
  current` instead of re-implementing config discovery. One disaster to
  design against: **rustfmt DOES rewrite paren/bracket macro
  invocations** — dioxus#3433 shows `cargo fmt` collapsing
  `rsx!(...)` and in one repro swallowing a trailing `//` comment into
  the closing paren, producing broken code. *The categorical
  non-formatting guarantee is a brace guarantee.* `k::rules!` must
  mandate braces and lint the other delimiters.
- **genemichaels** (whole-file rustfmt replacement that "attempts"
  macro bodies): formats them by heuristics — try parsing as Rust, else
  split on `;`/`,`, else **join tokens with spaces** — which is
  destructive to any DSL with meaningful adjacency (mangles
  `quote!{}` bodies, re-tokenizes `$(...)* =>` into `$(...) *=>`), and
  it has no `--check` mode. Unusable here. One idea worth stealing: it
  **re-parses its own output before writing and asserts every comment
  was consumed** — a cheap invariant against the worst bug class.
- **yew-fmt**: a fourth integration mode — a full **rustfmt CLI proxy**
  (`RUSTFMT=yew-fmt cargo fmt` just works, `--check` inherited) that
  shells out to real rustfmt and layers `html!` formatting on top. Best
  UX, but commits to mirroring rustfmt's whole CLI surface; dormant ~13
  months. Not the pick, but the fallback shape if `cargo fmt`
  invisibility ever becomes a hard requirement.
- **Slint** (`tools/lsp/fmt`): the architecture nobody else used —
  **`rowan` lossless CST + token rewriting** (`TokenWriter` emitting
  edits, not files). Comments and whitespace are first-class CST nodes,
  so comment preservation is *free*, and the same code path yields LSP
  `TextEdit`s later. Its one warned-against part: a hand-rolled
  heuristic scanner to *locate* the macro ("Technically, we should be
  lexing rust" — their own comment). Location belongs to
  `syn`/`proc-macro2` (`Span::byte_range()` is documented byte-accurate
  outside proc-macro context) or a minimal grammar, never a scan.
- **maudfmt / sqlx-fmt**: small confirmations — maudfmt's largest
  source file is its comment-and-whitespace module (18.6 KB, bigger
  than all its printers combined), and sqlx-fmt shows the
  locate+delegate+splice shape with a ready-made GitHub Action.
- **ascent — the counterfactual**: no formatter, no formatting story;
  just a nightly-only `rustfmt.toml` with `format_macro_bodies =
  false`, i.e. they told rustfmt to keep hands off and left users
  hand-aligning rule bodies forever (the 18-line hand-aligned rule of
  09 §D). That is precisely the rot doc 15's bet refuses.

## C. Architecture: comment handling picks it

Every surveyed tool decomposes the same way — locate the macro span,
parse the body, lay it out, splice, hand the rest to rustfmt — and the
axis they differ on, and bleed on, is comments:

| | Structure | Emit | Comments |
|---|---|---|---|
| verusfmt, cedar-policy-formatter | own grammar (pest/logos) | `pretty` (Wadler) | in the grammar as trivia — good, still "surprisingly hard" at line ends |
| leptosfmt, dioxus, maudfmt | `syn` (+DSL parser) | forked-prettyplease Oppen / hand-rolled | **lost by `syn`**, scraped back from span gaps, documented residual gaps in all three |
| Slint, Biome | `rowan` lossless CST | token rewriter | **free** — trivia are CST nodes |
| genemichaels | `syn` + guesswork | hand-rolled | out-of-band + re-parse check |

For KRS the choice is between the first and third rows — krs-syntax
either carries comments as trivia in its parse (verusfmt/cedar shape;
cedar's `WrappedToken { token, span, comment: {leading, trailing} }` is
the cleanest attachment model found) or moves to a rowan-style lossless
tree. **Never the second row.** prettyplease specifically is not a
substrate: its 22 modules are private behind one `unparse(&syn::File)`
function, its macro handling is a hardcoded ~25-name std allowlist plus
a token-spacing automaton (a `k::rules!` body would get the automaton),
and comment support is dtolnay-won't-fix (#50: "not something I am
interested in supporting"). leptosfmt's fork of it (36 ahead / 55
behind upstream) is the standing price of ignoring that.

Also ruled out as *delivery* vehicles: **dprint** (plugins route by
file extension; a `.rs` region can't reach a DSL plugin without first
writing a whole Rust formatter — and the official rustfmt plugin is
archived), and **Topiary** (the genuinely interesting tree-sitter
injection design — `serde_json::json!` bodies formatted as JSON — is
entirely in unreleased `main`; Rust support is "experimental… should
not use to format production code"; and tree-sitter-rust parses macro
bodies as untyped token soup anyway, so KRS would bring its own
grammar). One cheap Topiary-adjacent win independent of formatting: a
tree-sitter `injections.scm` rule for `k::rules!` bodies buys editor
syntax highlighting in Neovim/Helix/Zed — nvim-treesitter already
ships exactly this pattern for `slint!`/`html!`, including the
`(#offset! … 0 1 0 -1)` trick that strips the outer braces.

## D. The rustfmt substrate — sharper than 09 §D had it

- **The brace guarantee, characterized at source.** rustfmt's braced
  branch skips argument parsing entirely (`parse_macro_args` only
  parses non-brace delimiters), so even a body of valid Rust items is
  left alone — that is why "categorical" is the right word. The *one*
  thing it does is `trim_left_preserve_layout`: shift the body so its
  least-indented line — **the closing `}` participates** — lands at the
  macro's block indent, preserving relative offsets byte-for-byte.
  Verified empirically both ways (body at indent 0 pulled up to 4; a
  mis-indented closing brace pushed to 8). **Corollary: a canonical
  layout whose minimum indent line sits at block indent is a rustfmt
  fixpoint on stable** — `rustfmt --check` exits 0 byte-identical,
  comments included. This upgrades result-README item 4's "keeps its
  layout for free" from folklore to a testable invariant:
  `rustfmt(krs_fmt(x)) == krs_fmt(x)` belongs in the test suite.
- **Watch item**: rustfmt PR #7031 (open, 2026-08-16) touches exactly
  `trim_left_preserve_layout`, and its author writes "the formatting
  for macros with braces needs to be reworked. I'm opening this PR as a
  starting point." The only live change that could perturb the
  fixpoint; verusfmt's elide-and-splice is the immunization if wanted.
- **All three macro config options are nightly-only**, and two are
  irrelevant: `format_macro_matchers`/`format_macro_bodies` apply to
  `macro_rules!` *definitions*, not invocations. `skip_macro_invocations`
  (#5346, unstable) matches the *call-site source text* — `k::rules`
  and an imported bare `rules` need separate entries. Not needed given
  the fixpoint, and not usable on stable anyway.
- **No extension point exists, and none is coming.** The plugin
  proposal (#4849) was closed in 2021: "rustfmt is not supposed to be a
  generalized formatting platform." Macro-authors-declare-formatting
  has been re-raised and re-rejected on #8 (open since 2015, last
  activity 2025) — rustfmt runs on the AST before any macro knowledge
  exists. The 2024 IRLO thread on grammar-info-for-proc-macros went
  dormant with no RFC. Style edition 2027 contains nothing
  macro-relevant. The believed-no in pin question 2 is now a
  cited no.
- **rustfmt-as-a-library is officially dead**: last crates.io release
  2020, docs.rs build failed, `#![feature(rustc_private)]` + matched
  nightly required, and maintainer #5955: "**In short, don't** … we
  don't support that in any shape or form." The supported reuse is the
  *binary* on stdin — which is what all the shipped tools do.
- The Rust Style Guide explicitly scopes third-party macros out
  ("does not define formatting for any third-party macros"), so a
  KRS canonical layout contradicts nothing normative.

## E. Editors: one hook covers three of four

rust-analyzer formatting is a subprocess call — whole file in on
stdin, whole file out — and `rust-analyzer.rustfmt.overrideCommand`
swaps the binary. Since VSCode, Neovim (LSP), and Zed all route Rust
formatting through RA, a checked-in **`rust-analyzer.toml`** with
`overrideCommand = ["krs", "fmt", "--stdin"]` is zero-per-user-config
delivery for all three (leptosfmt's documented pattern; needs RA ≥
2024-06-10 and is flagged unstable by both RA and leptosfmt). Verified
traps: RA does **not** pass `--edition` to an override (recover it via
`rustfmt --print-config current`, the dioxus trick, which also yields
`tab_spaces`); `rustfmt.extraArgs` is silently ignored; setting the
override **disables RA range-formatting capability unconditionally**
(plan whole-file; range formatting never reached macro bodies anyway —
it is line-based `--file-lines` on nightly); relative command paths
resolve against the wrong root in multi-workspace repos (RA#18222) —
ship `krs` on `$PATH`. RustRover has no override; the fallback is its
File Watchers plugin, and leptosfmt's matching issue (#115) sits
unanswered — accept the gap. Neovim's conform.nvim and Zed can also
chain formatters natively if anyone prefers that wiring.

**Chaining order**: the established pattern is the custom formatter
invoking rustfmt *internally* (leptosfmt `--rustfmt`, verusfmt by
default, dioxus `--all-code`). Run **rustfmt first** (dioxus's order):
rustfmt decides the macro invocation's own indent, and the §D fixpoint
anchors the body to it. leptosfmt runs itself first and #54 is the
resulting oscillation breaking CI.

## F. Enforcement and the version-skew problem

- **CI gate**: `--check` → exit 1 + unified diff is the universal
  convention (rustfmt, verusfmt, leptosfmt, dioxus); implement it
  aggregate-all-files (verusfmt's lack of a walker forces `find -exec`
  contortions downstream), failing on parse errors too (leptosfmt's
  silent-pass bug), CRLF-normalized. Structure it as a job other jobs
  `needs:` — the Verus pattern. Alternatives on record: the autofix-bot
  pattern (leptos runs the formatter in write mode on PRs and pushes
  the fix), and pre-commit hooks — which run in *write* mode by
  contract, are per-clone opt-in and `--no-verify`-bypassable, so they
  are a latency optimization, never the gate.
- **Version skew is the ecosystem's recurring wound** — Verus installs
  `releases/latest` and compensates with a minimum-version pin plus a
  monthly corpus cron; jaunder pins a leptosfmt git revision because
  the fix it needs shipped to no release for 19 months; rust-lang/rust
  pins rustfmt by commit hash + artifact SHA256. **For KRS the whole
  problem evaporates: `krs fmt` is a workspace member**, pinned by the
  same `Cargo.lock` as the macros, built from the checked-out tree
  (`cargo run -p krs-fmt -- --check`; a `.cargo/config.toml` alias for
  ergonomics — the xtask pattern). It is also semantically right: a
  `k::rules!` grammar change and its formatter change land in one
  commit, reviewed together.
- The rust-analyzer `try_ensure_file_contents` primitive
  (write-and-fail: locally one run reports *and* fixes; CI discards the
  write) is the right shape for any generated-content checks that ride
  along.

## G. Idempotence: a runtime invariant, not just a test

Topiary checks idempotence **in the binary, by default** (format
twice, compare), at self-reported negligible cost, with two distinct
error variants — "output changed on the second pass" vs "**the output
no longer parses**" — and a `--skip-idempotence` escape. For a
workspace whose thesis is machine-checkable oracles, that posture is
the obviously right one; adopt it wholesale. The full ladder, each
rung attested in the field: (1) `fmt(fmt(x)) == fmt(x)` (Topiary
runtime; Ruff/Biome fuzz targets; rustfmt's own `tests/target`
idempotence suite), (2) every golden survives `--check`
(fixed-point corpus — verusfmt's `formatted == original` over vendored
real code; prettyplease's `regenerate; git diff --exit-code` CI job is
the cheapest version), (3) second pass re-parses, (4) self-hosting
(rustfmt formats itself; Topiary formats its own queries). KRS adds
rung (5): `rustfmt(krs_fmt(x)) == krs_fmt(x)` (§D). This also
subsumes the round-9 idempotence worry: idempotence is *tested, not
assumed* everywhere — verusfmt shipped three real non-idempotency bugs
and regression-tested them.

## H. Skip semantics — one policy for tables and rule bodies

Verified: `#[rustfmt::skip]` is stable on items **and on
statement-position macro invocations** (body byte-preserved, no
re-anchoring); expression position is nightly-only
(`stmt_expr_attributes`); `#![rustfmt::skip::macros(...)]` matches
bare idents only, so it can never match the `k::rules!` call-site
path — not an option. The 02b question (result README item 4) closes
as: **keep `#[rustfmt::skip]` on the enum tables** — it is the stable,
intended tool, dioxus honors the same attribute rather than inventing
one, and the macro bodies never needed it (§D fixpoint). If a
per-item escape hatch inside `k::rules!` bodies is ever needed
(the deep-nesting case, §A), it is `krs fmt`'s own attribute
(`#[krs::skip]`, the verusfmt precedent) since the semantics are then
ours, honored by our formatter, with the genemichaels
all-comments-consumed re-parse check as the safety net.

## I. What stays open (not answered by prior art, by design)

- **Canonical layout design** (pin question 3): where `=>`/`where`
  sit, the collapse rule, comments-in-rule-bodies. One requirement the
  survey *adds*: the round-9 single-cell tables are not merely
  one-liners — they are **column-aligned** (`imp_round9.rs:232-253`:
  aligned arrows, aligned `where`, blank-line rule groups). Vertical
  alignment across clauses is beyond what any surveyed DSL formatter
  emits (verusfmt/leptosfmt do not column-align; genemichaels's
  split-groups has alignment machinery; `pretty` exposes
  column/nesting primitives but alignment is the author's job).
  Whether the canonical layout *requires* cross-clause column
  alignment — and its stability under small edits (add one long label,
  every line moves) — is now the central layout-design question.
- **Provenance/span safety** (pin question 5): a formatter that
  rewrites author bytes moves the collector's byte-exact anchors
  (README method gate 2). The splice-edits architecture minimizes the
  blast radius (untouched regions keep their bytes), but
  anchor-stability under reformatting still needs its own check
  against gates 2 and 4. Unchanged by this survey; still internal
  work.
- **The krs-syntax API decision** (new, urgent): the formatter
  consuming krs-syntax as a library is what deletes this survey's #1
  recurring cost. That constrains krs-syntax now — public parse API,
  and comment/whitespace trivia representation (§C) — before the
  formatter exists.

## Consequences for docs 14/15

The doc-15 bet resolves **in favor of candidate A**, and the mechanism
is decided: **`krs fmt`, built after verusfmt** (§Verdict) — enforced
canonical layout is not just viable but the standard practice of the
closest comparable project (Verus), with a cheaper path available to
KRS than to anyone surveyed (shared grammar, in-workspace binary,
provable rustfmt fixpoint). The C/D fallback clause in 14 §Verdict is
released from formatter-viability duty; C/D remain recorded purely as
the alternative rule form. Next sessions: the canonical layout design
(§I first bullet, now with the alignment question sharpened) and the
krs-syntax trivia/API decision (§I third bullet) — both are now
design inputs *to* `krs fmt`, not gates on whether it exists.
