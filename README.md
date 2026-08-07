# k-rust — feasibility study: porting the K frontend to Rust

**Status:** investigation notes plus an implementation in progress. The single `k-rust` crate
now contains a WASM-compatible KORE AST, lexer, parser, string codec, compact/pretty printer,
lossless KORE JSON v1 codec, Scala-compatible ordering and explicit KAST normalization,
snapshot tests, property tests,
and upstream-derived text and JSON fixtures. The user-facing KAST term model now includes
KAST JSON v4, textual parsing/printing, and context-free KORE conversion. The portable
definition layer now includes the flat Scala-faithful sentence/module model and lossless
compiled-definition KAST JSON v4 interchange. Deterministic, WASM-compatible module-import
resolution uses `petgraph`, preserves visibility, and reports complete import cycles. Resolved
sentence identity and ordering reproduce Scala's explicit rules, including its deliberate gaps
and its unusual `Production` equality/ordering divergence. A deterministic `petgraph`-backed
partial-order layer now derives semantic/syntactic subsorts and both Scala overload mechanisms.
It also derives syntax-priority closure and Scala's left/right/non-associative tag-pair sets.
A shared deterministic production catalog provides stable identities plus label, sort, token,
function, locality, ordering, and signature indexes; overload relations use the same identities.
A Scala-compatible sort catalog covers arity-aware sort heads, declarations, synonyms, concrete
parametric instantiations, locality, merged attributes, hooks, token sorts, and user-list sorts.
Production label metadata and stable rule/claim/context catalogs cover merged label attributes,
result sorts, fresh generators, macros, locality, ordering, and Scala's `#withConfig` grouping.
A renderer-independent diagnostic model and the first Java-compatible structural checks cover
duplicate labels, syntax groups, associativity, multiple top sorts, and token productions.
Reusable KAST traversal now supports Java-compatible `CheckK`, `CheckRewrite`, and
`CheckAnonymous` validation for `#as`, rewrite placement, function contexts, existential
variables, and anonymous-variable usage.
Position-aware variable analysis ports `CheckRHSVariables`, including ML binders, semantic casts,
pattern/value positions, `unboundVariables`, and explicit symbolic/Haskell policy options.
The same shared positional traversal now powers `CheckFunctions`, using visible production
metadata and Java's special collection-hook matching behavior.
Production-shape validation covers strict and sequential-strict positions, sort-`K` holes,
stream-cell contents, duplicate configuration cells, and unsupported cell bags.
Definition-wide checking now composes those module checks deterministically, validates every
rule/context KLabel against visible productions and K's derived internal labels, rejects duplicate
production symbols across the main import closure, and enforces Java's concrete/symbolic function
rule consistency policy.
A canonical attribute registry now validates recognized attributes and their permitted module or
sentence kinds. Java-compatible attribute semantics cover rule-mode conflicts, hooked-sort
constructors, binders, format/color strings, symbol migration, overload restrictions, bracket
productions, deprecation warnings, and SMT-lemma symbols.
The definition layer also has a structured, Unicode-safe K-regex AST, recursive-descent parser,
anchor-preserving printer, and an explicitly Java-compatible printer retaining the pinned
frontend's asymmetric-anchor bug. `CheckRegex` validation covers lexical references and cycles,
named-syntax anchors, character and repetition ranges, and the frontend's Unicode restrictions.
The first unlowered outer-syntax layer now preserves source spans, modules, imports, syntax
declarations, user lists, priorities, associativity, lexical declarations, and rule-like bubbles;
the Java-compatible `CheckListDecl` and `CheckBracket` run against this source-shaped AST before
flattening. The initial `KILtoKORE`-shaped lowering expands user lists, derives production labels,
converts priorities and associativity, preserves source metadata, and leaves rule bodies as bubbles
for the inner parser. A probe over 1,504 `.k` files at the pinned K commit accepts 1,499; the five
exceptions are four intentional malformed-string tests and one legacy `Token{...}` fixture that is
not accepted by the pinned JavaCC grammar either.
A host-independent source loader now walks recursive `requires` graphs through a caller-provided
resolver, deduplicates canonical source identities, reports require cycles with their complete
paths, lowers all files with one global production-tag index, and hands the result to the existing
deterministic module-import resolver. Production result and nonterminal sorts are then normalized
through each module's visible sort-synonym map at the same boundary as the Java frontend. This
keeps filesystem and URL policy outside the WASM-compatible frontend core. A reusable portable
chart parser now consumes visible lowered productions, including left recursion, nullable rules,
default layout, regex restrictions, named lexical references, parse-forest sharing, and explicit
ambiguity/resource errors. The loader uses it with the implicit `CONFIG-CELLS` and K bridges to
replace configuration bubbles with structured KAST, covering nested and external cells, cell
properties, imported user syntax, configuration variables, semantic casts, and `ensures` clauses.
Dependency-ordered configuration expansion now generates ordinary, optional, and collection cell
syntax, fragments, initializers, Map helpers, and exit-code rules, and resolves external cells
against imported generated initializers before returning a loaded definition.
The loader then derives a `RULE-CELLS` grammar from visible user and generated syntax and replaces
unambiguous rule, claim, context, and context-alias bubbles with structured KAST. This first slice
supports rewrite bodies, semantic casts, user-defined conditions, optional cell dots, nested cell
bags, and `#withConfig`; genuinely ambiguous forests remain explicit errors until the canonical
disambiguation stack is ported.

**Question being answered:** how hard is it for an AI agent fleet to reimplement the
Java/Scala *frontend* of the K Framework in Rust, with WASM support for the pieces
third parties would realistically want to extract (KORE parsing, KAST parsing, …)?
Backends (LLVM, Haskell) are explicitly out of scope — they stay as they are.

## TODOs

- Preserve attributes on nested KAST terms, especially source locations and resolved production
  metadata. Diagnostics emitted for nested terms currently use the containing sentence's span,
  and semantic-cast sort context is recovered from its label; exact spans and parametric cast sorts
  are deferred until the lossless representation and parser carry term attributes end to end.
- Add Java-compatible unused-symbol warnings once nested term sources and include-directory
  provenance are available. Those warnings deliberately depend on both, so the current portable
  checker does not guess from sentence-level metadata.
- Port `CheckDeprecated` after terms retain their resolved-production attributes; sentence-level
  production catalogs cannot identify which overloaded production a parsed application used.
- Add an AST-level differential oracle against the JavaCC outer parser and extend exact lexical
  error coverage before treating the new source parser as a drop-in replacement.
- Add presentation adapters for diagnostics after the portable diagnostic model stabilizes. A
  renderer such as `miette` may be useful for a future native CLI, but it does not belong in the
  WASM-compatible core yet.
- Finish the representation-dependent Java checks, followed by specialized parser/layout views and
  the compilation passes.
- Implement binary KORE, the native `k-rust` command-line frontend, and Markdown/literate-K input.
- Add the native filesystem resolver's builtin/current-directory/lookup-directory precedence and
  auto-imported prelude policy alongside the future command-line frontend.
- Complete Java `RuleGrammarGenerator` parity: concretize every parametric production, reproduce
  scanner token precedence and automatic follow restrictions exactly, and port the priority,
  associativity, overload, list, cast, prefer/avoid, and type-inference disambiguation passes so
  ambiguous rule, claim, context, and alias bubbles resolve canonically instead of being rejected.
- Revisit package splitting only if compile times, dependency boundaries, or release needs justify
  moving beyond the current single-crate workspace.
- Measure and port both sort-inference paths, including the Z3 fallback described in §6.9.

**Provenance.** All figures below were measured directly against these trees, not recalled:

| Repo | Path | Commit |
|---|---|---|
| `runtimeverification/k` | `inspirations/runtimeverification/k` | `4a46d12314` (v7.1.337) |
| `runtimeverification/scala-kore` | `inspirations/runtimeverification/scala-kore` | `844214975c` (v0.3.3) |

Claims marked **[unverified]** were not checked and must be confirmed before being relied on.
Re-measure everything if the pinned commits move.

---

## 1. Headline conclusions

1. **Volume is not the problem.** The entire frontend is ~44k LOC. The extractable
   library core is ~2.5k. This is small.
2. **The hard problems initially identified were WASM-induced, not inherent.**
   Restricting WASM to the library layer (and leaving `kompile` native) means `flex`,
   Z3, and MPFR can keep being subprocesses / C bindings exactly as they are today.
   That removes all three research-flavoured blockers.
3. **The KORE parser is not in the `k` repo.** It is a separate ~2.5k-line artifact
   (`scala-kore`). It is also the most portable, best-oracled, most independently-useful
   component in the ecosystem — and it is the prerequisite for everything else. Build it first.
4. **The deliverable is bug-compatibility, not correctness.** That is the crux of the
   difficulty assessment, and it is what agents are worst at (§9).
5. **The residual top risk is collection iteration-order determinism** (§6.1), not parsing.
   It is *smaller than it first appears* — K has an explicit `Ordering[Sentence]` — but it
   needs a real investigation, not an assumption.

---

## 2. Inventory (measured)

### 2.1 `k-frontend`

```
39,589  LOC Java   (252 files)
 4,522  LOC Scala  ( 28 files)
 1,269  lines JavaCC/JJTree grammars
-------
~44,000 LOC total
```

By subsystem:

| Lines | Files | Path | Notes |
|---|---|---|---|
| 11,886 | 68 | `java/…/compile/` | ~60 passes + ~20 `checks/`. The bulk; the parallel fan-out target. |
| 9,015 | 38 | `java/…/parser/` | outer (JavaCC) + Earley + disambiguation |
| 3,676 | 45 | `java/…/utils/` | errors, files, options, Guice DI |
| 3,052 | 8 | `java/…/kompile/` | pipeline driver |
| 2,926 | 3 | `java/…/backend/kore/` | `ModuleToKORE.java` is 2,353 of these |
| 1,599 | 9 | `java/…/lsp/` | LSP server — probably out of scope |
| 1,577 | 5 | `scala/…/definition/` | **`outer.scala` (1,054) is the risk epicentre — see §6.1** |
| 1,445 | 22 | `java/…/kil/` | legacy AST — **[unverified: is this still live?]** |
| 839 | 8 | `scala/…/kore/` | K AST |
| 567 | 7 | `java/…/definition/` | includes `regex/` (475) — see §6.4 |

Largest individual files:

```
2353  backend/kore/ModuleToKORE.java              ← the output artifact generator
1135  parser/inner/kernel/EarleyParser.java
1072  parser/inner/disambiguation/TypeInferencer.java     ← Z3-backed
1054  scala/definition/outer.scala                ← Module: 77 lazy vals. §6.1
 954  compile/SortCells.java
 871  compile/GenerateSentencesFromConfigDecl.java
 823  parser/inner/RuleGrammarGenerator.java
 823  javacc/Outer.jj                             ← outer syntax grammar
 818  compile/ConstantFolding.java                ← MPFR floats. §6.3
 637  parser/inner/kernel/KSyntax2Bison.java      ← parser/scanner codegen
 591  parser/inner/disambiguation/inference/SortInferencer.java  ← newer, non-Z3
 532  compile/AddSortInjections.java
 523  parser/inner/kernel/Scanner.java            ← generates flex, shells out to cc
 493  unparser/ToJson.java                        ← KAST JSON out (format version 4)
 474  parser/json/JsonParser.java                 ← KAST JSON in
 295  compile/checks/CheckRegex.java
 211  definition/regex/RegexSyntax.java           ← 3 printers: K, Flex, …
 208  javacc/KastParser.jj                        ← KAST text in
 191  jjtree/TagSelector.jjt                      ← Markdown fence selector language
```

### 2.2 `scala-kore` — the KORE parser (external, 2,545 LOC total)

```
881  src/main/scala/.../parser/TextToKore.scala   recursive descent, LL(1), no backtracking
722  src/main/scala/.../interface.scala           abstract AST (traits + Builders factory)
273  src/main/scala/.../Default.scala             concrete AST impl
176  src/main/scala/.../parser/Scanner.scala      hand-written, line-based, 1-char pushback
136  src/main/java/.../utils/StringUtil.java      KORE string escape/unescape — §6.2
112  src/main/java/com/davekoelle/AlphanumComparator.java
--- tests ---
176  src/test/.../InterfaceTest.scala
 69  src/test/.../parser/TextToKoreTest.scala     ← essentially no coverage
```

`Scanner.scala` has no flex, no regex, no external tooling — just
`next()`/`putback()`/`skipWhitespaces()`/`skipComments()`. `TextToKore` is LL(1) recursive
descent over it with `consume(str)` for keywords and single-char lookahead. No backtracking,
no ambiguity, no error recovery. This is about as directly transcribable as a parser gets,
and it is WASM-clean by construction (the only I/O is `io.Source`, which becomes `&str`).

The `k` frontend contains only the thin adapter: `parser/KoreParser.java` (46 lines) →
`scala/…/parser/kore/parser/KoreToK.scala` (180).

### 2.3 External process dependencies — **all in the `kompile` path**

```
parser/inner/disambiguation/TypeInferencer.java  →  ProcessBuilder("z3", "-in")
parser/inner/kernel/Scanner.java                 →  flex, then cc, then run the binary
parser/KRead.java, kompile/Kompile.java          →  llvm-kompile / haskell backend tooling
```

None are in the library layer. This is the entire reason the WASM scoping decision matters.

### 2.4 Maven dependencies → porting implications

| Dep | Used by | Class | Notes |
|---|---|---|---|
| `mpfr_java` | `FloatBuiltin.java`, `ConstantFolding.java` | **semantic** | §6.3. `rug` binds the same C MPFR natively. |
| `dk.brics.automaton` | `scala/definition/outer.scala:1034` (`RegexTerminal.pattern`) | **semantic** | §6.4. Regex→DFA matcher. |
| `flexmark-all` | literate-K Markdown extraction | **semantic** | §6.5. Disagrees with `pulldown-cmark` on malformed fences. |
| `com.davekoelle` (vendored) | both repos | **semantic** | §6.6. Natural-sort ordering. |
| `jung-api`, `jung-graph-impl` | `compile/ComputeTransitiveFunctionDependencies.java` only (108 lines) | trivial | Just graph reachability. Replace with a hand-rolled DFS. |
| `pcollections`, `guava`, `commons-*` | pervasive | trivial | Standard collections/utils. |
| `guice`, `guice-multibindings`, … | pervasive DI | **structural** | Does *not* port. See note below. |
| `jcommander` | CLI options | structural | → `clap`. |
| `org.eclipse.lsp4j` | `lsp/` | structural | Only if LSP is in scope → `tower-lsp`. |
| `nailgun-server`, `ng` | `kserver/` | structural | Only if `kserver` is in scope. |
| `jline`, `jansi` | terminal I/O | trivial | → `rustyline`/`anstyle`. |
| `javax.json` | KAST JSON | trivial | → `serde_json`. |

**On Guice:** dependency injection is a pervasive structural pattern here, and it does not
translate. In Rust you pass structs. This means `utils/` and the frontend drivers are a
*rewrite of the wiring*, not a translation — less mechanical than the pass layer, and a place
where an agent will produce something that works but looks nothing like the original. That is
fine, but it breaks line-by-line reviewability, so plan to review those by behaviour instead.

### 2.5 Test surface available as oracles

```
229    test dirs in k-distribution/tests/regression-new
1,191  .out golden files in that suite
213    test dirs in pyk/regression-new (113 skipped, per k/CLAUDE.md)
2,035  .k files in the k repo
32     Java/Scala unit test files in k-frontend (5,933 lines)
245    lines of test in all of scala-kore
0      .kore golden files anywhere in the test suite
```

Note the last two lines. There is **no existing golden-file suite for `definition.kore`**, and
`scala-kore` is effectively untested. Building both corpora is a prerequisite, not a
nice-to-have (§5.1, §10).

---

## 3. Architecture: one crate, explicit portability boundaries

```
crates/k-rust/
├── src/lib.rs
├── src/kore/          WASM-compatible   lexer, parser, printer, AST, binary KORE
├── src/kast/          WASM-compatible   KAST terms, text/JSON, KORE conversion
├── src/definition/    WASM-compatible   definitions, JSON, resolved import graphs
├── src/kompile/       native-only       passes, checks, Earley, ModuleToKORE (planned)
└── src/bin/k-rust.rs  native-only       command-line frontend (planned)
```

Start with one Cargo package. The module boundaries preserve the option to extract crates later
if compile times, dependency boundaries, or independent releases justify it. Splitting packages
before those pressures exist would add coordination overhead without improving correctness.

Two properties make this the right internal cut:

- **The dependency order is favourable.** The shared data model — which everything else
  blocks on — remains in the portable portion of the crate. The small, independently useful
  KORE and KAST APIs are built first and become prerequisites for the native frontend.
- **The most-used code becomes the most-tested code**, because the native `kompile` module
  exercises the portable modules on every run.

**Enforce the boundary mechanically.** CI builds `k-rust` for `wasm32-unknown-unknown`.
Native-only modules and the CLI must be target-gated when they arrive. It is very easy for an
agent to reach for `std::fs` or `std::process` in portable definition code — source-location
handling and `requires` path resolution both tempt it — and silently cost the project its WASM
target. Make it a build failure, not a code-review convention.

---

## 4. Work decomposition

### Phase 0 — de-risking spikes (serial, human-supervised)
Run these *before* committing. Any of them could invalidate the plan.

- **S0. JSON round-trip integrity.** Verify Java → `--emit-json` → Java reproduces an
  identical `definition.kore`. **If this fails, the strangler-fig strategy in §5.1 does not
  work and the whole plan needs rethinking.** Cheapest high-information experiment available.
  Do it first.
- **S1. `StringUtil` differential.** Exhaustive test over all codepoints `0..=0x10FFFF` plus
  malformed-escape cases, Rust vs. Java, cross-checked against the other four implementations.
  136 lines — small enough to be *exhaustively* testable, a rare luxury. Take it. §6.2.
- **S2. `Module` determinism.** Trace which of `outer.scala`'s 77 lazy vals actually feed
  `ModuleToKORE` output, and whether the unsorted (`immutable.Set`) ones ever do. §6.1.

### Phase 1 — `k_rust::kore` (small, high confidence)
~1.5k LOC. Four reference implementations to cross-check (§7). Ship standalone as WASM.

It *shrinks* in the port: `interface.scala` (722) + `Default.scala` (273) are ~1000 lines of
abstract-trait + Builders-factory indirection existing so the K frontend can construct its own
AST. A standalone Rust lib collapses that to a plain `enum Pattern { … }` of maybe 150 lines.

Separable sub-deliverables:
- KORE text lexer + parser + AST — context-free and pure
- KORE printer — needs `StringUtil`, needs `AlphanumComparator` for any sorted output
- KORE binary format — spec at `llvm-backend/.../docs/binary-kore{,-2}.md`
- KORE → KAST conversion (`KoreToK.scala`, 180 lines) — the context-free conversion and
  injectable sort-hook map are implemented; populating that map from compiled definitions
  depends on `k_rust::definition`

### Phase 2 — `k_rust::kast` + `k_rust::definition` (serial prefix, needs human design review)
The inner KAST term model, flat definition model, their text/JSON formats, deterministic
import-graph resolution, and Scala-compatible sentence ordering are implemented. Next are
specialized parser/layout views and the remaining frontend validation checks. Production, sort,
and rule catalogs plus subsort, overload, and syntax-priority partial orders are implemented,
including Scala's distinct explicit-group and legacy same-label overload mechanisms and exact
associativity tag pairs. The dependency-light structural checks now include label, syntax-group,
associativity, sort-top, token, K term, rewrite, anonymous-variable, RHS-variable, function-LHS,
strictness, stream-cell, and configuration-cell validation backed by reusable position-aware KAST
traversal. This remains a reviewed design boundary because every downstream pass inherits its
bugs — especially its iteration order.

### Phase 3 — massively parallel fan-out (~14k LOC, the bulk)
The ~60 compile passes and ~20 checks. Each is `Module → Module`, pure, independently
harnessable via JSON in/out against the Java pass. Close to ideal agent work: one agent per
pass, mechanical oracle, no cross-talk. Only four are chunky: `SortCells` (954),
`GenerateSentencesFromConfigDecl` (871), `ConstantFolding` (818), `AddSortInjections` (532).

### Phase 3b — `ModuleToKORE` (parallel, do early, high value)
2,353 LOC. Pure `Module → text`, byte-exact oracle, and it is what gives you the end-to-end
acceptance criterion. Testable from Java's `compiled.json` before any pass is ported.

### Phase 4 — serial and genuinely hard (~4k LOC, majority of the cost)
Scanner, Earley kernel, disambiguation stack, sort inference. Coupled to each other, weakest
oracles, and where the remaining judgement calls live.

**Scanner shortcut worth taking:** keep the flex codegen approach. `Scanner.java` and
`KSyntax2Bison.java` *generate* a `.l` file, shell out to `flex` + `cc`, and run the binary.
Port the string-generation, not the lexing, and you inherit byte-identical tokenisation for
free. Only revisit this if `kompile` ever needs to be WASM.

---

## 5. Testability — the part that determines success

### 5.1 The strangler-fig strategy

The single most important architectural finding:

`ToJson.apply` / `JsonParser.parseDefinition` **already serialise the full definition at two
pipeline points** — `parsed.json` and `compiled.json`, behind `--emit-json`
(`Kompile.java:231-236`). So you can run a hybrid pipeline:

```
Java parses  →  JSON  →  Rust runs passes k..m  →  JSON  →  Java finishes  →  definition.kore
```

Every individual pass gets a real differential harness against the real corpus on day one, and
the port lands incrementally instead of needing 100% before anything is testable.
**Do not attempt a big-bang rewrite.** (Contingent on spike S0.)

### 5.2 Acceptance criteria differ by layer

This distinction matters and is easy to conflate:

| Layer | Criterion |
|---|---|
| Portable `k_rust::kore` and `k_rust::kast` APIs | parse-correctness + *semantic* equality. Byte-identical output not required. |
| KAST JSON specifically | **schema-exact.** `ToJson.java:56` declares `version = 4`; pyk's `kast/outer.py` (1,679) + `inner.py` (972) + `_ast_to_kast.py` are the de-facto consumer spec. Anything pyk can read, you must produce. |
| Native `k_rust::kompile` pipeline end to end | **byte-identical `definition.kore`**, over large external semantics. |

### 5.3 Oracles, ranked by strength

1. **Roundtrip property tests — no reference implementation needed.** Random KORE/KAST AST →
   print → reparse → compare. Same for text ↔ JSON ↔ binary. The only self-contained oracle in
   the project; finds real bugs with zero Java in the loop. Fuzz it.
   - ⚠️ Direction matters: for KORE strings `unquote ∘ enquote = id`, but `enquote ∘ unquote`
     is *canonicalisation*, not identity (§6.2 trap 4). Getting this backwards gives a test
     that fails for the wrong reason.
2. **Three-way vote across existing implementations** (§7). Divergence between Java/Scala,
   Python, and your Rust is a majority vote, not a coin flip. Where the *existing*
   implementations disagree with each other, you have found a real ecosystem bug and need a
   human decision.
3. **Byte-identical `definition.kore`** over `evm-semantics` / `wasm-semantics`. **This is the
   real acceptance test and it is not in this repo.** The 229 in-repo regression dirs are
   necessary but nowhere near sufficient.
4. **The 1,191 `.out` golden files** — catch gross regressions; weak on the hard paths.

### 5.4 Where differential testing quietly lies to you

- **Iteration order.** 69 files in `k-frontend` use raw `HashMap`/`HashSet`, plus Scala
  immutable collections. Java's hash order is arbitrary-but-stable-per-JVM; Rust's is
  randomised per process. You will get flaky diffs where real bugs and ordering flake are
  indistinguishable. Budget for canonicalising both sides *and* for the cases where order is
  load-bearing.
- **Error and warning text.** ~20 `Check*` passes exist *only* to emit diagnostics. There is
  no IR for these — the output is human-readable text with source locations. **Decide up front
  whether byte-exact diagnostics are in scope; if yes it roughly doubles the work.**
- **Ambiguity coverage.** Disambiguation is order-sensitive, and its correctness is only
  observable on genuinely ambiguous grammars. Real semantics are written to *avoid* ambiguity,
  so the corpus systematically under-covers precisely the hardest code. Needs generated
  adversarial grammars.
- **Malformed input.** Several paths throw Java runtime exceptions
  (`StringIndexOutOfBoundsException`) rather than structured errors. Rust will panic or return
  `Err`. Divergence on malformed input is guaranteed unless explicitly specified.
- **Java-isms with observable behaviour.** `String.format` is locale-sensitive in general
  (though `%02x` hex is not); `BigInteger` semantics; custom comparators. Audit rather than
  assume.

### 5.5 You will have to instrument the Java reference

Not all oracles exist yet. `--emit-json` gives you the pass boundary, but the scanner oracle
(token streams) and per-pass intermediate state for anything not covered by JSON require
*patching the Java frontend to emit them*. Budget for maintaining that instrumentation fork
for the life of the project, and for rebasing it as upstream moves.

Build/lint commands for the reference implementation (from `k/CLAUDE.md`):

```
mvn package -DskipTests          # compile the Java toolchain (Java 17 + Scala 2.13)
mvn spotless:apply               # required before any commit to the Java side
mvn verify                       # Java unit tests
make -C k-distribution/tests/regression-new              # Java regression suite
make -C k-distribution/tests/regression-new update-results   # regenerate .out baselines
make -C pyk check                # Python lint
make -C pyk test-unit            # fast Python tests, no K toolchain needed
```

---

## 6. Risk register (ranked)

### 6.1 `Module` iteration-order determinism — **top risk, but smaller than it looks**

`scala/definition/outer.scala` is 1,054 lines and is essentially one `Module` class carrying
**77 `lazy val`s** (7 `@transient`) forming a memoised derived-view graph: `sentences`,
`productions`, `productionsFor`, `productionsForSort`, `importedModules`, `definedKLabels`,
`tokenSorts`, `rulesFor`, `sortSynonymMap`, … Most are `immutable.Set`, which is unordered.
That ordering leaks into `ModuleToKORE` output. In Rust this becomes an
interning/arena/memoisation design problem.

**The good news, found by inspection:** there is an explicit `implicit val ord: Ordering[Sentence]`
at `outer.scala:581`, dispatching case-by-case to per-sentence-type orderings, and the class
provides deliberately *sorted* views — `sortedLocalSentences` (176), `sortedProductions` (215),
`sortedRules` (346) — alongside the unsorted ones. The codebase clearly knows Set order is
unreliable and uses sorted views where order matters. So the canonical ordering is
**specified in code**, not accidental, and can be ported faithfully.

**The actual investigation task (spike S2)** is therefore narrow: trace which lazy vals feed
`ModuleToKORE`'s output, confirm the sorted views are used consistently on those paths, and
identify any unsorted `Set` that reaches output. That is a bounded question with a definite
answer, not open-ended risk.

**Also note:** `outer.scala:49` is the one parallel site in the frontend —
`.par.map(f).seq.map(m => m.name -> m).toMap`. The result is a name-keyed Map so ordering is
not observable *there*, but confirm `f` is side-effect-free. **[unverified]** Otherwise the
frontend is single-threaded (`CompletableFuture` appears only in `lsp/`), which removes a
determinism concern that would otherwise be significant.

### 6.2 `StringUtil` — small, untested, and the entire byte-exactness surface
136 lines, zero tests. Four traps found by reading it:

1. **`\xNN` is a codepoint escape, not a byte escape.**
   `sb.append((char) Integer.parseInt(arg, 16))` — `\xff` means U+00FF, not byte `0xFF`.
   Rust's own `\x` and `escape_default` mean the opposite. A natural Rust implementation gets
   this wrong and it only surfaces on non-ASCII data. **Cross-check whether the
   C++/Haskell/Python parsers agree with Java here** — a plausible site of real ecosystem-wide
   divergence.
2. **Unknown escapes silently drop the backslash.** The if-chain has no `else`; if the char
   after `\` is not one of `" \ n r t f x u U`, nothing is appended and `i` advances by one.
   So `"\q"` unquotes to `q`, with no error.
3. **No bounds checks.** `str.substring(i+2, i+4)` on a truncated `"\x` throws
   `StringIndexOutOfBoundsException`, not a `ParseError`.
4. **`enquote ∘ unquote` is canonicalisation, not identity.** `ÿ` and `\xff` unquote to
   the same string; `enquote` only ever emits `\xff`.

Good news: `throwIfSurrogatePair` rejects `D800..DFFF` and `>= 0x110000`, and `enquote` escapes
everything outside 32..126. All output is pure ASCII and all escaped input is a valid Unicode
scalar value — **no UTF-16/UTF-8 impedance mismatch.** The concern one would flag blind turns
out not to apply.

Recommendation: hand-write and hand-review this file. Do not delegate it.

### 6.3 Floats / MPFR — silent numeric divergence
Contained to `compile/FloatBuiltin.java` (191) and `compile/ConstantFolding.java` (818), via
`mpfr_java`. Natively you can bind the same C MPFR through `rug`/`gmp-mpfr-sys` and get exact
agreement by construction — **do that.** If anyone is tempted to substitute a pure-Rust
arbitrary-precision float library for WASM reasons, the failure mode is silent divergence in
rounding mode, precision handling, NaN payloads, and signed zero — none of which the regression
corpus is likely to catch. This is the strongest argument for keeping `kompile` native.

### 6.4 Regex — K has its own AST; brics is one backend
Better-scoped than it first appears. K defines its own regex AST in `definition/regex/`
(475 lines: `Regex`, `RegexBody`, `RegexSyntax` 211, `RegexTransformer`, `RegexVisitor`), and
`RegexSyntax` provides multiple printers — `RegexSyntax.K` and `RegexSyntax.Flex` (the latter
feeds the scanner codegen). `dk.brics.automaton` appears only at `outer.scala:1034`:

```scala
lazy val pattern = new RunAutomaton(new RegExp(RegexSyntax.K.print(regex)).toAutomaton, false)
```

So brics is purely a *matcher* for the K-syntax rendering. A Rust port needs a matcher with
brics-compatible semantics for whatever `RegexSyntax.K.print` emits — a real but well-scoped
and identifiable compatibility surface. `compile/checks/CheckRegex.java` (295) is the validator.

### 6.5 Markdown / literate K
`flexmark-all` parses `.md` files with fenced K blocks, plus `jjtree/TagSelector.jjt` — a whole
selector mini-language (191 lines). `pulldown-cmark` disagrees with flexmark on malformed
fences. With the `kompile` module native-only there is no WASM constraint, so porting flexmark's
fenced-block handling directly is an option. pyk's `kast/markdown.py` (226) is a second
reference.

### 6.6 `AlphanumComparator` duplication
Natural-sort ordering, present in **both** `k-frontend` and `scala-kore` (`com.davekoelle`,
112 lines). Port once, share between modules, test against a generated string corpus.
Comparator bugs are order-dependent and will not reproduce reliably from a diff.

### 6.7 Earley + disambiguation
Order-sensitive; corpus under-covers it (§5.4). Unchanged by the WASM scoping decision.

### 6.8 Diagnostic fidelity
Large, tedious, non-parallelisable-by-inspection surface. Needs a scope decision (§8).

### 6.9 Sort inference — *deferred, not solved*
`ParseInModule.java:417` gates on `SortInferencer.isSupported(...)` (newer,
Hindley-Milner-ish, 591 LOC) and falls back to the Z3-backed `TypeInferencer` (1,072 LOC).
With native `kompile` you keep shelling out to Z3, so this is a straight port rather than a
design decision. **But measure what fraction of the corpus takes each path** — if the Z3
fallback is common it constrains any future attempt to make `kompile` WASM-capable, and it
makes output dependent on Z3's model choice across solver versions.

---

## 7. Reference implementations (five KORE parsers exist)

| Impl | Location | Size | Use as |
|---|---|---|---|
| **Python (pyk)** | `k/pyk/src/pyk/kore/` — `lexer.py` 256, `parser.py` 538, `syntax.py` 2273 | ~3k | **primary reference** — readable, tested (`pyk/src/tests/unit/kore/`) |
| **Scala** | `scala-kore` (external artifact used by the Java frontend) | 2.5k | authority on what K actually does today |
| **C++** | `k/llvm-backend/.../lib/parser/` — `KOREParser.cpp` 457, `KOREScanner.l` 191 (flex) | ~890 | lexical edge cases |
| **Haskell** | `k/haskell-backend/.../kore/src/Kore/Parser/` — `Lexer.x` + `Parser.y` (alex/happy) | ~440 + gen | grammar cross-check |
| **Haskell (Booster)** | `k/haskell-backend/.../booster/library/Booster/Syntax/ParsedKore/` | — | second Haskell datapoint |

For **KAST** rather than KORE, pyk has an independent pure-Python implementation —
`kast/outer_lexer.py` (959), `outer_parser.py` (418), `markdown.py` (226), `lexer.py` (265),
plus `outer.py` (1,679) and `inner.py` (972) as the JSON schema consumer. Free second
reference implementation *and* a free set of already-discovered edge cases.

### Specs
- `k/haskell-backend/src/main/native/haskell-backend/docs/kore-syntax.md` — normative KORE syntax
- `k/haskell-backend/.../docs/kore-implicits.md`
- `k/llvm-backend/.../docs/binary-kore.md`, `binary-kore-2.md` — binary format
- `ToJson.java:56` — KAST JSON `version = 4`

---

## 8. Open questions requiring a human decision

1. **Is byte-exact diagnostic text in scope?** Roughly doubles the work if yes.
2. **Which drivers are in scope?** `kompile` certainly; what about `kprove` (has its own
   `--emit-json` / `--emit-json-spec`), `kast`, `krun`, `kdep`, `ksearchpattern`, the LSP
   server (1,599 LOC), `kserver`/nailgun?
3. **Is `kil/` (1,445 LOC) still live, or dead legacy?** **[unverified]**
4. **Where do the five existing KORE implementations disagree?** Any divergence found is an
   ecosystem bug and someone must decide which behaviour is normative.
5. **Which external semantics form the acceptance corpus?** `evm-semantics` and
   `wasm-semantics` are the obvious candidates; neither is in this workspace, and both need
   vendoring and version pinning.
6. **Fork or upstream contribution?** Determines whether bug-compatibility is the permanent
   contract or a transitional one.
7. **Does `f` at `outer.scala:49` have side effects?** Small, but it gates whether the port can
   assume a single-threaded model. **[unverified]**

---

## 9. Difficulty assessment (the answer to the original question)

**The portable library modules (`k_rust::kore`, `k_rust::kast`):** low difficulty, high
achievable confidence.
~3k LOC of Rust, mechanically derivable from a hand-written recursive-descent parser, four
independent reference implementations, unlimited corpus, and a self-contained roundtrip oracle.
An agent can do most of this nearly unsupervised. The exception is `StringUtil`.

**The `kompile` pipeline:** the difficulty is *not* writing 35k lines of Rust — agents are good
at that, and the pass layer is nearly ideal for fan-out. The difficulty is that the deliverable
is **bug-compatibility, not correctness**, and the long tail of divergences each requires
understanding *why* the Java does something odd.

That is precisely what agents are weakest at: they fix a diff by special-casing rather than by
finding the invariant, and special-cases compound. The mitigation is structural — per-pass
differential harnesses via the JSON boundary (§5.1), so a divergence is localised to one pass
instead of surfacing 40 passes downstream as a mangled `.kore` file.

**Overall shape:** one small high-confidence library project, plus one large tedious port whose
remaining risk is concentrated in collection-ordering determinism — and that risk is bounded by
the fact that K already specifies its canonical ordering in code.

---

## 10. Suggested next actions

- [ ] **Spike S0 — JSON round-trip integrity.** Cheapest, highest-information, and it gates
      the entire incremental strategy. Do it first.
- [ ] **Spike S1 — `StringUtil` exhaustive differential.** Self-contained, and immediately
      tells you whether the five existing implementations agree with each other.
- [ ] **Spike S2 — `Module` determinism trace.** Which of the 77 lazy vals reach output, and
      are the sorted views used consistently on those paths?
- [ ] Build the `definition.kore` golden corpus that does not currently exist: kompile
      `evm-semantics` / `wasm-semantics` / the 229 in-repo tests, archive outputs, pin the
      toolchain version.
- [ ] Stand up the Java instrumentation fork (§5.5) and decide how it will be maintained.
- [ ] Measure the `SortInferencer` vs `TypeInferencer` (Z3) split across the corpus (§6.9).
- [ ] Answer the scope questions in §8.
