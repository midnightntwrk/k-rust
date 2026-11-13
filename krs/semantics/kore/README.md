# KORE in K

`kore.k` is a K definition whose configuration holds an encoded KORE object definition and an encoded initial term, and whose rules compute every configuration reachable from that term to which no rule of the object definition applies: the final configurations that `krun --search` returns.
Its job is to be mutated.
Each mutant of `kore.k` is a wrong reading of KORE, and a set of cases that kills the mutants is a set of small object definitions that tell those readings apart.
The cases are an external test suite for any implementation of KORE's semantics.

The expected result of each case comes from the reference backends run on the object definition itself, never from `kore.k`; `kore.k`'s result is only checked against it.

`kore.k` is written in K, not KRS; [Why K and not KRS](#why-k-and-not-krs) gives the reason and what a KRS port takes.

## The reading of KORE

`kore.k`'s header states the reading it implements; in short:

- a function application is evaluated innermost: arguments first; an undefined argument (`\bottom`) makes the application undefined; a constructor application is a value;
- an equation applies when its argument patterns match and its `requires` evaluates to `true`; among the applicable equations one of the least priority gives the result (`[owise]` is priority 200, no attribute is 50); an application no equation applies to stays as it is;
- a rewrite rule applies when its left side matches and its `requires` evaluates to `true`; the successors are the defined results of the applicable rules of the least priority; a rule whose result is undefined still blocks the rules of larger priority;
- a configuration is final when no rule applies to it; one to which rules apply, all with undefined results, has no successor and is not final;
- matching is syntactic up to injections: `inj{A,B}(P)` matches `inj{C,B}(V)` when `C = A` (`P` against `V`) or `C < A` in the reflexive-transitive closure of the stated subsorts (`P` against `inj{C,A}(V)`); a variable seen twice must be bound to equal values; an as-pattern `\and(P, V)` matches what `P` matches and binds `V` to it; `inj{A,B}(inj{C,A}(V))` is `inj{C,B}(V)`;
- hooks are strict: an undefined operand makes the operation undefined; `/Int` and `%Int` are undefined on a zero divisor;
- a `Map` is a finite map, a `Set` a finite set, a `List` a finite sequence, and a value of each is canonical (a map's entries ordered by key, a set's elements by value, no key or element twice), so that equal collections are equal terms; `_Map_` and `_Set_` are partial, defined on disjoint maps (sets) and undefined where keys (elements) overlap; `_List_` is total, associative and not commutative; a lookup of a missing key is undefined; a collection is strict in its elements;
- a collection pattern of element patterns and at most one frame variable matches every split of its subject: for `Map` and `Set` each element pattern takes any element, for `List` the element at its position, and the frame the rest; matching gives a set of substitutions, a rewrite rule gives one result for each substitution whose `requires` holds, and an equation the result of the first such substitution (on a consistent definition every such substitution gives the same result).

### The fragment

Covered: sorts, subsorts and injections, constructors, as-patterns, non-linear left sides, function equations with priorities, `requires` and `[owise]`, rewrite rules with priorities, `requires` and `[owise]`, the hooks `+Int -Int *Int /Int %Int <Int <=Int >Int >=Int ==Int =/=Int andBool orBool notBool #if_#then_#else_#fi`, and undefinedness propagating strictly.
Collections: the sorts `Map`, `Set` and `List` with their concatenation, unit and element symbols (in terms and in patterns, with a frame variable), and the hooks `Map:lookup`, `Map:lookupOrDefault`, `Map:update`, `_[_<-undef]`, `_in_keys(_)`, `size(Map)`, `Set:in`, `size(Set)`, `|Set` and `size(List)`.

Not covered: the other collection hooks (`keys`, `values`, `choice`, `-Map`, `-Set`, `intersectSet`, `List:get`, `List:set`, `range` and the rest); a `Map` or `Set` pattern with more than one frame; cell collections (cells of multiplicity `*`) and their generated map sorts; any hook outside the lists above; `ensures`; configurations of more than one cell (an object definition has the one cell `<k> $PGM:S </k>`); symbolic terms (an initial term is ground); conditions on results; projections such as `{M[K]}:>Int`, whose equations kompile writes in K's own modules (a case keeps a lookup's result in `KItem`).
The encoder stops with an error naming the construct when it meets one outside the fragment that it recognizes: a hook outside the list, a domain value of another sort, a matching-logic connective in a term, an `ensures`, a configuration of another shape, a `Map` or `Set` pattern with two frames.

## Layout

| Path | Content |
| --- | --- |
| `kore.k` | The interpreter: module `KORE`, syntax module `KORE-SYNTAX`; 480 lines, 220 rules and equations (11 rewrite rules for the search, the rest equations of 65 functions). |
| `tools/korek.py` | The KORE text reader; the encoder of kompile's `definition.kore` and the initial term's KORE into a program of `kore.k`; the decoders of `krun --search`'s and `kore.k`'s results into one canonical text. |
| `tools/case.py` | Builds a case's encoded program and its reference expected result (needs K). |
| `tools/check.py` | Runs `kore.k` on every case and compares its result with each backend's recorded result (needs only `krust`). |
| `differences.toml` | Each difference of `kore.k`'s result from a backend's recorded result, by case and backend, with its reason. |
| `cases/<id>/` | One case, below. |
| `FLOW.toml`, `MUTATIONS.toml` | The kink corpus: every case's `kore.pgm`, the argued coverage obligations, and the 53 mutations of `kore.k`. |
| `kink.lock` | kink-flow's verdict record of the corpus: each mutation's status and recorded killer, and the coverage verdicts. |
| `kill-matrix.json` | For each mutation, its status, every case that kills it and the cases on which its run gave no comparable result. |
| `tools/killmatrix.py` | Reduces `kink-flow run --full`'s JSON document to `kill-matrix.json`. |

### A case

| File | Content |
| --- | --- |
| `def.k` | The object definition: module `CASE`, syntax module `CASE-SYNTAX`, `configuration <k> $PGM:S </k>`, rewrite rules on the closed cell (`<k> L => R </k>`). Its first comment says what the case tests. |
| `pgm` | The initial term, in `CASE-SYNTAX`. |
| `pgm.kore` | `kast pgm --output kore` against `def.k` kompiled for the haskell backend: the initial term of sort `S`. The initial configuration is `<generatedTop>(<k>(kseq(inj{S,KItem}(PGM), dotk())), <generatedCounter>(0))`. |
| `kore.pgm`, `symbols.json` | The encoded program for `kore.k` (start sort `Pgm`) and the encoder's numbering of symbols and sorts; for a case with collections, `collections` names each collection sort's kind and its concatenation, unit and element symbols. |
| `expected.json` | The reference result. For each backend (`haskell`, and `llvm` kompiled with `--enable-search`), `finals`: the item `inj{S,KItem}(X)` the `<k>` cell holds in each final configuration of `krun --search`, as canonical text (`Lbl…(args)`, integers, `true`/`false`, `inj{SortA,SortB}(v)`; a collection as `SortMap{k|->v,…}` and `SortSet{x,…}` with its elements' texts sorted, `SortList[x,…]` in order, whatever order a backend prints them in; a result under a condition carries ` if defined(…)`), sorted; or `error`, the backend's failure without its temporary paths. `reference` names the K release and backend that produced each; `backends_agree`; `inputs`, the SHA-256 of `def.k` and `pgm` the results were computed from. |

The kompiled object definition is not committed.
`kompile` writes the absolute path of `def.k` and of K's own installation into the `Source` attributes of `definition.kore`, and a case's `definition.kore` is about 250 KB, almost all of it K's builtin modules.
`def.k` and `pgm` are the sources; `tools/case.py` rebuilds the kompiled text in its build directory, and the encoder selects the object definition's axioms by that build's `Source` path.
What a harness needs without K is committed: `pgm.kore` (which names no path), `kore.pgm`, `symbols.json` and `expected.json`.
A harness that reads KORE definitions kompiles `def.k` itself, as `tools/case.py` does.

## Building a case

From this directory, with the pinned K toolchain (`k/result/bin` at the repository root):

```sh
export K_KOMPILE=$PWD/../../../k/result/bin/kompile
python3 tools/case.py --all              # every case
python3 tools/case.py cases/<id>         # one case
python3 tools/case.py --refresh --all    # also recompute expected.json whose inputs did not change
```

A new case is a directory `cases/<id>/` with `def.k` and `pgm`; `tools/case.py cases/<id>` writes the rest.
The reference runs are cached in `expected.json` by the SHA-256 of `def.k` and `pgm`; with unchanged inputs only the haskell kompile (for the encoder) and `kast` run again.
A case costs about 15 to 80 s of reference runs (two kompiles, two searches; an llvm search that fails takes up to a minute), each under a 120 s timeout and a 12 GiB memory scope.
Keep the object search finite: on a cycle the haskell backend's search does not stop, and only the timeout ends it.

## Cases

33 cases, each a small object definition for one point of the reading above.
"haskell" is the number of final configurations of the haskell backend's search; "llvm" is the llvm backend's result against it.

| case | what it tests | haskell | llvm |
| --- | --- | --- | --- |
| c01-fn-prio | equations of three priorities, an `[owise]` equation, failing `requires` | 1 | same |
| c02-rule-prio | rules of several priorities: a rule whose `requires` fails does not block a larger priority | 1 | same |
| c03-nondet | rules of one priority give several successors; paths meet again and end in several final configurations | 4 | same |
| c04-subsort | the subsort chain `Int < Num < Val < Exp` and `Bool < Val`: matching through the transitive closure | 1 | same |
| c05-hooks | the Int and Bool hooks of the fragment, on negative operands too | 1 | same |
| c06-nonlinear | a variable seen twice in an equation's and a rule's left side | 1 | same |
| c07-strict-args | a function's argument is evaluated before its equations are matched | 1 | same |
| c08-undef-rhs-blocks | a rule that applies with an undefined right side has no successor and blocks a larger priority | 0 | error |
| c09-undef-requires | an undefined `requires` is not true: the rule does not apply | 1 | error |
| c10-strict-ite | `#if` is strict in its three arguments: an undefined branch makes it undefined | 0 | 1 final |
| c11-fn-no-equation | an application of a partial function that no equation applies to | 1 | error |
| c12-undef-init | an undefined initial term has no final configuration | 0 | error |
| c13-inj-bool | composed injections of a function's result; an undefined result under an injection; Bool literals and a Bool-sorted pattern against injected values | 3 | error |
| c14-fn-undef-requires | an equation whose `requires` is undefined does not apply; the `[owise]` one does | 1 | error |
| c15-nonlinear-rule | a variable seen twice in a rule's left side does not match distinct values | 1 | same |
| c16-bool-pattern | a Bool domain value in a left side matches only itself | 1 | same |
| c17-init-function | the initial term applies a function, evaluated before the first step | 1 | same |
| c18-div-signs | `/Int` truncates toward zero and `%Int` takes the sign of the dividend | 1 | same |
| c19-map-choice | `K \|-> V M` with a frame variable matches every entry: one successor per entry, the rest bound to `M` | 3 | same |
| c20-map-key-fixed | an entry pattern with a fixed key (a domain value, a variable bound earlier), an entry chosen under a `requires`, a pattern without a frame | 5 | same |
| c21-map-concat | `_Map_` is undefined on a common key, the union on disjoint keys; `M .Map` is `M` | 2 | error |
| c22-map-hooks | `Map:lookup`, `lookupOrDefault`, update of a present and of a new key, removal, `in_keys`, `size` | 1 | same |
| c23-map-lookup-missing | a lookup of a missing key is undefined | 1 | error |
| c24-map-fn-pattern | equations whose argument pattern is `K \|-> V M`; the substitution whose `requires` holds is not the first | 1 | same |
| c25-map-equal | `A B` and `B A` are one map: a variable seen twice matches them | 1 | same |
| c26-map-strict | a map with an undefined entry is undefined | 1 | error |
| c27-set-choice | `SetItem(X) S` matches every element | 3 | same |
| c28-set-overlap | `_Set_` on a common element: undefined in `kore.k`'s reading; `\|Set` is total | 2 | 3 finals |
| c29-set-hooks | `Set:in`, `size(Set)`, `\|Set` with an element below, between, above and equal to the present ones | 1 | same |
| c30-list-positions | `ListItem(X) L` takes the first element, `L ListItem(X)` the last; a pattern without a frame matches only its length | 3 | same |
| c31-list-concat | `_List_` is associative and not commutative; an element may occur twice; `size(List)` | 3 | same |
| c32-elem-strict | a set or list with an undefined element is undefined | 1 | error |
| c33-list-middle-frame | `ListItem(X) L ListItem(Y)`: elements on both sides of a frame | error | 1 final |

Both results are kept in each `expected.json`, labelled with the K release and backend that produced them.
Both backends give final configurations on 22 cases and agree on 20 of them (all but c10 and c28); the llvm backend fails on 10 cases and the haskell backend on 1 (c33).
`kore.k`'s result equals every recorded result except the 14 that `differences.toml` lists, each with its reason:

- c08, c09, c12, c13, c14, c26, c32 (llvm): the llvm backend aborts on a division by zero (`[hook_INT_tdiv]: Division by zero`), where `X /Int 0` is undefined (`\bottom`): no successor, a `requires` that is not true, an initial configuration that is `\bottom`, a collection with an undefined element.
- c10 (llvm): the llvm backend evaluates `#if true #then 1 #else 10 /Int 0 #fi` lazily and steps to `b(1)`; the hook `KEQUAL.ite` is a function of its three arguments, so an undefined argument makes it undefined.
- c11 (haskell, llvm): `half(3)`, which no equation of the partial function `half` applies to; the haskell backend returns `b(half(3))` under the condition `\ceil(half(3))`, which `kore.k`'s results do not carry, and the llvm backend aborts (`Called finish_rewriting with no output file specified`).
- c21, c23 (llvm): the llvm backend aborts on `_Map_` of maps with a common key (`Duplicate keys in map concatenation`) and on a lookup of a missing key (`Key not found for map lookup`); K's `MAP` module states both to be `#False`, so each rule has an undefined result.
- c28 (llvm): `S SetItem(1)` where `S` holds `1`. K's `SET` module declares `_Set_` idempotent (`idem`) and documents the concatenation of sets with a common element as `#False`; `kore.k` reads it as undefined, and the haskell backend's result is the same (that rule has no successor), while the llvm backend computes the union.
- c33 (haskell): the haskell backend's search stops with `ErrorRewritesInstantiation`, its unifier finding no solution for a List pattern with elements on both sides of the frame; `kore.k` matches it by position, as the llvm backend does.

## Rerunning the cases

One command runs `kore.k` on every case and compares each result with the case's expected result; no K reference tool runs, since `expected.json` is the cached reference result.
It needs a release `krust` (the repository's `k-rust` command-line tool) built from this tree:

```sh
with-z3-static-5.3.3 cargo +stable build --release -p k-rust --no-default-features --features cli --locked
python3 tools/check.py                   # every case; or name cases: tools/check.py cases/<id> ...
```

`tools/check.py` takes `krust` from `$KRUST`, else `$CARGO_TARGET_DIR/release/krust`, else the repository's `target/release/krust`, and exits 2 when there is none.
It kompiles `kore.k` once with `krust kcompile` (cached in its build directory by the SHA-256 of `kore.k` and of `krust`), runs each case's `kore.pgm` with `krust krun --sort Pgm`, decodes the result with the case's `symbols.json`, and compares it with each backend's recorded result (a backend's error differs from every result).
A case passes when, for each backend, the two are equal and `differences.toml` lists no difference of the case from that backend, or they differ and it lists one; a case whose `def.k` or `pgm` no longer has the SHA-256 its `expected.json` records fails as stale.
It prints one line per case and a `PASS` or `FAIL` summary, and exits 0 only when every case passes.

Measured in this tree: 33 of 33 cases pass, with 14 listed differences; each `krust krun` process takes 45 to 125 ms, the whole command about 2.5 s warm and 3 s with the `kcompile` (0.4 to 0.7 s).

## The kink corpus

The corpus is a kink-flow corpus of a K definition, as `kink/examples/imp` is: `FLOW.toml` names `kore.k` and its modules, and its programs are the cases' `kore.pgm` (start sort `Pgm`).
Each mutation of `MUTATIONS.toml` is a wrong reading of KORE, stated in its `misunderstanding` and written as text edits of `kore.k`'s labelled rules.
A case kills a mutation when the mutant's result on it, every final configuration of the object definition, differs from `kore.k`'s.

Build kink-flow in a target directory of its own (the portable profile, no Z3), then run from this directory:

```sh
export CARGO_TARGET_DIR=/tmp/kore-in-k-target   # any directory of its own
cargo +stable build --release -p kink-flow --no-default-features --locked
KF=$CARGO_TARGET_DIR/release/kink-flow
$KF check FLOW.toml --mutations MUTATIONS.toml
$KF coverage FLOW.toml --lock kink.lock              # obligations of kore.k; records [coverage]
$KF run FLOW.toml MUTATIONS.toml --lock kink.lock    # survivors; records [run]
$KF run FLOW.toml MUTATIONS.toml --full | python3 tools/killmatrix.py > kill-matrix.json
$KF run FLOW.toml MUTATIONS.toml --lock kink.lock --locked   # exit 1 when kink.lock is not current
```

Run kink-flow under a memory bound, for example `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0`.
Its caches are in `.kink-flow/`, which is not committed.

### Results

Measured in this tree with kink-flow built from it (portable profile):

- Coverage: 408 obligations covered (218 of 220 rules, 146 of 147 requirements, 44 of 44 syntax productions), 3 argued, 0 open, over 33 comparable cases.
  The argued obligations are `rule:KORE.ins-dup` and its requirement `requirement:KORE.ins-dup:held` (no `insert` receives a configuration its list already holds: a configuration is inserted into `seen` only when it is not a member, and into the finals only when taken from the frontier, which holds each configuration once), and `rule:KORE.tag-other` (configurations are values; `vr`, `hk`, `as`, `cb` and `bot` never reach `cmp` under `kore.k`, and `kv` and `el` are compared only with their own kind, since a collection holds elements of one kind; the rule is kept so that a mutant that makes `bot` a configuration still compares it).
- Mutations: 53, of which 52 are killed and 1 survives as expected: `fn-last-of-priority` (`expect = "survive"`).
  Two equations of one priority that both apply with different values state that the function has two values, an inconsistent definition; on a consistent object definition the first and the last applicable equation of a priority agree, so no case kills it.
  The 15 mutations of collections are wrong readings of matching (`subst-first-only`, `fn-first-subst-only`, `frame-dropped`, `col-pattern-open`, `col-first-split-only`, `list-match-commutative`, `list-split-at-head`), of collection values (`map-duplicate-keys`, `map-concat-overrides`, `set-idempotent`, `list-as-set`, `col-unordered`) and of hooks (`map-lookup-missing-defined`, `map-update-duplicates`, `set-union-partial`).
  The 38 earlier mutations keep their verdicts (their killing cases only gain collection cases); two of them were re-anchored on the rules that now carry a list of results (`rule-rhs-unevaluated` on `fire-holds`, `undefined-result-does-not-block` on `add-some`).
- Cost: `run --full` 32 s (host load about 20); `coverage` and `run --locked` about 1 s warm.

13 cases kill some mutation that no other case kills:

| case | mutations it alone kills |
| --- | --- |
| c04-subsort | subsort-dropped, subsort-not-transitive, subsort-reversed |
| c09-undef-requires | rule-undefined-requires-holds |
| c10-strict-ite | ite-lazy |
| c11-fn-no-equation | no-equation-undefined |
| c12-undef-init | undefined-init-is-final |
| c13-inj-bool | inj-composed-outer-source, inj-not-composed, subsort-unchecked |
| c14-fn-undef-requires | fn-undefined-requires-holds |
| c16-bool-pattern | bool-dv-any-value |
| c18-div-signs | tdiv-as-ediv, tmod-as-emod |
| c21-map-concat | map-concat-overrides, map-duplicate-keys |
| c23-map-lookup-missing | map-lookup-missing-defined |
| c24-map-fn-pattern | fn-first-subst-only |
| c28-set-overlap | set-idempotent |

c07, c15 and c17, which alone killed `dv-any-value`, `fn-owise-ignored`, `nonlinear-ignored` and `init-unevaluated` among the 18 cases, now share those kills with collection cases; the other cases each kill mutations that another case also kills.

## Next: cells

The collections unit is done (above). What remains of K's configurations:

- A configuration of more than one cell. The encoder strips `<generatedTop>(<k>(…), DotVar)` to the one item of the `<k>` cell; with several cells the encoded term becomes the cell tuple (each cell a constructor application, which `kore.k` already matches), and the decoders print each cell.
- Cell collections (`multiplicity="*"`, `type="Map"`): kompile declares a generated sort such as `SortXCellMap` with its own concatenation, unit and element symbols (`_XCellMap_`, `.XCellMap`, `XCellMapItem`), keyed by the cell's first child (`XCellMapItem(<id>…</id>, <x>…</x>)`). They have the `MAP.concat`, `MAP.unit` and `MAP.element` hooks, so `kore.k` reads them as maps already; the work is in the encoder (the generated sorts, their subsorts, the cell's wrapping) and in cases whose rules match `<x> <id> K </id> … </x>` in a cell collection with a frame.
- Other collection hooks as small definitions meet them (`keys`, `values`, `-Map`, `-Set`, `List:get` with its negative indices, `range`).

## Why K and not KRS

The other packages of `krs/semantics` are KRS crates whose K is emitted by `krs`.
`kore.k` stays K source because a port is not small, although every construct it uses has a KRS spelling (constructor enums with `#[k::syntax]` templates, `k::equations!` tables with `#[k::equation(owise)]` and `#[k::equation(priority = N)]`, `k::rules!` over a one-cell configuration, `kequal` guards):

- The definition: its 16 sorts as constructor enums whose syntax templates must reproduce exactly the program syntax the committed `kore.pgm` files are written in (`pgm(def(…), …)`, `T ; Ts`, `.Ts`, `bot`); the 209 equations of 65 functions as equation tables; the 11 rewrite rules of the search in `k::rules!`.
  Each sentence is judged by KRS's checks on the assembled definition (overlapping equations, catch-all rows that need `owise`, complementary guards of rules), which `kore.k` has never been put through; whatever they refuse is a change of the definition to be argued, not a transcription.
- The corpus: `krs kink` reads a corpus in its own layout, `kink/` beside the crate's `Cargo.toml`: `kink/FLOW.toml` naming the package (`[spec] krs = { package = …, definition = … }`), the cases as program files that bind the `#[k::init]` parameter, `kink/mutations/<topic>.toml`, and a committed `kink/definition.k`.
  The emitted K has KRS's module names, rule labels and spelling of each rule, so all 53 mutations are re-anchored (each edit's `rule` and `find`), the three argued obligations renamed, and the coverage and kill numbers re-measured.
- The evidence that the port is the same definition: `krs run` of every case's `kore.pgm` gives the result `kore.k` gives, and the kill matrix is the same up to the renaming of mutations' anchors.

By the size of the existing ports (the KWasm slice is 294 lines of Rust for 16 sentences), that is on the order of a thousand lines of Rust and a re-authored mutation list, a unit of its own.
A half port, part of the definition in KRS and part in K, would leave two definitions of one reading; it is not done.

## Status

Done: the definition, with `Map`, `Set` and `List`; the encoder and the case builder; 33 cases with their reference results; the kink corpus with this tree's coverage and kill matrix; and `tools/check.py`, which reruns the cases against both backends' recorded results.

Not verified here: the reading of KORE is argued in `kore.k`'s header and checked only against the two backends on these 33 cases; no case exercises a definition outside the fragment, so the encoder's refusals are untested (it was rerun on every case, and every committed encoding is unchanged); a `Map` or `Set` value's canonical order is `cmp`'s, which the decoders replace by the order of the elements' texts, so the order itself is checked only through `kore.k`'s own equalities (c25); kink's verdicts rest on k-rust's execution of `kore.k`, which is the same engine `tools/check.py` uses.

Next: cells (above); a KRS port of `kore.k`, if wanted, as a unit of its own (above); and feeding the cases to a harness that runs other KORE implementations on `def.k` (kompiled) and `pgm.kore`, comparing with `expected.json`.
