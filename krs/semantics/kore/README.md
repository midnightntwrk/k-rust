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
- hooks are strict: an undefined operand makes the operation undefined; `/Int` and `%Int` are undefined on a zero divisor.

### The fragment

Covered: sorts, subsorts and injections, constructors, as-patterns, non-linear left sides, function equations with priorities, `requires` and `[owise]`, rewrite rules with priorities, `requires` and `[owise]`, the hooks `+Int -Int *Int /Int %Int <Int <=Int >Int >=Int ==Int =/=Int andBool orBool notBool #if_#then_#else_#fi`, and undefinedness propagating strictly.

Not covered: collections (`Map`, `Set`, `List`) and their hooks, and therefore AC matching with frame variables and cell collections; any hook outside the list above; `ensures`; configurations of more than one cell (an object definition has the one cell `<k> $PGM:S </k>`); symbolic terms (an initial term is ground); conditions on results.
The encoder stops with an error naming the construct when it meets one outside the fragment that it recognizes: a hook outside the list, a domain value of another sort, a matching-logic connective in a term, an `ensures`, a configuration of another shape.

## Layout

| Path | Content |
| --- | --- |
| `kore.k` | The interpreter: module `KORE`, syntax module `KORE-SYNTAX`; 313 lines, 141 rules and equations (11 rewrite rules for the search, the rest equations of 44 functions). |
| `tools/korek.py` | The KORE text reader; the encoder of kompile's `definition.kore` and the initial term's KORE into a program of `kore.k`; the decoders of `krun --search`'s and `kore.k`'s results into one canonical text. |
| `tools/case.py` | Builds a case's encoded program and its reference expected result (needs K). |
| `cases/<id>/` | One case, below. |
| `FLOW.toml`, `MUTATIONS.toml` | The kink corpus: every case's `kore.pgm`, the argued coverage obligations, and the 38 mutations of `kore.k`. |
| `kink.lock` | kink-flow's verdict record of the corpus: each mutation's status and recorded killer, and the coverage verdicts. |
| `kill-matrix.json` | For each mutation, its status, every case that kills it and the cases on which its run gave no comparable result. |
| `tools/killmatrix.py` | Reduces `kink-flow run --full`'s JSON document to `kill-matrix.json`. |

### A case

| File | Content |
| --- | --- |
| `def.k` | The object definition: module `CASE`, syntax module `CASE-SYNTAX`, `configuration <k> $PGM:S </k>`, rewrite rules on the closed cell (`<k> L => R </k>`). Its first comment says what the case tests. |
| `pgm` | The initial term, in `CASE-SYNTAX`. |
| `pgm.kore` | `kast pgm --output kore` against `def.k` kompiled for the haskell backend: the initial term of sort `S`. The initial configuration is `<generatedTop>(<k>(kseq(inj{S,KItem}(PGM), dotk())), <generatedCounter>(0))`. |
| `kore.pgm`, `symbols.json` | The encoded program for `kore.k` (start sort `Pgm`) and the encoder's numbering of symbols and sorts. |
| `expected.json` | The reference result. For each backend (`haskell`, and `llvm` kompiled with `--enable-search`), `finals`: the item `inj{S,KItem}(X)` the `<k>` cell holds in each final configuration of `krun --search`, as canonical text (`Lbl…(args)`, integers, `true`/`false`, `inj{SortA,SortB}(v)`; a result under a condition carries ` if defined(…)`), sorted; or `error`, the backend's failure without its temporary paths. `reference` names the K release and backend that produced each; `backends_agree`; `inputs`, the SHA-256 of `def.k` and `pgm` the results were computed from. |

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

18 cases, each a small object definition for one point of the reading above.
"haskell" is the number of final configurations of the haskell backend's search, the expected result; "llvm" is the llvm backend's result against it.

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

The expected result is the haskell backend's, because its search gives a result on every case; the llvm backend's results are kept as a second reference: both backends give final configurations on 12 cases and agree on 11 of them (all but c10), and the llvm backend fails on the other 6.
The backends disagree on 7 cases, recorded in each `expected.json`:

- c08, c09, c12, c13, c14: the llvm backend aborts on a division by zero (`[hook_INT_tdiv]: Division by zero`), where KORE makes `X /Int 0` undefined (`\bottom`): no successor, a `requires` that is not true, an initial configuration that is `\bottom`.
- c10: the llvm backend evaluates `#if true #then 1 #else 10 /Int 0 #fi` lazily and steps to `b(1)`; the hook `KEQUAL.ite` is a function of its three arguments, so an undefined argument makes it undefined, and the haskell backend has no final configuration.
- c11: the llvm backend aborts (`Called finish_rewriting with no output file specified`) on `half(3)`, which no equation of the partial function `half` applies to; the haskell backend returns `b(half(3))` under the condition `\ceil(half(3))`.

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

- Coverage: 272 obligations covered (139 of 141 rules, 96 of 97 requirements, 37 of 37 syntax productions), 3 argued, 0 open, over 18 comparable cases.
  The argued obligations are `rule:KORE.ins-dup` and its requirement `requirement:KORE.ins-dup:held` (no `insert` receives a configuration its list already holds: a configuration is inserted into `seen` only when it is not a member, and into the finals only when taken from the frontier, which holds each configuration once), and `rule:KORE.tag-other` (configurations are values; `vr`, `hk`, `as` and `bot` never reach `cmp` under `kore.k`, and the rule is kept so that a mutant that makes `bot` a configuration still compares it).
- Mutations: 38, of which 37 are killed and 1 survives as expected: `fn-last-of-priority` (`expect = "survive"`).
  Two equations of one priority that both apply with different values state that the function has two values, an inconsistent definition; on a consistent object definition the first and the last applicable equation of a priority agree, so no case kills it.
- Cost: `coverage` 4.7 s and `run --full` 24.9 s cold (host load above 20); `run --locked` 1.2 s warm.

12 cases kill some mutation that no other case kills:

| case | mutations it alone kills |
| --- | --- |
| c04-subsort | subsort-dropped, subsort-not-transitive, subsort-reversed |
| c07-strict-args | dv-any-value, fn-owise-ignored |
| c09-undef-requires | rule-undefined-requires-holds |
| c10-strict-ite | ite-lazy |
| c11-fn-no-equation | no-equation-undefined |
| c12-undef-init | undefined-init-is-final |
| c13-inj-bool | inj-composed-outer-source, inj-not-composed, subsort-unchecked |
| c14-fn-undef-requires | fn-undefined-requires-holds |
| c15-nonlinear-rule | nonlinear-ignored |
| c16-bool-pattern | bool-dv-any-value |
| c17-init-function | init-unevaluated |
| c18-div-signs | tdiv-as-ediv, tmod-as-emod |

The other six (c01, c02, c03, c05, c06, c08) each kill 2 to 10 mutations that another case also kills.

## Why K and not KRS

The other packages of `krs/semantics` are KRS crates whose K is emitted by `krs`.
`kore.k` stays K source because a port is not small, although every construct it uses has a KRS spelling (constructor enums with `#[k::syntax]` templates, `k::equations!` tables with `#[k::equation(owise)]` and `#[k::equation(priority = N)]`, `k::rules!` over a one-cell configuration, `kequal` guards):

- The definition: its 15 sorts as constructor enums whose syntax templates must reproduce exactly the program syntax the committed `kore.pgm` files are written in (`pgm(def(…), …)`, `T ; Ts`, `.Ts`, `bot`); the 130 equations of 44 functions as equation tables; the 11 rewrite rules of the search in `k::rules!`.
  Each sentence is judged by KRS's checks on the assembled definition (overlapping equations, catch-all rows that need `owise`, complementary guards of rules), which `kore.k` has never been put through; whatever they refuse is a change of the definition to be argued, not a transcription.
- The corpus: `krs kink` reads a corpus in its own layout, `kink/` beside the crate's `Cargo.toml`: `kink/FLOW.toml` naming the package (`[spec] krs = { package = …, definition = … }`), the cases as program files that bind the `#[k::init]` parameter, `kink/mutations/<topic>.toml`, and a committed `kink/definition.k`.
  The emitted K has KRS's module names, rule labels and spelling of each rule, so all 38 mutations are re-anchored (each edit's `rule` and `find`), the three argued obligations renamed, and the coverage and kill numbers re-measured.
- The evidence that the port is the same definition: `krs run` of every case's `kore.pgm` gives the result `kore.k` gives, and the kill matrix is the same up to the renaming of mutations' anchors.

By the size of the existing ports (the KWasm slice is 294 lines of Rust for 16 sentences), that is on the order of a thousand lines of Rust and a re-authored mutation list, a unit of its own.
A half port, part of the definition in KRS and part in K, would leave two definitions of one reading; it is not done.

## Status

Done: the definition, the encoder and the case builder, 18 cases with their reference results, and the kink corpus.
Next: the command that reruns the cases.
