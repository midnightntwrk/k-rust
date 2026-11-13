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

Done: the definition, the encoder and the case builder.
Next: the cases with their reference results, the kink corpus, and the command that reruns the cases.
