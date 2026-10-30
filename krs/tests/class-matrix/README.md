# Class-test expectations

`expected.toml` states the expected outcome of every case that `krs_test_support::class_matrix`
generates: one construct in one slot of an accepted base, for readable records and claims, `cells!`
rules, initializers, the strict-subsort axis, every term shape at the term positions of every
sentence form, the module-import axis, and every sentence attribute on every sentence form. `pending.toml` lists the cases known not to conform.
The schema and the rules that read both files are documented in the `class_matrix` module.

For the term families (`terms/..`, `import/..`, `notation/..`) and the attribute axis (`attrs/..`,
K8 below), the outcome comes from the oracle (`class_matrix::oracle`, `class_matrix::attributes`),
not from refusal rules. Each term case carries its position (the form,
the slot, what a term there means: matched, evaluated, built or a guard, its root role and its
nesting) and its construct's nodes as data, and the oracle states, per construct, where the
construct means something and which mistake it is elsewhere. The precedence for a term case:

1. a refusal the oracle tells from the spelling and its position decides;
2. otherwise the most specific refusal rule of `expected.toml` decides: the rules left for these
   families name a term's sort and names (`condition-sort`, `let-sort`, `unbound-name`,
   `record-update-base`, `binder-sort`, `list-notation-sort`, `matches-pattern-binder`, ..), never
   its position;
3. otherwise a refusal the oracle tells by what a path resolves to or an operand's sort decides
   (a function in a pattern, a predicate as an operand), since a name or sort mistake is met first;
4. otherwise the case is accepted, with the K its accept entry records.

The term family's positions (`class_matrix::terms`) are of three kinds, each a path of openings
from a slot's root, so a case's position is data the oracle reads, never parsed from its ID:

- the argument positions of the 17 sentence forms (`terms/rule/subject/..`), a readable record's
  collection entries among them: a map read's key and value, and the elements of a List cell, a
  cons list (`terms/readable/cons-element/..`) and a List collection's instances
  (`terms/readable/collection-child/..`), which a pattern matches (decision D1), and an
  initializer's computation item, in an initializer that binds no name (`terms/init/item/..`, where
  a spelling's `x` is unbound) and in one whose configuration variable `x` the computation cell
  reads (`terms/init/variable-item/..`);
- the slots' roots: a fn's, an equation's, a simplification's, a context's and a static clause's
  whole subject, a `for KItem` clause's bare and in `k::term!` (`terms/sort-rule/subject-root-term/..`),
  a result's, a constant's and a computation item's (`terms/readable/item-root/..`);
- depth 2, a construct inside a position another construct opens (a set's element among them), at
  one host per kind (matched,
  evaluated, built, guard): `terms/sort-rule/result/let-body/Size(x)` is `Size(x)` as a `let`
  block's result in a `for Stmt` clause's result.

Besides the constructs of the product's table, the catalog applies the terms base's two static
productions, `Cmd::Dz()` (marked `#[k::desugar]`, expanding to `Cmd::Pair(2, 3)`) and `Cmd::Az()`
(marked `#[k::alias]`, to `Cmd::Pair(4, 5)`), at the matched positions of depth 1 below a subject's
root (`terms/desugar/subject/Cmd::Dz()`): the construct of NT-8-4 and NT-8 M2. A desugar's or an
alias's result root whose sort is not below its production's (a Bool, a String, a map, a `KItem`
term at a `Stmt` production) is the mistake `static-result-sort`, which `expected.toml` refuses
by the spelling's sort. The oracle reads
their application as the value it expands to (decision NT-14: a static application below a
desugar's or an alias's subject root expands when the expansion needs no value, as a ground
one's never does), and `cargo test -p krs-test-support --test k7` names a static production the
base gains without a spelling. The slot `terms/cells/result-map-framed/..` writes one key under two
spellings over the map a framed `cells!` subject leaves (`map![x -> 1, (x) -> HOLE, ..rest]`); the
slot `terms/cells/result-map-whole/..` writes an entry over a map the subject binds whole
(`map![x -> HOLE, ..m]` over `Cell(m)`, the form the class `framed-map-unmatched-key` advises),
and `terms/cells/result-map-framed-key/..` writes a key the framed subject does not match over the
remainder it leaves (`map![HOLE -> 1, ..rest]` over `map![x -> v, rest @ ..]`, finding NT-9-1 at a
key other than `x`).

A map key reads by its parent (decision D2): a key of a map in a pattern is evaluated, and a
pattern-only construct there selects an entry by matching the map's evaluated keys while a computed
one is looked up; a key of a map that is built is built. A position keeps every collection entry it
lies in (D4). The catalog covers every construct of the product's table, every notation form, and
the collection forms; `cargo test -p krs-test-support --test positions` fails, naming what is
missing, when a form of the table has no position, a slot of a form no root or argument case (but
the listed exceptions), or a construct, notation form or builtin operator no spelling.

The oracle is written independently of the product's position table (`krs_syntax::positions`),
which is written per position; `cargo test -p krs-test-support --test positions` compares the two
on every term case, and a case they disagree on must be pending.

A refusal of the oracle lies at the spelling, or at the entry (the outer construct's text) when the
refused construct is the one a depth-2 case's construct stands in.

**Size.** The term family is 5,063 cases, the import axis 172 and the attribute axis (`attrs/..`,
18 forms × 22 attributes and 26 malformed attributes, in the first shard of the fast tier) 422, of
6,494 in all, and
the notation family (`notation/..`: the term family's positions, templates and oracle for the
collection notation, `m[k]`, `s.contains(x)`, `map![k -> v]` and `set![x]`, and the calls it
denotes) 2,862. The generator caps
each shard of the fast tier at `FRONT_CASE_CAP` (6,000), whose documentation argues the fast tier's
budget (7.5 ms a case single-threaded); the notation family and the term family are shards of
their own (`FRONT_SHARDS`), one test of `class_front` each. The full tier's `terms` shard takes about 5
minutes with 22 workers, its `notation` shard about 3, and its `attrs` shard about one. The accept
entries of the families the oracle judges (the term families and the attribute axis) are most of
the table, so they live in `accepted-terms.toml`, in `expected.toml`'s accept schema and written by
the same record mode; `expected.toml` keeps the classes, the refusal rules and the other families'
accept entries, and holds none of theirs (`class_matrix::table`).

The generator's own tests check that every base expands, that every case's ranges point at its
construct, and that both files parse:

```sh
cargo test -p krs-test-support --test class_matrix
```

## The full tier: gate `krs-class`

`scripts/krs-class.sh` runs every case through Cargo, rustc, the collector, and `emit-k`'s lowering
(`krs/crates/krs-cli/tests/class_matrix.rs`). The rule-level cases of one base share batch packages,
one command constructor per case; a rustc or collector error is attributed to the case whose text
holds it, a failure no case owns is bisected, and once a batch collects, each case is lowered from
the descriptors of the base and its own. A case is judged by

- K2: when refused, exactly one error, with a registered KRS code of the author kind (the registry's
  `CodeKind`; a rustc error forwarded as `krs::rust-expansion::uncoded-error` does not count), located (its
  primary range or one of its labels) inside the site the table's rule names (the entry by default), without a panic or an internal error;
  and the table's outcome: accepted with the K the table records, or refused with the code of the
  case's mistake class. The table covers every case: a new case needs its entry.
  At a position rustc parses as Rust before any KRS macro reads it (a `#[k::rule]`,
  `#[k::equation]` or `#[k::simplification]` result, a `#[k::function]` shorthand's body, a
  `#[k::constant]` value; the generator marks these slots), a construct rustc's parser refuses
  (`y @ P`) is reported by rustc whatever KRS does. There the refusal conforms with rustc's parse
  error (an uncoded rustc error) beside KRS's one error, both inside the construct, and K2 judges
  KRS's error alone. The front stops at the same parse error (`krs::expand::parse`) and leaves the
  case to the full tier. No other position has this rule (`class_matrix::invariants`);
- K1, once collected: every anchor of the case's descriptors lies inside the case's text, and no
  semantic key is found twice during lowering;
- K3, once accepted (initializers aside): each case emits the K of every case its `same_k_as`
  names, the documented equal spellings; and the accepted cases of a batch are printed together by
  `krs expand`, the printed source is collected again, and each case's own K sentences must be
  emitted again, byte for byte or after the normalization of `class_matrix/closure.rs`
  (alpha-renaming, `... </k>` for an explicit computation rest, `...` for a frame variable used
  once or `_` there, and the digest of a generated label). Each shard prints, per form, how many cases are byte-identical, equal after
  normalization, different, or refused in the printed source. `KRS_CLASS_CLOSURE=0` skips it;
- K6, once accepted (initializers included) and not refused by the table: the definition the case
  emits, its base and the case alone, passes the judgement `krs check` makes without `--backend`
  (`krs_cli::CollectedDefinition::check`, the function `krs check` itself runs): `emit-k`'s
  emission, every native route's capability table, `krs build`'s native compile on both backends,
  and on the `native-rust` route the definition load of `krs run`, `krs search` and `krs prove`.
  K6 asks whether any `krs` command can use the K KRS wrote: a case KRS accepts but a native
  route refuses cannot be built, run or proved, however good its K. A refusal or a panic is a
  deviation keyed `k6/<case ID>`. A refusal's signature is the refusing route or command, as the
  note `krs check` adds names it (`native-rust`, `native-llvm`, `every native route`, `load` for
  the definition load, `emit-k`), and the code of each error, for example `every native route
  IllegalFunctionOnLhs`. `krs check` reports a panic of one of its route workers as the uncoded
  error "a check worker panicked", before any route note, so its signature is `uncoded: a check
  worker panicked` and names no route (a panic in the definition load is reported, and signed,
  under the `native-rust` and `load` notes); a panic on the harness's own thread (lowering,
  emission, the capability tables) is `panic: <message>`. The TSV's `k6-refusal` lines hold each
  refusal's messages.

  The native compile of a base costs far more than a case adds to it (on 2026-10-30, about 2 s a
  check for the machine base, the case's lowering under 0.01 s), so the accepted cases of a batch
  are judged together, as one definition, when it is exactly theirs: its emitted sentences are the
  base's and each case's own, as each emits alone. A refusal is bisected, as a collection failure
  is, down to the case whose definition alone is refused; a batch whose cases lower otherwise
  together is judged case by case. Each shard prints how many cases K6 judged, in how many checks,
  and the workers' time they took. `KRS_CLASS_NATIVE=0` skips K6, and `KRS_CLASS_NATIVE=alone`
  judges every case alone, which must give the same verdicts. K6 compiles natively, so the tier
  links the Z3 release `Krs.lock` pins (`KRS_Z3_LIB`, or the Nix store);
- K7, once K6 accepts the case: the case runs, and its sentence applies, with the value the
  generator states. Accepted K is K some command can load; K7 asks whether it does anything, and
  the right thing: a rule that never applies, a program that cannot be expanded and a built term
  with another value all look accepted to K1 to K6.

  *Witnesses and values* (`class_matrix::k7`, the spellings in `class_matrix/terms.rs`) are
  generator data, stated from what each construct denotes, never from what KRS emits or runs,
  with the templates' binders at fixed values (`x` is 1): a spelling's *witness* is a ground term
  it matches (`Cmd::Hold(x)` matches `Cmd::Hold(1)`, `_` matches `0`), its *value* what it denotes
  where it is built (`x + 1` is 2, `map![x -> 1, 2 -> 3]` the map `{1 ↦ 1, 2 ↦ 3}`,
  `set![x, 1]` the set `{1}`, `k::matches!(x, Cmd::Hold(_))` false). A spelling with none says
  why (a computed term matches no evaluated term; a pattern builds nothing; `{ let y @
  Cmd::Hold(_) = x; y }` has no value at `x` = 1), and the openers compose them: the witness of
  `y @ HOLE` is the hole's, of `set::item(HOLE)` the set of it, the value of `Size(HOLE)` the
  unevaluated `Size` of the hole's (`Size` has no equation, so it serves as a wrapper the run
  shows the hole's value in; `Size(x)` itself has no stated value). A spelling a pattern reads
  also has a *counter-witness* where one exists, a ground term it must not match (`Cmd::Hold(x)`
  must not match `Cmd::Pair(0, 0)`, `y @ Cmd::Hold(_)` neither): its case runs a second program on
  it, which must stop before the case's sentence, so a pattern lowered too loosely is caught. A
  disagreement with KRS is a finding, triaged as an oracle or a product bug.

  *Drivers* (`class_matrix/terms/drivers.rs`), one per slot, write the program that applies the
  case's sentence and state the cells the run ends with. A rule's command is applied to the
  witness (`Cmd::NAME(x, HOLE)` takes `cNAME(1, w)` and ends with `hold(1)`) or read for its
  value (`cNAME(1, 0)` ends with `hold(v)`); a condition's value decides whether the rule
  applies, and a condition with no value at `x` = 1 (`{ let Cmd::Hold(_) = x; true }`) does not
  hold; a map key and a set's element, a Set collection's instance included, read as decision D2
  reads them: a computed one is looked up by its value (`set::item(int::add(x, 1))` takes
  `sone(2)`), a selection by its witness; a map key, a list or cons element and a collection's instance are first set up by the
  terms base's driver commands (`then(setenv(..), cNAME(1, 0))`), one step each at priority 10,
  so that no driver rule overlaps a case's; an equation's function is applied from the base's
  rules `call(a, b) => hold(probe(a, b))` and `sizeof(a) => hold(size(a))`; a context heats the
  token `word`, which is no `KResult`; a desugar's or an alias's subject is written in the program,
  which the run's parse expands, and its result read in the expansion; an initializer, of the
  term family or of the configuration families' `init` (the machine and typed bases, with `$PGM`
  bound to `go` and `-c ANY=1`), is read before any step, each cell's stated value compared. Values the program grammar cannot write (a map, a set, a list, `$x`,
  `Wrap::<KItem>(..)`) are written through the base's makers, functions that build exactly them,
  which a static clause's expansion meets unevaluated, so a witness only a maker writes is no
  witness for a desugar's or an alias's subject. Claims and simplifications need a prover (L4
  keeps claims in the fixture gates); a context alias acts only through a production strict in
  it, which neither the base nor a case declares; a `#[k::function(internal)]` shorthand and a
  constant have no program syntax and no base sentence can name the case's: these have no driver.
  Nor have the readable, claim and `cells!` families: their cells start at the machine and typed
  bases' fixed values, and those bases have no driver commands yet.
  `cargo test -p krs-test-support --test k7` lists the spellings without a witness, a value or a
  counter-witness and the slots without a driver, with their reasons, counts every case's K7
  status (each skip reason, and the counter runs), and pins a plan of each driver kind.

  *Running*: where K6's check loads the definition the run commands load (on the `native-rust`
  route, `krs_cli::CollectedDefinition::check_visiting`), each accepted case's program is
  configured and run there exactly as `krs run` reads a file (`Semantics::configure`, then
  `Semantics::run`), on the compile K6 judged, and the run's verdicts are kept when the check
  passes; a case K6 refuses is not run. The run is bounded by the driver's step count, so a
  sentence that applies again to what it wrote is observed after its application, and by a time
  limit per program (`KRS_CLASS_RUN_SECONDS`, 60 by default), enforced by cancelling the
  backend's request: the program's configuration (its parse, the expansion of its desugars and
  aliases) and its run are one cancellable request (`k7_bounds_a_program_whose_expansion_or_run_does_not_end`
  shows an initializer that does not end giving a deviation at the limit). A panic of a run is its
  case's verdict, and the cases after it run on a definition apart. Each case's command is its own, so only its sentence can take its program;
  a sentence that holds no command of its own (a subject's root: a context's, an equation's, a
  simplification's) could take another case's, so where one shares K6's check with other cases,
  it and the others are run on definitions apart. The final cells are decoded
  (`StateView::value`) and compared with the plan's terms. A deviation is keyed `k7/<case ID>`:
  `not applied: N of M steps, then HALT; CELLS`, `no defined result: ..` (a sentence matched and
  its result has no value), `applied where it should not`, `counter-witness `PROGRAM`: ..` (the
  counter run's deviation), `failed: ERROR`
  (the program's parse or expansion, or the run), `time limit: ..`, `no configuration
  (\bottom)`, or `another value: CELLS, where the plan states CELLS`. Each shard prints how many
  programs K7 ran, in how much worker time, and what it checked of each case K6 accepted: a
  stated `value`, `liveness` only (a witness, or a value the generator does not state), or why
  nothing (`no driver`, `no witness`, `no value`). `KRS_CLASS_RUN=0` skips K7; without K6
  (`KRS_CLASS_NATIVE=0`) it does not run, and says so.

  K7 runs on K6's compile, so it costs its programs' runs (a few milliseconds each) and the
  checks apart: on 2026-10-30, 1,489 programs in the `terms` shard took 9.5 s of worker time and 2
  checks apart 4.1 s, 870 in `notation` 5.2 s, 99 in `import` 0.6 s and 1 check apart 2.2 s; each
  shard's wall time with and without K7 was within the noise of a loaded host (`terms` 356 s and
  364 s, `notation` 206 s and 205 s, at 15 workers).
- K8, the attribute axis and the advice check (`class_matrix::attributes`, `class_matrix::advice`).

  *Attributes × forms.* The `attrs` family (`attrs/FORM/ATTRIBUTE`, a shard of its own) writes
  every attribute an author can write on a sentence on every sentence form: each key of a
  sentence's marker (`#[k::rule(owise)]`, `#[k::equation(concrete)]`, `#[k::claim(all_paths,
  trusted)]`, `#[k::desugar(unbound_variables = [y])]`, ..) and each helper beside it
  (`#[k::requires(..)]` holding and failing, `#[k::ensures(..)]`, `#[k::exists(..)]`,
  `#[k::fresh(..)]`, the retired `#[k::priority(..)]`), each with a representative well-formed
  value, on each of the term family's 18 slot forms, written on the form's subject slot template
  with the marker's own keys removed; and a few malformed values (a value of the wrong shape or
  range, a key written twice, an unknown key, a missing key) and keys that cannot stand together
  (`owise` with `priority`, `heat` with `cool`, ..). The attribute list is read from the product:
  `cargo test -p krs-test-support --test attributes` parses `krs-syntax`'s attribute parsers and
  fails on a key they recognize that no attribute of the axis writes (or the other way round),
  and on an attribute macro of `krs_syntax::surface::AttributeMacro` that is neither a sentence's
  marker or helper nor a declaration's. What each pair means is the oracle's statement
  (`attributes::means`), from what the attribute denotes on that kind of sentence; a refused
  pair is judged by K2 like any case (one author error, at the attribute), with the class the
  oracle states (`attributes::expected`). An accepted pair runs by K7 where its form has a
  driver, and the run shows what the attribute does: a condition that does not hold, and
  `symbolic` on concrete values, leave the sentence unapplied; `owise` beside a sibling at
  `priority = 60` applies where the sibling does not, and its counter run, where both match,
  shows the sibling's result; `priority = 20` beside a sibling at `priority = 30` wins where
  both match; `heat` applies where its hole is no result (`word`) and not at `1`, `cool` the
  other way round; an anywhere rule applies below `hold(..)` as the configuration is built; a
  label, `nondet` (beside a sibling of its group), a restriction, `ensures`, an existential or a
  fresh value leave the sentence applying as its slot's driver states. The terms base's driver
  rules have priority 10, before every case's (20) and sibling's (30, 60), and match only the
  driver commands, which no case's sentence does: a case's priority neither shares a priority
  with them nor is applied after one of them at the case's command.

  *Advice.* A class whose refusal advises a rewrite carries `advice = "<case ID>"`, a case that
  writes the advised form, which the table must accept (a table error otherwise). What advises a
  rewrite is decided mechanically (`class_matrix::advice`): a message holding, after an advice
  verb in the imperative at a clause's start (`write`, `mark`, `declare`, `bind`, `place`, `add`,
  ..), a code span in the same clause, or saying how the refused construct `is written` (the form
  right after the verb) or how a pattern `writes` it; or a help line doing so, or showing a form at
  its end after a colon (the `for Sort` clause a whole-subject `_` is pointed to). The registry's
  summaries are read the same way: `cargo test -p krs-test-support --test attributes` fails on a
  class whose code's summary advises a form and that names no advised case. K8 judges, keyed
  `k8/<case ID>`: each class's advised case, which must be accepted, pass K6 and run as K7 states
  where it ran
  (`advice of CLASS: refused: ..`, `.. K6: ..`, `.. K7: ..`); and each case a class refuses as the
  table expects whose error advises a rewrite while its class names no advised case (`CLASS
  advises `FORM` and names no advised case`).

  K8 costs its own shard and a scan: on 2026-10-31, under a load of about 20 to 60 from other
  work, `attrs` (422 cases, 101 accepted) took 68 s at 15 workers, K6 46 checks in 45 s of worker
  time and K7 73 programs in 0.5 s; the advice check reads each refused case's errors, below
  measurement. The existing shards gained 8 cases (4 in `terms`, 4 in `import`) and took
  `readable` 66 s, `cells` 57 s, `init` 75 s, `import` 66 s, `notation` 203 s and `terms` 358 s at
  15 workers, each no longer than its last run on main (NT-12's, on 2026-10-30, under a heavier
  load: 120, 93, 129, 68, 236 and 665 s).

The `k4` shard compares KRS's sort judges with k-rust's subsort relations of each base's emitted
definition; its disagreements are keyed `lattice/class-BASE/JUDGE~JUDGE/CLASS`, and those about
`KItem ≤ K` or a list's element are only counted.

The `k5` shard checks `class_matrix::entry_points`: one package that uses all 53 entry points of
`krs-macros`, and one mutation per entry point that breaks its header and keeps every dependent.
Each mutation must give exactly one diagnostic, an error, under `krs check --message-format json`,
and exactly one error under plain `cargo check`, whose warnings are counted and not judged: a
failed item leaves its imports unused (`unused_imports`), which no proc macro can avoid without a
second error, and which `krs check` relays away. Its entry is keyed by the mutation,
`entry/attribute/cell`.

Run one shard (`readable`, `cells`, `init`, `terms`, `import`, `notation`, `attrs`, `k4`, `k5`), and choose the worker count yourself
when the default (from the available memory, 3 GiB per worker) does not suit:

```sh
scripts/krs-class.sh --shard cells --workers 4
```

To iterate on a few cases, run the test directly with a glob over case IDs, and write one TSV line
per case and verdict to a directory:

```sh
z3=${KRS_Z3_LIB:-$(ls -d /nix/store/*-z3-4.12.5-lib/lib | head -n 1)}
LIBRARY_PATH=$z3 LD_LIBRARY_PATH=$z3 KRS_CLASS_FILTER='readable/result/pc/*' KRS_CLASS_OUT=/tmp/class \
  cargo test -p krs-cli --no-default-features --features z3-inference --test class_matrix -- --ignored readable
```

K6 judges with the sort inference `krs check` uses, Z3's, so the test refuses to judge K6 when it
was built without `z3-inference`; `KRS_CLASS_NATIVE=0` runs the other checks without it.

## Recording the accepted K

An accepted case's K, the sentences it adds to its base after K3's normalization with the case's
tag written `TAG` (for an initializer, its `configuration`), is written by the record mode, never by
hand:

```sh
scripts/krs-class.sh --record --shard readable --shard cells --shard init --shard terms --shard import --shard notation
```

It writes `k` for every accepted case that the table does not refuse (the oracle included),
creating its `[accept."ID"]` entry if needed, and keeps `same_k_as`. Review the change to
`expected.toml` as a diff: a changed K is a changed emission.

## Pending entries

A case that deviates fails the suite until `pending.toml` records it, keyed by the test and the case
(`readable/result/pc/None` for K2, `k1/..`, `k3/..`, `k6/..`, `k7/..` and `k8/..` for K1, K3, K6, K7 and K8), with the finding that owns it (`unassigned` while none does) and the
deviation exactly as the harness prints it. `KRS_CLASS_OUT` writes the entries of every unrecorded
deviation to `<shard>.pending.toml`, with `finding = "unassigned"`, for review. A pending case that
conforms, or deviates differently, also fails: remove its entry, or record the new deviation.
