# kink-flow

The primary usage flow of kink:
a K specification, a concrete corpus of programs an LLM writes for it,
cached results, a mutation list, a kill search and a survivor report.
The root README's "Using kink-flow" section is the walkthrough; this file is the reference.

This crate provides the corpus manifest and the `check` command (flow F-02),
the result cache (flow F-03), which the `coverage` command reads: the obligations the specification states, family by family, each covered or open, with a target for each open one ("`kink-flow coverage`" below),
the mutation list with its resolution into patches (flow F-04),
the kill search with its killer cache, the `run` command (flow F-05),
the survivor report with the `report` command (flow F-06),
Markdown sources (flow F-10),
the outcome cache: proved outcomes kept across commands and `run --verify` (flow F-14),
one baseline run per program per command (flow F-12),
report usability: named oracle slots, timings, leaf censuses in the causes of stopped runs, and the rules no mutation targets (flow F-13),
per-input pattern checks with the `query` command (flow F-18; "Checking a pattern" below),
the `fuzz` command: hole values of a template program that kill a mutation, match or fire a rule, or hit a pattern, found by k-rust-fuzz on kink's own sides (fz26 P7-KINKFLOW T3a and T5; "Killing a survivor with `fuzz`" below),
the mutations directory, anchors by a suffix of a label's components and the required `misunderstanding` (CF-13; `MUTATIONS.toml` below),
the resolve-only check of a mutation list, `check --mutations` (CF-18; "Checking mutations" below),
the definition exclusions read at admission, each named with its causes by one formatter for every command, with `check` failing when a fact known before any mutant runs makes a verdict impossible (CF-02; "When `check` fails" below),
the compared cells: the specification's unobservable cells left out of every comparison, a manifest's narrowing, and every document naming the cells compared ("Which cells are compared" below),
the corpus record, a `kink.lock` with one section per command that `run --lock`, `coverage --lock` and `compare --lock` read and rewrite, each its own: `[run]`, one recorded killer per killed mutation, kept while it still kills, `[coverage]`, the same for the condition flips with each family's open and argued obligations, and `[compare]`, one verdict per implementation, program and view ("The corpus record" below),
the comparison of other implementations of a corpus's system with the definition, over its programs, inputs and `[stop]`, under declared views, with `compare` (FB-47; "Comparing implementations" below),
the report of which programs are redundant, from the mutations the corpus kills, the patterns it hits and the items `coverage` covers, each cell of the kill and pattern matrices asked only where a decision needs it (`--full`: `run --full` and `query --full`, with the same decisions), with `prune` (FB54-PRUNE, FB56; "Redundant programs" below),
and the library for both front ends, kink-flow's command line and the krs front end (`krs kink <verb>`): one manifest schema with a K or a KRS `[spec]`, one command layer, and the deterministic `--output verdicts` rendering (CF-40; "Front ends" and "Verdicts" below).

## Building

Build the portable (no-Z3) profile for the LLM loop, from the root of k-rust's checkout:

```sh
cargo build --release -p kink-flow --no-default-features
```

The executable is `target/release/kink-flow`.
kink-flow's default features are the Z3 solver profile, as k-rust's and the other kink crates' are (the root README, "Gate"), and k-rust's own workspace build and test run use it.
Under Z3 every solver query of kink's backends is bounded by Z3 resource units (`budget.smt_resource_limit`), never by the clock, so the caches are on in both profiles ("The cache directory").
A complete exploration with no match is `no` under Z3 only when the search received no undecided solver answer (`query`, "Answers"), and its `cause` then names that count.

## `FLOW.toml`

```toml
[spec]
entry = "calc.k"              # relative to this file's directory
main_module = "CALC"
syntax_module = "CALC-SYNTAX" # optional
include_dirs = ["."]          # optional
md_selector = "k"             # optional
assume_joined = ["root:CALC.add-one,CALC.add-two#752d82d62beba044ce8ec11b8e06014e"]   # optional; findings named as premises

[corpus]                      # optional; the cases are in this file's directory when absent
root = "../corpus"            # the corpus root, relative to this file's directory ("The corpus root")

[budget]                      # optional
time_ms = 10000
max_depth = 100000
work_factor = 4               # optional; default 5: a mutant's run may use max(5 × P, P_max) polls
baseline_max_work = 200000    # optional; baselines bounded by time and depth only when absent
smt_resource_limit = 370000   # optional; Z3 resource units of a query's first attempt

[result]                      # optional
cells = ["k", "regs"]         # compare only these cells; default: every observable cell

[stop]                        # optional; every run ends where its paths end when absent
after = ["CALC.frame-end"]    # and/or before = [...]: rewrite rules by exact K label
count = 60                    # optional; default 1
when = { function = "Frame", cells = ["frames"] }  # optional; krs kink only: a stop condition

[[program]]
id = "add"
file = "programs/add.calc"    # or: text = "1 + 2"; neither on a definition without $PGM
start_sort = "Exp"            # optional; only with file or text
variables = { N = "42" }      # optional; configuration variable $N = 42
stop_count = 120              # optional; only with [stop]: this program's count

[[patterns]]                  # optional; the patterns `query` and `fuzz --pattern` ask
files = "patterns/*.toml"     # kink pattern lists, matched as a [[program]] glob matches cases
```

A KRS corpus declares its specification as the K a KRS package emits, which the krs front end (`krs kink <verb>`) binds:

```toml
[spec]
# The Cargo package (krs --package) and its definition facet (krs --definition).
krs = { package = "story-plus", definition = "main" }
assume_joined = []             # optional, as above
```

With `krs`, `[spec]` takes no other key but `assume_joined`: `entry`, `main_module`, `syntax_module`, `include_dirs` and `md_selector` are each the error `spec.<key>: not allowed with spec.krs: the krs front end supplies it`, and `krs` takes exactly the keys `package` and `definition`, both required.
A KRS flow names the definition it is for, `PACKAGE:FACET`.
Every file of a flow is a function of one definition: `definition.k` is its emitted K, a mutation is a patch of that K, and each section of the corpus record holds its verdicts.
So the flow says which definition that is; a record that does not name its subject can be overwritten by another's.
A declaration without `package` is the error `spec.krs.package: missing`, which says what to add.
The corpus record's header states the same name ("The corpus record").
Every other table is the same for both kinds of corpus.
kink-flow refuses a KRS corpus (``spec.krs: a KRS corpus: run `krs kink <command>` in the package``, stage `manifest`); the krs front end refuses a K corpus (`spec.entry: a K corpus`, naming `kink-flow`), and refuses a KRS corpus of another package or facet than the command selected before it builds or writes anything (stage `definition`, reason `another-definition`, naming both).
A `krs kink` command given `--corpus DIR` takes the package and the facet from the flow, so it needs no `--package` and no `--definition`.

Every path is relative to the manifest's directory and must stay inside it, except the paths of the cases in a flow that names a corpus root, which are relative to that root and must stay inside it ("The corpus root").
Unknown keys, values of the wrong type, duplicate or empty program ids,
a program with both `file` and `text`, a `start_sort` on a program with neither, and a pattern that is invalid or matches nothing are errors that name the key or the program id.

A program is a case: an assignment of a value to each configuration variable of the definition.
`file` or `text` is the program text bound to `$PGM`; every other variable is bound by name.
A definition without `$PGM` takes no program text: its case gives neither `file` nor `text` and binds every variable under `variables`,
and a program text given to it is refused (stage `inputs`, reason `stray-program`, naming `$PGM` and every declared variable with its sort), since it would bind nothing.
A case of a definition that declares `$PGM` without a program text is refused as missing it (`inputs`/`assemble`), unless a front end gives `$PGM` a default (below).

A program may also have `inputs`, a table of typed inputs by input name (`inputs = { rom = { "$file" = "rom.bin" } }`): documents of an encoding derived from the specification's declared types, which only a front end that knows those types reads (the krs front end, `krs kink`).
kink-flow keeps them as written and never reads them; a front end sets its decoder on the manifest it decoded (`FlowManifest::with_input_decoder`, the `InputDecoder` trait), which gives for each input the configuration variable it binds and the K term it denotes, reading the files a document names inside the manifest's directory.
kink binds the term as it binds a parsed value: it types the term in the definition's grammar and refuses it when its sort is not at most the variable's.
A manifest read at the K level has no decoder, so a program with `inputs` is refused (`inputs`/`typed-inputs`): at the K level, bind K text under `variables`.
A typed input may bind `$PGM` on a program without `file` or `text`: kink binds the term as a program built without the parser.
A document the decoder refuses, or a variable bound twice (by both `variables` and `inputs`, by two inputs, or `$PGM` by an input and the program's `file` or `text`), is refused (`inputs`/`input-value`, with the decoder's message or the two bindings).
A file a document names is read as a program file is: its path is relative to the manifest's directory (or, for a file a decoder reads from another, to that file's directory), resolved by the operating system, links included, and an absolute path or one that resolves outside the manifest's directory is refused.
A front end that knows the definition's main input may also read each program's bytes itself (`InputDecoder::program`) and say which variable they bind, as K text read at the variable's sort or as a term: the krs front end binds a program file to the `#[k::init]` main parameter, whatever its K name, as the file's bytes where that parameter's type is exactly `Bytes`.
Where the decoder gives no answer, or without a decoder, the program is UTF-8 text bound to `$PGM`, as above.
A front end whose definition declares defaults gives, for the variables a case binds no value for, each declared default (`InputDecoder::defaults`: the krs front end, an input's `#[k::config_var(.., default = D)]`), the value the front end lowered with the definition at the variable's declared sort; kink binds it as that value, so the case is the one that binds the default by hand, and a value the case binds replaces the default whole.
A variable with no default and no value is refused as missing (`inputs`/`assemble`, naming the variable).
A K definition declares no defaults, so without a decoder no default is bound.
A default a case takes is in its program digest (`defaults`: each variable's name and the SHA-256 of its default's KORE text), since the K text, and so the execution digest, is the same whatever the default; a case that takes none keeps the digest it had before defaults existed.
A program the decoder refuses, one it binds otherwise than as `$PGM` text while the program gives a `start_sort` (which reads `$PGM` text only), and a variable the program and `variables` or an input both bind are refused (`inputs`/`input-value`).
Whichever way a program binds, its digest holds the SHA-256 of its bytes (`program_sha256`), or, where a front end rewrites the text it binds to `$PGM`, of that text.
`fuzz` reads a template's own `file` or `text` as admission reads a program's, so a template binds what the same text as a `[[program]]` binds.
It refuses a template of a program with typed inputs, one whose program (its own, or the `[[program]]` it names) the front end binds otherwise than as `$PGM` text, and one that leaves a variable to its declared default: it varies and replays `$PGM` text and `variables` only.

### The corpus root

```toml
[corpus]
root = "../../corpus/cpu"     # relative to this file's directory; it may climb above it
```

A flow may read its cases from a corpus root it names, so that the flows of several definitions read one tree of cases.
A case is a value for each input of a machine, which every definition that takes those inputs reads alike.
Every other file of a flow is a function of one definition: the emitted K, a mutation (a patch of that K), a pattern list (a statement over its runs), a template, the corpus record, the cache, and an implementation's command and identity file (one build of one system).
So the cases live under a root that belongs to no definition, and a definition's files stay beside its flow.

Two definitions over one corpus, each flow naming `root = "../../corpus"`:

```text
corpus/                       the corpus root
  cases/t1.nat                a case; its id is cases/t1.nat in every flow
  cases/t2.nat
spec/kink/                    the flow of one definition
  FLOW.toml                   [spec] names the definition; [corpus] root = "../../corpus"
  definition.k                under `krs kink`, the K that definition emits
  mutations/plus.toml         patches of that K
  PATTERNS.toml               patterns over that definition's runs
  TEMPLATES.toml              case templates for `fuzz`
  kink.lock                   that definition's verdicts
  .kink-flow/                 its cache
refined/kink/                 the flow of another definition
  FLOW.toml                   the same root
  definition.k
  mutations/zero.toml
  kink.lock
  .kink-flow/
```

What each owns:

- The corpus root owns the cases: the program files, the case documents, and the files they include or name. Each has one id, its path relative to the root, in every flow.
- A flow owns what is a function of its definition: the manifest's tables that name the definition's rules and cells or bound its runs (`[stop]`, `[observe]`, `[budget]`, `[[implementation]]`), the specification's files, the mutation lists, the pattern and template lists, an implementation's command and identity file, the corpus record and the cache.
- A KRS flow and its corpus record each name the definition they are for (`[spec] krs`, and the record's `definition`), and a command that selects another package or facet is refused before it builds or writes anything ("`FLOW.toml`").

What is relative to the root, and must stay inside it:

- a `[[program]]`'s `file`, and its `files` and `cases` patterns ("Programs from a pattern");
- a case document, the files it includes and the files its inputs and its expectation name;
- a file the `inputs` of a listed `[[program]]` name.

A program id that is a path (a pattern's match) is the path relative to the root.
Two flows that name one root therefore give each case the same id, in every document and in each flow's record.
The containment rule has the root as its boundary: a path may not climb above the root, and a file that a link leads out of the root is refused, the message naming the root as the manifest writes it (``programs/out.calc escapes the corpus root `../corpus` ``), never by an absolute path.
The flow's own directory is outside the root unless the root contains it, so a case cannot name a file of one definition.
The rule keeps what it kept for a manifest's directory: an id is relative to a tree that is checked in, and a flow reads two named trees and nothing else of the host.

What stays relative to the manifest's directory, whatever `[corpus]` says: `[spec] entry` and `include_dirs` (under `krs kink`, `definition.k`), `[[patterns]] files`, an `[[implementation]]`'s `command` and `identity.file`, and the files a command line or a front end's layout names beside the flow (the mutation lists, `PATTERNS.toml`, `TEMPLATES.toml` and a template's own `file`, the corpus record `kink.lock` and the cache `.kink-flow/`).
Every file a command writes is among these, so no command writes under a root that does not contain the manifest's directory.

`root` is a relative path of names, `.` and `..`; an absolute path is refused, and so is a path that names no directory (`corpus.root`).
The root may be the manifest's directory itself (`"."`), contain it (`"../.."`, flows kept under the corpus) or be a sibling of it.
Without `[corpus]` the root is the manifest's directory: the layout every corpus had before the key existed, with the same documents and records.

No digest and no cache key holds the root or the manifest's directory, as written or resolved: a program's digest is of its bytes and its decoded inputs, the specification's of its files by their names relative to the manifest's directory, and a request to an implementation names the program by its id.
A flow moved to another depth, naming the same root by another path, reads the cache it had.

What the layout does not give:

- No comparison between the definitions. Each flow runs the cases on its own definition and records its own verdicts; nothing checks that two definitions end a case alike. An `[[implementation]]` compares a definition with one other system ("Comparing implementations"). A statement about two definitions (that one refines the other) is a claim about every run of both, not a verdict on the corpus's runs: it belongs to the proof tool, and no kink command makes it.
- No shared verdicts. Each flow has its own record and cache; a case added under the root is run by every flow that reads it on that flow's next command, and each flow's `--locked` gate judges it for that flow's definition.
- No shared expectation scope. A case's `expect` is checked by every flow that reads the case, so an expectation true of one definition only is unmet in the others.
- No corpus-wide `prune`. A flow's report is of that flow's obligations and answers for that flow only; a case redundant in one flow may be the only discharger of an obligation of another, so a case is removable from the root only when the cases kept discharge every flow's obligations ("Redundant programs").
- No check that two flows are of one interface. A definition that cannot read a case's inputs refuses that case (`inputs`), naming it.

### Programs from a pattern

A `[[program]]` entry may name a pattern of case files instead of one program, so that a corpus of many cases needs no generated manifest:

```toml
[[program]]
files = "programs/**/*.imp"   # each match is a program text, as `file = "<match>"`
start_sort = "Pgm"            # optional; the entry's start_sort, variables and inputs are every match's
variables = { IN = "3" }

[[program]]
cases = "cases/*/case.toml"   # each match is a case document: one case, or named cases
```

Each match is a program whose id is its path relative to the manifest's directory (the corpus root, where the flow names one: "The corpus root"), as matched (`programs/sum.imp`, `cases/boot/case.toml`), and each named case of a matched case document is a program whose id is that path, `#` and the case's name (`cases/boot/case.toml#reset`).
Adding a matching file adds a program and removing it removes it, without editing the manifest; the id depends only on where the case is, never on the host, the corpus's absolute path or the pattern that matched it, and every document reports it as a listed program's id.
The entry is replaced in place by its matches, sorted by path, each document's named cases in document order, so the program order, and every document, never depends on the order the file system lists a directory in.
A pattern entry takes no `id`; an id that a listed program or another entry's match also gives is an error (`duplicate program id`, naming both entries).

A pattern is components separated by `/`: a literal name; a glob of literal characters, `*` (any run of characters) and `?` (one character); or exactly `**` (zero or more directories; a trailing `**` matches every file below).
It is relative to the manifest's directory; `.` and `..` components, empty components, `\`, and `[`, `]`, `{`, `}` (no classes, alternatives or escapes) are refused.
A `files` pattern has at least one wildcard (one program text is `file`); a `cases` pattern may name one case document by its path, since no other key names one.
A wildcard never matches a name that starts with `.` (the cache directory `.kink-flow/`, editor and version-control files): `**` never enters one, and a glob matches one only by its own literal first `.` (`.cases*`), as a literal component may name one;
`**` descends into real directories only, never through a link, while literal and glob components follow links.
A match is a regular file, links followed, or a link that does not resolve, which is refused when it is read, so a case never disappears silently; a directory is no match, and a named pipe, socket or device the pattern matches is an error, since reading one can block for good.
A name that is not UTF-8 is an error when the pattern matches a path through it, since no id can name that match, and is ignored otherwise.
A pattern that matches nothing is an error, not an empty corpus: a typo or a run in the wrong directory would otherwise judge every mutation by no program.

`files` takes `start_sort`, `variables` and `inputs` beside it (`file` and `text` are the matches').
`cases` takes no other key but `stop_count`: a match is a case document, the document `krs run --case` reads, so the document is the whole case in every tool.
A document of one case holds the case's typed inputs under `[inputs]` by input name and the end it expects under `[expect]` ("Expectations", below), and no other top-level key.
A document of named cases holds only `case`, the list of its cases: an array (`[[case]]` tables) of named cases, each a table of `name`, `inputs` and `expect`, and of includes, `{ "$data-file" = "path" }`, each naming a `.toml` or `.json` file whose document is such a list (an array, or a table whose one key is `case`), whose cases stand at the include's place; `case` may itself be an include.
A name is a nonempty string that no other case of the document has, the included files' cases included, so that the document's path and the name identify the case; the cases are programs in document order.
A case's `run`, how `krs run --case` runs it on its own, is refused, in a case and beside `case`: kink runs every program as the corpus says (`[stop]`, `stop_count`, `[budget]`), and the ends a kill compares are those of that one observation.
A `stop_count` beside `cases` is not part of the case but of how the corpus observes it ("Where a run ends"), and applies to every case the entry matches.
A value many cases share is written once in a file the documents include, through the encoding.
The paths a case document's inputs name are relative to the document's directory as matched, not that of the file a link leads to, which is the directory `krs run --case` resolves them against for the same path; those an included file names, its includes' and its cases', are relative to that file, links resolved.
The document and its included files are read when the manifest is, inside the manifest's directory by the rule a program file is read by; a document that cannot be read, is no TOML, has another key, an `inputs` that is not a table, an unnamed case, a name given twice, an include that includes itself, directly or through others, or a list of no case is a manifest error naming its program and the position.
The last component of a `cases` pattern must end in `.toml`: kink hands typed inputs to the front end's decoder as TOML values, so it reads case documents in TOML, and an included JSON file as TOML values, refusing JSON's `null` and an integer outside TOML's 64-bit range, which have none.
At the K level, which has no decoder, each case with inputs is refused as a listed program with `inputs` is (`inputs`/`typed-inputs`).

### Declared patterns

A corpus declares the patterns `query` and `fuzz --pattern` ask ("Checking a pattern", below) in `[[patterns]]` entries, as it declares its programs in `[[program]]` entries:

```toml
[[patterns]]
files = "patterns/*.toml"     # each match is a pattern list ([[pattern]] tables)

[[patterns]]
krs = "sm83-patterns"         # a KRS patterns package, which only the krs front end compiles
```

Each entry has exactly one of `files` and `krs`, and no other key; an entry with both, with neither, or with another key is an error naming it (`patterns[1]`, `patterns[1].id`).
- `files` is a pattern with the grammar and the matching rules of a `[[program]]` glob ("Programs from a pattern", above), relative to the manifest's directory. As for `cases`, it may name one list by its path without a wildcard, and its last component must end in `.toml`, since a pattern list is a TOML document. A glob that matches nothing is an error, not an empty list of patterns, and a list two entries match is an error: a list is declared once.
- `krs` names a KRS patterns package. Its patterns are compiled by the front end that compiles KRS (`krs kink query`, `krs kink fuzz --pattern`), which hands them to kink-flow each with the item, file and line it is written at, after the checks a list's `[[pattern]]` passes (an empty field, `expect` beside `programs`, the rules of `steps`): a front end gives each pattern as written, and kink-flow's one check makes the entry. The front end is asked for a package only when a command assembles the declared patterns and reaches its entry, so a command that names a list, and every command that asks no pattern, builds no package. A package the front end cannot build, or one of whose patterns the checks refuse, refuses the entry with the reason. kink-flow compiles no KRS package, so its own commands refuse such an entry (``patterns[1].krs: a KRS patterns package, which only the krs front end compiles: run `krs kink query` ...``) rather than skip a declared obligation. A package two entries name is an error.

The globs are matched when the manifest is read; the lists are read only by the commands that ask patterns, inside the manifest's directory by the rule a program file is read by.
The corpus's patterns are, in order: the entries as written; within a `files` entry, the lists it matched, sorted by path; within a list, its `[[pattern]]` tables in file order; within a `krs` entry, the package's patterns as the front end gives them.
So the order never depends on the order the file system lists a directory in.
A pattern's id is the one its author wrote, with no prefix naming its list: moving a pattern from one list to another keeps its id, its cached answers and its `[query]` lock row.
An id two patterns of the corpus give is an error naming both (``pattern "three": duplicate pattern id: patterns/a.toml pattern[0] and more/b.toml pattern[1] both give it``), and an error of a list's own names the list (`bad/c.toml pattern "a".label: unknown key`).
`[[patterns]]` is in no digest or key: a pattern decides no result, outcome or verdict, so declaring or editing patterns reruns no program and moves no `run` or `coverage` record.

### Expectations

A case's `expect` states the end the specification computes for it, as the front end writes an end (the krs front end: `krs run --case`'s expectation, a halt, the cells by Rust field path and the cells compared).
kink reads none itself: the front end's renderer of ends (`EndRenderer::read_expectation`, `check_expectation`) reads it, so a case with `expect` is refused at the K level (`inputs`/`typed-expectation`), and one whose expectation the front end refuses is refused (`inputs`/`expectation-value`), before it runs.
After the baseline runs, the renderer checks the expectation against the baseline's ends, and the case's row in the `coverage`, `run` and `query` documents carries `expectation`: `{verdict, detail, difference}`, `verdict` `met` (every end agrees with it), `unmet` (the front end's document of the first difference in `difference`) or `inconclusive` (`detail` says why: the baseline is not `comparable`, or the expectation states what kink does not observe of the case).
`detail` of a met or unmet verdict says how the check compared what kink does not observe in full: under `[stop]` an end is stuck or stopped at a rule of the stop, which the ends do not say, so the krs front end compares only the cells of an expectation of either halt (unmet when they differ, inconclusive when they agree, since met is agreement on the halt as well) and finds an expectation of another halt unmet at the class, since no end has it.
In a definition that declares ends, an expectation may state the declared class of a stuck end, `class`, `end` and `reason` ("Declared ends"), each compared only where it states it, as `krs cases` compares them: without `[stop]` the krs front end reads each baseline end's class from the definition's own end functions before it compares, and a class it cannot decide (or ends of both classes) makes the check inconclusive; under `[stop]` the halt, and so the class, is not observed, as above.
`check` runs nothing: it checks each expectation against the case's current result record, and is inconclusive for a case without one.

A baseline that misses its own expectation is a finding about the specification against the reference the case was written from; it is reported, and the case is kept.
Every kill by the case is still a difference between a mutant's ends and the baseline's, which is what a kill means whatever the case expects, so no verdict or status depends on an expectation.
Only `coverage`, which asks whether each baseline meets its expectation, exits by it: 1 for an `unmet` one, 3 for an `inconclusive` one ("Exit status").
No run depends on one either: it is in no digest, no cache key and no stored record, and every command that reports it checks it again from the baseline's ends.

Defaults:

| Key | Default | Note |
| --- | --- | --- |
| `spec.syntax_module` | none | k-rust then uses `<main_module>-SYNTAX` if it exists, else the main module (a kompile warning). |
| `spec.include_dirs` | `["."]` | The manifest's directory. |
| `spec.md_selector` | `"k"` | |
| `spec.assume_joined` | none | The findings of the definition's full critical-pair check you accept as premises (fz26 KINK-BASELINE-FINDINGS; kink's `trust.md`, "What a kill trusts"), each by the name `coverage` prints in `data.findings` (k-rust-backend `data_term::names`: k-rust-fuzz's `definition-findings` name, byte for byte). A name is the finding's kind, its sentences and a digest of the compiled sentences it is about (KINK-FINDING-NAMES): `root:A,B#D` (two equations at the root, either order read), `self:A#D`, `inner:A,B@1.0#D`, `hook:A#D`, `equation:A#D`, `precondition:A#D` or `precondition:KIND:SYMBOL..#D`, each sentence by its K label (`id:UNIQUE_ID` for an unlabelled one, `overload:G:L` or `witness:...` for a generated one; under krs by the KRS item that wrote it, `crate::plus_zero`). It holds no position, so a line inserted above the named equations, a reformatting or a renaming of variables leaves it naming the same premise; an edit of the sentences themselves, or of the declarations of the symbols they apply, changes the digest. A premise assumes the findings whose name is byte-equal to it; anything else refuses the specification (stage `assume-joined`) with one reason per name: `malformed` (no name; refused at decode, key `spec.assume_joined[i]`), `position-name` (a name of the former grammar, `FILE:LINE:COLUMN,...@POSITION`, with the names of the findings at that position now), `unnamed-sentence`, `no-digest` (with the full names it reads as), `changed` (the sentences changed: the new name, to review again), `no-finding`, `decided` (a decided or genuine finding, or one the check now joins) or `ambiguous`. The refusal's `reason` is the first refused name's, and its `detail` gives each refused name with its reason and what to write; every refusal involving an `id:` sentence suggests a label. A k-rust release that changes how definitions are internalized refuses every premise once with its new name. With a finding left unnamed, no end of the definition is data: every mutation is `unknown` (`baseline-findings`), no comparable program can kill, and no query `no` is given. The list is in the specification digest (when not empty) and every document prints it (`data.assume_joined`). |
| `budget.time_ms` | `10000` | Wall-clock bound of one program run; must be positive. It decides no verdict: a run it stops is cancelled, and is reported as not decided on this host ("What decides a verdict"). |
| `budget.max_depth` | `100000` | Rewrite-depth bound of one program run; must be positive. A run is never unbounded. |
| `budget.work_factor` | `5` | `k`, the work budget of a mutant's run of a program, in the backend's polls (k-rust `max_polls`: its interruption points, counted inside a step too, each solver query once): at most `max(k × P, P_max)` polls, where `P` is the polls of the program's baseline run (its row's `polls`) and `P_max` the largest `P` of the corpus's comparable programs (the run document's `poll_floor`); must be positive. The floor keeps a program whose baseline is cheap from being cut before it has done the work of the corpus's most expensive baseline, and a mutant that never ends, by a loop of states or inside one step (a function equation that applies itself to a growing argument), costs at most `k` program-worths. A mutant that runs past it is `unknown` on that program, with a cause naming the polls and the bound (`the mutant's run used more than 5 × the baseline's 1234 polls (6170), its work budget ...`), long before `time_ms` would stop it, unless the part it ran already holds a final configuration the baseline's program never ends in: then the program kills it one-sidedly (re-pin L1-2, decision 6; kink's `trust.md`, "What a kill trusts"). A cut never makes a verdict wrong, so `k` decides how many outcomes are decided, never which way one goes: it is a cost and completeness setting. The count is a function of the request and the definition, so a cut outcome is cached, locked (the lock's `work_factor` line) and checked by `--locked` like any other. It never bounds a baseline run; `budget.baseline_max_work` does. A chain pattern's run (`query`, "Chains") is a run of the program other than its baseline too, and has the same bound, so a chain that can never complete costs at most `k` program-worths, and one the bound cuts is a cached `unknown`. |
| `budget.baseline_max_work` | absent | The most states one baseline run of a program may visit across all its paths (k-rust `max_work`), and so one run of the baseline's definition that `query` makes (a stopped run, and a chain's run beside its work budget, whichever bound it reaches first); must be positive. A bound only stops a run: a baseline it does not stop is the run without it (same row, same `run_sha256`, same work `W` for `work_factor`), and one it stops is `unknown`, with the bound in its cause. Unlike a `timeout`, which depends on the host's load, such an `unknown` is a function of the result key, which names the bound, so it is cached. Absent: baselines are bounded by `time_ms` and `max_depth` only, and a program that never ends is a `timeout` in every command. It has no default because any value turns some baseline that completes today into `unknown`; the right value depends on the corpus's programs. |
| `budget.smt_resource_limit` | `370000` (kink-native `SMT_RESOURCE_LIMIT`) | The Z3 resource units of the first attempt of every solver query of a run, the baseline's and each mutant's; each of the 3 retries of an undecided answer gets twice the previous units, and no attempt is bounded by the clock. Whether a query is decided is then a function of the query, this budget and the Z3 build, never of the host's load, and the budget enters every cache key with the Z3 build. The default is about what Z3 5.3.3 counts in 125 ms (k-rust `DEFAULT_SMT_RESOURCE_LIMIT` states the calibration); a build that counts at another rate reaches it after another time (Z3 4.16.0 after about 1.2 times it, Z3 4.12.5 after about 0.4 times it), and what it decides there is known only from runs on that build. Must be positive and at most 536870911, so that the last retry's eight times it fits in 32 bits. |
| `program.start_sort` | the sort of `$PGM` | |
| `program.variables` | none | Every configuration variable other than `$PGM` must be given, here or under `inputs`, unless a front end gives it a default (above); streams default to empty (`$IO` to `"off"`, `$STDIN` to `""`). A variable's text is read with the rule every tool reads it with (k-rust `variable_reading_modules`): with the syntax module's grammar first wherever that module has the variable's sort, then with the main module's, so one text denotes one term in kink, krs-exec, krun's `-c` and a `fuzz` campaign. On a definition with stream cells a program may not bind `$IO` (refused at `inputs`, reason `stream-mode`): with IO off the stream cells hold the text printed and the input not yet read, so a final configuration states the program's output. |
| `program.inputs` | none | Typed inputs, read only by a front end's decoder (above). |
| `program.files`, `program.cases` | none | A pattern of program texts or of case documents (above, "Programs from a pattern"); at most one, in place of `id`. |
| `result.cells` | absent | The cells the programs' second slot compares, by K name (below, "Which cells are compared"); a nonempty array of distinct nonempty names. Absent: every cell the specification does not declare `unobservable`. In the specification digest when present. |

### Which cells are compared

A program's run is compared by two oracle slots: the exit stop (no exit-code cell), then its final configurations.
A cell declared `unobservable` (`<w unobservable=""> 0 </w>`; KRS does not accept its spelling `#[k::cell(unobservable)]` yet) holds state no use of the definition may observe, so no kill may rest on its content.
The second slot therefore compares every cell except the unobservable ones:
it is `cells`, the final configuration with the content of each cell left out replaced by `\top` of its sort (kink-campaign `StateProjection::Cells`), exactly when some cell is left out,
and `whole-term`, the whole final configuration, otherwise.
Either way `<generatedCounter>`'s content is erased, as before.
Two final configurations agree under `cells` exactly when they are equal outside the cells left out, so a kill is a difference some compared cell shows, and a survivor survives relative to the cells compared: every document names them (`result`, below).
A cell wrongly declared unobservable can hide kills, never make one.
The projection is defined on every configuration, so the one-sided kill applies to a `cells` slot as to `whole-term` (kink's `trust.md`, "What a kill trusts").
Whether an end is data is still judged on the whole end: an unobservable cell holding a non-value makes the slot `unknown`.

`[result] cells` narrows the compared cells to the cells named and the cells inside them.
A name is a cell's K name, whether or not the cell lies inside a `?` or `*` cell: a cell inside one is compared in each instance, with no index.
A Map collection holds each instance by its key, the instance's key cell, so a cell compared inside a Map's instances is compared per key: the key of every Map that encloses a named cell is compared too.
Every other cell is left out, except the cells that enclose a compared one; an unobservable cell inside a compared cell is left out too.
A manifest can narrow the compared cells, never widen them past the specification's statement.

A cell inside a `?` or `*` cell is left out of each instance, at its position relative to the instance (kink's `trust.md`, "What a kill trusts", the bullet "Unobservable cells"): an optional cell's presence is compared, a Map's instances by key, a Set's as a multiset of the projected instances (two instances the projection makes equal stay two), and a List's in order.
A `?` or `*` cell can itself be left out, the whole optional cell or collection.
A Map's key is never left out: each element holds the key as its first argument beside the instance, and the projection leaves out positions of the instance only, so the key's content would still be compared in the element.
The specification is refused at stage `result`, naming the cell, when
an unobservable cell is a Map's key or lies inside one (`map-key-left-out`: drop `unobservable` from it, or compare no cell inside the Map so that its `*` cell is left out whole, by marking it unobservable without a narrowing, or by narrowing to cells outside it; under a narrowing that names a cell inside the Map, marking the Map unobservable is refused as `result-cell-unobservable`), unless the cells left out include the whole collection,
an unobservable cell production is placed by no configuration (`unobservable-cell-outside-configuration`),
`[result] cells` names no cell of the configuration (`result-cell-unknown`; `<generatedTop>` and `<generatedCounter>` are compilation's, not the specification's),
or names an unobservable cell or one inside an unobservable cell (`result-cell-unobservable`);
`cell-layout` (the configuration's cells cannot be placed in its KORE terms) is a k-rust defect to report.
The layout is a premise only of leaving a cell out, so a specification that declares no unobservable cell and names no `[result] cells` is never refused with `cell-layout`: its slot is `whole-term`, and `compared` is null when its cells cannot be placed.

The `check`, `coverage` and `run` documents (and so `report`) carry `result`, `{slots, compared, not_compared, unobservable}`, null when the specification is refused:
`slots` the slot names (`["exit-stop", "whole-term"]` or `["exit-stop", "cells"]`),
`compared` the outermost cells compared (the named cells and the keys of the Maps that enclose them when the manifest narrows them; a cell listed is compared except for the cells of `not_compared` inside it, in each instance; null for a `whole-term` slot whose cells cannot be placed),
`not_compared` the cells left out, and `unobservable` every cell the specification declares unobservable, each in configuration order.
Where the slot is `cells`, a program's recorded final configurations and ends are the projected ones.
A mutation that only adds or removes `unobservable` compiles to the same KORE and is `equivalent`.

### Where a run ends

A definition that never ends on its own (a console that runs frame after frame) has no end of its own to compare; the observer names one.
`[stop]` names it: every program's run ends at its `count`th stop event, a step by a rule of `before` or `after` that is its state's one successor (before the step for a rule of `before`, after it for a rule of `after`), or where the definition's own run ends, whichever comes first.
The ends of this truncated system are what both slots compare, so a kill is relative to the stop: two definitions whose truncated runs end alike are not told apart, whatever they do after the stop.
A program's `stop_count` replaces `count` for that program (the count is a property of the observation of one program, a ROM that needs more frames than another), while the rules are the corpus's.

| Key | Meaning |
| --- | --- |
| `before`, `after` | The rewrite rules a path stops before or after, each by its exact K label (`MODULE.label`, as `coverage` names it); at least one name in all, none twice and none in both, kept sorted. A KRS corpus names them by KRS item or label, which the krs front end maps to the labels before kink-flow reads them. |
| `count` | The stop event a path ends at, a positive integer; default 1. |
| `stop_count` (in `[[program]]`) | That program's count, a positive integer; refused without `[stop]`. Beside `files` or `cases` it is the count of every program the entry matches. |
| `when` | A stop condition, `{function, cells, observer}`, `observer` optional: a stop event is then an arrival whose stop state the condition holds of. Only a front end that reads the definition's values states one (`krs kink`, with KRS's spellings); kink-flow's own front end refuses it. A case document names it `run.stop_when`, which `[stop]` refuses with a hint toward `when`. |

Each name must label a rewrite rule of the specification, or the specification is refused at stage `stop`, reason `stop-unresolved`, naming the side and the name: an equation's label, a `UNIQUE_ID` or a suffix of a label selects no step.
A backend that cannot list the specification's rules refuses it at stage `stop` with reason `backend-error` instead, since the names were never checked.
A mutant on which a name labels no rewrite rule (the edit deleted the rule, or made it an equation) is `not-admitted`, reason `stop-unresolved`: the observation the stop states is not defined on it, and running it without the stop would compare ends of two different observations.

kink runs a program to its count in one request (kink-campaign `Stop`): k-rust counts each path's stop events and ends the path at its `count`th, taking each earlier one as any other step.
`budget.max_depth` bounds the whole path from the program's initial configuration, as without `[stop]`, so it must cover every step up to the last stop, not only those between two stops.
A stop leaf is an end of the truncated system by a fact of its own path, so it completes a path as a stuck leaf does, and a poll-bound mutant run (one its work budget cut) can kill one-sidedly at a stop leaf (kink's `trust.md`, "What a kill trusts").
A step of a named rule that has another successor stops nothing in k-rust; a run that went on past one is excluded (`passed-stop`), so every verdict is a fact of the system in which every step of a named rule is a stop event.
A mutant that never reaches its last stop meets `max_depth` or its work budget (or `time_ms` first, under a large `work_factor`), so its program is `unknown` (or `timeout`) for it (a one-sided kill still possible); one that ends on its own first has another end.

Under a stop before a rule, a program whose count is 1 never takes the rule's step, so an edit of only the rule's right-hand side or `ensures` changes no end of it and survives there; a count above 1 takes the rule's earlier steps, and an edit of its left-hand side, `requires` or attributes moves the stops.
`check --mutations` warns of an edit of such a rule (`stop-hides-edit`), and a survivor that edits one says so in the run document (`stop_hides_edit`).
It warns instead of a mutation that deletes a rule the stop names (`stop-rule-deleted`): `run` does not admit that mutant (`stop-unresolved`).

The `check`, `coverage` and `run` documents (and so `report`) carry `stop`, `{before, after, count}` with `counts`, each program's own count by id, when a program has one; it is absent without `[stop]`.
Each `ends` entry of a comparable program run with a stop has `halt`: `stop` where some path of the run reached the end at its last stop, `own` where every path that reached it ended on its own.
It is evidence for a reader, never compared: a state set that merges a stopped path with a stuck one at the same configuration keeps one leaf of the two, so which halt it reports for that end can depend on the order the run explored them.
The stop keys what it changes: each program's result key holds `stop`, its rules and that program's count, and the tier-1 context holds the document's `stop`; both are absent without `[stop]`, so a corpus without a stop keeps its keys.
`query` answers a corpus with `[stop]` through each program's stopped run ("Checking a pattern", "A corpus with `[stop]`"): a state past a path's last stop event is no state of the case, so a pattern only such a state matches is a `no`, and a passed stop, a condition that refused or was left undecided, or an undecided solver answer makes the answer `unknown`.
`fuzz` runs every job of a corpus with `[stop]` on the truncated system ("Killing a survivor with `fuzz`", "A corpus with `[stop]` or `[observe]`"): every request of its campaign carries the stop's rules and the template's count, so a case's coverage, reach, hit and kill are those of the runs the corpus states.
It refuses a stop condition (stage `stop`, reason `unsupported-verb`): its campaign runs its cases on k-rust-fuzz's wire route, which carries no callback to ask the condition at each arrival.

`[stop] when` names a stop condition: a function of named cells of the stop state, the state before a `before` rule's step or the successor of an `after` rule's, evaluated in one fixed observer definition (the named one, else the baseline) for the baseline and every mutant alike (kink-campaign `StopWhen`).
An arrival, a step by a named rule that is its state's one successor, is a stop event only where the condition holds, and `count` counts events; every other arrival is taken as any other step.
The names are the front end's: `krs kink` names the function by KRS path, the cells by Rust field path and the observer as `PACKAGE:DEFINITION`, resolves them as `krs run --stop-when` does and refuses a condition `krs run` refuses at stage `stop`, reason `stop-condition-unresolved`.
kink-flow's own K front end reads terms, not values, and has no observer, so it refuses `when` at stage `stop`, reason `unsupported-front-end`.
A program whose run's condition is undecided at an arrival, or has no value there, is `unknown` with the cause `stop-condition`, on a mutant, and not judged on the baseline (class `unknown`, never cached: an undecided answer can be its evaluation's budget).
The condition reads every side's cells as the specification declares them, and refuses a term with a part the specification does not declare, so a mutant that declares a sort or symbol the read cells reach otherwise than the specification (or a new subsort of a reached sort between two sorts the specification declares) is `not-admitted`, reason `stop-condition-incompatible`; a constructor added under a new name, or one removed, is admitted.
Under a condition a stop rule's step is taken wherever the condition fails, so `stop-hides-edit` is given for a rule the stop stops before exactly when the coverage decides and no comparable program fired the rule (each arrival at it was the event that ended its path).
The documents' `stop` gains `when`, the condition's identity as the front end resolved it (for `krs kink`, `{observer: {definition, definition_ir}, function, cells}`, with `subject: {definition_ir}`, the baseline's digest, whose declarations read the cells, beside a named observer), and so do each program's result key and the tier-1 context; a stop without a condition keeps its keys.

The tool supplies everything else: the k-rust revision is the build's (every output's `k_rust_revision` is k-rust's build identity, `k_rust::build_identity`: the version of the in-repo k-rust kink is built with and a digest of its sources; the semantics identity and the cache keys name the version, `kink_native::K_RUST_REVISION`, beside the executable's digest),
and the below-floor conformance cases (kink-corpus `BELOW_FLOOR`) are refused for the entry and for every file the load reads (stage `refused-case`).

### What a run observes

A program that never ends has no end to compare, but its run still shows what it does on the way.
`[observe]` declares observation channels, and every run is compared by them besides its end, so such a program is a case, compared over the prefix its budget explores (kink-campaign `Observe`; kink's `trust.md`, "What a kill trusts").

```toml
[[observe.point]]
name = "clock"
before = ["CONSOLE.tick"]
stutter = "collapse"
cells = ["n"]

[[observe.log]]
name = "out"
cell = "out"
at = ["clock"]
```

A point class (`[[observe.point]]`) samples the state at the steps of named rules.
Its point event is a step of a path by a rule of `before` or `after` whose successor is defined; the event observes the state before the step for a rule of `before`, and the normalized successor for a rule of `after`.
The class's channel is the sequence of its events' contents in path order, each content the named cells' contents as the cells hold them.
A log (`[[observe.log]]`) reads a `List` cell at the events of the named classes and where the path ends; its channel is the concatenation of the items the cell appends, each item an element.

| Key | Meaning |
| --- | --- |
| `name` | The channel's name, unique among the declaration's channels. |
| `before`, `after` (point) | The rewrite rules whose steps are the class's events, each by its exact K label; at least one name in all, none twice and none in both. |
| `stutter` (point) | `collapse`: an element equal to the previous one is dropped, so only changes are observed; `count`: every event is an element, so how many events there were is observed. Required: which is meant is a property of the specification. |
| `cells` (point) | The cells whose contents, in this order, are each event's element, by K cell name: each a leaf cell of multiplicity 1 below cells of multiplicity 1, not `unobservable`. |
| `cell` (log) | The `List` cell, by K cell name. |
| `at` (log) | The point classes at whose events the log is read; it is also read where the path ends. |
| `observer`, `views`, `components`, `when`, `element` | Functions of an observer, evaluated on the cells' values: only a front end that reads values can state them. `krs kink` resolves them and sets them on the manifest (`FlowManifest::with_observe_functions`), and then gives every content, filter and log element, its functions' identity named in `observe.functions`; a filter not known at a point, and every filter of a request the front end gives no evaluator, opens its class's channel there; kink-flow's own front end refuses them at stage `observe`, reason `unsupported-front-end`. |

Positions are where elements are read, not what they are: which rule of a class fired, and the relative order of two classes' events, are not observed.
To tell two rules apart, put them in separate classes, or observe a cell one of them writes; to observe an order, put both rules in one class.

The specification is refused at stage `observe` when a class names a rule no rewrite rule is labelled with (`point-unresolved`; an equation's label names no step), when a cell states no observation (`cell-refused`: a cell the configuration does not have, an `unobservable` one, one inside a `?` or `*` cell, a log cell that holds no `List`), and when the backend cannot list the rules (`backend-error`).
A mutant on which a class's rule labels no rewrite rule is `not-admitted`, reason `point-unresolved`, so no kill rests on an edit of a label; `check --mutations` warns of a mutation that deletes such a rule (`point-rule-deleted`).
A mutation can state that a rule never fires as `requires false`, which keeps the label and is judged.
A mutant whose declarations could make an observed cell's content denote another value (a sort or symbol the observed cells reach declared otherwise, or a constructor of one heading an axiom) is `not-admitted`, reason `observation-incompatible`.

A path that ends at a determined end closes every channel with END, a path whose last step is undefined closes them with UNDEF, and a channel stays open where its path was cut by a bound, and at an undecided element (under `count`, an undecided element is one unknown position, and the elements after it are still compared).
A baseline run that `budget.max_depth` or `budget.baseline_max_work` cuts, every other path of it complete, has no end: its program is `comparable-prefix`.
Its end slots compare nothing, and each channel is compared up to its horizon, the number of elements the baseline recorded before the channel's open point; a horizon is a function of the result key, so the class is cached.
Every horizon names why its channel opened, its `opening`: `bound` where a bound cut the path, `undecided-element` at an element that is no value (or a log cell that holds no list of known items), `branch` on every channel of a record of a run with several paths, at 0, since its prefix sets hold what it observed (below), `undecided-path` where the path's states or end are not decided, and, in a survivor's horizon only, `cycle` (below).
Only a `bound` horizon moves with the budget; a channel of a baseline that ended can be open too, at an undecided element, and so can a prefix program's before its bound.
A program whose baseline the clock stopped stays `timeout`, since its horizon would depend on the host.
`coverage` exits 0 for a `comparable-prefix` program: it answers what the baseline computes for the declared observation, up to its horizons.
A prefix program none of whose channels kept an element within its budget or closed by a cycle observed nothing, so no mutant can differ from it within its horizons: it is `unknown`, its cause beginning `observed-nothing` and naming why each channel opened, and `coverage` exits 3 for it as for any program it cannot compare.
An element kept undecided under `count` is an observed event, so a program with one is `comparable-prefix`.
An end expectation on it is `inconclusive`, since it has no end.

A path that returns, before it has several successors, to an earlier state of itself with nothing new observed closes each channel not yet open or past the baseline's horizon by a cycle (`closed = "cycle"`): the path runs forever and adds no element, so the channel is complete and has no element at its length, ever.
This proves divergence, which a bound never does.
k-rust recognizes the return only between states whose configurations are the same ground term with no constraint, with equal stop counts, effects and console, so a symbolic state is never compared; among the states reached since the channels last changed it keeps a fixed number (kink-campaign `CYCLE_STATES`), and a return to a state past them is not recognized.
A baseline closed so is still `comparable-prefix` (its run goes on to its bound as without observations), and a channel closed by a cycle has no horizon.

A mutant is killed on the channels at the first channel and index at which both sides' elements are decided to differ, END, UNDEF and a cycle's silence being elements; no element past either side's open point is read, so a budget never kills.
An undecided element (under `count`) is a content whose value is not known: it differs in every model from END, UNDEF and a cycle's silence and from no content, so a mutant whose path ends where the baseline kept an undecided element is killed by its END.
A channel closed by a cycle has no element at its length, ever: a mutant that idles forever where the baseline still emits, or ends, is killed there, and so is a mutant that emits, ends or is undefined past a baseline channel closed so, while a mutant closed alike at the same length agrees with no horizon.
The mutant's run stops at that difference, at its own return, or, on a prefix program, once every channel has reached the baseline's horizon or opened.
A mutant that agrees with a prefix program up to every horizon survives, with each horizon: the row has `horizon`, `[{program, horizon: {<channel>: {elements, opening}}}]`, its action says that the mutant may differ past it, and `--output verdicts` renders it, so a survivor that rests on a prefix says so.
Against a baseline channel closed by a cycle, a mutant whose channel stopped being observed past every baseline element (its path cut, or its channel opened) agrees up to the baseline's elements, with the opening `cycle`.
The action follows the openings: it asks to raise the bound only when some horizon's opening is `bound` or `cycle` (where the mutant's path may have been cut), and otherwise for another program, since a larger budget reaches the same horizon.
In `coverage`, an `undistinguished` flip whose search rests on a horizon has the row's `horizon` too.
An agreement up to horizons that are all 0 observed nothing, and is `unknown`.

Each executed entry's `slots` has `observations` after the end slots: `position: {channel, index, at_end}` where it distinguished (`at_end` when the difference was read where the mutant's path ended), `horizon` (`{<channel>: {elements, opening}}`) where it agreed up to the baseline's horizons, and `cause` where it was unknown.
The baseline's record keeps 8 bytes of each element's digest, not its value, so the evidence of a kill only the channels decided is re-derived: a capture run runs the baseline's request again, with a probe that ends the path at the reported element, and the element read there must be the recorded one (a content with the recorded digest, or an undecided element where the record kept one undecided), and the two elements must differ in every model, or the mutation is an `error` with reason `observation-capture:<program id>`; the mutant's element is its probe's.
That evidence is kink's own (`kink-k/1`): `{format, position, baseline: {element}, mutant: {element}}`, each element `{cells: {<cell>: value}}` for a class, `{item: value}` for a log, each value printed as K text, or `end`, `undefined`, `cycle` (the side's channel was closed by a cycle there) or `undecided`.
A `killed` outcome record keeps it, as it keeps an end difference, so the capture runs once per kill; a test whose ends also distinguished keeps its end evidence.

A program whose run has several paths is compared by each channel's prefix sets over its paths (kink's `trust.md`, "What a kill trusts"): a mutant is killed by a prefix one side has and the other lacks, at an index to which the lacking side is explored on every path, and its slot's `position` has `outside`, `mutant` where the mutant's prefix is outside the baseline's set and `baseline` where a real baseline prefix is outside the mutant's.
No one baseline path holds such a difference, so no capture run re-derives it: its evidence is `kink-k-sets/1`, `{format, position: {channel, index, at_end, outside}, mutant: {element}}`, the mutant's element at the index where its prefix is outside and `absent` where the baseline's is.
A baseline record of such a run holds `paths`, `{paths, real, channels: [{prefixes, complete_to}]}`: the number of paths, whether every leaf of the run is real and clean and every path the run stopped exploring is known up to where it was left, and per channel the 8-byte chain truncations of each index's prefixes and the horizon to which every path is explored (null where every path is).
Its `channels` hold no element, each open at 0 by `branch`.
A path the run stops exploring with no leaf of its own (a pending state the work budget drops) counts up to where its parent split, the part a leaf of the run stands for, and bounds its channels there; one no leaf stands for bounds them at 0 and makes the record not real (kink's `trust.md`).

The `check`, `coverage` and `run` documents (and so `report`) carry `observe`, the declaration as every run compares by it (`{points: [{name, before, after, cells, stutter}], logs: [{name, cell, at}]}`); it is absent without `[observe]`.
Each program row of a corpus with `[observe]` has `observations`, `{channels: [{name, elements, closed, open}], horizon}`: the number of elements its baseline recorded per channel, `closed` (`end`, `undefined` or `cycle`) or `open` (`{index, opening, reason}`), and each open channel's horizon, `{elements, opening}`; a channel closed by a cycle has none.
For a run with several paths it is `{paths, real, channels: [{name, complete_to}], horizon}` instead: the number of paths, whether the record is real, each channel's horizon to which every path is explored (null where every path is explored to its end), and `horizon` each such horizon by channel name.
The declaration keys what it changes: each program's result key and the tier-1 context hold `observe`, absent without `[observe]`, so a corpus without one keeps its keys.
`query` admits a corpus with `[observe]` and ignores the declaration, and its document says why (`observe`, `{declaration, ignored}`): a pattern query asks which states one definition's run reaches, while an observation channel compares two definitions' runs and changes neither which states a run reaches nor where it ends.
Its one effect on a query is indirect: a program a bound cuts is `comparable-prefix`, not `comparable`, and a `no` keeps requiring `comparable`.
`fuzz` admits a corpus with `[observe]` for its single-definition jobs (rule, coverage-gap and pattern jobs), which run their cases as without it and say why (`job.observe`, `{ignored}`): they ask what one definition's run reaches, matches or fires, which no channel changes, and a rule or coverage-gap witness is confirmed when `coverage` counts it, `comparable-prefix` included (the search itself finds `comparable` witnesses only).
It refuses a kill job there (stage `observe`, reason `unsupported-verb`): its campaign compares the two definitions' ends, while a kill of such a corpus is a decided difference of a channel, so a search judged by ends would look for another kill than the one `run` judges.

## Exit status

Every command exits with what its caller does next, one of four statuses, as krs's executing commands do:

| Status | Meaning | What to do |
| --- | --- | --- |
| 0 | yes: the command answered its question | rely on the answer |
| 1 | no: the answer is a finding | act on the finding |
| 2 | the question could not be asked | fix the input or the command |
| 3 | no answer | retry with more budget or another approach |

A command that answers for several parts (programs, mutations, pairs of a pattern and a program) exits 2 when one part could not be asked, since the answer is then incomplete; else 1 when one is a finding; else 3 when one has no answer; else 0.
A usage error exits 2 with its message on stderr, then the usage line of the verb the command line names (every command line's shape when it names none) and the command that lists the verb's options: the whole help would bury the message, and the verb's usage line is what a misspelt option, a missing operand or a bad value is corrected against.
Every refusal exits 2 too, and the document names it with its stage and reason: a manifest that does not decode, a refused specification, program, mutation list, lock, mutation, pattern list or template, a failed run, and a cache file or lock that cannot be written.
A `--verify` mismatch (a stored record that differs from the live value) is a finding, 1, in every command that takes `--verify`.
So is a lock a command's `--locked` (`run`, `coverage`, `compare`, `query`) would change: the lock is a stored record too. A lock whose only differences rest on runs the clock stopped is no answer, 3 ("What decides a verdict").

What else is a finding, or no answer, follows from what each command asks:

| Command | It asks | 1 (a finding) | 3 (no answer) |
| --- | --- | --- | --- |
| `check` | whether every verdict the corpus promises is possible before any mutant runs | a program every baseline run of which is `excluded`, or a baseline without data (`spec.baseline_findings`) | none |
| `coverage` | what the corpus covers, whether each program's baseline run can count, and whether it meets its expectation | an `unmet` expectation; an end in no declared class the case does not expect (`undeclared-end`, "Declared ends"); a needless argument (an argued item a program covers, or that is no obligation); a refuted argument (an invariant whose connection or evidence fails, "Argued obligations"); under `--locked`, a coverage lock the command would change (an open obligation is no finding) | a program that is `timeout` or `unknown` (a `comparable-prefix` program is an answer); an `inconclusive` expectation; an end whose declared class is not decided (`end-undecided`); an argued item whose standing is `unchecked` ("Argued obligations") |
| `run` | each selected mutation's verdict, and whether it is the verdict the mutation expects | an `unmet` expectation (`expect`, "`MUTATIONS.toml`"), with or without `--locked`; under `--locked`, a lock the run would change (a stored record that differs from the live value, as a `--verify` mismatch is); a verdict alone is no finding: `killed`, `survived`, `equivalent` and `unkillable` are answers | a mutation that is `timeout` or `unknown`; an `inconclusive` expectation |
| `report` | what the last `run` answered | as that run | as that run |
| `query` | whether each asked program reaches a state matching each pattern, and whether each pattern's obligation is discharged ("Checking a pattern") | a refuted claim (`no` for a program the pattern claims); an `unmet` expectation (`expect = "no"` on a hit); under `--locked`, a `[query]` section the query would change (an `open` or `undecided` obligation is no finding) | an `unknown` answer; an `inconclusive` expectation; under `--locked`, a section whose only differences rest on runs the clock stopped |
| `compare` | whether each implementation ends as the definition does on every program, under each required view, and whether its record of the `[observe]` channels agrees with the definition's up to the definition's horizon, under each required trace view ("Comparing implementations") | a `different` verdict of a required view | a required view `not-compared` with no answer (`several-ends`, `several-paths`, `observed-nothing`, `undecided`, a baseline `timeout` or `unknown`); a required trace view `agree-up-to` a horizon the implementation's answer set; a `timeout` of an implementation with a required view |
| `prune` | which programs are redundant, from what the corpus discharges ("Redundant programs") | none: the report refutes nothing | none: an unknown cell makes the report conservative, and the report it states holds |
| `fuzz` | which hole values of the template are a witness of the job | a witness of a kill job whose mutation expects to survive (it refutes the expectation); otherwise none: a witness and `equivalent` are answers | a search that ended without a witness kink accepts (table under "The document") |

`check`'s warnings, and a case's expectation in `check` and `run`, decide no status: `check` runs nothing and asks only whether verdicts are possible, and `run` asks about the mutations.
A mutation's expectation joins `run`'s status from its row's status on every run, cached or live, whatever the schedule: `run` exits non-zero and prints one line on stderr (`mutation ID: ...`) for each expectation that is unmet or inconclusive, whatever the output format.
In `run`, `invalid-mutation` and `not-admitted` name a mutation its author must fix before it is judged, 2, as does an `error` that is not a `--verify` mismatch (a corpus error that stopped the run, no comparable program, a failed run); a program that times out or is unknown on the baseline only cannot kill, which the mutations' verdicts already show.
`report` exits with the status its document gives as `run` reads it, so that it exits on the answer as the run did; 2 when there is no stored document.

## What decides a verdict

A verdict, a killer and a lock entry are functions of the definition, the corpus, the lock before the run and the counted budgets, never of the host's load.
The bounds that can decide a verdict are counted: `budget.max_depth` (rewrite steps), `budget.work_factor` (a mutant's run, in the backend's polls: `max(work_factor × P, P_max)`, `P` the program's baseline polls and `P_max` the corpus's largest, on by default), `budget.baseline_max_work` (a baseline's run, in states visited), and, under the Z3 profile, the solver's resource units (`budget.smt_resource_limit`, with the Z3 build that counts them); each stops a run at the same point on every host, so the `unknown` it gives is cached under a key that names it.
The work budget counts the work inside a step too, so a mutant whose function equation applies itself for ever, which the clock alone would stop at a load-dependent point, is `unknown` by the budget, the same on every host; an exact self-application (a function applied to the same argument again) the backend decides without it, as a stuck leaf that holds the application unevaluated, which is no value (`open-application`).
A run the work budget cuts is `unknown` (or a one-sided kill the part it ran justifies), never a kill or a survivor it would not be without the budget, so the budget decides how many verdicts are decided, never which way one goes, and the lock names it (`work_factor`): raising it re-runs only the outcomes it cut, since a run it did not cut is the run without it.
`budget.time_ms` is not one of them: it is a wall clock, which only cancels a run, and a run it cancelled has no outcome, since a faster host could have ended it with any.
So a `timeout` is never cached ("Programs and the result cache"), and a cancelled run is reported as not decided on this host, never as a fact about the corpus.

An entry of a lock is decided on this host only when it would be the same whatever each cancelled run would have given; a run the clock cancelled changes no recorded status, killer or obligation (kink-flow `clock`):
- A run the clock stops is a program's baseline run (the program is then `timeout` and not comparable, so it can kill and cover nothing on this host), its run on a mutant (its executed entry is `timeout`), or an argued item's evidence run of a program (the item's `argument_check.evidence.clock_stopped` names it), which leaves the evidence unread there.
- A mutation's status decided before any run (`equivalent`, `unkillable`, a refusal, `error`) depends on no run, and neither does a kill by its recorded killer: that run ended and distinguished.
- Any other kill is still a kill, since the program that killed ended, but the killer is not decided when the clock stopped the recorded killer's run (it could have killed: the killer rule's first case), a run of a program before the killer in the search order, or any program's baseline (that program would be comparable, somewhere in the order).
- Every other status (`survived`, `unknown`, `timeout`) depends on every program whose run on the mutant or baseline the clock stopped, since each could have killed.
- A flip's entry in the coverage lock follows the same rule (`distinguished` is a kill; `undistinguished`, `unreached`, `argued` and an `unknown` of a survivor, unknown or timeout depend on the stopped runs), its row naming the programs whose run on its mutant timed out (`timed_out`).
- An obligation is covered when some comparable program covers it, so a covered obligation is decided, and one that is not depends on every program whose baseline the clock stopped. So is an argued item's standing (its evidence reads the comparable programs' runs), unless it is `text`, and so is a standing one of whose own evidence runs the clock stopped.
- A `compare` row rests on the implementation's run of its program and on the program's baseline and depth-0 runs: where the implementation's run gave no answer (it failed, or its `time_ms` cancelled it) or the clock stopped a definition run, the rows of that implementation and program keep their recorded values ("Comparing implementations").

Where an entry depends on a stopped run, the lock keeps its recorded value: the lock compared and written is the rendering with that value, and the document's `lock.kept` lists each entry kept over another value (`{mutation | flip, recorded, now}`, `{family, obligation, recorded, now}`, `{argument, recorded, now}`), and `lock.clock_stopped` each stopped run some entry depends on (`{program, run: "baseline"}`, `{program, run: "mutant", mutation | flip}`, `{program, run: "evidence", argument}`).
The exceptions are facts the runs that ended decided against the record: a kill where the lock records none (a recorded survivor killed now by a program that ended), a recorded status no run could give, and a row the lock does not have, which is written from the run.
Under `--locked` a lock that differs only in kept entries is not a difference: its `lock.status` is `undecided`, exit 3, and `kink-flow` prints on stderr one line per stopped run and per kept entry, such as `kink.lock: countdown-escapes: the clock (budget.time_ms) stopped the run of countdown on its mutant: its entry is not decided on this host` and `kink.lock: countdown-escapes: kept killed (killer countdown) unverified: this host gives killed (killer one)`; a decided difference still makes it `stale`, exit 1.
Without `--locked` the same lines say what the written lock kept unverified, and the run's exit status is what its rows give.
A lock does not list a covered obligation, so it cannot tell one it recorded covered from one that was no obligation when it was written: after a definition edit on a host whose clock stops a program, a new obligation that shows open stays unlisted, and `--locked` says the lock is not decided, until a host on which every run ends writes it.

## `kink-flow check FLOW.toml [--mutations MUTATIONS] [--cache DIR]`

Admits the specification through kink's admission stages (kink-corpus's `admission` module, the library kink-flow is built on):
`manifest` (this crate: the manifest does not decode), `refused-case` (a below-floor conformance case), `load`, `semantic-input`, `compile`,
`representation`, `declaration-census`, `result` (this crate: the compared cells, above under "Which cells are compared") and `inputs`, then `stop` (this crate: the rules of `[stop]` on the input backend, "Where a run ends") and `assume-joined` (this crate: the definition's full
critical-pair check on the input backend, against `[spec] assume_joined`), then `syntax` (this crate: a front end's syntax selection names one template binder under its axiom's `UNIQUE_ID` and again under its label, reason `binder-selected-twice`; the same binder named twice under one name, with two caps, is refused by `FlowManifest::with_syntax`).
The declaration census passes a hooked symbol whose hook its reference declares with the same argument and result sorts (rule H), or one whose hook the reference does not declare and k-rust has no evaluator for (inert); any other hooked symbol is refused (`vi-t13`).
The reference is k-rust's embedded builtin files and blockchain-k-plugin's `plugin/krypto.md` at `651a2db5` (kink-native `census::KRYPTO_REFERENCE_TEXT`, pinned by digest), so a declaration of one of the plugin's `KRYPTO` hooks with its documented sorts is admitted whichever file or symbol declares it, and one with other sorts is refused, also for a hook k-rust does not evaluate (`KRYPTO.sha512`).
Sorts are compared by name: a builtin sort's name is backed by its sort hook, but the point sorts `G1Point` and `G2Point` are not, so the BN128 hooks are admitted on any sort of that name, and their value is k-rust's reading of the point constructor (the definition's only constructor of that sort with two, or four, `Int` arguments; `docs/compatibility.md` "Cryptographic hooks", which states k-rust's contract for these hooks against this revision of `krypto.md` and is pinned by kink-native's `the_krypto_reference_is_k_rusts_crypto_contract`).
Admission is not a verdict: until k-rust records the values `krypto.md` leaves open on each run, every hook k-rust evaluates stays in the exclusion census, so a definition that declares one has no kill and no `no` (`implementation-chosen-hook`), and `fuzz` refuses it at `exclusions`; a query's `hit` through such a hook stands (query "Answers" below), and rests on k-rust's evaluation as that contract states it (lowercase hex, the ECDSA failure values, the point constructor by signature).
Then each program is admitted on its own (file read: stage `load`; typed inputs: `inputs`/`typed-inputs` or `inputs`/`input-value`; an expectation: `inputs`/`typed-expectation` or `inputs`/`expectation-value`; parse: `inputs`/`parse`;
a program text on a definition without `$PGM`: `inputs`/`stray-program`; other assembly failures: `inputs`/`assemble`; the concrete-state check and the input gate: `inputs`/`input-gate`;
an initial configuration with no value: `inputs`/`initial-undefined`).
A refused specification skips the programs; a refused program never stops the others.

A test's expected result is what the specification computes from its inputs.
When the baseline's initial configuration has no value (an input divides by zero, directly or through a function), the specification computes no start, so the case has no expected result: a kill by it would be false.
Admission runs each program's initial configuration on the baseline to depth 0, bounded by `budget.time_ms`, and refuses it (`initial-undefined`, listing the case's inputs) when that run ends in vacuous leaves only, whether the inputs are text or typed.
The bound is part of the rule: admission runs no step of a program, and a case whose start has a value and whose later step has none is admitted, since that step is the program's behavior, which its run reports.
The refusal needs the run to be evidence: where the initial configuration is excluded (below) or the depth-0 run is (a contradicted `total` claim, ...), whether the start has a value depends on what the definition leaves open, and the program is admitted and reported as excluded instead.
An input whose definedness the definition leaves open (a partial function applied outside its equations) is not refused either: its run reports what it finds.

A mutant's initial configuration is not checked at admission: it is part of what the program observes of the mutant.
Where the mutant's run of a program ends in vacuous leaves at depth 0 only (its start is decided to have no value, as `krs run` reports `undefined`), with no diagnostic and within the time bound,
the mutant computes no start where the specification computes one.
That is an end undefined after 0 steps, compared as a later undefined step is (kink-campaign runner `no_start`):
every state slot holds no end (`exit-stop` `[]`, `whole-term` `final_configurations: 0`), which the baseline's end distinguishes,
and every observation channel is closed by `undefined` at 0.
Where the mutant's start is not decided to have no value (an application no equation reduces, a solver's unknown, a timeout, a backend failure), the program decides nothing, as before.

Beside the data facts, admission reads the definition exclusions of the input backend's load, the facts the campaign runner reads for every run (kink-native `DefinitionExclusions`; kink's `trust.md`, "What a kill trusts"),
and decides for each admitted program whether every run of it on the baseline is excluded before it runs a step:
by the definition exclusion, which excludes every run on the specification, or by the exclusion of the program's initial configuration (it applies a hook whose value the definition leaves open, or it applies a function or operator whose value depends on the short-circuit reading and its depth-0 run, the normalization every run of the program starts with, lists a reading that counts against it).
A rule the short-circuit analysis flags is no definition exclusion: the campaign runner judges each run of such a definition by k-rust's list of that run's short-circuit readings (kink's `trust.md`, the short-circuit bullet), so whether such a program's run is excluded is known only once it runs, and `coverage` names the step that excluded it.
An initial configuration that applies a reading-dependent function is judged by the same list, on every definition: where its normalization lists no reading that counts, the run starts from the same state in both readings.
Neither refuses anything: `coverage` still runs such a program and gives it no comparable class; its cause says this exclusion as `check` says it, unless a reason only the run shows comes first (a timeout, or a run that contradicts a claim).

**When `check` fails.** `check` fails when a fact known before any mutant runs makes a verdict impossible.
`check` is the compile step of the loop: passing it and then reporting no verdict is the outcome it exists to prevent.
Two kinds of fact are known then, and each is an instance of the rule, not a special case:

- A program that cannot be judged on the baseline takes part in no verdict: no run of it can kill a mutant or show that one survives.
  A program is judged on the baseline when `coverage` can give it a class from its baseline run, and it cannot be when the specification is refused, when the program is refused, or when every run of it is excluded.
  A definition exclusion makes every program `excluded`.
- A baseline with no data gives no mutation a verdict but `unknown`.
  When the baseline's full critical-pair check has a finding that `[spec] assume_joined` leaves unnamed, or did not read the whole definition, no end of the definition is data (kink's `trust.md`, "What a kill trusts"): every mutation with a program to run is `unknown` (`baseline-findings`), no comparable program can kill, and no query answers `no`.
  The programs are still judged (`coverage` gives each its class and marks it `unable_to_kill`), so they stay `ok`; `spec.baseline_findings` names each finding with what to do about it.

What only a run shows (a timeout, a final configuration kink does not compare, an exclusion a run's own lists give) is `coverage`' class, not `check`'s: `check` runs no program.

It prints one JSON document:

```json
{"schema": "kink-flow-check", "version": 14, "k_rust_revision": "...", "profile": "no-z3",
 "spec": {"outcome": "admitted", "stage": null, "reason": null, "detail": null,
          "files": [{"name": "calc.k", "sha256": "..."}], "exclusion": null,
          "short_circuit": null, "baseline_findings": null},
 "programs": [{"id": "add", "outcome": "ok", "stage": null, "reason": null, "detail": null}],
 "data": {"assume_joined": [], "has_data": true, "incomplete": null, "findings": []},
 "result": {"slots": ["exit-stop", "whole-term"], "compared": ["k"], "not_compared": [],
            "unobservable": []},
 "mutation_list": null, "mutations": null, "coverage": null}
```

A program's `outcome` is `ok`; `refused`, with the stage, reason and detail of the refusal; or `excluded`: admitted, but every run of it on the baseline is excluded, with stage `definition` (the definition exclusion) or `initial-state` (its initial configuration's), the exclusion's name as `reason` (`implementation-chosen-hook`, `equals-condition`, `load-stack-stop` at stage `definition`; `implementation-chosen-hook` or `short-circuit-reading` at stage `initial-state`) and why as `detail`.

`spec.exclusion` is the definition exclusion, null when there is none (or the specification is refused): `{exclusion, detail, causes}`.
`detail` says what makes it hold, naming each sentence with its position (`file:start_line:start_column-end_line:end_column`, the file as the load named it; a builtin's is `krust-builtin://...`), at most eight causes; `causes` lists every one.
`spec.short_circuit` names the rules the short-circuit analysis flags, null when it flags none: `{detail, causes}`, the places where a run can read the definedness of an operand a short-circuiting backend may skip; they make no program `excluded` and `check` does not fail on them.
Each cause is one rule's chain `{rule, effect, part, links}`:
`effect` is `applicability` (whether the rule applies can differ between a backend that evaluates every operand and one that skips an operand a short-circuit operator does not need) or `result` (its result can be undefined in k-rust's reading where a skipping backend gives a value);
`part` is where in the rule the first link sits (`{part: "condition", leaf}` or `{part: "right-side"}`);
and `links` go from the rule to the operator, each `{link: "function", function, dependence, equation, part}`, a function applied there with the equation (and the part of it) through which it depends on the reading (`dependence` `valued` or `undefined`),
or `{link: "operator", operator, position, operand, term, term_symbol}`, the short-circuit operator, the position of the operand a backend may skip, the operand, and the application in it that may be undefined.
A sentence is `{name, module, label, id, source, location, authors}` (`id` its compiled `UNIQUE_ID`, `module` its KORE module), where `authors` lists the baseline sentences it was compiled from, each named as `coverage` names a rule (`{module, index, label, file, start_line, end_line}`), and is empty for a sentence a compiler pass generated; a symbol `{id, module, label, hook, source, location}` (`id` its KORE name), and a term (`leaf`, `operand`, `term`) is printed as kill evidence prints a value (`{text, rendering, truncated}`, below under "Kill evidence").
For `implementation-chosen-hook` a cause is `{sentence, symbol, hook}`, for `equals-condition` `{sentence}`; a `load-stack-stop` has none (`detail` gives the count).
`coverage` and `run` print the definition exclusion with the same formatter (kink-flow `exclusion`), `coverage` the flagged rules too, and `fuzz` the exclusion's `detail`.

`data` is the baseline's full critical-pair check under `[spec] assume_joined`, as the run, `coverage` and `query` documents print it (`{assume_joined, has_data, incomplete, findings}`, below under `run`); null when the specification is refused.
`spec.baseline_findings` is null when the baseline has data (or the specification is refused), else `{detail, findings, incomplete}`:
`findings` lists each finding no name assumes, `{name, verdict, description, next}`, with `next` saying what to do about it by its verdict;
`incomplete` is null, or `{detail, next}` when the check did not read the whole definition;
and `detail` says both in one text, naming at most eight findings.
A name assumes a finding away, so naming one is right only where the definition is right and the checker could not show it:
for an `undecided` finding, review it: name it in `[spec] assume_joined` if it does not hold of the definition (the pair joins; for an equation, it agrees with its hook or applies as written; for a precondition, it is met), or else fix the definition;
a `genuine` finding is a pair a ground input of which has two normal forms, so fix the definition (its name is refused, `decided`: the premise would be known to be false);
a `decided` finding, or one with no name, cannot be named, so fix the definition;
and no name can assume what the check did not read, so an incomplete check is a limit of k-rust's checker to report.

Version 2 (CF-18) adds `mutation_list`, `mutations` and `coverage`, which are null without `--mutations`.
Version 3 (CF-02) adds `spec.exclusion` and the program outcome `excluded`, and `check` exits 1 when a program cannot be judged on the baseline; before, a definition with a definition exclusion passed `check` with every program `ok`.
Version 4 adds `data` and `spec.baseline_findings`, and `check` exits 1 when the baseline has no data under `[spec] assume_joined`; before, such a specification passed `check`, and `run` then reported every mutation `unknown`.
Version 5 adds `result`, the slots and the cells compared (above), and the stage `result`.
Version 6 (CF-03) adds `spec.short_circuit`: the rules the short-circuit analysis flags are no longer the definition exclusion `short-circuit-reading`, which made every program `excluded` and `check` exit 1.
A program whose initial configuration applies a reading-dependent function is `excluded` at stage `initial-state` only when its depth-0 run lists a reading that counts against it; before, every such program was, and on a definition the analysis flags none was.
Version 7 gives `unreached-rule` for an edited rule no comparable program reached, whatever the edit, and adds `unapplied-rule` (below); before, an edit that left the rule's `requires` alone was warned about as `unreached-rule` when no program applied the rule, a reading of the edit from the rule's text that `run` no longer makes (`run` step 3).
Version 8 (CF-40c2) names that warning `unmatched-rule`, after the predicate it reads ("Coverage predicates"), and its text and `unapplied-rule`'s say "matches" for "reaches".
Version 9 adds `stop` for a corpus with `[stop]` (absent without one), the stage `stop` (reasons `stop-unresolved` and `backend-error`) and the warnings `stop-hides-edit` and `stop-rule-deleted` ("Where a run ends").
Version 10 (CF-24g) adds the named cases of a case document, each a program whose id is the document's path, `#` and its name, and each case's `expectation`, checked against the program's current result record without running it (it decides no exit status), and refuses a program whose expectation no front end reads at stage `inputs` (`typed-expectation`, `expectation-value`) ("Expectations").
Version 11 lets `result` name cells inside `?` and `*` cells, each compared or left out in every instance, and a narrowing's `compared` name the key of each Map that encloses a named cell; the reasons `unobservable-cell-position` and `result-cell-position` are gone, and a Map's key left out is refused (`map-key-left-out`) ("Which cells are compared").
Version 12 adds `stop.when` under a stop condition, the reason `unsupported-front-end` at stage `stop`, and, under a condition, reads `stop-hides-edit` from the comparable programs' coverage ("Where a run ends").
Version 13 adds `observe` for a corpus with `[observe]` (absent without one), the declaration as every run compares by it, the stage `observe` (reasons `point-unresolved`, `cell-refused`, `backend-error` and `unsupported-front-end`) and the warning `point-rule-deleted` ("What a run observes").
Version 14 adds `z3` under the Z3 profile, the Z3 build, `{version, library_sha256}`, as the run document names it ("The report: the run document"); the portable document has no such member.
Version 15 (KINK-FINDING-NAMES) names each finding by its kind, sentences and digest (`spec.assume_joined` above), gives each finding its `sentences` (`{part, at}`, `at` the generated K's position, information only), and refuses a `[spec] assume_joined` name with its own reason where version 14 refused every one as `name-refused`; a genuine finding's name is refused.
Each case's expectation and the coverage warnings are read from result records, whose classes and coverage the baseline runs decided by asking the solver, and a record is read only under a key that names the Z3 build ("The cache directory"), so under Z3 what `check` says is a function of the build as much as of the profile.
The document every verb prints for a manifest that does not decode is built from the check document's header, so it names the build too.

Exit status ("Exit status"): 0 when every program is `ok` (so the specification is admitted), `spec.baseline_findings` is null and, with `--mutations`, the list decodes and no mutation is refused (warnings do not count);
1 when a program is `excluded` or the baseline has no data (`spec.baseline_findings`), and nothing is refused;
2 when the manifest, the specification, a program, the mutation list or a mutation is refused, which `run` would refuse too, or on a usage error (message on stderr).

### Checking mutations

`check FLOW.toml --mutations MUTATIONS` resolves every mutation of the list against the current specification, exactly as `run` resolves it, and runs no program: no mutant is compiled and nothing is written.
It is the compile step of an author's loop: run it after every edit of the list or of the specification, before `run`.
`MUTATIONS` is a `MUTATIONS.toml` or a mutations directory (`MUTATIONS.toml` below).
The check compiles no mutant, so `ok` means that the mutation resolves, not that `run` will judge it:
a mutant that kink does not compile (a replacement with an unbound variable, say) or whose equations may have no model (`inconsistent-mutant`) is found only by `run`, which gives it the status `not-admitted` and exits 2.

The command is library code in two steps, so that a front end can add findings of its own between them and print the document `kink-flow check` prints:
`kink_flow::cli::check_corpus_mutations` admits the specification and the programs, reads the cached coverage and checks every mutation, returning all of it as data (each mutation's resolution and findings: `kink_flow::check::MutationCheck`);
`kink_flow::cli::check_mutations_document` renders the document and decides the exit status.
A finding a front end adds with `refusal: true` refuses its mutation as a resolution failure does.
A resolved mutation gives each edit as it was applied (`ResolvedMutation::edits`: the edit's byte range in the file's K view, its replacement, and where the replacement lies in the edited view), beside each edited rule's before and after, which merge the edits of one rule.

The document is the check document above, with:

- `mutation_list`: `{outcome: "ok" | "refused", detail}`; a list that does not decode is refused with the key at fault, and `mutations` is then null.
- `mutations`: one row per mutation, in list order, `{id, misunderstanding, outcome, digest, rules, refusals, warnings}`.
  `outcome` is `ok`, `refused`, or `error` for a resolution the host refused (`host-stack-refused`, which is not the mutation's fault).
  `rules` are the edited rules, as in the run document: `{module, index, file, label, start_line, end_line, edits, before, after}` (null when the mutation does not resolve).
  Each refusal and warning is `{reason, edit, rule, detail, next}`: `edit` the index of the edit at fault (or null), `rule` the baseline sentence `{module, index}` it is about (or null), and `next` one sentence saying what to do.
- `coverage`: `{decides, without_record, incomplete, detail}`, what the cached results (`coverage`, read from `--cache DIR` or `.kink-flow/`, never written) say about which rules the corpus uses: `decides` is true when every program has a current result record and every comparable program's coverage is complete; `without_record` and `incomplete` name the programs that keep it false.
A program whose result is never cached (a timeout, an error, an `unknown` the host caused) has no record, so it keeps `decides` false however often `coverage` runs: which programs are comparable is then a fact of the host's run, not of the cached results, and `detail` names the remedy (`budget.baseline_max_work` makes a run that does not finish a cached `unknown`).

A refusal is a reason of the table below (`MUTATIONS.toml`) with its next step: a stale anchor (`unknown-label`, `find-not-found`, `line-outside-rules`, `source-changed`), overlapping edits (`overlapping-edits`), a sentence that is not a rule (`non-rule-sentence`), an edit that changes nothing (`no-change`), and the others.
A refused mutation is one `run` reports as `invalid-mutation`.

Warnings refuse nothing:

| Warning | Meaning |
| --- | --- |
| `line-anchor` | The edit addresses its rule by `line`. A line moves whenever anything above it changes; the edit then fails, or lands on whichever rule holds that line and the text. `next` names the rule's label to address it by, when it has one. |
| `text-anchor` | The edit addresses its rule by its `find` text alone. After an edit of the specification the text can occur once in another rule, and the edit then lands there. `next` as for `line-anchor`. |
| `unmatched-rule` | No comparable program matched this rule (k-rust `matched`: began to decide a matched instance of it) in the cached results, so no program of the corpus exercises it. `run` reads which programs witness an edit from the compiled mutant (step 3), and `check` compiles none, so this is the coverage of the edited rule, not `run`'s witness rule. It is given per edited rule: a mutation that edits several rules may still be killed by a program that matches another of them, and an edit (such as a widened left-hand side, or a claim it withdraws) can make a program that never used the rule use the mutant's. Given only when `coverage.decides`. |
| `unapplied-rule` | Some comparable program matched this rule but none applied it (k-rust `applied`: built a candidate of it, defined or rolled back) in the cached results, so every program that matches it refutes its `requires`. An edit of only its right-hand side or `ensures` keeps its left-hand side, condition and attributes, so every program's run of the mutant refutes the edited rule where its baseline run refuted the rule: no program of the corpus can kill such an edit except through a claim the edit withdraws, or through another rule the mutation edits. The warning is about the rule, not the edit: an edit of the `requires` can still be killed by the programs that match it. Given only when `coverage.decides`. |
| `stop-hides-edit` | `[stop]` stops before this rule, and some program's run ends before the rule's step: without `when`, some program's count is 1; under `when`, the coverage decides and no comparable program fired the rule (each arrival at it was the event that ended its path). An edit of only its right-hand side or `ensures` then changes no end of that program ("Where a run ends"). The warning is about the rule, since `check` compiles no mutant to tell which part an edit changes: an edit of its left-hand side, `requires` or attributes moves the stops, and a program with a count above 1, or under `when` an arrival where the condition fails, takes the rule's step. The run document repeats it on a survivor (`stop_hides_edit`). |
| `stop-rule-deleted` | The mutation deletes a rule `[stop]` names. A K label names one rule, so no rule of the mutant has the label, the stop states no observation of the mutant, and `run` reports it `not-admitted` (`stop-unresolved`) rather than judging it. Given in place of `stop-hides-edit` for that rule. |
| `no-coverage-signal` | k-rust's coverage cannot record the rule (a macro, alias, `smt-lemma` or non-executable rule, as in `coverage`), so no program can be shown to match it. |

`kink-flow --version` prints `kink-flow VERSION (k-rust REVISION)`, where `REVISION` is k-rust's build identity (`k_rust::build_identity`: its version and a digest of its sources, such as `0.8.0+src.<hex>`), the value every document's `k_rust_revision` names (GUIDE-USABILITY 5, KINK-R4: within each document's version, since the field's shape did not change; before, every document but `fuzz`'s named the version alone), and exits 0.
`kink-flow --help` (or `-h`) prints the usage line, the loop, the mutation format and the exit statuses on stdout, and exits 0;
after a verb, anywhere among its operands and options (`kink-flow run --help`), it prints the verb's help instead: its usage line, what it asks, and each of its options with what it does (`kink_flow::cli::verb_help`, which a front end such as `krs kink` prints for its own verbs).

## Coverage predicates

A program's coverage is k-rust's run coverage of its baseline run, and each predicate over it has one name in every kink-flow document, flag and output, the name k-rust and `krs run --coverage` give it.
Each predicate implies the one above it.

| Predicate | A program's run of a rule or equation | Named in |
| --- | --- | --- |
| `matched` | began to decide its condition for an instance whose left-hand side matched, whatever the verdict, or applied it (k-rust `matched`) | a `coverage` rule item's `matched_by` and status `matched`, the result record's `coverage.sentences`, `check`'s `unmatched-rule`, `fuzz --matched` |
| `applied` | built a candidate of it, defined or rolled back because its result was undefined, or found the step undefined; for an equation, an instance gave a result (k-rust `applied`) | the result record's `coverage.applied_sentences`, `check`'s `unapplied-rule`, `run`'s witness rule (step 3) |
| `committed` | took a step by the rewrite rule on some path: the step's successor was committed, its own normalization having shown it defined (k-rust `committed`) | `krs run --coverage`; in kink-flow only inside `fired` |
| `fired` | for a rewrite rule, `committed`; for an equation, `applied` | a `coverage` rule item's `fired_by` and status `fired`, which covers the rule, the result record's `coverage.fired_sentences`, `fuzz --fired` |

`fired` is kink-flow's own predicate: a rewrite rule fires when a path takes its step, and an equation, which no path takes as a step, fires when it gives a result.
A rule is covered when it fires, not when it matches: a rule whose left-hand side matched and whose condition never held never built its right-hand side on a path, so no program can tell a change of its result apart.
The programs whose coverage witnesses a mutant's compiled edit (`run` step 3: applied for an edit confined to a rule's right-hand side or `ensures`, matched for any other site-local edit, every program otherwise; a definedness claim kink withdraws adds none through coverage) are a mutation row's `witnesses`.
The result record names the matched sentences `coverage.sentences`: it is a cache record, read only by kink-flow, and renaming its keys would miss every result cache without changing what any record means.

## `kink-flow coverage FLOW.toml [--tier 1|2] [--depth N] [--verify] [--lock FILE [--locked]] [--cache DIR] [--output json|text|verdicts]`

Asks what the corpus covers of the obligations the specification states.
An obligation is an item derived from the definition alone, before any program runs, so each family's universe is a function of the definition, and the document states its size.
An obligation is covered when the baseline run of some comparable program shows the family's predicate.
Only comparable programs count: a program that cannot be compared can kill nothing, so it tests nothing, and an item that only such programs touch lists them as `touched_only_by`, its target then being to make one of them comparable.
Each family's coverage is set arithmetic over the programs' result records, so a command runs only the programs whose record is not current, and adding a program runs that program alone.
The command replaces `results`, whose program rows and rule rows it holds: two documents listing rule statuses would be two answers to one question.
`kink-flow results` is a usage error that names `coverage`.

`--tier 2`, the default, asks for both tiers: the families read from the baseline runs, and tier 2's one family, condition flips, whose mutants the kill search runs.
`--tier 1` asks for the first alone, and runs no mutant.
The flips come from a front end that derives them from the definition's source and judges each (`FrontEnd::derived`, "Front ends"); kink-flow's own command line reads K alone, so it derives none, and its flips family says so.
A document states only the tiers it computed: `settings.tiers` is `[1, 2]` where the flips ran, else `[1]`.
`--depth N` computes depth N in place of `[coverage] depth`, to explore another depth without editing the manifest; `settings.depth` is the depth computed.
`--lock FILE` and `--locked` keep the `[coverage]` section of the corpus record, the coverage lock ("The corpus record").
`--output text` prints a summary for a reader: the covered, argued and open counts, one line per family with covered / obligations and the measure, the programs that count for nothing with their causes, each argued item with its argument, each needless argument, and one line per open target with its position, its pattern and its fuzz job; its wording may change with no coverage changing, so it is no lock.
`--output verdicts` is the lock format ("Verdicts").

### Programs and the result cache

Each program runs on the baseline as its own zero-mutant campaign (kink-campaign's runner),
with two oracles: the exit stop (no exit-code cell) and the final configuration without the cells left out (`whole-term` or `cells`, above under "Which cells are compared").
The document's `result` names the slots and the cells compared, and, where the slot is `cells`, a comparable program's final configurations (its baseline row's `cells` side) and `ends` are the projected ends.
A program's class is

| Class | Meaning | What to do |
| --- | --- | --- |
| `comparable` | The run ended and its final configuration is a value kink compares. | Nothing: this program can kill mutants. |
| `comparable-prefix` | Under `[observe]`, `budget.max_depth` or `budget.baseline_max_work` cut the run before it ended, and every other path of it is complete: it has no end, and its observation channels are compared up to their horizons ("What a run observes"). | Nothing: this program can kill mutants by its channels; raising the bound observes more of a channel whose opening is `bound`, and of no other. A prefix program none of whose channels kept an element is `unknown` (`observed-nothing`). |
| `timeout` | The run did not end within `budget.time_ms`; `cause` gives what k-rust returned when the bound fired (see below). A timeout depends on the host's load, so it is never cached: every command runs the program again. | Make the program terminate, raise `time_ms`, or set `budget.baseline_max_work` to bound the run by work, which gives a cached `unknown` instead. |
| `unknown` | The run ended without a comparable value (for example a collection holding a `Float`, `budget.max_depth` or `budget.baseline_max_work` reached, an undecided step), or the run is excluded (`cause` then names the exclusion, such as `contradicted-claim`); `cause` says which. | Write a program whose final configuration kink can compare; for a `contradicted-claim` exclusion fix the claim the row's `specification_diagnostics` names, not the program; for a `short-circuit-reading` exclusion write a program whose run does not read the operand the row's `short_circuit_readings` names (or make that operand defined in the specification). |
| `refused` | The program was not read, parsed or assembled; `cause` is the refusal. | Fix the program. |
| `error` | The run or the runner failed. | Report it. |

Only comparable programs can kill a mutant; the others are reported and never count as covering an obligation.

The cache is `.kink-flow/` next to `FLOW.toml` (or `--cache DIR`); deleting it is always safe.
One JSON record per program, `results/<execution digest>/<program digest>.json`, holds its key
(result schema version `kink-flow/result/v27`, kink's build identity `kink_build`, kink's semantics identity `kink`, the execution digest `execution: {kind, digest}`, the program digest, the budget, with `[stop]` the program's `stop`, its rules, its count and, under `[stop] when`, the condition's identity `when`, and, where a front end gives the syntax family's selection, `syntax`, its authored sorts and template binders), class and cause,
the writer's specification digest `spec_digest` (outside the key: it only tells a reader that a record was written under other bytes),
the baseline row exactly as the campaign report encodes it with the digest of its `run` part
(`run_sha256`, comparable programs only), whose whole-term (or `cells`) side holds the final configurations as KORE text (an undefined step's pre-step configuration is none, so a run whose every path takes an undefined step lists none, and its baseline row's exit stop holds no class for it; since v7, kink27 R1-UNDEF), each end once: since v12 a comparable record does not repeat them in `final_configuration`, which holds the final state of each leaf of an `unknown` program's diagnostic run (`results::record_final_configuration` reads either), the rule
coverage (each sentence `{module, index, label}`: documents render file and lines from the current load), `wall_ms`, the wall time of the program's live baseline run (outside the key and
the run digest; it orders the kill search, see `run`), and, since v5 (re-pin adoption A-1),
`specification_diagnostics`, the baseline run's contradicted-claim records (see `run`), and
`smt_unknowns`, its count of undecided solver answers (both outside the key and the run digest),
and, since v9 (CF-16), for a comparable program, `ends`: each final configuration's `{head, class}`, in the order of the final configurations (outside the key and the run digest),
and, since v11 (CF-03), `short_circuit_readings`: for a run excluded as `short-circuit-reading`, each entry of its list of short-circuit readings that counts against it, `{operator, outcome, head, operand, rule, observed_in}` (the operator whose operand after the deciding one the run read, `undefined` or `undecided`, the operand's head symbol and one instance of it as KORE text, the rewrite rule whose work read it `{id, label, source, location}` or null for work of no rule, and `run` or `load`), the step that excluded the run, which the row's `cause` also names; empty for every other run (outside the key and the run digest).
Since v23 the record's coverage holds `windows`, the rule windows the baseline run took, each a list of `{module, index}` in step order, null for a run that asked for none, whose windows of length 1 are its fired rules.
Since v24 it holds `depth`, the depth the run asked for, the longest rule window and syntax path it collected (1 for a run that asked for neither), which every depth-dependent family reads, and `bindings.paths`, the syntax paths of length up to that depth its fired instances touched, per sentence `{module, index, label, paths: [{symbols, positions}]}` (`positions` 0-based), null for a run of depth 1.
Since v25 its `guards` hold, at each function application, the entries of every equation of the deciding priority group whose left-hand side matches, also those the run did not try ("Guard outcomes"); a v24 record holds the tried entries only.
A record collected at depth `D` answers a command of any depth up to `D`, for the rule windows and the syntax paths alike; a command of a greater depth runs the program again and replaces its record with one at its own depth ("Rule windows", "Syntax paths").
An end's `head` is its computation head, the first item of its computation cell (or the cell's content when that is no sequence of items), printed as one line of K text (`{text, rendering, truncated}`, below under "Kill evidence"); null when the end has no computation cell.
The computation cell is the first cell, from the top, whose production has the `maincell` attribute: k-rust gives it to a cell named `k`, and a configuration may declare it on a cell of another name (`<code maincell="">`).
Its `class` is the class the exit-stop slot projects it to, `normal` for every end under the flow's classifier.

#### Declared ends

A definition may declare ends (krs: `#[k::end(finished)]`, `#[k::end(refused)]`): each a Bool function of the configuration, true exactly on the end, and for a refused end a function giving its reason.
Only a front end that reads the definition at its own level knows them, so the front end's renderer gives each end's class (`EndRenderer::declared_ends`); kink computes none, and the definition's own end functions are the only source of a class.
A declared end is a statement about a state at which no rule applies, so only such an end has a class: without `[stop]` every end, and with it every end whose `halt` is `own`; an end reached at a stop is not known to be one, and has none.
In a definition that declares ends, each such entry of a program row's `ends` adds:

| Key | Meaning |
| --- | --- |
| `declared` | `finished`, `refused`, `none` (no declared end holds: a gap), `undecided` (an evaluation stopped or ended short of `true` or `false`, or the class depends on a cell the slot leaves out), or `overlap` (ends of both classes hold) |
| `declared_by` | the item of the first declared end that holds (`crate::machine::halt`), for `finished` and `refused` |
| `reason`, `reason_text` | a refused end's reason, as the front end writes it (krs: a document at the reason's declared type, and its K text) |
| `declared_detail` | why it is `undecided` or `overlap` |

The krs front end evaluates each end's function with `krs run`'s default budget of polls; where the slot leaves cells out, each cell it replaced by `\top` is a variable of its sort, so a class decided there holds whatever the cell holds, and one that depends on it is `undecided`.
The class is computed again by every command, from the ends the result record holds: it is in no record, digest or key, and the result schema is unchanged.

A row whose classes are a finding has `declared_end`, `{finding, detail}`: `undeclared-end` for an end of class `none` that the case does not expect (its `expect` does not state `class = "none"`), `end-classes-overlap` for one of both classes, `end-undecided` for one whose class is not decided; where several ends are findings, the first of the most severe (overlap, gap, undecided).
`coverage` exits by it, as by an expectation: 1, 2 and 3 respectively ("Exit status"); the other commands report it, since they ask about the mutations, the patterns and the implementations.
This answers a case as `krs cases` answers one that states no expectation; unlike `krs cases`, an expectation that states no class does not replace the finding, since it says nothing of whether the definition accounts for the end.

The class is evidence and a finding, never part of a compared observation.
The slots compare final configurations, which an edit of only a declared end's function does not change, so such a mutant cannot be killed by any program: its equations are no obligation (`declared-end`, "Families"), no flip is derived from them, and a mutation of one in a list survives whatever the corpus holds.
Putting the class into the exit-stop slot would need the classifier, a function of the term alone that every campaign call shares, to evaluate the mutant's own end functions with its backend at each leaf, which it cannot.
`kink_build` is the SHA-256 of the executable that wrote the record (kink-campaign `identity::kink_build`, packet CACHE-ID-fix-1), so a record another build wrote, or one without `kink_build`, is recomputed: the code that decides a result class mostly has no version constant, and only the build tells that it changed.
When the executable cannot be read, no record is read or written, and each row says so (`cache_error`).

A record may be stored only under a key that names every input its value depends on, and only when the value is a function of those inputs on every host.
So only `comparable` and `unknown` records are written, and of `unknown` only one whose cause is not a host event.
A `timeout` depends on the host's load; an `error` can come from the host (a refused stack segment, a solver that could not be created), and kink cannot tell when; a run excluded for a stack stop, a load stack stop or an allowance refusal is excluded for a fact of the host; and an `unknown` whose live run the watchdog stopped, or that failed without naming an exclusion, took its class from a second run, as did one that second run excluded for a fact of the host.
None of these is written: the row says why (`not_cached`, for example `timeout: the watchdog stopped the run at time_ms = 500; a timeout depends on the host's load, so the next command runs this program again`), the command's exit status is unchanged (an `error` row still fails it), and a stored record of such a class, one another writer left or a hand edit, is never read.
An `unknown` whose live run failed but whose campaign named an exclusion of the definition or the program is written: that exclusion, which the second run reached without a host exclusion, decides its class, not the failure.
Under the Z3 profile every solver query a command asks is bounded by Z3 resource units (`budget.smt_resource_limit`): a run's, and kink's own outside a run (leaf feasibility, the observation decider), which judge the run.
Whether such a query is decided is a function of the query, the units and the Z3 build, which the key names (below), never of the host's load or of what the backend asked before (k-rust's `docs/compatibility.md`, "Execute", clock-free solver mode), so a class is a function of its key and the result cache is on, as it is without Z3.
A record counts the undecided answers, k-rust's in the run (`smt_unknowns`) and kink's in its judgement of the run (`decider_smt_unknowns`), and every program row carries both.
They are reported, never an exclusion: an undecided answer can make a leaf or a comparison unknown, never a kill, and a stored class is the class the same run gets again; a nonzero count says where a larger `budget.smt_resource_limit` could decide more.
The cache is off under Z3 only where the key cannot name the solver: a Z3 build that cannot be named (below), and solver queries bounded by the clock, whose answers depend on the host's load (kink's own commands never build such a backend; a library caller may).
The document says whether the cache is on (`result_cache: {enabled, reason}`).

The execution digest (kind `kink-flow/execution/v1`, `digest::execution_digest`) is the digest of the loaded definition without positions: each module's header (name, imports, attributes) and each sentence, in definition order, by its position-free fingerprint (kink-patch's, which tier 1's mutation identity uses) with the two origin facts kink's judgement reads (whether it is located, and its source when that is builtin); with the k-rust revision, the solver profile, the main module, the syntax module the loader resolved, the names, in the K spelling, of the findings `[spec] assume_joined` assumes (a name holds no position, so a line inserted above the named equations leaves the execution digest as it was), and `[result] cells`.
So a comment, a blank line, a rustdoc comment KRS emits as a K comment, or any other layout edit keeps every record, and editing a rule, an attribute, the order of two rules or an `unobservable` declaration misses.
A definition with a sentence that has no fingerprint (a context alias) falls back to the specification digest (kind `kink-flow/spec/v1`), which only costs misses.
The specification digest covers the k-rust revision, the solver profile, how the
specification is loaded and every source file the load reads, every byte; it names the specification in every document (`spec.digest`, beside `spec.execution_digest`) and keys the memos.
The program digest covers the
program's bytes (when it has a program, whichever variable the front end binds them to and however), start sort, variables and typed inputs, never its id.
A typed input enters by what it denotes: the variable's K name and the SHA-256 of the KAST JSON of
the term the decoder gave (`{name, kast_sha256}`), so editing a value in a file an input reads reruns
the program and reformatting the file does not; a program with no typed inputs has the digest it
had before typed inputs existed.
A declared default the case takes enters by its value (`defaults`, `{name, kore_sha256}`), since the execution digest, the loaded K definition's, does not see a default.
The budget in the key is the bounds a stored class depends on, `{max_depth, max_simplification_iterations, max_breadth}` and `baseline_max_work` when it is set: each stops a run deterministically.
Under the Z3 profile it also names the solver, `smt: {resource_limit, retries, z3: {version, library_sha256}}`: whether a query is decided within `budget.smt_resource_limit` depends on the Z3 build that counts the units, and two builds of one Z3 version can count them differently, so the key names the build by the digest of the library file its code comes from (the shared library of a dynamic link, the archive a static link took), not only by its version. When that file cannot be named (a shared library replaced or deleted since it was mapped, a static link whose archive the build could not name), every such build would share one key, so the caches are neither read nor written.
`time_ms` is not in it: a run the watchdog stopped is never stored, and a run it did not stop is the uncancelled request, whose result does not depend on the bound, so raising `time_ms` to get past timeouts keeps every record.
A record is used only when its key is
the current key, so editing a program reruns that program, and editing the meaning of the specification,
a bound in the key or kink's result schema reruns everything. So does a kink build with another semantics
identity (packet CACHE-ID): the identity (kink-campaign `identity`) names every kink algorithm a
program's class can depend on (the definition exclusions, the execution request, ...), and a
record written by a build before CACHE-ID has no `kink` in its key, so it is recomputed.

Within one command each program's baseline runs at most once: every campaign call of the command
(the zero-mutant campaigns here, the kill search's calls in `run`) goes through one in-memory
baseline session (kink-campaign `BaselineSession`), which reuses a baseline run this command made
live for a later request with the same program, oracles, module and budget. Nothing of it is
written to disk, so every command runs the baselines it needs live again; the document's
`baseline_runs: {live, reused, diagnostic}` counts them (outside every digest and key).

When the zero-mutant campaign refuses a baseline, the class and the cause come from this command's
live run of it if that run stopped on time: the class is `timeout` and the cause continues with the
run's leaf census. k-rust answers a cancelled run with an error and returns no leaves (re-pin L1-1,
`cancelled_result: error`), so the census reads `the run did not finish within time_ms = 500; when
the bound fired k-rust returned no leaves, so neither the paths nor the depth reached are known`; a
census with leaves, depths and applied rules is given for runs that ended otherwise (a depth bound,
a work bound, an undecided end). The cause ends with `a timeout depends on the host's load and is not cached: the next command runs this program again`, and, without `budget.baseline_max_work`, `set [budget] baseline_max_work to bound the run by work instead`.
Likewise when the live run reached `budget.baseline_max_work` and the campaign named no exclusion: the class is `unknown` and the cause is `the run reached baseline_max_work = N; ` with the run's leaf census. No second run is
made in either case. For any other refusal (an `unknown` or `error` run) one diagnostic run of the initial state, the campaign's request (the same budget and `baseline_max_work`),
supplies the class, the cause, the final states and the coverage (`diagnostic` counts them). When
the campaign named the exclusion of the baseline run, the cause says that exclusion and why it
holds, never a guess from the shape of the leaves (an excluded run's leaves can all be values); for
`contradicted-claim` it points at the row's `specification_diagnostics` and says to fix the claim,
not the program (re-pin adoption A-1b). An exclusion that holds for every run of the program, the
definition exclusion or its initial configuration's, is said as `check` says it (its program
`detail`), and the document's `spec.exclusion` is the definition exclusion with its causes, as in
the check document (null when there is none; added to version 4 without a new version, since it is
additive). When no exclusion is named and every path ended, the cause
names why a final configuration is not a value kink compares (fz26 KINK-CAUSE-SUBTERM): in the first
leaf whose state's term has no terminal value, the first node, in pre-order, that fails its own test
with its children ignored (a head that is not a free constructor, an overload application k-rust does
not judge data, a domain value without a trusted codec, a collection node, ...), its cells and
collection entries (`<T>/<store>/Map entry 1 value`), the test, and its KORE cut after 160
characters; for an overload application, also the first node inside it that fails its own test.
Naming the first subterm without a value would always name the root. The judgement is kink-native's
`ObservationDecider::first_non_value`, from the walk the runner's terminal value takes, with the
decider built as the runner builds the baseline's (collection trust, the baseline's data facts). It
judges the baseline alone: whether an end is data under a mutant's definition is decided for each
pair by the runner, never in this cause. Only the campaign admitting a baseline makes a program
`comparable`.

`--verify` reruns every program that has a current record and compares: a different class,
a different `run_sha256`, or a record whose `run_sha256` is not the digest of its own baseline
row is a mismatch. Mismatches are listed (program, record path, detail) and records are never
rewritten by `--verify`; delete a mismatching record (or the cache) to recompute it.

### Families

Every family shares one scope, a function of the definition, the front end's marks and the manifest's `[[coverage.invariant]]` tables, read before any program runs.
A sentence is no obligation of any family when it is, in this order, a simplification, `symbolic` or ceil equation (`out-of-scope`), a rule none of whose compiled ids a run's coverage can name (`no-coverage-signal`), an equation of a function only claims apply (`claim-helper`), an equation of a function only the manifest's invariants reach (`invariant`), or an equation of a function only the definition's declared ends reach (`declared-end`).
A declared end's function is applied by the front end to a run's last state to read its class ("Declared ends", below), never by a step of a run, and the slots compare final configurations, not classes: an edit of such an equation changes no end any slot compares, so no program can tell it apart.
The front end names those functions (`FlowManifest::with_end_functions`), and the reach is the one invariant-only functions use (below), seeded with them.
The rules family gives such a sentence that status; the requirements, syntax, field-value and syntax paths families read the rules statuses, so they count none of its conditions, touches or paths; the rule windows family's may-follow graph has no node for it; and a front end's flip that changes only such sentences is listed under the flips family's `not_generated`, never resolved, run or counted, while a flip that also changes a sentence in the scope is that sentence's obligation.

A claim helper is outside the scope whatever the programs did.
No initializer, program production or sentence a run can take applies it, so a run reaches it only through an input that applies it, and an edit of it changes no step of any run that does not.
The claims it serves are what tell its equations apart, and a proof of the claims checks that; no case of the corpus can close an obligation on it.
An item that became an obligation because a typed input applied it would make the universe depend on the corpus: a case that applies a helper would raise the measure without testing any run of the definition, and a corpus would not be done until it did.

An invariant-only function is outside the scope for the same reason.
An invariant ("Argued obligations") is read off a run's states by the argued items' checks, after the run and outside it, never applied by a step: no run of the semantics applies its function, nor a function only it applies, except through an input that applies one, so their equations are no behaviour a program exercises, and an edit of them changes no step of any other run.
The reach is that of the compiled equations, the relation kink's consistency gate reads (kink-native `consistency::EquationReach`): evaluating an application of a symbol can apply every symbol its equations and its `simplification` and ceil lemmas apply, in their sides and conditions, transitively, both ways within an `overload` family, and whatever an equation indexed at no symbol or a predicate lemma applies.
A run of a result record can evaluate everything that reach gives from: every rewrite rule of the compiled definition (heating, cooling and stream rules included), `initGeneratedTopCell` and the `configuration` sentences, every labelled production of the syntax module programs are parsed in and of the modules it imports, every symbol the rules of such a production's macro apply (`macro`, `macro-rec`, `alias`, `alias-rec`, transitively through the macros those rules apply: a macro is expanded before the run and has no equations, so the reach of its label gives nothing, while every program that writes it applies what its expansion applies), and the front end's functions of an observer, `[stop] when` and the `[observe]` views, components, filters and log elements, as the front end names them (taking these in keeps more sentences obligations, since an observer is not the definition being run; a front end that cannot name them leaves no sentence invariant-only).
A function is invariant-only when the reach from the resolved invariants' functions gives it and the reach from those does not, and a sentence is `invariant` when every compiled id it authored is an equation or lemma of such a function, with its `reason`.
A function the semantics also applies stays an obligation: `inRom` in `rule outsideRom((K |-> _) _, E) => false requires inRom(E, K)` is an obligation wherever a rule's condition applies `inRom` too.
Its guard states no requirement, and a front end's flip that changes only its sentences is `not_generated` with reason `invariant`.
A `[[mutation]]` an author writes on such a sentence runs as written, as one on a claim helper does: it is the author's question, which coverage does not count, and it survives wherever no program's input applies the function.
Removing an invariant table (with the entries that name it) makes its functions' equations obligations again, which a coverage lock shows as obligations opening.

**Rules.** Every authored rewrite rule and function equation (`owise`, `anywhere` and the authored equations of an overloaded function included), in sentence order, each an item `{id, module, index, label, file, start_line, end_line, status, obligation, covered, matched_by, fired_by, touched_only_by, uncounted, rewrite, guard?, reason?}`.
Its status is named for the predicate it tests:

| Status | Obligation | Meaning |
| --- | --- | --- |
| `fired` | yes, covered | some comparable program fired it |
| `matched` | yes, open | some comparable program matched it and none fired it: its left-hand side matched and its condition was entered, but its right-hand side was never built on a path |
| `unmatched` | yes, open | no comparable program matched it |
| `out-of-scope` | no | a simplification, `symbolic` or ceil equation: it states a fact of the definition's functions, which the definition means the same without, so no step computes it and no program needs to run it |
| `claim-helper` | no | an equation of a function only claims apply (below) |
| `invariant` | no | an equation of a function only the manifest's `[[coverage.invariant]]` functions reach (above) |
| `declared-end` | no | an equation of a function only the definition's declared ends reach (above); `counts.declared_end`, present where there is one |
| `no-coverage-signal` | no | none of its compiled ids can appear in a run's coverage: it compiles to no axiom, or it is a `non-executable`, macro, alias or `smt-lemma` rule; `reason` says which |

The statuses partition the rules with the precedence `out-of-scope`, `no-coverage-signal`, `claim-helper`, `invariant`, `declared-end`, `fired`, `matched`, `unmatched` (firing implies matching); the first five are the shared scope above.
A program matched a rule where its run began to decide the rule's condition for an instance whose left-hand side matched, or applied it (k-rust `matched`), or entered its condition ("Guard outcomes"): a function equation is matched wherever an application's arguments matched its left-hand side and its priority group decided the application, whether or not the run tried it there, which is a fact of the arguments and the equation and not of the order in which the backend tries a group's equations (of the complementary `f(A) = .. requires A <Int 32768` and `f(A) = .. requires A >=Int 32768`, a corpus that applies `f` below 32768 only matches both, in either order).
The measure is `fired / (fired + matched + unmatched)`; `counts` gives each status.
`uncounted` lists the programs that are not comparable and match or fire the rule; `touched_only_by`, on an open rule, those of them that would raise its status.
`rewrite` says whether the rule compiles to a rewrite rule, which a fuzz job can target.
A front end that reads a sentence's match at its own level gives `krs.status`, which takes the place of `status`.

A claim helper is an equation of a function that, within the definition, only claims apply.
Claims are proof obligations outside the executable definition, so a claim helper serves a proof, which checks it, and not the definition's runs.
No program text reaches it, but that does not set it apart: no program text reaches a function nothing applies either, and the K alone cannot tell the two apart.
Only a front end that sees the claims beside the definition names the claim helpers (`FlowManifest::with_claim_helpers`; the krs front end names the sentences its emission marks so, and a K corpus has none).
A function nothing applies stays `unmatched`: neither a run nor a claim accounts for it.
A claim helper is `claim-helper` whatever the programs did, with its `reason`, and no guard row: one a typed input applied lists the programs that matched and fired it (`matched_by`, `fired_by`) as information, and is still no obligation (above).

The family also has the heating rules the compile generates, each an item of `kind` `heating` (an authored rule's `kind` is `rule`) at the authored sentence it was generated from: a `strict` or `seqstrict` production has one per argument position its attribute names and per context alias it uses, and a `context` sentence has one.
A context says: evaluate the subterm at the hole before the construct around it.
The compile states it as two rewrite rules, heating, which moves the subterm to the front of the computation while it is not a result, and cooling, which plugs the result back.
The obligation is the heating rule: it fires exactly where a run put a term that is not a result at the position, the one situation the attribute governs, so a corpus whose runs never heat a position cannot tell the definition from one without that position's strictness.
Cooling follows from heating wherever the subterm's evaluation reaches a result, and where it does not, the step after it (the authored rule that reads the result) is open on its own, so the cooling rule is shown and not counted.
The item's status is its heating rule's: `fired` where some comparable program took the step, `matched` where some matched its left-hand side and its condition never held (the subterm was a result there, or, for `seqstrict`, a position before it was not yet one), `unmatched` where no comparable program brought the construct to the front of the computation.
An item is `{id, kind, module, index, label, file, start_line, end_line, status, obligation, covered, matched_by, fired_by, touched_only_by, uncounted, rewrite, pattern, heating, reason?}` with `heating` `{attribute, production, position, alias, heat: {axiom, label}, cool: {axiom, label, matched_by, fired_by, uncounted}}`: `attribute` `strict`, `seqstrict` or `context`, `production` the production's K label and `position` its 1-based argument position (both `null` for a `context`), `alias` the context alias sentence (`null` for the default one), `cool` `null` where no cooling rule pairs with it.
Its id is `rule:<production>:heat:<position>` (with `:<alias>` where it uses one), a front end's name of the production and the position where it gives them (`rule:crate::Arith::Add:heat:lhs`), and `rule:<context>:heat` for a context, the context named as a rule is.
The two rules of one context share their input sentences, and their labels differ only in the suffix (`-heat`, `-cool`); the label the compile gives a production's context, `MODULE.label` followed by the position, names the position, and a context without a label has one heating and one cooling rule, so its sentence alone pairs them.
Every heating rule of one production has the production as its sentence, so the sentences a record lists cannot say which position a run heated: a record keeps the heating and cooling rules its run matched and fired by compiled id (`coverage.strictness`, `{matched, fired}`).
`counts.heating` (`{obligations, fired}`) gives the heating items apart, and the text rendering's rules line says `heating N of M fired`.
A heating item does not count in the syntax family: its step touches its own production by construction, which the item already states; what the syntax family adds is whether the definition's rules took a step with the production.

**Requirements.** For each guarded rule of the rules family whose condition has an authored conjunct ("Guard outcomes"), each distinct pair of a node and a truth: the condition's root with each outcome (`held`, `refuted`) and each authored operand node with outcomes of its own (an atom, or an exclusive connective) with each truth (`true`, `false`), each an item `{id, rule, node, truth, text, file, line, status, covered, covered_by, undecided_by, touched_only_by, entered_by, reaching?, node_truth?}`.
A node's truth is covered when some comparable program reached the node with that truth, a node being reached, in written order, only where the operands before it decide nothing yet: in a conjunction where every operand before it is `true`, in a disjunction where every one before it is `false`, the right operand of an implication where the left one is `true`.
So the reached truths per node encode the short-circuit outcome classes of every connective, and one unit serves them all.
Where the root's outcome is reached exactly where a node is reached with a truth, the two are one obligation, listed once as the root's `held` or `refuted` with the node (`node`, and `node_truth` its truth) and the programs of both: a root that is itself an atom (its `held` is its `true`), a condition's last conjunct (the condition holds exactly where it is reached `true`), a condition's only conjunct (also for `refuted`), through a negation (with the other truth) and a disjunction's last operand or an implication's right one (for `refuted`).
For `A && B` the items are A's `true` and `false`, B's `false`, the root's `held` (B reached `true`) and `refuted` (A or B reached `false`): the outcome classes A `false`, B `false` and `held` are three of them, and the other two hold wherever those do.
A condition that is one atom `A` has two items, `held` (A `true`) and `refuted` (A `false`).
Undefined and undecided outcomes, the tests a front end inserted and a pattern's templates are shown apart and never counted; `undecided_by` beside an open item says that the gap may be the report's and not the corpus's (an untried entry the evaluation left open is undecided with cause `untried`, not covered).
A function equation's condition is reached at every application its left-hand side matches whose deciding priority group is its own, tried or not ("Guard outcomes"), so its requirements do not depend on the order in which the equations of a group are declared or tried: two complementary equations have the same covered and open requirements in either order.
`entered_by` lists the comparable programs that entered the condition, the rule's `matched_by` (a front end's `krs.matched_by` where the templates moved its match into the condition, which reads the guard's own nodes), so also one that applied the function by another equation of the group and never tried this one; a requirement's target names them as `programs`.
Two kinds of equation still depend on the trial order, because the backend makes no untried entry of them: an equation holding a literal whose element the definition leaves open (k-rust's implementation-chosen hook values), and an equation whose attempt failed in an earlier evaluation of the same application. Where the run did not try such an equation, it has no entry there, so it is neither matched nor its condition reached at that application.
`reaching` lists the truths of the author's earlier nodes that reach the node, which its target states.
The universe is a function of the definition: the nodes come from the definition's skeleton of each condition, so a guard no program entered has its requirements, all open.
A condition whose skeleton the definition cannot give (an atom the backend cannot encode as KORE) shows no node, whichever programs entered it, and its guard's `operands_reason` says why: its requirements are its root's alone.
The measure is covered / obligations.

**Unique-cause MC/DC (opt-in, per rule).** The outcome classes are the default level of the requirements; `[coverage] mcdc` adds a deeper one to the rules it names (`true` names every rule whose condition states requirements).
A selected rule gains one requirement per authored atom of its condition, an item `{id, rule, level: "mcdc", node, text, file, line, status, covered, covered_by, pair, needed, truncated_by, entered_by}` with id `requirement:<name>:<operand>:mcdc`, listed after the rule's outcome-class items and counted with them.
An atom is covered by a unique-cause pair: two valuation combinations the comparable programs' baseline runs recorded ("Guard outcomes", `guard.combinations`), one where the condition held and one where it was refuted, in which the atom has the two truths and every other atom has one decided truth, the tests a front end inserted and the conjuncts the compile added included; `pair` gives each side's `valuation` (each operand's `{node, text, truth}`), `outcome` and `programs`, and `covered_by` the programs of both.

- Why every other atom is fixed: on a pair, the condition differs from the condition with the atom replaced by either constant, so a corpus with the pair tells the condition from both conditions in which the atom decides nothing.
  A pair in which another atom changes too does not: for `A andThenBool B`, (true, true) held and (false, false) refuted cannot tell the condition from `B`, although A is reached `false`.
  Letting a masked atom differ, as the short-circuit reading would, gives the pairs the outcome classes already count; fixing it states what they cannot.
- A combination holds every atom's truth under the strict reading, also an atom the short-circuit reading did not reach, so the pairs are read from the records with no run; an `undecided` atom has no known truth and fixes nothing.
- An atom without a pair is `open`, and its target names the valuation needed (`needed`, each `{valuation, outcome, against}`): a recorded combination with the atom's truth negated, where the condition, evaluated on the definition's skeleton of it, takes the other outcome, against the combination it pairs with (`a case that enters MCDC.both with A:Bool false and B:Bool true, where its condition is false: against one's A:Bool true and B:Bool true, where it holds, A:Bool alone decides it`, the mcdc fixture's).
- An atom whose truth is a function of the others (`X >Int 0` beside `X >Int 10`, which implies it) has no possible pair; its target says so, and the obligation is argued ("Argued obligations"), as any other.
- Where a comparable program's record of the condition left a combination out (`truncated_by`: the record keeps the least combinations up to a bound, "Guard outcomes"), an atom without a pair is `undecided`: the pair may be among those left out.
  An undecided requirement is neither covered nor open (`counts.undecided`); it keeps its target, which says why, and counts in `summary.open`, since nothing has settled it.

Under a selection the requirements family has `mcdc` (`{rules, obligations, covered}`, `rules` the selected rule ids) and `counts.undecided`, and a selected rule's guard keeps its `combinations`; every other guard drops them, so without a selection the document is what it was.
A name that selects no rule whose condition states requirements (a misspelling, a rule the definition no longer has, an unconditional rule) is refused at stage `coverage`, reason `mcdc-stale`, before any mutant runs.
Selecting rule by rule is the author's judgement: a unique-cause pair per atom multiplies the obligations, and operands that coupling makes inseparable are common, so the level belongs where each operand deserves to be shown deciding.

**Syntax (depth 1).** Each production of an authored sort, an item `{kind: "production", id, module, index, file, start_line, sort, production, symbol, text, status, covered, reached_by, inspected_by, operand_of, built_by, uncounted, touched_only_by, inspecting, building, inspecting_rules, building_rules}`.
The authored sorts are the front end's where it gives them (`FlowManifest::with_syntax`), else every sort the specification's own sentences declare and no library sentence declares: a library sort's meaning is the library's, so a production an author adds to it is not counted.
A production is an obligation when it builds a term with a constructor of the compiled definition: a function's application is evaluated away, a token is a domain value, a bracket and a subsort are erased, a macro is expanded and a cell is the configuration's, so none of these is.
The universe is a function of the definition and the front end's selection.

A production is `reached` when a fired instance of a sentence of the rules universe (status `fired`, `matched` or `unmatched`), in some comparable program's baseline run, touched it:
- inspected: the production is at a non-variable position of the sentence's left-hand side (`inspected_by`);
- an operand: it is the head, through injections, of a value the instance bound to a variable of its left-hand side that the sentence reads elsewhere: in its right-hand side, `requires` or `ensures`, twice in its left-hand side, or under a concreteness attribute (`operand_of`);
- built: it is at a non-variable position of the right-hand side (`built_by`).

An axiom with several alternatives touched only what the alternative its instance took inspects and builds: k-rust loads one rule per disjunct of a left-hand side `A #Or B` (and per reading of a function equation's argument binders), all under one `UNIQUE_ID`, and a rewrite rule with a disjunctive right-hand side builds one successor per alternative, so the sentence's fired status cannot tell them apart, and the backend records the alternatives the fired instances took (the record's `coverage.bindings.alternatives`).

A production elsewhere in a state was carried, not touched, and stays `unreached`, and so does a value a sentence binds and never reads, such as the old value of a cell a rule overwrites (`<c> _ => v </c>`): the step is the same whatever it holds, so it carried the value to its end and dropped it. The initial state holds the whole program, so "anywhere in a reached state" would read every production of a branch no run took, and a value in a cell no rule reads, as reached; "at the head of `<k>`" would miss the values a step passes to a function or keeps in a cell, and would depend on how strictness presents a term.
Only the head of a bound value counts, so a continuation, which binds a sequence, never counts the rest of a program; the one over-claim left is a statement a sequencing rule takes as an operand and nothing runs afterwards, whose own rules stay unfired in the rules family.
Inspected and built are static per axiom alternative, read from the loaded axioms once (kink-native `syntax_facts`; a function equation's argument patterns are in its left-hand side) and joined with the record's fired sentences, and, for an axiom with several alternatives, with the alternatives its fired instances took; the operand heads are what the backend recorded at the fired instance (the record's `coverage.bindings`).
A production of a sentence whose syntax facts the backend's definition could not give is not counted: the family then has its `reason`, and null `obligations`, `covered`, `measure` and `counts`, as has its entry of `summary.per_family`.
`inspecting` and `building` list the sentences of the rules universe that inspect and build the production (`inspecting_rules` and `building_rules` by rule id), whichever programs ran: what an author makes fire to reach it.
The measure is reached / obligations; `counts` gives `reached`, `unreached`, and productions and field values apart (`productions`, `field_values`: `{obligations, covered}`).

Field values are a front end's: a value of a field of a `k::bits!` template is reached when some fired instance of the template's sentence bound its binder to a value with that field.
K has no notion of such a template, so kink-flow selects no binder and builds no field-value item.
A front end that has templates names their binders in its selection (`SyntaxSelection::binders`, `(axiom, variable, cap)`), every baseline run records the values they took, and the family lists them (`binders`: per binder `{axiom, variable, sentences, values: [{value, programs}], truncated_by, nonliteral_by, uncounted}`); the front end adds an item of kind `field-value` per field value of its universe, with its `status` and its target's text (`krs.target`), before `coverage::derive` counts them.

**Flips.** Tier 2: each condition flip a front end derives from the definition's source is an obligation.
A flip negates one condition atom, or toggles one bit of an encoding, in a closed set of sentences that the atom keeps apart, so the flipped definition is one the source language admits and the question is whether the corpus notices the swapped outcomes.
Generating the flips needs the source language's guard families and admitting each needs its judge, so the front end supplies the list: each entry with its id, its operator (`flip` or `bitflip`), the atom's text, its judgement (the K patch, in `MUTATIONS.toml`'s edit format, or the judge's refusal) and the occurrences it changes, each a node of a sentence's condition (by its path in the rule item's `guard.operands`) or a sentence's match.
A flip every occurrence of which changes a sentence outside the shared scope (a claim helper, an invariant-only equation or an equation only declared ends reach, above) is no obligation: kink-flow moves it to `not_generated` as `{reason, id, atom, sentences, pair, detail}`, `reason` the status (`claim-helper`, `invariant`, `declared-end`) of its first occurrence's sentence, in occurrence order, and `detail` each sentence's status, before any run, whatever the front end gave, so the list stays a function of the definition and no mutant is spent on it.
A flip that changes some sentence in the scope stays an obligation of those sentences, with all its edits, and keeps only its occurrences in the scope: the scope sets a sentence aside, not a flip, and an edit outside it adds nothing a family counts, so a program that reaches only an occurrence outside the scope meets no obligation.
Each obligation is an item `{id, operator, text, atom, occurrences, sentences, status, kink_status, judge, reason, next, detail, digest, killer, killer_source, recorded_killer, killer_change, witnesses, horizon, causes, waits_on, live_runs, calls}`:

| Status | Counted | Meaning |
| --- | --- | --- |
| `distinguished` | yes, covered | the kill search killed the mutant; `killer` is the coverage lock's recorded killer while it still kills, else the first killing program in the search's order ("The corpus record") |
| `undistinguished` | yes, open | the search ran the mutant on every comparable program, and none told it apart |
| `unreached` | yes, open | no comparable program reached an occurrence in the scope (below): deduced, with no mutant run |
| `unknown` | yes, open | the search gave no verdict (kink's `unknown` or `timeout`, or an error), with kink's reason where one holds for the whole search, and each executed program's cause (`causes`, `[{program, cause}]`, in the search's order; empty for every other status) |
| `refused` | no | the front end's judge, or kink-flow's resolution or admission of the patch (`judge`), refused it, with the reason: a disagreement between the generator and an admission, which a definition's tests pin to zero |
| `equivalent` | no | kink proves no program can tell the mutant apart (its `equivalent` or `unkillable` status) |

These are not kink's `killed` and `survived`: an `unreached` status rests on a deduction, not on runs, and the family reports what the corpus covers.
The measure is distinguished / (obligations − refused − equivalent); `counts` gives each status and `not_generated` the flips the generator does not generate (listed apart with their reasons, never counted); `search` gives the search's `outcome_cache` counts and its `live_runs`.
Every admitted flip is resolved first: one kink-flow cannot resolve is `refused`; one whose occurrences no comparable program reached is `unreached`; every other one runs, in the list's order, through `run`'s kill search, first-kill, with its outcome cache.
An outcome record is keyed by the mutation's patch digest, never by its id or its list, so a flip equal to an authored mutation shares its records: what `run` learned of a program, `coverage` decides from the cache, and the other way round.

The unreached deduction reads the comparable programs' cached records.
A condition node is reached where it took an outcome (`true`, `false` or `undefined`) in the rule's guard row; a match is reached where the sentence was entered at the front end's level (`krs.matched_by` where the front end reads templates, else `matched_by`).
An occurrence is undecided, and counts as reached, where the records cannot say it was not evaluated: a node a program left undecided, a guard a program left undecided or stopped in or the solver refuted (the solver reads every atom of the condition), a program whose recorded coverage is not complete, and an occurrence the rows do not place (no rule item, no guard, an unreadable skeleton, no node at the path; `unplaced` says why); a flip that names no occurrence is undecided too.
A flip is `unreached` when it names occurrences in the scope and none is reached or undecided.
It is sound for the flip of the sentences in the scope: the flip changes only those occurrences, in place, and the operands before each are unchanged, so the mutant's run reaches the same positions with the same states, and by induction on the steps of a baseline run that never evaluates an occurrence, the mutant's run takes the same steps, every guard verdict and every function value it uses agreeing; for a bit flip the closed set of arms has a domain the toggle maps onto itself, so an input no arm of it matched matches none in the mutant either.
So no comparable program can tell the flip apart, and running it would say no more; the deduction saves the costliest outcome, a survivor run on every program, and points at the tier-1 obligations that explain it (`waits_on`: the open requirements of a node, else the rule).
Each occurrence lists `reached_by`, `undecided_by`, `unplaced`, a node's `true_by` and `false_by`, and its `rule`.

Under `--tier 1`, or where the front end derives none, the family is `{tier: 2, run: false, obligations, reason, items: []}`: `obligations` is the derived count under `--tier 1` (null where none is derived) and no status is shown, since a status read from the cache alone would depend on what the cache holds.
kink-flow's own front end derives none: it reads K alone, which gives neither the guard families nor a judge, and the family's `reason` says so.
krs's front end derives and judges a definition's condition flips and gives coverage every one, refused ones too, each with the guard nodes or the arms it changes; a definition with no flip has `run: false` and krs's reason.

**Rule windows (depth above 1).** At depth `d` above 1 (`[coverage] depth`, or `--depth`), each window of length `2..=d` of the may-follow graph is an item `{kind: "window", id, length, rules, rule_ids, status, covered, covered_by, uncounted, touched_only_by, frontier, pattern}`, `rules` the window's sentences `{module, index}` in step order and `rule_ids` their rule ids; at depth 1 the family is `null`.
A window is a sequence of rewrite rules some path took as consecutive committed steps (k-rust `coverage.windows`; under a state set, a path merged into a state explored earlier takes the windows that go on into that state's successors, so the windows are those of the path set).
Its windows of length 1 are the rules family's fired rules, so the family starts at length 2; equations take no step, so none is in a window, and neither is a heating or cooling rule, whose sentence is a production or a `context`, not a rule: a window with such a step between two authored rules is no window of theirs.
The universe is the walks of the may-follow graph over the rules family's authored rewrite rules: rule `B` may follow rule `A` when `A`'s right-hand side unifies with `B`'s left-hand side, every function application, builtin-domain value, collection and conjunction read as a fresh variable, each occurrence of a variable its own, through injections, a variable unifying with a constructor its sort may hold, and conditions ignored (kink-native `coverage::may_follow`).
The successor of a step of `A` is the normal form of an instance of `A`'s right-hand side, and normalization leaves every free constructor in place, so wherever the right-hand side has a free constructor below free constructors, the successor has it, and a rule whose left-hand side matches the successor unifies with the right-hand side: the universe over-approximates what can follow, and never omits a window a run can take.
A `K` sequence whose first element is a `K`-sorted variable or computed term is read as a fresh variable too: that element may be the empty sequence or several items, which shifts every later element.
A window of authored rules that a comparable record holds and the graph lacks would be a failure of that argument: it is listed in `outside_universe` and not counted.
A window is `covered` when some comparable program's record holds it, else `open`.
The measure is covered / obligations over every length, and `counts` gives `covered`, `open`, `argued`, `frontier` and `by_length` (`{"2": {obligations, covered}, ...}`); `nodes` and `edges` give the graph's size.

The universe's size is computed from the graph before any program runs, as a count of walks.
A universe above `[coverage] max_obligations` refuses the command at stage `coverage`, reason `max-obligations`, before any program runs, its detail giving the count of each length and the graph's size: the count grows with the graph's branching to the power `d - 1`, and a budget is the author's statement of how many obligations a corpus is meant to answer, so the command does not guess a smaller depth.

A target is listed only for a window on the frontier (`frontier`): an open window whose first `length - 1` rules are covered, as a window, or, for a window of two rules, as a fired rule; the measure still counts every window.
A window off the frontier extends an open rule or an open window, whose own target comes first, so an agent extends what the corpus already does.
The target asks for a case whose run takes a step of the window's last rule right after its other rules, names the programs that took those as its templates (`programs`), and carries as `pattern` the unifier of the right-hand side of the last rule but one with the left-hand side of the last rule, every abstracted subterm and every variable a fresh variable (`W0`, `W1`, ...), printed as K: a `PATTERNS.toml` pattern of the configurations a step of the one leaves that the other can match, which `query` and `fuzz --pattern` take; null where the printer cannot print it.
Its `fuzz` is `null`: no fuzz job's facts name a window.
A window no run can take is argued (`[[coverage.argued]]`, by its id); a window containing a part (a rule, or a shorter window) that an entry argues while no program covers it is `argued` too, with `argued_by` naming the part and its argument: a path that takes the window takes each of its parts as consecutive steps.
Each window id is `window:<rule>,<rule>,...`, each rule by the name its rule id gives it, so a front end's names are in it (`window:crate::step,crate::stop`).

**Syntax paths (depth above 1).** At depth `d` above 1, each path of length `2..=d` of the grammar graph of the syntax family's productions is an item `{kind: "path", id, length, symbols, positions, status, covered, covered_by, uncounted, touched_only_by, frontier}`, `symbols` the productions' symbols outermost first and `positions` the 0-based argument positions between them; at depth 1 the family is `null`.
A path `(P1, i1, P2, ..., Pn)` is a sequence of productions along consecutive argument positions, `P(j+1)` at argument `ij` of `Pj`.
It is `reached` when a fired instance of a sentence of the rules universe, in some comparable program's baseline run, touched it, else `unreached`; a sentence outside the shared scope (a claim helper) is no sentence of the rules universe, so its fired instances reach no path.
The terms an instance touched are its left-hand side and the right-hand side alternative it built, under its substitution: it inspected the left-hand side's own positions, built the right-hand side's, and took as an operand the value of each variable it reads (as the syntax family reads it).
A path is touched when it starts at one of those positions (a non-variable position of either side, or the root of a read variable's value) and descends through argument positions of those terms, so its first production is reached in the syntax family, and its paths of length 1 are the syntax family's reached productions.
Only those starts count: a step touched the root of a value it took and none of the positions below it, which it carried, so no path starts below a value's root, and a value a sentence binds and never reads gives none; a path reaches into a value no further than `d - 1` positions below the position it starts at.
A function application, a cell, a `K` sequence, a collection and a builtin value break a path: the paths through a list stop at the list, and its elements start paths of their own where a sentence writes them; a function's argument is the function's to evaluate, not a position of the production around it.
k-rust records the paths at the fired instance (`collectBindings` with a `depth`, the record's `coverage.bindings.paths`), and reads each length the same way at every depth, so a record collected at `D` answers every depth up to `D`.

The universe is the walks of the grammar graph (kink-native `coverage::grammar_graph`): production `Q` may stand at argument `i` of `P` when `Q`'s sort is at or below the sort of `P`'s argument `i`.
A well-sorted term holds an application of `Q` at that argument directly or below a subsort injection, so every path a run records is a walk of the graph, and the graph, which reads sorts alone, over-approximates what a run can touch: it never omits a path a run can take.
A path a comparable record holds and the graph lacks would be a failure of that argument: it is listed in `outside_universe` and not counted.
The universe's size is computed before any program runs, as a count of walks, and held to `[coverage] max_obligations` as the rule windows' is ("Rule windows"): a universe above it refuses the command at stage `coverage`, reason `max-obligations`, its detail giving the count of each length and the graph's size (`productions`, `edges`); where both families exceed it, the detail gives both.
The measure is reached / obligations over every length, and `counts` gives `reached`, `unreached`, `argued`, `frontier`, `by_length` (`{"2": {obligations, covered}, ...}`), and the paths and the joint field values apart (`paths`, `field_values`: `{obligations, covered}`).

A target is listed only for a path on the frontier (`frontier`): an unreached path whose first `length - 1` productions are reached, as a path, or, for a path of two, as a production of the syntax family.
It asks for a case in which a fired step touches the path's first production holding the next at its argument, and so on (`a case in which a fired step touches exec holding neg at argument 0; the comparable cases that reach exec: mov`), names the programs that reached its prefix (`programs`), and is placed at its first production's declaration; its `pattern` and its `fuzz` are `null`: no fuzz job's facts name a path.
A path off the frontier extends an unreached path or production, whose own target comes first.
A path no run can take is argued (`[[coverage.argued]]`, by its id); a path whose first production, or one of whose prefixes, an entry argues while nothing reaches it is `argued` too, with `argued_by` naming that item and its argument: an instance records only paths that start at a position it touched, and with a path each of its prefixes. A later production of a path argues nothing: it lies below a touched position without being touched itself, so a production no step touches can still be reached by a path.
Each path id is `path:<production>/<position>/<production>...`, each production by the name its syntax id gives it, so a front end's names are in it (`path:crate::Instr::Ld/0/crate::R8::B`).

The joint values of a template's fields are a front end's, as its field values are: kink-flow builds none.
A front end that has `k::bits!` templates adds, at a depth above 1, one item of kind `field-values` per combination of a template's field values its arm domain gives, for a template with several fields (the paths of length 2 through the template, whose fields are its arguments), `{kind, length: 2, status, covered_by, uncounted, frontier, programs, krs}`, with its own frontier, its target's text (`krs.target`) and the field values it joins by name (`krs.parts`); kink-flow names it `path:<krs.item>`, and a field value argued while unreached argues every combination that holds it.

The measure is per family: no weighted total is given, since nothing weighs a rule against an operand's truth.
`summary.open`, the count of open targets, is the one scalar, and zero means done: every obligation is covered or argued ("Argued obligations"); an open rule window off the frontier has no target, but it extends an open rule or window, which has one, or an argued part, which argues it, and so does an unreached syntax path off the frontier, which extends an unreached production, path or field value, or an argued one.

Every item has a stable `id`: `rule:<name>`, `requirement:<name>:<detail>`, `syntax:<production>`, `window:<rule>,...` and `path:<production>/<position>/<production>...`.
A rule's name is its KRS item where a front end named it (`krs.item`), else its label, else its `file:line`, with `:<label>` added where two rules share a name; a requirement's detail is `held`, `refuted`, or the node's text (the front end's source text where it gives one, else the K text, with `@<path>` added where two nodes of one condition share a text) and its truth; a production is named by its front end (`krs.item`) where it names it, else by its K label, with `@<sort>` added where two share a name, `@<symbol>` where two share a name and a sort, and `#<n>` for the `n`th of items that share all three; two declarations of one label build terms of one symbol and are one production, listed at its first declaration.

### Argued obligations

Some obligations no program can cover: a requirement whose truth no reachable state gives, a rule kept as a defence against a state the definition never builds, a flip whose atom no reachable state decides.
The corpus's author argues such an item instead of chasing it, in `FLOW.toml`:

```toml
[[coverage.argued]]
item = "requirement:GUARDS.wake:held"
argument = "no program halts the machine, and only a halted machine wakes"
```

`item` is the obligation's `id` as the document names it, in any family: a rule, a requirement, a syntax production or field value, or a flip (a front end's ids where it names the items, such as krs's `syntax:crate::Instr::Jump`).
`argument` is a nonempty text for the reader, which nothing parses; an entry has exactly these two keys and, optionally, `invariant` (below), and an item is argued at most once.

- An argued open obligation has status `argued`, keeps the status it would have as `unargued_status`, and carries its `argument`.
  It stays in its family's obligations, so the measure, covered / obligations, does not move: an argument is not a program, and the measure states what the programs cover.
  It is neither covered nor open, so it has no target; each family has `argued` and `counts.argued` (taken from the count of the status it had), and the summary counts it apart.
- An entry whose item no family lists refuses the command at stage `coverage`, reason `argued-stale`, naming each such entry, before any mutant runs: it is a misspelt id or an item the definition no longer has, and its argument is about no obligation the document counts.
  A flip's id is listed where the front end derives the flip, under `--tier 1` too, so a manifest is valid under one tier where it is under the other.
- An entry whose item a program covers, or that is listed but no obligation (an out-of-scope rule, a refused or equivalent flip), is a needless argument: the item keeps its status and carries the argument with `argument_needless` (`covered` or `not-an-obligation`), `summary.needless_arguments` lists it (`{family, item, reason}`), and the command exits 1.
  An argument kept on a covered item would turn its next regression into `argued` instead of `open`, hiding the gap coverage exists to show; and where the argument claimed the item cannot be covered, the program refutes it.
  Remove the entry.
- A flip's argument is judged where the flips run; under `--tier 1` the family shows its obligations alone.

An argument can rest on an invariant, a property claimed of every state the baseline definition reaches, which the entry names:

```toml
[[coverage.invariant]]
name = "memory-outside-rom"
function = "crate::machine::MemoryOutsideRom"   # krs: a KRS path; kink-flow's K front end: a K label
cells = ["memory", "rom_end"]                   # krs: Rust field paths; K front end: K cell names

[[coverage.argued]]
item = "requirement:crate::micro::read_z:refuted"
argument = "a write into the ROM region stores nothing, so memory never holds a ROM address"
invariant = "memory-outside-rom"
```

- A `[[coverage.invariant]]` table has exactly `name`, unique among the tables, `function`, a Bool function of the cells compiled into the baseline definition, and `cells`, the cells it reads, one per parameter, nonempty and without repeats; an entry's `invariant` names a table the manifest declares.
  Entries share an invariant by its name.
- An invariant argues the `rule:` items of rewrite rules and their held, refuted and node requirements: it is a property of states, and an item's argument rests on it through the rule's left-hand side, a whole configuration whose cells the invariant reads, with the valuation that defines the item.
  An entry that names one on any other item is refused at stage `coverage`, reason `argued-invariant-unsupported`, naming each such item with what it is:
  `equation`, whose left-hand side binds a function's arguments, not cells;
  `out-of-scope`, `claim-helper`, `invariant` or `no-coverage-signal`, a rule that is no obligation, or a requirement of one;
  `mcdc`, a unique-cause requirement, whose obligation is a pair of runs showing one operand's independent effect, not a valuation at one left-hand side;
  `syntax`, `rule_windows` or `syntax_paths`, none of which is one left-hand side with a valuation;
  `flip`, which changes the definition, of whose runs an invariant of the baseline says nothing.
- A table no entry names is refused at stage `coverage`, reason `invariant-unused`: it would be resolved and checked on no item's behalf.
  Where both apply, the first refusal also names the tables that only its refused entries name, which removing those entries' `invariant` would leave unused, so that one run names both.
- Each argued item has `argument_check`, what its argument rests on, and its `standing`: `text` where its entry names no invariant (`{standing: "text"}`); under an invariant, `{invariant, standing, reason, function, connection, evidence, proof}`.
  The standings are `text`, `connected` (the connection holds and the evidence is vacuous), `checked-on-runs` (both hold), `proved` (also a proof) and `unchecked` (a check did not decide, or did not run).
  An item argued by a part (`argued_by`) has the part's `argument_check`.
- Once every entry names an item an invariant can argue, the front end resolves each table's `function` and `cells` to the definition's KORE symbol and cell paths, before any mutant runs.
  kink-flow's own front end reads K: the function by its K label, the cells by their K names; `krs kink` reads KRS: the function by its KRS path, the cells by Rust field path, through krs-exec's resolver, as `[stop] when` is.
  Refused at stage `coverage`: a function or a cell the front end cannot resolve (reason `invariant-unresolved`, with the front end's message: a function the definition does not hold, not a function, parametric, or not one parameter per cell; a cell the configuration does not have, or one that is or lies below a `*`, `?` or unobservable cell), a function whose result is not Bool (`invariant-not-bool`), and any invariant where the front end resolves none (`invariant-unsupported-front-end`).
  `settings.invariants[].identity` is what the checks are about: `{definition, symbol, cells}`, the execution digest, the KORE symbol and the cell paths, and under `krs kink` also `function`, the KRS path it resolved to, and `definition_ir`, the Definition IR digest.
- The connection checks each argued item under an invariant: a run covers the item with one of the facts `fuzz --cover` searches for (a guard node reached with a truth, a guard outcome, a firing), each a valuation of one compiled axiom at its left-hand side; for a `rule:` item, which only a firing covers, its condition holding, whether or not the rule was matched.
  A fact that names its rule otherwise than by its `UNIQUE_ID` is kink-flow's own error, which refuses the command (`internal-error`).
  For each fact, kink-native asks whether the invariant applied to the left-hand side's cells and the valuation have a model there.
  `argument_check.connection` is `{status, axioms, reason, model, cached, smt_unknown}`: `holds` where no fact has one, `fails` where kink shows a state the axiom matches that satisfies the invariant and the fact, else `undecided` with `reason`, the first undecided fact's cause; `axioms` lists each fact `{axiom, valuation, answer, reason, cached}`, `model` is null (no model is reported), and `smt_unknown` counts the solver's `Unknown`s.
  Each rule's decision is bounded by a budget of the backend's polls, kink-native `invariant::EVALUATION_POLLS` (10,000,000; kink-native `invariant`, "The work bound"): the simplifier's iteration budget does not count a determined step of a ground function application, so without it a question that applies a function rewriting a ground term without end would never be answered; a decision that spends it is undecided, with a reason naming the bound.
  Each answer is kept in the cache's connection memo under the execution digest, the axiom, the valuation, the symbol and the cells, kink's build and the solver, where each of its rules' answers is connected, not connected, or the solver's `Unknown` (a missing solver, a solver or simplification failure, a stop, the work bound, an approximate model or an instance not shown is asked again); `--verify` reads and writes none, and `cached` is true where every answer was read from it.
  `proof` is null.
- A connection that holds shows only that the invariant excludes the item at its rule's left-hand side, not that the invariant holds of any state the definition reaches: an invariant false everywhere excludes everything.
  Its premise, that the invariant holds at every reachable state the left-hand side matches, is tested on the corpus's runs by the evidence.
  At a state the left-hand side matches, some rule takes a step and its left-hand side matches too, so it unifies with the item's (kink's may-follow unification, every function application, builtin value and collection read as a fresh variable), or the state is an end.
  So a state of a path where the left-hand side matches is before a step of a rule of `S_R`, the rewrite rules whose left-hand side unifies with one of the item's axioms', or an end, or the last state of a path that ends at an undefined step, or the state at which a bound cut the path.
  The evidence reads the invariant at the initial state, before every step of `S_R` and at every end; it reads no state of the last two kinds, so a run with an undefined step, or a `comparable-prefix` program's run, leaves it incomplete.
- One evidence run per invariant and comparable or `comparable-prefix` program, over the union of the `S_R` of its entries whose function check is not `not-shown` (below): the program's baseline run with the corpus's `[stop]` and budget, observing one point class per rule label, each before its rule's steps, every event an element, whose content is the invariant evaluated in the baseline definition with its equations on the proof route; a value is decided only at a ground `true` or `false`.
  The corpus's `[observe]` plays no part, and the run is not the program's result record: no invariant channel takes part in a comparison, and editing an argued entry changes no record `run` reads.
  The budget's `time_ms` bounds the program's run, not the reading of it: each evaluation of the invariant is off the run's clock, so a program the baseline ran within its bound is read at the states of that run, whatever the invariant costs to evaluate; an evidence run the watchdog stops all the same gives no sides, and the reason says so, with how many evaluations the run made and their time, and the evidence's `clock_stopped` names the program, so that the coverage lock keeps the standing it recorded ("What decides a verdict").
  Each evaluation, at a point, at the initial state and at an end, is bounded instead by its own work bound, the connection's budget of polls: the simplifier's iteration budget does not count a determined step of a ground function application, which every evaluation of ground cells takes, so it bounds nothing here.
  The bound is spent by the evaluation's own polls, not by the host's time; an evaluation it cuts is undecided, and the state leaves the evidence `incomplete`, never `fails`.
  It is a bound per evaluation, not a total of the run: a total would make whether a state is read depend on what every evaluation before it cost.
  A cut leaves every item the state serves unchecked (the items whose `S_R` holds its rule; every item, for the initial state and an end), and only a `false` could still change their answer, so after it a state is not evaluated where every item it serves is unchecked already: its element is undecided, the reason counts the states and ends not read, and where the initial state is cut the evidence run is not made.
  A state an item still checked is served by is read as before, so a `false` found before the cut or at such a state refutes as before; each cut leaves one more item unchecked, so a program's run makes at most one cut per item, besides one at the initial state or an end, whatever its length.
  An undecided state's reason says why the evaluation did not decide (a condition left, a spent simplification budget, the work bound, which it names, no `Bool` value).
  Only states of real, clean paths count (the channels' leaf rule, "What a run observes").
  A run of several paths is read through its prefix sets, which keep only the nearest index at which some path stops being explored: where a channel has one, what the other paths hold past their own such point is not known, and the channel is undecided.
  What each run reads is kept in the cache's evidence memo under the program's result key, the invariant's identity and the labels observed, except a record with an evaluation the work bound cut or the host decided (the simplifier ran out of native stack, or the system refused a stack): where the bound cuts is the count of the evaluation's polls, which is not shown to depend on the cells, the definition and the bound alone (kink-flow `coverage::evidence`, "The cache"), so such a record is computed again by the next command; `--verify` reads and writes none, and `summary.invariant_runs` is `{run, cached}`, the evidence runs this command ran and read from the memo.
- `argument_check.evidence` is `{status, rules, states, steps, programs, stepped_by, failure, reason, cached, clock_stopped}`: `rules` the item's `S_R` (labels, or `UNIQUE_ID`s of rules with none), `states` the states read for the item (each program's initial state, its steps of `S_R` and its ends), `steps` those before a step of `S_R`, `programs` the programs read, `stepped_by` those of them whose run read a step of `S_R` (since coverage document version 24), `cached` whether every program's record was read from the memo, `clock_stopped` the programs whose evidence run the clock (`budget.time_ms`) stopped (since coverage document version 21), and `status`:
  `fails` where some state read gives `false`, with `failure`, `{program, at, rule, index, cells, cells_missing}`, the first such state in path order (the initial state, the steps, the ends; `at` `initial`, `step` with the rule's label and its arrival index, or `end` with the end's index; `cells` the cells read there as KORE, or null with `cells_missing` saying why: in a run of several paths, whose record orders no state across rules, or where the run's log of its evaluations is not its record, the failure is the first `false` of the first rule in label order that has one);
  `incomplete` otherwise where a state of the item's set is undecided, a program is not comparable or its evidence run gave no sides, a path ends at an undefined step (whose state is no end and no point), a bound cut a prefix program's run, a path of a run of several paths stops being explored, or a rule of `S_R` has no label a run observes it by, with `reason`;
  `holds` where every state read gives `true` and one is before a step of `S_R`;
  `vacuous` where every state read gives `true` and none is: nothing tested the premise at a state the item's rule can match.
- Both checks evaluate the invariant's function with the backend's choice of matching, and the connection also the functions of the item's valuation, the rule's guard functions among them, since it simplifies the whole question; each check presupposes that the equations it uses define functions: one value at each input, whichever equation and whichever binding of a collection pattern is chosen.
  `argument_check.function` is `{status, findings, reason}`: `findings` lists every finding of the baseline's full critical-pair check (the document's `data`) that involves an equation of a function the item's connection question applies, the invariant's function and its valuation's, or that such a function reaches (the reach of "Families"), `{name, verdict, assumed, description}`; `status` is `shown` where there is none and the check is complete, `assumed` where each is assumed by a `[spec] assume_joined` name, and `not-shown` where one is not, or the check is incomplete, with `reason` naming each function of the question whose reach holds such a finding, the findings, and for the invariant's own function the canonical form below.
  An item not shown to rest on functions is `unchecked` with that reason (so `coverage` exits 3), and refutes nothing: a failing connection or evidence read the functions at one choice, and another could give them other values there.
  The function is checked before the evidence, and such an item's evidence is not read (`argument_check.evidence` is `{status: "not-run"}`): no state's value could refute or credit it, so the evidence runs of an invariant observe only the rules of its other items, an invariant whose every item is `not-shown` makes none, and `summary.invariant_runs` counts only the runs made.
  An `assumed` function keeps the standing the checks give, which rests on that premise besides: the verdicts rendering, so the coverage lock, names it (`{ id = "<id>", standing = "checked-on-runs, assuming joined <name>, ..." }`), so that a premise added or removed moves the lock.
- The standing is `checked-on-runs` where the function is not `not-shown` and the connection and the evidence hold, `connected` where the connection holds and the evidence is vacuous, and otherwise `unchecked`, with `argument_check.reason` naming the function's, the connection's or the evidence's cause (what each standing trusts: kink's `trust.md`, "What an argued item's standing trusts").
  An `unchecked` item makes `coverage` exit 3: a corpus whose argument rests on an invariant no check confirmed is done only by its own claim, so the answer is inconclusive.
- A connection that fails refutes the argument, and so does an evidence that fails: the invariant is false at a state of a run, so it is no invariant of the definition.
  The item is not argued but keeps its status, its target and its argument, and gains `argument_failed`, `{check, detail}` (`check` `connection` or `evidence`); `summary.failed_arguments` lists it, `{family, item, check, detail}`, and `coverage` exits 1, with or without `--locked`. An argument stands in for a program, and a refuted one stands in for nothing.
- `summary.argued_by_standing` counts the argued items by standing, `{text, connected, checked_on_runs, proved, unchecked}`, adding up to `summary.argued`.
- The text rendering states each argued item's standing, and its invariant where it names one (`  requirement:x:held [unchecked, invariant ordered]: <argument>`), and lists each refuted argument under `failed arguments:` (`  rule:x [the connection fails]: <detail>; it is open again`).

Write an invariant that holds of every binding of a collection as its violation: one equation that gives `false` where some binding breaks it, under a condition on that binding, and an `owise` equation that gives `true`.
In K, for a memory whose keys lie outside a ROM region below `E`:

```k
rule outsideRom((K:Int |-> _) _, E) => false requires inRom(E, K)
rule outsideRom(_, _) => true [owise]
```

and in KRS:

```rust
#[k::requires(InRom(rom_end, addr))]
#[k::equation]
fn memory_in_rom(k::term![MemoryOutsideRom(map![addr -> _, ..], rom_end)]: Term<Bool>) -> Term<Bool> { false }
#[k::equation(owise)]
fn memory_outside_rom(k::term![MemoryOutsideRom(_, _)]: Term<Bool>) -> Term<Bool> { true }
```

Why it is a function: the map pattern can match one map at any of its bindings, so the critical-pair check pairs the first equation with itself; its result, `false`, reads no variable the choice binds, so every choice whose condition holds gives the same value, and the check joins the pair by that syntactic rule, with no premise.
The `owise` equation is a priority group of its own, applied only where no binding satisfies the condition, so it overlaps nothing.
The connection decides it at a rule's map pattern: the `false` equation applies at the rule's own binding under the obligation's condition.
A recursive walk, `outsideRom((K |-> _) M, E) => notBool inRom(E, K) andBool outsideRom(M, E)`, reads the binding the pattern chose, and the check's model does not join its two-binding peak: in it a total function's stuck application is a normal form and `andBool`'s executable equations are literal-first, so `g1 andBool (g2 andBool F(R))` and `g2 andBool (g1 andBool F(R))` are distinct normal forms.
The walk is reported as a finding, which leaves every argued item on it `unchecked`, and makes every mutation `unknown` (`baseline-findings`) unless `[spec] assume_joined` names it.
The same violation form covers several bound entries, pairwise properties and nested collections; combine two invariants as a function `G(..) andBool H(..)` of two such functions rather than two `false` equations in one function.
The invariant's function and any function only it applies are no obligation of any family ("Families"); a function the semantics also applies (`inRom`, which a read rule's condition applies) stays one.

The verdicts rendering lists each family's argued ids beside its open ones, each with its standing (`{ id, standing }`), and an argued flip's status `argued` with its `standing`, so adding or removing an argument, or a standing that moves, moves the coverage lock; rewording one does not ("Verdicts").

### Targets

`targets` holds one entry per open obligation, in tier, family, then sentence order: `{family, item, text, file, line, programs, pattern, fuzz}`, and a syntax target also `rules`.

- An `unmatched` rule asks for `a case whose run reaches a state that <rule> matches`, with `fuzz`, the `fuzz --matched` job of a rewrite rule (of a function equation, `fuzz --cover <item>`), and `pattern`, the rewrite rule's left-hand side as a `PATTERNS.toml` pattern (below).
- A `matched` rule asks for `a case where <rule> is entered and its condition holds`, naming its open requirement `held`, with the programs that entered it (`programs`, the templates of a fuzz job) and the `fuzz --fired` job of a rewrite rule (of a function equation, `fuzz --cover <item>`).
- An open heating rule asks for `a case whose run brings <production> to the front of the computation with a term that is not a result as its argument <position>, so that heating evaluates it` (for `seqstrict`, with results as the arguments before it; for a context, `reaches a state the context <context> matches with a term that is not a result in its hole`), adding, for a `matched` one, that the comparable runs that reached it did not, with those programs, and the `fuzz --cover <item>` job; `pattern` is `null`.
- A requirement asks for `a case that enters <rule> with <valuation>`: the truths of `reaching`, then the node's own; each step of `reaching` is an author's node and its truth, a negation restated as its operand with the other truth, so an `else` reads as the condition before it `false` (`a case that enters f with x < 0 false, y < 0 true`), and a negation inside a compound step is written `!` before its operand (parenthesized unless one token); for the root, its condition holding or false, with the valuation of its node where it has one; with the `fuzz --cover <item>` job, except for a unique-cause requirement, whose `fuzz` is `null`.
- An unreached production asks for `a case in which a step takes <production> as an operand, or inspects or builds it`, naming the rules that inspect it and those that build it (`rules`, both), each a thing to make fire; a production no rule writes says that only a step that takes it as an operand reaches it. A field value states the front end's text. Both have the `fuzz --cover <item>` job, a field value only where its item names the binder it reads (`binder: {axiom, variable, encodings}`, the front end's).
- An item with `touched_only_by` adds the programs that touch it but are not comparable, and asks to make one comparable.
- An `undistinguished` flip asks for `a case whose result changes when <atom> is negated in <rules>` (`toggled` for a bit), naming the values of the atom the corpus reached in each rule, with the programs that reached an occurrence (`programs`, the templates of a fuzz job) and the `fuzz --kill <flip id>` job.
- An `unreached` flip asks for `a case that reaches <atom> in <rules>`, naming the tier-1 obligations it waits on, the open ones then the argued ones.
- An `unknown` flip asks for a comparable run of its mutant, with why kink gave no verdict: kink's reason, else its status where it is not `unknown` (`timeout`, `error`), then each executed program's cause (`kink gave no verdict (timeout; p1: <cause>; p2: <cause>)`).

`file` and `line` are the front end's position of the rule where it gives one, else the K source's.
`pattern` is, for an `unmatched` rewrite rule, its left-hand side as K text that `query` and `fuzz --pattern ID --patterns PATTERNS.toml` take ("Checking a pattern"): the rule's body as written, each rewrite replaced by its left side, without the `requires`, each variable written without a sort given the sort the rule's parse inferred for it, and, where the compile places the rule in the main cell (a body of one item that is no cell, for a rule that is not `anywhere`, macro-like or a simplification), placed at the head of that cell's contents, as the compile places it.
The sorts keep what the right side and the condition told the parse about the variables, which a pattern without them would not know, so the pattern matches what the rule's left-hand side matches; a pattern denotes its left side, and a variable only on a right side is refused there, so the right sides are left out.
It is `null` for every other target, where the rule's text cannot be read, and for a sentence a front end matched through templates (`krs.templates`), whose K left-hand side is a bare variable.

### The document

`{schema: "kink-flow-coverage", version: 16, k_rust_revision, profile, result_schema_version, spec, settings, programs, families, targets, summary, mismatches, baseline_runs, data, result, lock, stop?, observe?}`.
Version 1 replaces the results document (its last version 11): the program rows and the rules' rows are as they were, the rules' rows now items of the rules family, in sentence order.
Version 2 builds the syntax family, where version 1 had `null`.
Version 3 runs the flips family where a front end derives the flips: `settings.tiers` `[1, 2]`, the family's items, counts, measure and search, its targets, and `summary.per_family.flips`.
Version 4 adds `lock` (null without `--lock`; else `{path, status, reason, header, header_changes, changes, open_changes, difference}`, or `{path, outcome: "refused", detail}`; "The corpus record"), each flip's `recorded_killer` and `killer_change`, and `settings.depth` as the depth computed (`--depth`, else `[coverage] depth`).
Version 5 adds `observe` for a corpus with `[observe]`, each program row's `observations` and the class `comparable-prefix` ("What a run observes").
Version 6 reads `[[coverage.argued]]` ("Argued obligations"): `settings.argued`, an argued item's status `argued` with its `argument` and `unargued_status`, a needless argument's `argument` and `argument_needless`, each family's `argued` and `counts.argued`, and the summary's `covered` and `needless_arguments`.
Version 7 names why each horizon's channel opened ("What a run observes"): a program row's `observations.horizon` is `{<channel>: {elements, opening}}` and each open channel's `open` has `opening`, each flip has `horizon` (an undistinguished flip's agreements up to a horizon, null otherwise), and a prefix program none of whose channels kept an element within its budget or closed by a cycle is `unknown`; a program row's channel can be `closed` by `cycle`.
Version 8 reads `[coverage] mcdc` ("Unique-cause MC/DC"): `settings.mcdc` may be `true`, and under a selection the selected guards' `combinations`, the unique-cause requirements, the status `undecided`, the requirements family's `mcdc` and `counts.undecided`; without one, the document is version 7's.
Version 9 lists the heating rules in the rules family ("Families"): each rules item's `kind`, the heating items with `heating`, and the family's `counts.heating`.
Version 10 gives a program row's `observations` of a run with several paths its prefix sets' facts, as the run document's version 36 does.
Version 11 (CS-8) spells the `fuzz --cover <item>` job in the `fuzz` of every open requirement but a unique-cause one, every unreached production, every unreached field value whose item names its `binder` (a front end's `{axiom, variable, encodings}`), every open heating rule and every open function equation, where version 10 had `null` ("Covering a rule and hitting a pattern").
Version 12 (CS-4) computes a depth above 1 instead of refusing it (`depth-unsupported`): `families.rule_windows`, its targets and `summary.per_family.rule_windows`, and the refusal `max-obligations` ("Rule windows").
Version 13 (FB-37, FB-42) gives every family one static scope ("Families"): a claim helper is `claim-helper` whatever the programs did, where version 12 counted one some program matched or fired, and a front end's flip that changes only sentences outside the scope is listed under the flips family's `not_generated` (`{reason, id, atom, sentences, pair, detail}`), so the rules, requirements, syntax and flips families' denominators can differ from version 12's on the same definition; an `unknown` flip has `causes` (`[{program, cause}]`), which its target states, and a requirement's `reaching` restates each step through negations.
Version 14 (CS-4) builds the syntax paths family at a depth above 1, which version 13 left `null`: `families.syntax_paths`, its targets and `summary.per_family.syntax_paths`, held to `max_obligations` too ("Syntax paths"); the text rendering says a depth-dependent family is computed above depth 1 only, where version 13 said it was not built.
Version 15 (FB-38) matches a function equation, and covers its requirements, at every application its left-hand side matches whose deciding priority group is its own, tried or not ("Guard outcomes"), where version 14 read the tried equations only, so that of two complementary equations the one tried second was never refuted and, where the other applied, not matched: a rule's `matched_by` and status, a requirement's `entered_by` and a flip's reached occurrences follow, and an undecided program can have the cause `untried`.
Version 16 (FB-39) reads `[[coverage.invariant]]` and an entry's `invariant` ("Argued obligations"): `settings.invariants`, each `settings.argued` entry's `invariant`, every argued item's `argument_check`, the summary's `argued_by_standing` and `failed_arguments`, the refusals `invariant-unused` and `argued-invariant-unsupported`, `lock.argument_changes`, and each argued item's standing in the text rendering.
Version 17 (FB-39) checks an argued item's invariant by its connection ("Argued obligations"): `settings.invariants[].identity` as the front end resolved it, the document's `argument_checks` (`{invariant, connection}` by item id), each argued item's `argument_check.connection` and `reason`, a refuted item's `argument_failed` and its entry in `summary.failed_arguments`, the refusals `invariant-unresolved`, `invariant-not-bool` and `invariant-unsupported-front-end`, and the text rendering's `failed arguments`.
Version 18 (FB-39) also checks an argued item's invariant by its evidence on the corpus's runs ("Argued obligations"): `argument_check.evidence` and each `argument_checks` entry's `evidence`, the standings `checked-on-runs` and `connected`, the check `evidence` of a refuted item's `argument_failed`, and `summary.invariant_runs`.
Version 19 (FB-39) sets aside the functions only the manifest's invariants reach ("Families"): the rules status `invariant` with its `reason`, the rules family's `counts.invariant`, the text rendering's `invariant` count, and a flip that changes only such sentences under `not_generated` with reason `invariant`, so the rules, requirements, syntax and flips families can have fewer obligations than version 18 gives the same corpus; and it rests an argued standing on its invariant being a function ("Argued obligations"): `argument_check.function` and each `argument_checks` entry's `function`, `{status, findings, reason}`, and an item whose invariant is `not-shown` is `unchecked` with that reason and refuted by nothing.
Version 20 (KINK-FINDING-NAMES) names each finding of `data`, and the findings an argued item's `argument_check.function` and standing name, by its kind, sentences and digest (`spec.assume_joined` above), where version 19 named them by generated-K positions; a finding has `sentences`.
Version 21 (FB45-LOCKED-TIMEOUT) keeps a coverage lock entry a run the clock stopped could change ("What decides a verdict"): `lock.kept`, `lock.clock_stopped`, the `lock.status` `undecided`, each flip's `timed_out`, and an argued item's `argument_check.evidence.clock_stopped`. It also gives the document's `lock` its `legacy`, `{path, status, moved}`, where the command was given an old lock file that is still there ("The corpus record", "Old files"; FB48-ONE-LOCK, unreleased with this version).
`settings` is `{tiers, depth, mcdc, max_obligations, invariants, argued, source}` (`mcdc` the names as written, or `true`; `invariants` the tables as written, `{name, function, cells, identity}`, `identity` what the checks are about once the front end resolved the invariant, null on a document refused before that; `argued` the entries as written, `{item, argument, invariant}`, `invariant` null where the entry names none) (`source` `manifest` when `FLOW.toml` has a `[coverage]` section, else `default`).
`programs` lists every program `{id, digest, class, cause, cached, verify, wall_ms, specification_diagnostics, smt_unknowns, decider_smt_unknowns, ends, short_circuit_readings, expectation?, observations?, not_cached?, cache_error?, unable_to_kill?}` (`observations` under `[observe]`, "What a run observes") (`ends` from the result record, null unless comparable; `short_circuit_readings` the readings that excluded the baseline run, empty for every other run; `specification_diagnostics` and `smt_unknowns` absent on a `refused` row; a `comparable` row has `unable_to_kill: "baseline-findings"` while the baseline has a finding `[spec] assume_joined` leaves unnamed, its class and coverage being facts of the run k-rust made).
`families` holds each family by name: `{tier, obligations, covered, argued, measure, counts, items}` where built.
`summary` is `{programs, comparable, computed, mismatches, covered, argued, open, per_family, needless_arguments, argued_by_standing, failed_arguments}`, `per_family` giving each built family's `{obligations, covered, argued, open}` (the flips' where they ran, their obligations less the refused and equivalent ones), `open` being obligations less covered less argued; `covered`, `argued` and `open` are the sums over the families computed, `open` the number of targets.
The exit status is `coverage`'s (above), joined with 3 for an `unknown` flip and 2 for a flip whose search ended in an error; a refused flip is no finding about the corpus.
`baseline_runs` counts the command's baseline runs (`coverage --verify` runs every program live: `live` is the number of programs, `reused` 0).
`spec.execution_digest` (`{kind, digest}`, the result cache's key, beside `spec.digest`), `spec.exclusion`, `spec.short_circuit` and `result_cache: {enabled, reason}` are as in the run document.
A refused specification has `families` null.
Under the Z3 profile the document also has `z3`, the Z3 build its classes were decided on, as the run document has, which the verdicts rendering's header names.
The families, the targets and the summary are derived from the rules' items as the front end annotated them (`coverage::derive`), so a front end's names are in every id, target and count.

### `[coverage]`

```toml
[coverage]
depth = 1                # the length of the sequences the deeper families count; default 1
mcdc = []                # the rules whose requirements gain unique-cause obligations, by name, or true for every rule
max_obligations = 100000 # the most obligations a universe of depth above 1 may hold

[[coverage.invariant]]   # any number, each named by an entry; "Argued obligations"
name = "spin-bounded"
function = "spinBounded"
cells = ["k", "counter"]

[[coverage.argued]]      # any number; "Argued obligations"
item = "rule:LOOP.spin"
argument = "a defence against a state the definition never builds"
invariant = "spin-bounded" # optional: the invariant the argument rests on
```

Every command decodes the section, and refuses a malformed one as it refuses any manifest key; `coverage` refuses a depth whose rule windows or syntax paths outnumber `max_obligations`, at stage `coverage` before any program runs (`max-obligations`, "Rule windows", "Syntax paths").
`mcdc` names rules as the document's ids do (`rule:<name>`), each once; `false` is the empty list. A name that selects no rule whose condition states requirements is refused at stage `coverage` (`mcdc-stale`) once the rules are named, before any mutant runs ("Unique-cause MC/DC").
The other commands read `depth` only to collect the rule windows of every baseline run they make up to it, so that their records answer `coverage` at that depth; they read nothing else of the section.

### Guard outcomes

A rewrite rule or function equation with a `requires` (not a simplification) whose status is `fired`, `matched` or `unmatched` carries `guard`: what the comparable programs' baseline runs saw of its condition (kink-flow `guards::row_guard`, from the result record's `coverage.guards`, which the baseline run collects with k-rust's `collect_guards`).

- `held_by`, `refuted_by` (with `undefined_by`, the refutations whose false conjuncts are all an undefined Boolean, and `solver_refuted_by`, those only the solver or the path condition refuted, the evaluation finding no conjunct false; any false conjunct refutes the condition, whatever the others are, since each is two-valued), `undecided_by` (`{program, causes}`, the attempt's causes: `no-solver`, `solver-unknown`, `untranslatable`, `inconsistent-path`, `solver-error`, `simplification`, `open`, and `untried` for an entry the run did not try whose solver-free evaluation left the condition open) and `stopped_by`; `never` lists `held` and `refuted` where no program saw them.
- A function equation's entries are those of every application its left-hand side matches whose deciding priority group is its own (the first, in priority order, that applies or blocks), whether or not the run tried the equation there.
  An equation states its value where its left-hand side matches, its condition holds and no higher group applies, so its condition decides something at exactly those applications; the backend tries a group's equations, and the instances of a left-hand side that matches in several ways, in an order the definition does not state, and stops at the first instance that applies, and k-rust enters every instance of the group whose match is decided and whose guard it did not decide as an untried entry (`coverage_guards_untried`, which kink-native requires of a run that collects guard outcomes), evaluated as a tried entry is, with a guard outcome classified as a tried entry's is.
  So the outcomes do not depend on the order in which the equations are declared: of `f(A) = .. requires A <Int 32768` and `f(A) = .. requires A >=Int 32768`, both are seen `held` and `refuted`, by a corpus that applies `f` on both sides, in either order.
  A lower group, `owise` included, states nothing where a higher group applies and has no entry there, and a function applied inside an untried entry's evaluation is applied by the record, not by the run, and counts for nothing; a rewrite rule has an entry only where a step tries it.
- `operands`: the written condition's nodes in preorder, each `{path, kind, connective?, operands?, text, true_by, false_by, undefined_by, undecided_by, never?}`. `path` indexes the written condition (`0` its root, `0.1` the root's second operand); a left-nested chain of one conjunction or disjunction is one node; `kind` is `conjunction`, `disjunction`, `implication`, `exclusive`, `negation`, `equals` or `atom`; `text` is the node printed as K; `never` lists `true` and `false` where no program saw them.
  Only an atom and an exclusive connective carry `never`: a conjunction is `true` where its last operand was reached `true` and `false` where some operand was reached `false`, a disjunction dually, an implication reads `notBool A orBool B`, and a negation restates its operand, so their gaps are their operands' gaps; the operands of `xorBool` and `\iff` are both reached on every entry, and its truth is a function of their joint values, which the per-node outcomes do not hold.
- A node's outcome counts only where the node is reached, in written order: in a conjunction where every operand before it is `true`, in a disjunction where every one before it is `false`. So for `A andThenBool B` the outcomes "A false", "A true and B false" and "both true" are A's `false`, B's `false` and the guard's `held`, and `andBool`, which K reads as `andThenBool` wherever either is defined, reports the same.
- An operand the solver-free evaluation leaves open is undecided with its cause (`symbolic`, `unevaluated`, `stopped`) and adds no `true` or `false`, nor any outcome to the operands after it; a `never` next to undecided entries may be the report's and not the corpus's.
- `compiled` lists, apart, the conjuncts of the loaded `requires` that are not the written condition, and `operands_reason` says why there are no operands when there are none: the sentence compiles to conditions of different shapes, or the condition binds variables of its own (one atom).
- The nodes are read from the definition: admission takes the skeleton of every guarded axiom's written `requires` from the loaded definition (kink-native `coverage::guard_skeletons`, k-rust `guard_skeletons`), the nodes a run that entered the axiom would report, so a guard no comparable program entered shows its nodes with no outcome, and what a guard can show does not depend on which programs entered it.
- `uncounted`: the outcomes the programs that are not comparable saw (`held_by`, `refuted_by`, and per node path `true_by` and `false_by`), null when none entered the condition; no outcome above counts them, and an open requirement lists them as `touched_only_by`.

The record also holds each guard's distinct valuations of its atoms with the guard outcome (`combinations`, bounded: the least ones in their order, with `combinations_truncated` where a run made more), each atom's truth under the strict reading, also where the short-circuit reading did not reach it.
Under `[coverage] mcdc` a selected rule's guard shows them as `combinations` (`{atoms, rows, truncated_by}`): `atoms` the display path of each atom of the record's combinations in preorder (`null` for an atom of a conjunct the compile added), `rows` each distinct combination of the comparable programs (`{truths, outcome, programs, flipped}`, `flipped` the outcome the condition takes with one shown atom's truth negated, evaluated on the skeleton, `null` where another atom has no two-valued truth), and `truncated_by` the programs whose record left one out; the unique-cause requirements read them ("Unique-cause MC/DC").
The requirements family reads these outcomes ("Families").
A front end that groups a guard by its own constructs (krs's `guard.krs`: the author's operands by source text, its inserted tests and a pattern's templates apart) gives the reading the family uses: its authored operands and its reading of the author's condition; a rule's `krs.status` and `krs.matched_by`, which read a sentence's match at the front end's level, take the place of `status` and `matched_by`.
The grouping's `held_by`, `refuted_by` and `never` read the author's condition alone, since a template that did not match or an inserted test that was `false` refutes nothing the author wrote: a guard with no authored conjunct has `held_by` and `refuted_by` `null` and no gap, and states no requirement (`guards::authored_condition`).
Whether a condition has an authored conjunct is a fact of the definition, so the front end groups every guard, also one no program entered: one with an authored conjunct then has `held_by` and `refuted_by` empty and `never` both outcomes.

A rule's coverage is k-rust's run coverage of each comparable program's baseline run (kink-native
`coverage`, `kink/coverage/v2` since re-pin L2-1, v3 since L2-1-tail, v4 since a rewrite rule edit is witnessed by `applied` only when it is confined to its right-hand side or `ensures`), rewrite rules and equations alike: `matched_by` lists the
programs that began to decide one of the rule's conditions for an instance whose left-hand side matched, or
applied it (k-rust `matched`), or entered its condition (an entry of its guard, tried or untried, above), and `fired_by` those that fired it: for a rewrite rule, some path of the run takes its
step (`committed`: a step built a successor of the rule that its own normalization showed defined), and for an
equation, an instance gave a result (`applied`). Since result schema v6 (KINK-R4) a rewrite rule's `fired_by` no longer
lists a program whose candidate of it was rolled back because its successor was undefined, or whose step by it was
undefined (both are in `applied`, and no path takes either): it reads the predicate `fuzz --fired` targets (k-rust
`committed`, k-rust-fuzz's goal `covered`), so a program `fuzz --fired` confirms is one `fired_by` lists, although
`fuzz` offers one program, found under its own budget, not every program `fired_by` lists.
Neither is an over-approximation of what can change a result: a
higher-priority rule whose left-hand side never matched is not matched, although its failure is what lets a
lower-priority or `owise` rule fire. The record holds the matched, applied and fired sentences (`coverage.sentences`,
`coverage.applied_sentences`, which orders `run`'s programs, and `coverage.fired_sentences`).
Since result schema v17 it also holds `coverage.bindings`, what the baseline run's fired instances bound (k-rust `collectBindings`, kink-native `ResultRun::bindings`): `operands`, per sentence `{module, index, label, symbols}`, the syntax family's production symbols that were the head of an operand of a fired instance of it, and `binders`, per template binder a front end selected and some fired instance bound, `{axiom, sentences, variable, values, truncated, nonliteral}`; null for a diagnostic run, which collects none.
Since v19 an operand head is recorded only for a variable the sentence reads beside its left-hand side, and `bindings` also holds `alternatives`, per alternative of an axiom with several that a fired instance took, `{axiom, lhs, rhs, sentences}` (`lhs` and `rhs` null where the side has one alternative).
Since v24 `bindings` also holds `paths` at a depth above 1 (above).
A `non-executable` rule is one k-rust never runs (it internalizes executable axioms only), so no program can match it:
since re-pin L2-1-tail it has status `no-coverage-signal` with reason `a non-executable rule: k-rust never runs it, so no
program can match it` (`reach` for `match` before version 7), never `unmatched`; before, it was listed `uncovered`, as a next program to write.
What coverage is meant to cover, what it is not and why, and what is not built yet are stated once in [kink's README](../../README.md#what-coverage-covers), "What coverage covers".

Exit status ("Exit status"): 0 when every program is `comparable` and meets its expectation, if it has one; 1 when an expectation is `unmet` or `--verify` found a mismatch; 3 when a program is `timeout` or `unknown`, or an expectation is `inconclusive`; 2 when the manifest, the specification, a `[coverage]` value or a program is refused, a run failed, a record could not be written, or on a usage error.
An open obligation is no finding: coverage states the gap, and the corpus's author decides what to write.
A timeout or unknown program is no error: it covers nothing and cannot kill.

## `MUTATIONS.toml`

A mutation is one or more text edits of the specification's rules, applied together or not at all
(several edits make a correlated mutation), and the plausible misunderstanding of the specification it writes:

```toml
[[mutation]]
id = "add-becomes-sub"
misunderstanding = "addition evaluates as subtraction"   # required prose; `note` is its alias
expect = "kill"            # optional: "kill" or "survive", the verdict the corpus gives it

  [[mutation.edit]]
  file = "calc.k"            # optional when the spec reads one file, or when rule is given
  rule = "add"               # optional: a rule label ("add", "CALC.add"), or a unique suffix of its components
  line = 21                  # optional: any line inside the rule
  find = "I1 +Int I2"        # exact text, exactly once in the addressed rule
  replace = "I1 -Int I2"

  [[mutation.edit]]          # a second edit of the same mutation
  rule = "CALC.mul"
  delete = true              # removes the addressed rule
```

An edit has `find` and `replace` (`find` non-empty, `replace` may be empty), or `delete = true` (which needs `rule` or `line`).
With neither `rule` nor `line`, `find` must occur exactly once in the file, inside one rule.
A label is `MODULE.x` or the bare `x` for both of K's label forms: k-rust stores `rule [x]:` as `MODULE.x`
and `[label(x)]` as the bare `x`, and either input addresses either form in module `MODULE`.
The anchor also addresses a label it is a suffix of, in whole components, components being separated by `.` or `--` (the separator of KRS's labels):
`plus_zero` addresses `nat--plus_zero` (and `NAT.nat--plus_zero`), `mul--plus_zero` addresses `nat--mul--plus_zero`, and `zero` addresses neither.
The anchor must address exactly one label, whether as the label itself or as a suffix of it: no label takes precedence over another.
A mutation is stored and replayed after every edit of the specification, so a precedence would move an anchor silently: `plus_succ` addressing `nat--plus_succ` would move to a rule that later comes to be labelled `plus_succ`; instead the anchor is refused there, as a stale anchor is.
(`krs prove --claim` lets the whole label win, which suits a filter typed once.)
An anchor that several labels match is `ambiguous-label`, naming each with its module-qualified label (`NAT.plus_succ`, `NAT.nat--plus_succ`), the fullest anchor a label has; one that matches none is `unknown-label`, naming the labels that contain its last component.

`misunderstanding` says, in prose, which mistake an author could make that the mutation writes down: a mutation is meant to be one, a reviewer judges it by what it says, and the next program for a survivor follows from it.
It is required (`note`, its former name, is accepted as an alias; giving both is an error), and it enters no digest or key; the run document's row keeps it under `note`.
`expect` states the verdict the author claims the corpus gives the mutation, and `run` fails when the corpus does not give it.
`expect = "survive"` makes the mutation a control: a claim that no program of the corpus distinguishes the mutant from the specification, such as an edit of a cell the definition never lets a run observe.
`expect = "kill"` claims that some program does: a misunderstanding the corpus must catch.
Without `expect` the mutation states no expectation, and every verdict is an answer: a survivor is a gap of the corpus, the normal state of the loop, so no default is implied, and a list has no file-level default either (an expectation is a claim about one edit, and moving a mutation between files must not change it).
`run` checks the expectation against the row's status, which no schedule moves (`--full` and first-kill give one verdict), on every run, cached or live, and never from the lock:

| Status | `expect = "survive"` | `expect = "kill"` |
| --- | --- | --- |
| `killed` | unmet (1): a kill is a difference in every model, so the control's claim is false of this corpus | met |
| `survived` | met; with `horizon` or `stop_hides_edit`, met only within what the runs observed (no program observed past the horizon, or took the edited step), which the detail says, and the row keeps its action | unmet (1): the corpus misses a misunderstanding it must catch |
| `equivalent`, `unkillable` | met, and the row says it is vacuous: no program of any corpus can kill the mutant, so the control tests no observation | unmet (1): no program of any corpus can kill it |
| `timeout`, `unknown` | inconclusive (3): kink could not decide whether some program distinguishes, so the claim is neither confirmed nor refuted | inconclusive (3) |
| `invalid-mutation`, `not-admitted`, `error` | inconclusive; the row's own status gives the run 2 (1 for a `--verify` mismatch) | the same |

An unmet expectation is a finding: fix the specification, the corpus or the expectation.
An inconclusive one is no finding, since nothing shows the definition wrong, but it is no answer either: an undecided program may be exactly where a control's edit is observable.
The expectation changes no verdict and enters no digest, key, memo, outcome record or lock: adding one moves no lock line, and the lock still records the verdicts.
A run that fails on an expectation still writes its lock (without `--locked`), which states the current verdicts; the next run fails again on the same expectation.
`check --mutations` decodes `expect` (a value other than `"survive"` or `"kill"` is an error naming `mutation "ID".expect`) and checks no expectation, since it runs nothing.

Unknown keys, values of the wrong type, duplicate or empty ids, a mutation without edits and one without its misunderstanding are errors naming the key.
`testdata/flow/calc/MUTATIONS.toml`, `testdata/flow/register/MUTATIONS.toml` and `testdata/flow/markdown/MUTATIONS.toml` are complete examples.

### A mutations directory

Every command that reads a mutation list (`check --mutations`, `run`, `fuzz --mutations`) takes a file or a directory.
A directory, such as a KRS package's `kink/mutations/`, holds one `<topic>.toml` per topic, each with one or more `[[mutation]]` in the format above:

```text
kink/mutations/add-carry.toml    [[mutation]] id = "ge" ...   -> mutation add-carry/ge
kink/mutations/add-carry.toml    [[mutation]] id = "gt" ...   -> mutation add-carry/gt
kink/mutations/sub-borrow.toml   [[mutation]] id = "lt" ...   -> mutation sub-borrow/lt
```

Every regular file directly in the directory whose name ends in `.toml` and does not start with `.` is read, in byte order of the names; subdirectories and other files are not.
A mutation's id is qualified by its file's stem, `<stem>/<id>`, so that ids are unique across files (a stem holds no `/`) and agents adding mutations to separate files never conflict; `--only` and `--kill` take the qualified id.
An error names the file (`add-carry.toml: mutation "ge".edit[0]: ...`).
The id names the row and the lock's record of the mutation ("The corpus record"): a mutation resolves and is cached the same under either id, and a renamed id is a new row of the lock.

### Markdown sources: the K view

Every text an edit addresses, every occurrence count, every line and every rule text the report shows
is in the file's **K view**, the text k-rust parsed: a `.k` file's text, or for a `.md` file the extraction
of the fences `spec.md_selector` selects, in which prose and fence lines are whitespace.
Lines are the Markdown file's lines and columns on code lines are its columns, so `line` is the line an editor shows;
a `find` that occurs only in prose is `find-not-found`, and `before`/`after` are K text.
kink-flow never edits the Markdown file: the edits apply to the K view, and the edited view is loaded as a new
Markdown text with one fence around it (the envelope), which k-rust's extractor must turn back into the edited view.
`testdata/flow/markdown/spec.md` is a literate example, and `spec-view.k` beside it is its K view written as a `.k` file.

Resolution (`kink_flow::mutation::resolve`) builds the K view of each source file it touches and checks it against
the baseline's source table (the loaded definition must hold that extraction of the file), addresses every edit to one
authored rule (a rule's span is its offset attributes, which must name the same text as its location),
applies the edits to the views (a delete removes the rule's text: a one-line rule keeps its line, a rule over several lines leaves one, so later sentences move up; only their `Location` changes), loads the edited views with the
specification's load options, and checks that the edited load has the baseline's modules and sentences, in order and
with equal fingerprints, except at the addressed rules: a replaced rule is still exactly one rule sentence with the
same label, a deleted rule is gone. In every edited file each sentence must also start where the edits move it, and
end there too unless it is a replaced rule (which may end earlier by whitespace only), so an edit cannot rewrite the
text of a neighbouring sentence even into an equal one. The edited rules then become one pinned kink-patch `Patch`
(`ReplaceSentence`, `DeleteSentence`) whose digest is the mutation's identity; the mutant is always the patched
baseline, never the edited load. Only rules are editable. Every program runs on that mutant without the trusted claims
the edit leaves unbacked (re-pin R0c-fix-2; kink's `trust.md`, "What a kill trusts"): the `total` and other claims of every
function whose equations reach an edited equation, the lemmas about them and the `preserves-definedness` of the rules
that apply them. A mutation whose edit leaves a claim no removal takes away (for example a replacement that writes a
claim, or edits a lemma or an equation's `ensures`) is `unknown` with reason `unsupported-claims`; one whose claim-free
mutant does not compile is `unknown` with reason `stripped-claim-compile-failure`. The claim-free mutant must also be a
theory with models (re-pin R0c-fix-3): a mutation that makes two equations of one function apply to one input with
different values, or whose pairs of equations k-rust's critical-pair check does not show to join, is `not-admitted` with
reason `inconsistent-mutant`, and its row's `inconsistent_pairs` names the pairs. A mutation that only weakens the
specification (it deletes equations of functions or lemmas, or replaces one by an instance of itself) is `unkillable`
before either check and builds no mutant (kink's `trust.md`). The functions whose pairs are read
are those whose compiled equations the edit changes or reaches (a `#let` or `#fun` lambda included), with kink-patch's
source reading as a fail-closed cross-check (re-pin R0c-fix-4): a sentence the edit touches that compiles to an
equation of a function the source reading does not redefine makes the mutation `unknown` with reason
`unsupported-claims`, and the row's `removed_claims.unsupported` names each such equation (key `unread-equation`,
value `{head, equation}`; re-pin R0-tail).

A mutation that fails any check is `invalid-mutation`, with the offending edit (`edit[i]`) when one is at fault,
a reason and a detail; it is never compiled. `check --mutations` gives each reason's next step (`InvalidReason::next_step`). Reasons:

| Reason | Meaning |
| --- | --- |
| `unknown-file` | `file` is not a source file of the specification. |
| `file-required` | The specification reads several files and the edit names neither `file` nor `rule`. |
| `unknown-label` | No rule has the label, and no label ends with it as whole components: the rule was renamed, moved or removed (a stale anchor), or the anchor is misspelt. The detail names the near labels, at most five, by the last component of the label: one that is the anchor's up to case and `_` (a respelling, `plusZero` to `plus_zero`), contains the anchor's (a moved item keeps its last component), shares a word of three or more characters with it (words are separated by `_`), or is within a third of its length, and at least one, in single-character edits; respellings first, then containing, then by edit distance; or it says that none is near. |
| `ambiguous-label` | The anchor names several rules, as their label or as a suffix of their labels' components; write more of the label: more of its components, or the module-qualified label the detail gives for each. |
| `line-outside-rules` | No sentence covers the line. |
| `line-ambiguous` | Several rules share the line; address one by `rule`. |
| `address-mismatch` | `rule`, `line` and `file` name different rules. |
| `non-rule-sentence` | The edit addresses a syntax declaration, configuration or other non-rule sentence. |
| `find-not-found` | `find` does not occur where the edit looks. The detail says what is there now (see below). |
| `find-ambiguous` | `find` occurs more than once there; make it longer. |
| `edit-outside-rule` | `find` occurs in the file but not inside the addressed rule (or inside no rule). |
| `overlapping-edits` | Two edits of one rule overlap, or a deleted rule is also edited. |
| `source-changed` | A source file changed since the specification was loaded. |
| `source-view-mismatch` | The file's K view is not what k-rust parsed: for a `.md` file, the view under `md_selector` differs from the extraction of the same bytes under the selector the load used (for example `md_selector` changed since the load); or the loaded definition holds no such extraction of the file; or an addressed rule's spans index another one. Since k-rust 501f18b9 every extraction's offset map is the identity, so only the text comparison tells two selectors' views apart. |
| `markdown-envelope` | A Markdown file's edited K view cannot be loaded as K text: an edit makes a line a Markdown fence line (three or more backticks or tildes after at most three spaces), or the envelope does not extract to the edited view. |
| `edited-load-failed` | The edited sources do not load (parse or sort error); the detail is k-rust's message. |
| `structure-changed` | The edit changed something besides its rule: a sentence split, merged, added, removed, changed kind or changed elsewhere. |
| `span-changed` | In an edited file a sentence does not start (or, unless it is the replaced rule, end) where the edits move it: the edit's text reaches past its rule: a replacement that ends in a comment, or one that comments out a neighbouring rule and writes a copy of it. |
| `label-changed` | The edit changes the rule's label. |
| `no-change` | The edited rule loads to the same sentence as the original, or an edit's `replace` is its `find`: the edit changes nothing. A loaded sentence keeps no layout or comment, and a rule without `requires` or `ensures` loads with `true` there, so an edit that only adds `requires true` changes nothing either. |
| `edited-rule-too-deep` | An edited rule is too deep for kink: its patch's document would nest deeper than kink-patch `MAX_JSON_DEPTH` (two JSON levels per term level: terms about 300,000 levels deep in a release build, 64,000 in the unoptimized test build), so the mutation has no encoding and no identity. This is kink's limit, not a fault of the mutation. A patch holds each edited rule whole, so the detail gives the rule's depth as a whole and the specification's rule's: when the specification's rule alone is already past the limit, it says that no mutation that keeps the rule's deep part can be judged in this build (target other rules, or replace the deep part by a shallow one; re-pin L1-4); otherwise a mutation that keeps the whole rule within about half the limit in term levels is judged (re-pin L1-3-tail). Below the limit a rule's depth decides nothing: its typing and its patch's encoding run on a stack sized from that depth, on any thread (re-pin L1-3-fix-2; before, a rule about 230,000 terms deep aborted the whole run in typing). |
| `host-stack-refused` (status `error`) | The host refused the native stack that encoding the mutation's patch needs: the system would not map a stack segment of the size the patch's depth needs (an address-space limit such as `ulimit -v`, or memory it will not commit). It is the host's limit, neither a fault of the mutation nor a verdict, so the row is `error`, not `invalid-mutation`; rerun where the host grants the stack. Only a deep patch needs a segment: the segment is sized from the patch's own document depth (re-pin L1-3-tail; at L1-3-fix-2 every patch more than 48 term levels deep took a segment sized for `MAX_JSON_DEPTH`, 768 MB in release, and a refusal was reported as `patch-rejected`). |
| `no-usable-span`, `patch-rejected` | Defensive: a rule's offsets and location name different text of its K view, or kink-patch refused the patch for a reason other than typing (a stale pin, a patch that does not resolve); not expected on rules k-rust loaded. No typing error refuses a mutation (re-pin L2-2-fix-1): a mutant is valid when it compiles, so compilation decides, and kink-patch records the edited rules' errors in compilation's typing view (`SentenceTyper::for_compilation` with `typing_in`) as the row's `typing_diagnostics`. k-rust documents that view's errors as errors compilation stops at, but at 501f18b9 it refuses shapes compilation accepts: a local function with a variable in a cell with children (`CellCompletion`), and a rule `a(X) => b(X)` whose sorts `A` and `B` have a second common supersort in the main module (a non-unique least upper bound). At the pin 8f8ad57c5 that view types the second shape (k-rust KINK-21/1), so its rows carry no typing diagnostic; the first remains. |

A stale anchor is a broken input, and kink does not re-anchor it: a respelled text need not be the text the mutation meant, so the author chooses.
The detail of a stale anchor is written so that the choice takes one look.
An `unknown-label` detail names the near labels, as above.
A `find-not-found` detail names the text nearest `find` in the addressed rule (with neither `rule` nor `line`, in the file):
the substring fewest single-character edits away, of equally near ones one as long as `find` and then the first,
with its `file:line` (or lines), when it is within a third of `find`'s length in edits (at least one) and keeps some character of `find`;
otherwise it says that no text is that near.
For an addressed rule it then quotes the rule's text now, whole up to 400 characters, else 400 characters from the line of the nearest text, marked `...` where cut.
Each text is quoted as Rust's `{:?}` prints it, which a TOML basic string holds as printed when the text has no control character but tab, carriage return and line feed, so it can be copied into `find`.
A search longer than 16 million cells (characters of `find` times characters searched) is not made, and the detail says so.
The detail is the document's free text: a lock and the `verdicts` rendering keep the reason alone, so neither changes with it.

## `kink-flow run FLOW.toml MUTATIONS [--only ID]... [--verify] [--full] [--lock FILE [--locked]] [--compile-workers N] [--no-memo] [--progress] [--cache DIR] [--output json|verdicts]`

Runs the kill search: for each mutation of the list (in file order; with `--only`, only the named ones),
is there a program of the corpus whose result the mutation changes?

`--progress` prints a line on stderr before the result cache is brought up to date, naming how many mutations and programs the run has;
one as the specification's admission starts (its load, compile and checks, `kink-flow: run: admitting the specification (its load, compile and checks)`), and one as the baseline runner's preparation starts (`kink-flow: run: preparing the baseline runner`), the two phases before the first program;
one as each program gets its baseline row, with its place, its id, its class and `stored` when its record was already in the cache (``kink-flow: run: baseline of program 2 of 20, `t2`: comparable, stored``);
one before the list's mutations are resolved;
and one as each mutation gets its row, with its place, its id and its status (``kink-flow: run: mutation 3 of 81, `calc/add-sub`: killed``);
the command line prints them without the flag when stderr is a terminal.
The lines depend on the corpus and the cache alone, never on time, and stdout is the document with or without them, so a caller that reads stderr (a CI step, an agent) asks for them, and its other stderr lines stay the refusals and notes.

1. The result cache is brought up to date first (`coverage` without `--verify`).
   Only `comparable` programs can kill; the others are never run.
   No stored record is a `timeout` (a timeout depends on the host's load and is never cached), so a program whose baseline timed out was run live by this update.
2. The mutation is resolved into one patch (see `MUTATIONS.toml`); an `invalid-mutation` stops there.
   A mutation whose edit only weakens the specification (it deletes equations of functions or lemmas, or replaces one by an instance of itself, a narrower pattern or `requires`) is `unkillable` and stops there too (kink's `trust.md`), unless a program is in O (step 3) and the baseline has a finding `[spec] assume_joined` leaves unnamed: then it is `unknown` with reason `baseline-findings`, as every such mutation is, since the weakening argument reads the baseline's normal forms as a model of the specification, which such a finding puts in doubt, and fixing the specification comes first.
   When every edited equation only adds to its `requires` conjuncts that hold under every valuation of their variables (the sort predicate of a variable of that sort, written or inferred, `isNat ( N:Nat )`: kind `valid-condition`), the equation is the specification's own and the mutant has exactly its models, so the mutation is `equivalent` with reason `valid-condition` instead, on the same terms.
3. The programs O are the comparable programs in the manifest's order.
   Each live call runs first the programs of its call whose cached coverage witnesses the mutant's edit, then the rest, each group in O's order: the search order C.
   The order is fixed: a project that wants cheap cases tried first lists them first in `FLOW.toml`, which is an input, so the order stays a function of the inputs.
   The edit is read from the compiled mutant, once it compiles, as kink-campaign's coverage selection reads it (`CompiledEdit::between` of the compiled baseline and the claim-free mutant every program runs on; kink's `trust.md`), but for one change: when kink withdrew only definedness claims from the mutant (a symbol's `total` or `functional`, a rule's `preserves-definedness`), the edit is read from the mutant as written (kink-campaign `CompiledEdit::for_ground_tests`).
   A withdrawn `total` or `functional` changes a declaration, which the claim-free side's edit reads as not site-local, and a withdrawn `preserves-definedness`, a rule attribute, makes the claim-free side edit rules the author did not edit, or edit beyond the right-hand side one whose right-hand side alone the author edited.
   But a program is ground, and a ground program whose complete coverage reaches no sentence the author's edits change applies the specification's sentences to the same terms on the claim-free mutant, where each application its equations evaluate is defined by its value with no claim, and one they leave unevaluated in a step's result is a contradicted claim or an end that is no data, on either side.
   One case escapes coverage: an application in an operand a short-circuit operator skipped in the baseline run (the right operand of `orElseBool` after `true`) was trusted defined by the claim and never evaluated, so the program's coverage holds none of its equations; without the claim k-rust's strict reading must establish its definedness, and can do so through an equation the author edited, so the claim-free mutant's run can differ from the specification's (it is judged as any run is: where the mutant's short-circuit analysis flags the rule that read the operand, which the withdrawal makes partial, the run is excluded as `short-circuit-reading`).
   Such a program is no witness, and runs after the witnesses.
   So the withdrawal adds no witness through coverage, and a row's `witnesses` are the programs whose coverage reaches an edited rule, while its `removed_claims` still names each withdrawn claim; witnesses order programs and decide no status.
   Any other withdrawn claim (`injective`, `smt-hook`, `smtlib`, `smt-lemma`, or a `simplification` lemma, whose deletion can make a run that used it evaluate an edited equation) keeps the claim-free side's reading.
   Each removed compiled axiom whose edit is confined to its right-hand side or `ensures` is witnessed by a program that applied a baseline sentence behind it (`applied`: a step built a candidate of it, defined or rolled back; wider than `coverage`' `fired_by`, since an edit can make a rolled-back candidate defined), since the axiom is tried, matched and decided as before and a program that only refuted its guard never runs what it builds; every other removed axiom of a site-local edit (a rewrite rule's `requires`, left-hand side or attribute, a deleted rewrite rule, a rewrite rule kink cannot pair with its edited form, an equation's `requires` alone or with its right-hand side or `ensures`) by one that matched such a sentence (k-rust `matched`: it began to decide the condition), since the edit changes whether the axiom applies at a state its left-hand side matches: after an edit of the `requires` or the left-hand side, a program that matched it and refuted its old guard can take the edited axiom's step; an attribute edit or a deletion keeps the guard wherever the rule stays, and a rule whose guard is refuted takes no step and blocks no lower priority group wherever it is placed, so at a state the rule matched such an edit shows only where a program applied the rule or left its guard undecided, and `matched`, which holds the rule whatever the verdict, is the smallest recorded superset of those programs. A widened left-hand side, or an attribute edit that raises a rule in its site's trial order (a higher priority, a removed `owise`), can also show at a state where the old rule was not tried or its match was left undecided, and a deletion, or an attribute edit that lowers the rule (a lower priority, an added `owise`), at a state where its match was left undecided, since such a match blocks the lower priority groups of its site; only k-rust's `offered` names those states, and kink does not collect it, so such a program still runs, after the witnesses.
   An edit that is not site-local (an equation's left-hand side or attribute, an edit of an `owise` or `smt-lemma` equation, the `requires` of a `concrete` or `symbolic` equation, a deleted or inserted equation, a changed declaration, claim, macro, syntax or rewrite order) is witnessed by every program, so that call keeps O's order, and the row's `witnesses_global` is true: an equation whose pattern changes can match terms no baseline run tried, an application no program's coverage holds anything of.
   An alias of a left-hand side (K's `P #as V`, written `\and(P, V)` in KORE, which k-rust's compiler also writes for a subterm of the left-hand side that the right-hand side builds again) is read as the pattern it names, with `P` for `V` in the rest of the axiom: the alias matches exactly the terms `P` matches and binds `V` to `P`'s instance, so the axiom has the same instances, and an edit whose result reuses a subterm of the left-hand side (`plus(s(M), N) => s(plus(s(M), N))` for `plus(s(M), N) => s(plus(M, N))`) is confined to its result, whatever its mutant then does.
   A program whose cached coverage is not complete (the record's `coverage.complete` is not true) witnesses every edit, as kink-campaign's coverage selection counts it (`coverage_selected`): its coverage lists only what its run explored before it stopped, so it does not show that the program misses the edit.
   The coverage records list baseline sentences, so a removed axiom is read through the compiled baseline's rule authors, where kink-campaign reads its tests' coverage by compiled id. The two readings differ only in the order: a removed axiom with no baseline sentence (one a compiler pass generated) is witnessed by no program, and a sentence behind several compiled axioms is witnessed by a program that matched or applied any of them, not only the removed one.
   The mutation's outcome file keeps the compiled edit so read ("The cache directory", `witness`), so a row tier 1 decides with no compile still has its `witnesses`.
   What is decided before any mutant compiles (tier 1, step 4, and which mutants are compiled ahead) depends only on the set of programs in O, not on their order.
   C is a function of the inputs: the witness set is computed from the compiled edit and the result records' coverage, both keyed facts, by the one predicate a live call and tier 1 share, so the outcomes written are reproducible byte for byte.
   In either profile, while no `budget.time_ms` bound fires, the order never changes a status: a kill outranks every other outcome under first-kill, and a mutant that fails as a whole
   fails before any program runs; it changes which killing program a call finds first and the cost.
   That needs each program's outcome to be independent of the programs run before it in the same call. Without Z3 k-rust's Execute promise gives it; under Z3 it gives it for the resource-bounded queries kink asks (`budget.smt_resource_limit`), whose answers, decided or not, are functions of the query, the units and the Z3 build, so the mutant's backend, reused for every program of a call, cannot answer a query otherwise because an earlier program asked it.
   Under a solver bounded by the clock it would not hold: a query could time out, and an answer an earlier program cached could turn a program that times out alone into a kill or an agreement, so the order could move a status between `killed`, `unknown` and `survived` (never to a false kill: a kill is still a proved difference); tier 1 is off for such a solver for the same reason.
   A run near its `budget.time_ms` bound can time out in one order, while caches are cold, and finish in another, in either profile; a `timeout` is host- and timing-dependent anyway (review L2-1-tail-1 D1, D2).
4. **Outcome cache, tier 1.** Each program of O may have a cached outcome for this mutation: `killed` (a proved difference), `agree`, or `unknown` (since CF-33d: an inconclusive outcome that is a function of its key, step 8).
   A cached outcome is used only when its key is exactly the current one (see "The cache directory" below) and the program's
   current result record has the baseline run digest the outcome was compared with.
   The cached outcomes decide with no compile and no run when they decide the killer the row must name ("The corpus record": the recorded killer k while it kills, else the first killing program in C).
   A cached kill of k decides: the killer is k. If k is a program of O with no cached outcome, they do not decide: k must run (step 5).
   Otherwise (no record, a record naming no program of O, or a k whose cached outcome is not a kill) they decide when every program of O has a cached outcome (with no cached kill, the status is the fold of the cached outcomes: `survived`, or `unknown` when one of them is),
   or when C is known from the compiled edit the outcome file keeps and every program before the first cached kill in C has a cached outcome (that kill is the killer, and the row lists that prefix, the kill and k's cached outcome),
   or when every program has a cached outcome and exactly one of them is a kill.
   With several cached kills, every program cached and no stored compiled edit, the row runs as if nothing were cached, so that the killer is still the first in C (outcome files are written with the edit, so this does not arise from the files `run` writes).
5. **The recorded killer, tier 2.** If k is a program of O with no cached outcome, the mutant runs on k alone; if it kills, that is the verdict (`killer_source` `record`).
   Otherwise the canonical call runs every program of O with no cached outcome, k included, in C, cut before the first cached kill in C when C is known (from k's call or the outcome file); the killer is the earlier in C of the call's first kill and the first cached kill.
   The cut is a saving only: the call ran every uncached program before its own first kill in C.
6. Every status is the one kink-campaign's own fold (`derive_mutant_report`, under the run's schedule) gives over the cached outcomes
   followed by the last runner call's tests. kink-flow compares no terms; only a proved difference of the exit stop or the
   final configuration without the cells left out kills, live in this command or cached under an exactly matching key.
   A cached agreement is the fold's bottom, so the status is the one a run without any cache gives.
7. Each program's baseline runs live at most once per command: the result update and every runner call share one
   in-memory baseline session, so a program the update ran, or an earlier call ran, is not run again on the baseline;
   its live run of this command is reused where the runner produces baseline evidence (`baseline_runs` counts both).
   After every runner call, each program's baseline run is checked against its cached result (`run_sha256`).
   A difference is a corpus error: the mutation gets status `error` with reason `baseline-mismatch:<program id>`
   (or `baseline-count-mismatch`), nothing is cached for it, and the run stops (exit 2). Run `coverage --verify`.
   A cached agreement next to a mutant that no longer compiles is the corpus error `outcome-conflict`: run `run --verify`.
   A mutant that fails as a whole for an infrastructure reason (`reason` `infrastructure`: the equivalence check or the
   mutant's backend failed while it was prepared) is not a conflict: its status is `error`, as without any cache, and its
   cached agreements are left out of the row and the counts.
8. After a verdict, every live program outcome that is a function of its key is cached: `killed`, `agree`, and (CF-33d) `unknown` when every slot is `agree` or `unknown` and kink judged the mutant's run.
   Such an unknown comes from the run's leaves and kink's judgement of them, never from the clock (the watchdog makes a run or a path a `timeout`): a run the work budget cut (`work_factor`: `max(work_factor × P, P_max)` polls; a poll-bound mutant run is one-sidedly killed or stays unknown by the `one_sided` rule of kink's identity), a depth, simplification or breadth bound, a leaf left indeterminate or a state left undecided (under Z3 every query is bounded by resource units, so an undecided answer is a function of the query, the units and the Z3 build), an end that is no value kink compares or is not data under the other definition (on the mutant's side or, through the pair's judgement under the mutant's definition, on the baseline's, whose run the record's `baseline_run_sha256` names).
   Each counts work or reads the run, and the context names every input but the work budget: the bounds (`budget`), the solver's units and Z3 build (`budget.smt`), the stop, the projection, the definition and kink's build and identity ("The cache directory", the context).
   The work budget is in the record instead (`polls: {count, bound, cut}`: the polls the mutant's run counted, the bound it ran under and whether it ended there): a record of a cut run serves exactly the bound it was cut at, and one of a run that ended serves every bound from the smaller of its bound and its count up, since it is the run without the bound. So raising `work_factor` re-runs only the cut runs, lowering it re-runs only the runs that used more than the new bound, and neither touches another record.
   Its record keeps the live entry's `cause`, so a cached unknown says why as the live one did, and whether the program is undecided by open applications of an edited function (`open_application`, below), so a row's `reason` `open-application` is the same whether its unknowns ran live or were read from the cache.
   Never cached: a timeout, an error or incomparable slot, every failed run (the watchdog's clock, an infrastructure failure, a host exclusion such as a stack stop, a load stack stop or an allowance refusal, an exclusion of the definition or the run, whose row's `reason` the live call gives, and, conservatively, an `indeterminate` or `resource-limit` failure, which the runner does not produce), an unknown of a run whose judgement kink could not make for a reason that need not be the run's (kink-campaign `RunNotes::unjudged`: the backend refused the decider, a pattern judgement, the definition's facts or the pair's judgement of ends, through a refused stack segment, solver initialization or prelude, which can be the host's doing, or a definition's full check ran out of native stack, so it admits no end as data), a skipped run, and every outcome of a call whose mutant failed as a whole.
   Every solver query of the kill search, the mutants' runs included, is bounded by `budget.smt_resource_limit`, the units the context names.
   The run document is written after every mutation (a corpus error included), so an interrupted run keeps its finished work, and the outcomes it cached make the next run's canonical decisions cheap; the lock is settled once, at the end ("The corpus record").

**The full matrix (`--full`).** The steps above are the first-kill search, which stops at the first killing program: right for finding whether a mutation survives and naming one killer, but it leaves the other cells unrun.
`--full` runs every comparable program on every selected mutation, in corpus order, under kink-campaign's full schedule (kink-corpus's `schedule = "full"`), so that the document holds the whole kill matrix:
- O is every comparable program in `FLOW.toml`'s order, and a live call keeps that order (step 3; `witnesses` still names the witnessing programs of the compiled edit, in that order).
- Tier 1 (step 4) decides with no call only when every program of O has a cached outcome: a cached `killed` outcome does not decide a full row, which needs every cell. The cached outcomes, kills and agreements alike, are not run again, and the mutant runs once on all the others, in corpus order.
- No one-program call is made for the recorded killer (step 5): every program with no cached outcome runs in the one call anyway.
- The status (step 6) is kink-campaign's fold under the full schedule over the cached outcomes and the call's, with the same `outcome-conflict` and `infrastructure` rules (step 7), except that a cached kill does not decide alone: a cached kill next to a mutant that no longer compiles is an `outcome-conflict` too (its next step is `run --full --verify`), and an infrastructure failure leaves the cached kills out of the row as it leaves the agreements; outcomes are cached as in step 8, so a full run caches every cacheable cell.
- Each row carries `killed_by`, every killing program in corpus order, cached or live; `killer` is the recorded killer when it is among them, else the first of them in C (the first-kill row's killer: "The corpus record"), so it is not always the first of `killed_by`; `killer_source` is `outcome-cache` when that cell was cached and `search` otherwise; `executed` lists every program of O in corpus order; the document carries the per-program `matrix` (below, "The report").

A full row's status is the first-kill row's: both are the same fold over the same per-program outcomes, in which a kill ranks above every inconclusive outcome, and under first-kill the fold only reads fewer of the outcomes below a kill.
A cached outcome is the outcome of one executed test, and the schedule decides only whether a test is executed, never what an executed test's request, sides or slots are; a program's outcome does not depend on which programs ran before it in the call (step 3).
So an outcome does not depend on the schedule, the tier-1 context does not name one, and the outcomes a first-kill run cached serve a full run and the reverse: a full run after a first-kill run calls, per mutation, exactly the programs that have no cached outcome.
`killed_by` is a function of the specification, the corpus, the mutation and the budget (no `budget.time_ms` bound firing; under Z3 the budget names the solver's units and build), complete over the comparable programs: one absent from it agreed or was undecided, and the matrix's `undecided` names the latter.
The killer is a function of the lock and of the same inputs under both schedules ("The corpus record"), so a first-kill run and a full run name the same killer and write the same lock.
A first-kill row's `killed_by` is null, not a one-element list, because first-kill establishes one killer, not every one.
`run --verify --full` runs the cold call over every comparable program under the full schedule, so every cached outcome is compared with a live cell, and the status the cache would have given is the fold of every cached outcome with the live outcomes of the others (no killed-outcome shortcut).

### The killer record, compile workers and memos

`--lock FILE` names the corpus record, whose `[run]` section is the killer record: one recorded killer per killed mutation, kept while it still kills, which the search tries first ("The corpus record", which states the killer rule, when the section is written and what `--locked` compares).

**What it costs.** With a lock, a killed mutation whose cached outcomes are gone (a fresh checkout, a specification edit) costs one cell, its recorded killer's run; a survivor costs every program, with or without a lock.
Adding a case runs, warm, only the new case for each survivor and nothing for a killed mutation, whose recorded killer still kills; with the full rendering as the lock, every mutation would run the new case.
Without a lock, a run after a specification edit computes the canonical prefix of C up to each killer again.

**Compile workers.** `--compile-workers N` (4 by default) compiles mutants ahead of their turn on up to N threads, capped at the host's parallelism and at half the process's memory allowance, counting for each worker one compile in flight and the at most 8 compiled mutants it keeps (kink-native `NativeValidator::compile_workers`; re-pin L1-3, L1-3-fix-1).
The mutations are taken in chunks of 4 N; for each chunk the mutants of the mutations that would make a live call given the stores at the chunk's start (each mutant and, when claims are removed, its claim-free definition) are compiled, every worker is joined, and then the chunk's mutations run exactly as with one worker, one at a time in list order, every load, consistency check and execution on the calling thread.
A worker thread runs only two steps: relinking an applied mutant and compiling it, which k-rust documents as independent of the thread; each patch is applied (and its edited rules typed, a recursion with no stack guard) on the calling thread, before the workers start (review L1-3-1 D1).
A mutant compiled ahead is the mutant its call would compile (k-rust documents relinking and compiling, and nothing after them, as independent of the thread: `docs/compatibility.md`, "Concurrency"); a refused or panicking patch or compile is not kept, so its call applies and compiles it again on the calling thread.
A guess that a mutation would call costs a compile when it does not, and the call compiles as usual when it does not guess, so no row, outcome, lock or report depends on N (`tests/compile_workers.rs`, cold and warm, 1, 2 and 4 workers).
On `examples/imp`, cold, mutant compiles are about 28 % of the run's wall time; a warm run, which tier 1 decides, compiles nothing.

**Memos (re-pin L1-4).** A run does once, or not at all, what is a function of inputs that did not change (kink-flow `memo`):
- The specification's baseline compiles once per command: program inputs are assembled with the admission's compile (kink-corpus `assemble_input_with`), where each program bound a fresh validator and compiled the baseline again (49 of the 81 baseline compiles of the flow lists cold).
- The specification's input grammar (kink-corpus `InputGrammar`: the program grammar with its macro-expansion definition, the declared variables, the start sort, whether the definition has stream cells) and one configuration assembler are built once per command, on the first program it assembles, and serve every later program (`InputSession`, R5-INPUT-COST); before, each program rebuilt them, about three whole-definition resolutions and two parser constructions per program, and its derived views once per configuration value. Each is a function of the specification alone and the assembler is cleared before each program, so every initial configuration and refusal is the one a fresh assembly gives (`tests/check.rs` `programs_share_one_input_grammar`, kink-corpus `tests/input.rs` `one_assembler_assembles_what_assemble_input_does`). A session is opened with its specification (`ProgramInputs::session(&spec)`), and the inputs accept only the specification admitted beside them, so no program is assembled with another specification's grammar.
- The resolution memo, `memo/resolutions/<spec digest>/<entry digest>.json`, holds per mutation the facts of its resolution a row decided by tier 1 reads: the patch digest, the edited rules (texts, lines, label), the tier-1 mutation identity, the typing diagnostics and the claims the edit leaves unbacked. A mutation whose record has exactly the current key and that tier 1 decides with no call (run step 4, given the lock; or no comparable program) is not resolved: its row is built from the facts by the code that builds it from a live resolution. Every other mutation is resolved live and its facts are written, so every mutation that compiles or runs anything was resolved in this command; the record holds no patch (the patch's canonical JSON does not carry k-rust's term metadata, so a decoded patch would not be the one resolution builds). The key names every input resolution reads: the specification digest (the k-rust revision, the profile, how the specification is loaded and every source file's name and SHA-256: resolution reads the admitted load, each touched file's bytes checked against that SHA-256, and an edited load of the same files under the same options), the mutation's edits in order with every field (`file`, `rule`, `line`, `find`/`replace` or `delete`; the id only names the row and the misunderstanding is never read), `kink_build` and `kink`. Records are read only while every source file still has the SHA-256 the admission recorded. A typing diagnostic that says a rule was not typed (a refused stack segment) depends on the host, so facts that carry one are never written.
- The census memo, `memo/census/<spec digest>.json`, holds the declaration census of the admission (the VI-T13 gate), a function of the compiled baseline and of kink's build (its reference: the builtin files, the pinned `krypto.md`, and the hooks k-rust implements), keyed on the specification digest, `kink_build` and `kink`.

The premises are those the result cache and tier 1 already rest on: k-rust's load and compile are deterministic (the same files under the same options give the same definition, C-12), and the key names every input (`tests/memo.rs` pins each field of a mutation's edits: a key differs when any one field differs, it decodes back to the edits, and two mutations that differ in one field never share a record; it builds both keys member by member, the version, kink's build and semantics identity, the specification digest and the edits, and requires them equal to `memo`'s, and `tests/coverage.rs` requires the specification digest to change with each `[spec]` field, so a key that drops an input fails a test; re-pin L1-4-tail). Before any resolution record is read, every source file must still have the SHA-256 the admission recorded, so a file changed between the admission and resolution reads no record (`tests/memo.rs` changes one there). One premise is new, the host premise: a record exists only because resolution succeeded on the host that wrote it, and success can depend on the host (the native stack segment of the patch's encoding, which live gives `host-stack-refused`; the heap and address space of the edited load, which live aborts the process when exhausted; and the native stack segment each edited rule is typed on, which a host can refuse while it grants the encoding's, and which live gives a typing diagnostic saying the rule was not typed, with the row's status unchanged). The key does not name the host's capacity: a memo hit returns the tier-1-decided row that a host which could resolve the mutation computed for the same mutant identity, where live resolution on a smaller host would end `host-stack-refused`, abort, or give the same row with a typing diagnostic saying the rule was not typed where the memo gives the writer's typing diagnostics (re-pin L1-4-tail). That cannot make a false kill or hide a survivor (the mutant is judged where the host grants the stack, as this README recommends for `host-stack-refused`, and typing diagnostics decide nothing), but before L1-4 every resolution was recomputed in every command. So run documents with and without memos are equal on hosts that grant the stack and heap resolution needs. The memos are off where tier 1 is (under the Z3 profile a solver the clock bounds or a Z3 build that cannot be named; an unreadable executable) and with `--no-memo`. `run --verify` decides nothing from a memo: it resolves every mutation and runs the census live, compares each record that has the current key, reports one that differs (the row's status `error`, reason `resolution-mismatch`, and an entry `{mutation, program: null, cached: {resolution}, live: {resolution}}` in `mismatches`, also for a mutation `--only` does not select or that a corpus error left unsearched, which has no row; a census, `{mutation: null, program: null, cached: {census}, live: {census}}`, also when the live census refuses the specification, so a stored census that admits a specification the live census refuses is reported in the refused document) and writes no memo. A memo never enters the run document, an outcome record or the killer record: on such a host a run with and without memos writes the same ones (`tests/memo.rs`, cold and warm, with every status and a Markdown source; each key input changed, a forged record under the current key used and reported by `--verify`, in both directions for the census). A memo that cannot be written only means a later recomputation, so it is not reported.

### Cost model

Where a run's wall time goes (release build, 4 compile workers; re-pin L1-3 and L1-4 measurements, shared 32-core host at load 15-35):

| Stage | Cost | Cold | Warm (tier 1 decides) |
| --- | --- | --- | --- |
| Admission: load | one load of the specification and the prelude, about 0.12 s on `examples/imp` | once | once |
| Admission: baseline compile | about 0.22 s on `examples/imp` | once per command (before L1-4: once more per program run live) | once |
| Admission: declaration census | 0.52 s, of which its reference prelude's compile 0.22 s (measured before kink27 GK-3 added `krypto.md` to the reference) | once | read from the census memo |
| Resolution | one full load per mutation (0.11-0.15 s on `examples/imp`: the definition's every rule bubble is parsed again) | every mutation | only mutations tier 1 does not decide; the rest read the resolution memo |
| Result update | each new or changed program's baseline run | new programs | nothing |
| Kill search | per live call: the mutant's compile (compiled ahead on the workers), its backend, the consistency check and every program run | every mutation | nothing, or the mutations tier 1 does not decide |

On `examples/imp` (21 mutations, 7 programs) a warm run took 3.8-7.2 s before L1-4 (median 5.1 s over 7 interleaved rounds), 70-75 % of it resolution and 20-25 % admission, and takes 0.4-1.9 s since (median 0.5 s), nearly all of it the admission's load and compile. A cold run saves about 1.5 s, the 7 baseline compiles of its program inputs, which is within run-to-run noise on a shared host (medians 18.0 s before and 16.3 s since over the same 7 rounds). The 16 flow lists warm take 30-40 s before L1-4 and 10-14 s since; cold, the 49 program-input compiles they no longer make cost about 12 s of 47.3-93.3 s (the sum of the 16 lists' walls, over every cold run of main and of L1-4 with memos; single runs on a loaded host), again of the order of the host's noise (L1-4 and L1-4-fix-1 handoffs and both L1-4 reviews). A mutation the LLM adds, or one whose programs changed, costs its own resolution and calls only: a cold mutation still pays one full load.
A comment or layout edit of the specification (a rustdoc comment KRS emits as a K comment included) keeps the execution digest, so every stored result record and every cached outcome stays in use, and resolution is paid again, since the resolution memo is keyed by the bytes.
What was never cached is computed again, as by every command: a program whose result is never stored (a timeout, an error, an `unknown` the host caused), and a mutation tier 1 does not decide (one with an outcome that is not cacheable on some program: a `timeout`, an `error`, a failed run, run step 8), whose call runs the baselines of its programs live.
A mutation addressed by `line` follows its line, not its rule: when a layout edit shifts that line, the mutation resolves to another sentence or to none, and its cached outcome is not the one used; addressed by `rule`, it keeps it.
A program whose baseline times out costs up to `time_ms` in every command, since a timeout is never cached; `budget.baseline_max_work` turns it into a cached `unknown`.

**The full matrix.** Per mutation, cold, `--full` pays the one compile (with the mutant's backend and consistency check) the first-kill search pays, and runs every comparable program instead of the programs up to the first kill: it adds at most one run per (mutation, program) cell and never a compile.
On `examples/imp` (21 mutations, 7 programs, 147 cells; debug build, 4 compile workers, shared host) a cold first-kill run in corpus order took 31.5 s and 0.33 GiB peak and ran 48 cells, a cold full run 33.4 s and 0.87 GiB peak: the compiles dominate, and the cells first-kill skipped are cheap runs.
A full call holds every program's mutant evidence for one mutant at once, where first-kill holds those up to the kill, so peak memory grows with the corpus per mutant: on a definition with large ends, run it under a memory scope.
Every distinguishing cell computes its `difference` and every `killed` outcome stores one, so the document and `outcomes/` grow with the killed cells (imp: 47 differences instead of 20).
Warm, every cacheable cell is cached, so a later first-kill run is decided by tier 1 for every killed mutation, and a full run calls only for a mutation with a cell that is not cacheable, compiling it again. Before CF-33d a work-bound `unknown` was not cacheable: imp had 136 of 147 cells cached (against 40 after a first-kill run), and a warm full run called the 6 mutations with a work-bound `unknown` cell again, 10.4 s; it now answers them from the cache.
After a first-kill run, a full run calls once per killed mutation, over the programs with no cached outcome.

**The killer record.** With a lock ("The corpus record"), a killed mutation with no valid cached outcome costs one cell, its recorded killer's run, and a survivor costs every program with no cached outcome, as without one.
So a case added to a corpus of M mutations, S of them survivors, costs S runs warm (each survivor runs the new case) and none for a killed mutation, whose cached kill or recorded killer decides; and a fresh checkout with a lock and no cache costs one cell per killed mutation and every program per survivor.

**Trust.** With identical inputs, a cached proved difference stands without being re-run in this command.
This rests on k-rust's compile and execution determinism, on the key naming every input the outcome depends on,
and on the integrity of the cache directory: whoever can write `.kink-flow/` can forge a kill, as whoever can write the kink build can.
Identical inputs are an identical loaded definition up to positions (the execution digest), not identical bytes, which rests on three premises (`digest::execution_digest`).
P1, k-rust's compile: for one build compiling is deterministic, and positions and source names reach `definition.kore` only through its `Source` and `Location` attributes, so two loaded definitions equal up to positions compile, for the baseline and for every mutant, to KORE definitions equal up to those attributes.
P2, k-rust's execution digest: KORE definitions equal up to `Source` and `Location` give equal results outside the Execute exclusions, except in texts that cite a position.
P3, kink: kink's judgement reads a sentence's origin only as whether it is located and whether its source is builtin (kink-patch's authored sentences, its conjunction and cell-frame readings, the definition-level census of kink-native, kink-campaign and kink-flow), both in the digest; every other read of a position (the rule rows and coverage a document renders, the census memo's findings, mutation resolution, a refused string spelling's file in a cause) is presentation, a memo value or resolution, none of which the execution digest keys.
A new read of a position in a judgement would break P3, and a layout edit could then be a wrong hit.
Tier 1 also needs a congruence: a mutation's identity addresses a sentence by fingerprint and occurrence and requires a replacement to keep its position attributes, so two baselines with one execution digest give, after one such replacement or deletion, mutants equal up to positions, and P1-P3 apply to them; k-rust's own KORE execution digest is not such a congruence (compiling maps several definitions to one KORE definition), and it does not see the `unobservable` attribute, which decides which cells are compared.
A failed premise shows as a `--verify` mismatch, never silently: `coverage --verify` and `run --verify` re-derive every stored value from the current bytes.
A stored `comparable` is the result of the uncancelled request, which every host that completes it computes; a host that cannot complete it would compute a `timeout` live, so the stored record answers what the specification computes, written where the host allowed it, in the direction of the memos' host premise (**Memos**), and is never a false kill.
Each record carries a digest that detects corruption and a record moved under another key, not forgery.
`run --verify` re-proves: it updates the results with `--verify`, decides nothing from tier 1 or the memos,
runs the recorded killer alone when it is a program of O (under first-kill), then, unless it killed, every program of O on each mutation, then each program that has a cached outcome and that run skipped, alone,
and compares every cached outcome (and the status the cache would have given) with the live ones.
A difference gives the mutation status `error`, reason `outcome-mismatch:<program id>`, and an entry `{mutation, program, cached, live}`
in the top-level `mismatches` (`program` null for a status difference); the run goes on and exits 1, a finding. It writes no outcome and no lock.
The outcome file's compiled edit (`witness`) is compared with the cold call's too: a difference is an entry `{mutation, program: null, cached: {witness}, live: {witness}}` in `mismatches`, and the run exits 1, but the row keeps its status, which the compiled edit does not decide.
The Execute promise of k-rust (`docs/compatibility.md`, "Execute") is what makes an outcome a function of its key, and it
excludes some runs; each is excluded for the whole program (both sides, both slots) before a record could be written: a
cancelled run is a timeout; kink sets no step timeout; a run with a nonzero `stackStops`, a run on a definition whose load
counted a stack stop (`discharge_counts().stack_stops`, `value_claims().counts().condition_stack_stops`) and a run with a Bytes
hook refused for the memory allowance, on a leaf or on k-rust's `allowanceRefusals` list of the run or its load (re-pin adoption
A-1: a refusal in a passed-over equation or an undone attempt leaves no diagnostic), are `unknown` (failure `stack-stop`,
`load-stack-stop`, `allowance-refusal`; on the baseline the program is not comparable); and in a build with the Z3 profile
every query of kink's backends is bounded by Z3 resource units (`budget.smt_resource_limit`), so none times out: the promise
covers such a run whether or not an answer was undecided, and tier 1 is on (it is off, `outcome_cache.enabled` false with the
reason, only for a solver the clock bounds or a Z3 build that cannot be named). k-rust counts a run's undecided solver answers
(`smtUnknowns`) and kink those of its own queries about the run (leaf feasibility, the observation decider); kink reports both
(`smt_unknowns` and `decider_smt_unknowns` in a program's row and, when nonzero, in an executed entry) and never reads either
as an exclusion (decision D-7 (a1)). So an `unknown` outcome of a compared run is a function of the key too, and is written since
CF-33d (run step 8), unless the backend refused kink's judgement of the run (kink-campaign `RunNotes::unjudged`), which can be
the host's doing. Each record carries
`allowance_bytes`, the writing process's memory allowance, for diagnosis only: it is in neither the key nor the record digest.
This closes the stack dependence of k-rust KINK-06/4 and KINK-06/5 for every comparison through `execute`, live and cached.
What remains is kink's verdict-path calls outside `execute` (`definition_facts`, `BackendRelations` unification, the bridge's
internalization; re-pin finding B-13(a)), which decide nothing for ground programs; under the Z3 profile their solver
questions are bounded by the same Z3 resource units as a run's, which tier 1's context names.
A mutation whose specification uses a hook for which k-rust chooses a value the definition leaves open with no run-level record
of it (`String2Bytes` and `Bytes2String`, whose encoding `domains.md` does not name and k-rust's amendment AM-1 states as one
byte per code point, kept by kink's own choice until GK-1/GK-2, and the `KRYPTO`, `HASH`
and `SECP256K1` hooks no builtin file documents; k-rust's own classes, such as `choice`, the order of `keys_list`, `values` or
`Set2List`, mixed-format or NaN-sign Float, `Base2String`'s letter case and substitution's renamed variables, are judged per run
through `implementationChosenValues` below since kink27 R3-CENSUS-RUNLEVEL; an open hook k-rust cannot
evaluate in an execute request, a console operation such as `#getc` or `#write` or one without an evaluator such as
`Float2String`, is judged per run through `unsupportedHooks` below instead, so stock SIMPLE's stream cells exclude nothing), or
that has a rule or equation condition equating two terms (`{ A #Equals B }`, a gap of k-rust's answers), is `unknown` with reason
`implementation-chosen-hook` or `equals-condition` when the exclusion is the mutant's. A rule whose condition or result depends on
whether `andBool`, `orBool`, `impliesBool`, `#if`, `andThenBool` or `orElseBool` skip an operand that may be undefined excludes no
definition: on such a definition a program whose run reads such an operand that counts (k-rust's `shortCircuitReadings` list; root
README, the short-circuit bullet) is `unknown` for that mutation (failure `short-circuit-reading`, the executed entry's
`short_circuit_readings` naming the step), and every other program is compared. One of the
baseline excludes every baseline run instead: each program's result is `unknown` with the exclusion as its cause, no program
is comparable, and every mutation gets the status `error`, reason `no-comparable-program`. Since re-pin adoption A-1 a program whose run reads
such a value of one of k-rust's own classes (k-rust's `implementationChosenValues` list, wherever the run reads it: a rule, an
equation, a condition, the initial state) is `unknown` for that mutation (failure `implementation-chosen-value`), and so is one whose run or definition's load left an application unevaluated as an
unsupported hook (k-rust's `unsupportedHooks` list; failure `unsupported-hook`); on the baseline the program is not comparable. A program whose run takes an undefined step that falsifies a
`total` or `preserves-definedness` claim the mutant still carries (a baseline claim its edit does not reach: the claims the
edit leaves unbacked are removed from the mutant, above), or an undefined step through such an operator, is `unknown` for
that mutation (failure `contradicted-claim` or `short-circuit-reading`), and a kill by another program, whose runs are clean,
stands (kink's `trust.md`, "What a kill trusts"; decision 2 is per program). Since re-pin adoption A-1 so is a program whose run
lists any record on k-rust's `contradictedClaims` list, observed by the run (a candidate a defined sibling covered, an arrival
a state set absorbed, a condition decided through the contradiction) or by the load of the definition (`observedIn: load`, on
every run's list, so no program of that definition is comparable). On the baseline a contradicted program is not
comparable. Every record is reported as a specification diagnostic, `specification_diagnostics`: in a program's row (from its
result record, the baseline run's records) and in a mutant's executed entry, each `{claim, symbol, k_label, rule_id,
rule_label, application, undefined, observing_rule_id, observing_rule_label, ground, observed_in, says}`, where `says` states,
for a ground record, that the claim is false at the application ("the `total` claim of `td` is false at ..."), which the
author can act on.

| Status | Meaning | What to do |
| --- | --- | --- |
| `killed` | A program's result differs on the mutant; `killer` names the first such program. | Nothing. |
| `survived` | Every program ran to a comparable result and agreed. | Write a program that matches the edited rule and whose result the edit changes (`witnesses` lists the programs whose coverage witnesses the mutant's compiled edit: they applied the edited rule, k-rust `applied`: a step built a candidate of it, defined or not, for an edit confined to its right-hand side or `ensures`, or matched it for any other edit of a rewrite rule and for an edit of an equation's `requires`; every program witnesses an edit that is not site-local, and a program whose cached coverage is not complete witnesses every edit, `run` step 3. `applied` is wider than `coverage`' `fired_by`, which lists only steps a path takes: a candidate rolled back because its result was undefined is a site an edit can make defined). |
| `equivalent` | kink shows the mutant to be the specification: it compiles to the baseline's executable definition, or every edited equation only adds to its `requires` conjuncts that hold of every value of their variables' sorts, the sort predicate of a variable of that sort, written or inferred (reason `valid-condition`; `weakening` names each such equation, kind `valid-condition`, decided at resolution as `unkillable` is). | Nothing can kill it; drop or change the mutation. |
| `unkillable` | The edit only deletes equations of functions or lemmas, or replaces one by an instance of itself, a narrower pattern or `requires` (reason `weakening`; `weakening` names each edited equation or lemma): every model of the specification is a model of the mutant, so no program can kill it. Decided at resolution, after the `baseline-findings` check (run step 2); no program runs. | Write what the misunderstanding gives on the inputs the narrowed equation no longer covers, or change a right-hand side or a rewrite rule, or drop the mutation. |
| `not-admitted` | kink did not admit the mutant for judging (`reason` is the runner's failure): it does not compile (`rejected`), its lowering does not terminate, or k-rust's critical-pair check does not show its equations to have a model (`inconsistent-mutant`, the pairs in `inconsistent_pairs`). Named apart from `invalid-mutation`, a mutation that does not resolve, and from the compile-stage reason `rejected`; before run document version 18 it was `invalid`. | Fix the mutation; for `inconsistent-mutant`, rewrite the edit so that the check shows each named pair to join, for example with guards it refutes as disjoint. |
| `timeout` | No program killed it, and a program did not finish on the mutant within `budget.time_ms`. | Write a program that terminates under the mutant and shows a different result. |
| `unknown` | No program killed it, and a program's result on the mutant is not comparable; or, with reason `baseline-findings`, the baseline's full critical-pair check has a finding `[spec] assume_joined` does not name (`findings` lists each with its name and verdict; no call is made and no store is read), or, with reason `mutant-findings`, the claim-free mutant's findings outside the heads its edit can change differ from the baseline's. With reason `stack-stop`, a program's mutant run met a stop for lack of native stack (the mutant recursed without end there); with reason `open-application`, every program the mutant left undecided is undecided because each leaf of its run that keeps it so holds an application of a function the mutation edits that no equation of the mutant reduces (each cause names one); with reason `work-budget`, every program the mutant left undecided was cut by the work budget (`[budget] work_factor`: the mutant's run did more than `max(work_factor × P, P_max)` polls; each cause names the polls and the bound), so the program did not stop the comparison, the mutant's work did. | Write a program whose result on the mutant kink can compare; for `baseline-findings`, fix the specification or name the findings you accept as premises; for `stack-stop`, a program on an input the mutant ends on, or, when it recurses without end on every input that reaches the edit, the misunderstanding as a mutant that ends; for `open-application`, a program on which the mutant reduces the application, or, when the edit leaves the function's value open on every input that reaches it, the misunderstanding as a replacement whose result differs; for `work-budget`, raise `[budget] work_factor` if the mutant may end after more work (only the programs the budget cut run again), or, when it recurses without end on every input that reaches the edit, accept it as unknown, since no program can tell it apart by its end, or write the misunderstanding as a mutant that ends; or drop the mutation. |
| `error` | The runner failed for the mutant, a corpus error (`reason`: `baseline-mismatch:<id>`, `baseline-count-mismatch`, `campaign-refused`, `program-refused:<id>`, `outcome-conflict`, `no-comparable-program`), `run --verify` found a cached outcome that differs from a live run (`outcome-mismatch:<id>`) or a memo of the mutation's resolution that differs from its live resolution (`resolution-mismatch`, re-pin L1-4), or the host refused the stack the mutation's patch needs (`host-stack-refused`, see the reason table). | Report it, or fix the corpus; for `outcome-mismatch`, delete `outcomes/`; for `resolution-mismatch`, delete `memo/`; for `host-stack-refused`, rerun where the host grants more address space. |
| `invalid-mutation` | The mutation does not resolve (`reason`, `edit`, `detail`; see the table above). | Fix the mutation. |

A kill folds above every inconclusive outcome: a mutation that one program kills is `killed` even if an earlier program timed out on it.

The document is the report (see "The report: the run document" below).

### The cache directory

Besides `results/` and `report.json` (the last run's document, also written when the specification is refused or no mutation is selected):

- `outcomes/<context digest>/<mutation identity>.json`, tier 1:
  `{schema: "kink-flow-outcomes", version: 6, context, context_sha256, mutation_identity, mutation_id, removed_claims, witness, records: {<program digest>: {program_id, baseline_run_sha256, outcome, slots, mutant_run_sha256, difference, cause, open_application, smt_unknowns, decider_smt_unknowns, allowance_bytes, record_sha256}}}`.
  `outcome` is `killed`, `agree` or (version 5, CF-33d) `unknown` (run step 8).
  `difference` is a `killed` record's kill evidence (below, "Kill evidence"), null on any other record: outside the key, which names every input it is a function of, and inside `record_sha256` (domain `kink-flow/outcome-record/v4`), so a record whose evidence was altered is ignored; no status is read from it.
  `cause` (version 5) is an `unknown` record's cause, the live executed entry's, null on any other record, and `smt_unknowns` and `decider_smt_unknowns` are the mutant run's undecided solver answers, k-rust's and kink's, as the live entry counted them: outside the key, of which they are functions, and inside `record_sha256`; the report prints them on the cached entry and decides nothing from them.
  `open_application` (version 6) is whether an `unknown` record's program is undecided because every leaf of the mutant's run whose path is incomplete holds an application of a function the mutation edits that no equation of the mutant reduces (an executed entry's `cause`, below); `false` on any other record, and a record with `true` on another outcome is ignored. It is a function of the run, so of the key, and inside `record_sha256`; a row's `reason` `open-application` is folded from it for a cached unknown as from the census for a live one.
  A version 1 file, which has no evidence, is not current: its records are ignored and recomputed.
  Since version 4 the evidence names its format (`format`, below); a file of an earlier version is not current, and so is one before version 5, which has no `cause`, or before version 6, which has no `open_application`.
  `witness` (version 3; a version 2 file is not current) is the mutant's compiled edit as `run` step 3 reads it, `{reading, global, matched: [{module, index}], applied: [{module, index}]}`: the baseline sentences a program witnesses the edit through by matching them (k-rust `matched`) and by applying them (`applied`), or every program when `global`; null when no call that wrote the file compiled the mutant.
  `reading` is `ground-programs`: the edit as a ground program witnesses it, the mutant as written's when only definedness claims were withdrawn (step 3).
  A `witness` without `reading` was written from the claim-free side alone: it is read when the row's `removed_claims` names no withdrawn claim or one that is not a definedness claim, since that side's edit is then the one step 3 reads, and is otherwise not read (with only definedness claims withdrawn the claim-free side's edit can be wider than the author's, step 3), so the row has no `witnesses` until a live call writes the file again; while tier 1 decides the row with no call, none does, and removing the file (or the cache's `outcomes` directory) makes the next `run` compile the mutant and record it.
  It is a function of the key (the claim-free mutant compiles from the mutation's patch under the context's kink identity, and the rule authors are the compiled baseline's), resting on the compile determinism every record rests on.
  A row tier 1 decides with no compile reads it for `witnesses` and for which cached killer it names (step 4); it decides no status and orders no call, so it is in no digest, and one that does not decode gives no `witnesses`.
  `removed_claims` is the row's (below), for the reader only: it is read back by nothing and is in no digest.
  The context is `{outcome_schema: "kink-flow/outcome/v4", kink_build, kink, profile, execution_digest: {kind, digest}, budget, oracles, classifier}` (`budget` does not name the work budget, which each record's `polls` does; `oracles` names the slots, and where the second is `cells` the context also holds `not_compared`, the cells left out, so that the context says on its face which projection an outcome was decided for; with `[stop]` it also holds `stop`, the run document's, so that an outcome answers only for the stop it was decided under; where a front end renders kill evidence, it also holds `evidence`, `{format, identity}`: the format of that evidence and every further input it depends on beyond the ends, the definition the execution digest names and the build (`krs kink`'s: the SHA-256 of the Definition IR without its provenance, since the evidence names cells, constructors and fields by Rust names a constructor's fields do not carry into the emitted K), so that a store never serves evidence another renderer, or the same renderer over other names, would not write):
  `kink` is kink's semantics identity (kink-campaign `identity`, packet CACHE-ID), `{k_rust_revision, fingerprint, canonical_patch, compiled_kore, patch_admission, claim_removal, mutant_consistency, mutant_effect, weakening, data_facts, terminal_value, definition_exclusion, execution_request, result_schema, coverage, one_sided, stop}`, the version of every kink algorithm an outcome can depend on. Among them:
  `claim_removal` is kink-patch's `CLAIM_REMOVAL_VERSION`, since the mutant every record ran on depends on the claim-removal algorithm (v2 since re-pin R0c-fix-3: the reach follows the overload and unit axioms; v3 since R0c-fix-4: a rule with configuration context is an equation of its head);
  `mutant_consistency` is kink-native's `MUTANT_CONSISTENCY_VERSION`, since a mutant runs (and a record exists) only when its equations are shown consistent (v2 since R0c-fix-4: the check's guard reads the equation and skipped-pair counts; v3 since k-rust FZ-CONFLUENCE: k-rust pairs the equations at evaluated hooks with the hooks' written meanings and refutes more overlaps; v4 since fz26 phase 8: k-rust refutes still more overlaps and splits residuals, joins pairs over sorts with no normal form through the witness equations it adopts, whose adoption can flip between a baseline and its mutant, and the gate reads the mutant's full check from its per-definition facts, `data_facts` below, with their completeness guard);
  `mutant_effect` is kink-native's `MUTANT_EFFECT_VERSION`, since the symbols the check reads, and the cross-check of kink-patch's source reading, come from the compiled definitions (re-pin R0c-fix-4; v2 since fz26 KINK-WITNESS: a head whose adopted witness equations differ from the baseline's counts as changed, a witness reaches the symbols it applies as an equation of its head does, and a flip of the adopted witness pass checks every head);
  `weakening` is kink-patch's `WEAKENING_VERSION`, since whether a mutation is `unkillable`, and so runs nothing, is that test's verdict (v1 since kink27 R5-WEAKENING; v2 since its fix round 1: a label is a conjunction only when it denotes conjunction in every model, so a macro production hooked `BOOL.and` no longer makes an edit a narrowing; v3: a replacement by an instance of the sentence, a narrower pattern or `requires`, is a narrowing, and a lemma may be narrowed; v4: the instance test reads each variable's sort from the loaded sentence, written or inferred, so a narrowing written without sorts is one, and two mutations that load to one sentence get one verdict; and a `requires` that adds only the sort predicate of a variable of that sort keeps the axiom, kind `valid-condition`, and a mutation of only such edits is `equivalent`);
  `data_facts` is kink-native's `DATA_FACTS_VERSION`, since what kink refuses on each definition's full critical-pair check decides whether a mutation can be killed at all (v1 since fz26 KINK-BASELINE-FINDINGS: a mutation is `unknown` with reason `baseline-findings` while the baseline has a finding no `[spec] assume_joined` name assumes, and with reason `mutant-findings` when the claim-free mutant's findings outside the heads its edit can change differ from the baseline's);
  `terminal_value` is kink-native's `TERMINAL_VALUE_VERSION`, since which ends a slot compares depends on it (v1 since fz26 KINK-OVERLOAD-VALUE: an instance-normal overload application is admitted where k-rust's `is_data` holds, and every compared end is judged under both definitions; v2 since fz26 KRUST-ANYWHERE-HEAD: k-rust's data heads also take an `anywhere` head with plain equations declared total or `value-production`, such as SIMPLE's `_[_]`, and drop an overload head declared neither; v3 since kink27 R5-BYTES-ENDS: a `Bytes` domain value, its payload in its sort's stored form, has a trusted injective codec, so an end holding one is compared);
  `definition_exclusion`, `patch_admission` and `execution_request` name the definition exclusions (re-pin R0-tail; v2 since re-pin adoption A-1, which reads k-rust's run-level lists; v3 since fz26 KS-PIN-SCDEF and KINK-CENSUS-RUNLIST: a short-circuit operator is flagged only when a term its skipped operand may leave undefined is not one another operand must evaluate, and the definition-level census reads only the open hooks k-rust evaluates without a record, the others being judged per run through `unsupportedHooks`; v4 since kink27 R3-CENSUS-RUNLEVEL: k-rust's classes leave the census and the initial-state check, a run that reads one being excluded by its `implementationChosenValues` list; each only narrows what is excluded), the rule that no typing error refuses a patch (L2-2-fix-1) and the execution request with its state-set modality and work budget (L1-1);
  `kink_build` is the SHA-256 of the running `kink-flow` executable, so any rebuild (debug or release) starts a new context;
  `execution_digest` is the result cache's (kind `kink-flow/execution/v1`, the loaded definition without positions, "Results" above; kind `kink-flow/spec/v1`, the specification digest, on its fallback), so a comment or layout edit keeps the context and editing the meaning of the specification starts a new one;
  `budget` is the result key's, the bounds a stored class depends on (no `time_ms`: a cached outcome is decided from complete evidence, which no clock stopped).
  The context names no schedule: an outcome is one executed test's, which the schedule does not change, so the first-kill search and `run --full` share the store ("The full matrix" above).
  The mutation identity hashes each edit's kind, module, the addressed rule's fingerprint, its occurrence among equal fingerprints of the module,
  and the replacement's fingerprint: positions excluded, so it is the same after an edit that only moves the rule.
  `baseline_run_sha256` is the program's result `run_sha256` when the outcome was proved, and `mutant_run_sha256` the same digest of the mutant's evidence.
  A record is used only when the file's schema, version, context and identity are the current ones, its `record_sha256` recomputes,
  its outcome agrees with its slots (`killed` exactly when a slot is `distinguish`, `agree` exactly when both are `agree`, `unknown` exactly when each is `agree` or `unknown` and one is `unknown`), it has a `cause` exactly when it is `unknown`,
  and its program is comparable with that baseline run digest; anything else is ignored.
  If the executable cannot be read, tier 1 is disabled for the command (`outcome_cache.reason` says why) and every mutation runs.
- `memo/resolutions/<spec digest>/<sha256 of the mutation's edits>.json` and `memo/census/<spec digest>.json`, the warm path's memos (re-pin L1-4, **Memos** above), keyed by the exact specification digest, not the execution digest, since their values cite file names, lines, rule texts and census sources and locations:
  `{schema: "kink-flow-memo", key, value, record_sha256}`, where `key` is `{version: "kink-flow/resolution-memo/v4", kink_build, kink, spec, mutation}` (`mutation`: the edits, each `{file, rule, line, find, replace, delete}`) or `{version: "kink-flow/census-memo/v2", kink_build, kink, spec}`, each with `smt` under the Z3 profile, the result key's solver member (k-rust's load infers the sorts of a term the portable inference does not support by asking Z3, with no bound, so what a load gives can depend on the Z3 build; no memo value depends on the units, which only make a record miss when they change),
  `value` the facts `{digest, rules, identity, typing_diagnostics, removed_claims, weakening}` (v2 since kink27 R5-WEAKENING added `weakening`) or the census (kink-native `DeclarationCensus::value`), and `record_sha256` the digest of `{key, value}` under the version.
  A record is used only when its key is exactly the current one and its digest recomputes under that key; the path only finds it.

- `patterns/<execution digest>/<pattern digest>/<program digest>.json`, the cached answers of `query` (flow F-18, "Checking a pattern" below). `run` neither reads nor writes them.

Every file is written atomically; deleting any of them, or the whole directory, is always safe.
The `killers/` directory of F-05 and the `hints.json` of F-14 are no longer read or written and can be deleted: the killer record (`--lock`, "The corpus record"), a file of the corpus outside the cache, replaces them.

Exit status ("Exit status"): 0 when every selected mutation got its verdict (survivors included);
1 when `--verify` found a mismatch, or `--locked` found that the run would change its lock;
3 when a selected mutation is `timeout` or `unknown`;
2 when the manifest, the mutation list, the lock, the specification or a program is refused, the lock cannot be written, a selected mutation is `invalid-mutation` or `not-admitted` (its author must fix it before it is judged: it does not resolve, or its mutant does not compile or may have no model), a run failed, a cache file could not be written,
no program is comparable, a corpus error stopped the run, or on a usage error (including an `--only` id that names no mutation, or `--verify` given twice).
The document is the same whatever the status: the exit status is how a script or an agent's loop notices an invalid mutation or a mutation with no verdict, and `check --mutations` finds the unresolved ones without running anything.

## The report: the run document

`run` prints one document and writes the same document to `.kink-flow/report.json` (after every mutation, and once more at the end):

`{schema: "kink-flow-run", version: 31, k_rust_revision, profile, result_schema_version, kink_build, kink, spec, programs, unusable_programs, mutations, counts, survivors, result, stopped, outcome_cache, mismatches, baseline_runs, schedule, matrix, untargeted_rules, data, lock}`; `data` (fz26 KINK-BASELINE-FINDINGS, also in the `coverage` and `query` documents; null in the run and `coverage` documents when the specification is refused, absent from a refused `query` document) is `{assume_joined, has_data, findings: [{name, verdict, assumed, description}]}`, the baseline's full critical-pair check under the premises.
Version 3 (F-13) names the oracle slots of an executed entry, versions 4 to 6 add row fields (below), version 7 (packet CACHE-ID) adds `kink`, kink's semantics identity, version 8 (packet CACHE-ID-fix-1) adds `kink_build`, the SHA-256 of the executable that wrote it, version 9 (re-pin adoption A-1) adds `specification_diagnostics` and `smt_unknowns` to program rows and executed entries, version 10 (fz26 KINK-BASELINE-FINDINGS) adds `data`, the `findings` of a `baseline-findings` row and a comparable program row's `unable_to_kill`, version 11 (kink27 R5-WEAKENING) adds the status `unkillable` and each row's `weakening`, version 12 (CF-16) adds each executed entry's `difference`, the sides of a cached or one-sided kill, and each program row's `ends`, version 13 (CF-02) adds `spec.exclusion`, version 14 adds `result` and the slot name `cells`, version 15 (CF-03) takes the short-circuit reading out of `spec.exclusion` (each run of a definition whose analysis flags a rule is judged by its own list of readings) and adds `short_circuit_readings`, the readings that excluded a run, to program rows and executed entries, version 16 (CF-23) adds `schedule`, `matrix` and each row's `killed_by`, version 17 reads each row's `reaching` from the compiled mutant (step 3), or from the outcome file's copy of it on a row tier 1 decided, `[]` on a `no-comparable-program` row and otherwise `null` on a row with neither, and lists each call's `programs` in the order the call ran them, version 18 (CF-40c2) names each row's `reaching` `witnesses` and the status `invalid` `not-admitted`, so that each coverage predicate and each status has one name in every kink-flow document ("Coverage predicates"), and version 19 witnesses a rewrite rule edit that is not confined to its right-hand side or `ensures` (its left-hand side, an attribute, a deletion) by `matched` instead of `applied` (step 3), so a row's `witnesses` and each call's program order can name more programs for the same mutation, version 20 adds `stop` (absent without `[stop]`), each end's `halt` under a stop, each survivor's `stop_hides_edit`, and the reason `stop-unresolved` ("Where a run ends"), version 21 names each `difference`'s format and makes it a front end's evidence where a front end renders one ("Kill evidence"), and version 22 adds the programs of named cases (`<path>#<name>`) and a case's `expectation` in its program row, with the refusals `typed-expectation` and `expectation-value` ("Expectations"), version 23 (CF-33c) adds `decider_smt_unknowns`, the undecided solver answers of kink's own questions about the run beside k-rust's `smt_unknowns`, to every program row and to an executed entry where it is not zero, with the outcome cache on under the Z3 profile where the solver is resource-bounded, version 24 (CF-33d) lets an executed entry from the outcome cache (`cached: true`) be an `unknown` with its `cause` and the cached run's undecided-answer counts, and names each side's `cause`, `smt_unknowns` and `decider_smt_unknowns` in a program's `mismatches` entry, version 25 lets `result` name cells inside `?` and `*` cells, each compared or left out in every instance, and a narrowing's `compared` name the key of each Map that encloses a named cell ("Which cells are compared"), version 26 reads an alias of an edited axiom's left-hand side as the pattern it names (step 3), so a row's `witnesses` can name fewer programs for the same mutation, and adds each row's `witnesses_global`, and version 27 names in a cause the open application of an edited function that a stuck leaf, an undefined step or a stop's end holds, as it did an indeterminate leaf's, with its arguments, gives a row the reason `open-application`, names each side's `open_application` in a program's `mismatches` entry, and gives a `run --verify` row the reason `run` gives its cold call, and adds the reason `open-application` (below), version 28 adds the `weakening` kind `valid-condition` and the `equivalent` row with reason `valid-condition` of a mutation whose every edited equation keeps its axiom, version 29 adds the killer record ("The corpus record"): `lock`, each row's `recorded_killer` and `killer_change`, the `killer_source` `record` in place of `hint`, a killer that follows the record under both schedules, and no `order` (the search order is fixed) nor `stale_killer`, version 30 adds `[stop] when` ("Where a run ends"): `stop.when`, the condition's identity, the cause `stop-condition` of an `unknown` program whose run's condition was undecided or had no value at an arrival, the reason `stop-condition-incompatible` of a `not-admitted` mutant, and a survivor's `stop_hides_edit` read under a condition from the comparable programs' coverage. Version 31 names in `lock.difference` the first line in which a compared lock differs from the rendering, and gives a run refused before its lock is read (a manifest or a mutation list that does not decode) the `lock` it left unwritten, and gives an `equivalent` row an empty `removed_claims`.
Version 32 adds `z3` under the Z3 profile, the Z3 build the verdicts were decided on, and `lock.header_changes`, each header key whose value differs from the compared lock's.
Version 33 adds `[observe]` ("What a run observes"): `observe`, each program row's `observations` and the class `comparable-prefix`, the slot `observations` of an executed entry with its `position`, `horizon` or `cause`, kink's observation evidence of a kill only the channels decided, a survivor's `horizon`, and the reasons `point-unresolved` and `observation-incompatible` of a `not-admitted` mutant and `observation-capture:<program id>` of an `error`.
Version 34 names why each horizon's channel opened: a horizon is `{elements, opening}` in the slot `observations` and a survivor's `horizon`, a program row's `observations` gives each open channel's `opening`, a survivor's action asks to raise the bound only where some horizon's opening is `bound` or `cycle`, and a prefix program none of whose channels kept an element within its budget or closed by a cycle is `unknown`; and it names the cycle closure: a channel's `closed` can be `cycle`, and an element of kink's observation evidence `cycle`.
Version 35 compares a program whose run has several paths by its channels' prefix sets ("What a run observes"): the slot's `position` has `outside` for such a difference, whose evidence is `kink-k-sets/1`.
Version 36 gives a program row's `observations` of a run with several paths its prefix sets' facts, `{paths, real, channels: [{name, complete_to}], horizon}`, where version 35 showed each channel open at 0 by `branch` whatever was explored.
Version 37 adds a mutation's expectation ("`MUTATIONS.toml`"): each row's `expect` and `expectation`, the action of a met control's `survived` row, and `expectations`.
Version 38 (KINK-FINDING-NAMES) names each finding of `data` and of a `baseline-findings` row by its kind, sentences and digest (`spec.assume_joined` above), where version 37 named it by generated-K positions; a finding has `sentences`, and a `[spec] assume_joined` name is refused with its own reason.
Version 39 (FB45-LOCKED-TIMEOUT) keeps a lock entry a run the clock stopped could change ("What decides a verdict"): `lock.kept`, `lock.clock_stopped` and the `lock.status` `undecided`. It also gives `lock` its `legacy`, `{path, status, moved}`, where the run was given an old lock file that is still there ("The corpus record", "Old files"; FB48-ONE-LOCK, unreleased with this version).
`report` prints the stored statuses without re-deriving them, so it refuses (`unreadable`) a document of another version, one written by another build (or naming none), and one whose `kink` is not this build's.

| Field | Meaning |
| --- | --- |
| `spec` | `{outcome, stage, reason, detail, digest, execution_digest, files, exclusion}`: the specification's admission and its digest, the execution digest that keyed the result cache and tier 1 (`{kind, digest}`, null when the specification is refused; added to version 14 without a new version, since it is additive), and its definition exclusion with its causes (`exclusion`, since version 13; as in the check document, null when there is none). |
| `programs` | The `coverage` rows `{id, digest, class, cause, cached, verify, wall_ms, specification_diagnostics, smt_unknowns, ends, short_circuit_readings}` (`ends`, each end's computation head and class, since version 12; `short_circuit_readings`, the readings that excluded the baseline run, since version 15), plus `not_cached` for a result that depends on the host and was not written (no `rerun` any more: no stored record is a timeout). `specification_diagnostics` (the baseline run's contradicted-claim records, above) and `smt_unknowns` (its undecided solver answers, reported only) come from the result record (absent on a `refused` row, which has none). |
| `unusable_programs` | Every program whose class is neither `comparable` nor `comparable-prefix`, once: `{id, class, cause}`. These programs are never run on a mutant. |
| `mutations` | One row per selected mutation, in the list's order (below). |
| `counts` | The number of mutations per status (all nine statuses). |
| `survivors` | The ids of the mutations whose status is `survived`, `timeout` or `unknown`: no program killed them, and a new program could. Each survives relative to the cells compared (`result`). A control (`expect = "survive"`) is listed too: the list is of statuses. |
| `expectations` | `{met, unmet, inconclusive, unchecked}`: the ids of the rows whose `expectation` has each verdict, in row order, and in `unchecked` the ids of the mutations of the list that state `expect` and have no row, in list order (the run stopped at a corpus error before them, which already exits 2, or `--only` left them out), so that no expectation the run did not check reads as met; a mutation without `expect` is in none. Since version 37. |
| `result` | `{slots, compared, not_compared, unobservable}`: the slots and the cells the programs' second slot compares (above, "Which cells are compared"); null when the specification is refused. |
| `stop` | `{before, after, count, counts}` of `[stop]` ("Where a run ends"); absent without it. Each survivor survives relative to the stop. |
| `observe` | `{points, logs}` of `[observe]` ("What a run observes"); absent without it. Each survivor survives relative to the declared observation, and one that rests on a horizon has `horizon`. Since version 33. |
| `stopped` | `null`, or `{mutation, reason}` of the corpus error that stopped the run. |
| `outcome_cache` | `{context_sha256, enabled, verify, reason, mutations_from_cache, programs_from_cache, records_written}`: tier 1's context (null when disabled), whether it decided statuses, whether this is `run --verify`, why not, the mutations decided with no call, the cached program outcomes used, and the records written (one per program, also when the recorded killer ran in two calls). |
| `z3` | Under the Z3 profile, `{version, library_sha256}`: the Z3 build the document's verdicts were decided on (k-rust's `z3_build`; `library_sha256` null when the build cannot name its library); absent under the no-Z3 profile. The verdicts rendering names it ("Verdicts"). Since version 32. |
| `lock` | Null without `--lock`; else `{path, status, reason, header, header_changes, changes, difference, clock_stopped, kept}` ("The corpus record"; `clock_stopped` and `kept` since version 39, "What decides a verdict"), with `legacy`, `{path, status, moved}`, where the command was given an old lock file that is still there (since version 39, "The corpus record", "Old files"), or `{path, outcome: "refused", detail}` for a lock that does not decode. A run refused before the lock is read (its manifest or its mutation list does not decode) has `{path, status: "not-written", reason: "refused", ...}`, as a run whose specification is refused. |
| `mismatches` | `run --verify`'s differences `{mutation, program, cached, live}`; empty otherwise. A program's entry gives each side's `outcome`, `mutant_run_sha256`, `cause`, `smt_unknowns` and `decider_smt_unknowns` (the last three since version 24) and `open_application` (version 27), all compared. |
| `baseline_runs` | `{live, reused, diagnostic}`: the baseline runs this command made live (the result update's and the calls'), at most one per program, the baseline requests of its calls answered by one of them, and the diagnostic runs of refused baselines that did not stop on time; null when the specification is refused. Outside every digest and key. |
| `schedule` | `first-kill`, or `full` for `run --full`; present on every run document, a refused one included (a manifest or a mutation list that does not decode). |
| `matrix` | Null unless `schedule` is `full` and the specification was admitted; then `{programs: [{id, kills, sole_killer_of, undecided}]}`, one entry per `comparable` program in `FLOW.toml`'s order (a list, since a JSON object would order the ids by name): `kills` the mutations, in row order, whose `killed_by` holds the program; `sole_killer_of` those whose `killed_by` is exactly that program (the only proven killer: where another program's cell is undecided, that program might kill too); `undecided` those whose `executed` has an entry of the program with an outcome other than `agree` and `distinguish` (a timeout, unknown, incomparable, error or failed run), where the program might kill and the run could not tell. A row with no cell (`invalid-mutation`, `unkillable`, a corpus error, a mutant that failed as a whole) is in no list. It is computed from the rows, so the document written after each mutation holds the rows finished so far. It gives the facts a corpus minimization needs; choosing a subset also needs coverage and the survivors, and is the user's. |
| `untargeted_rules` | The rules no resolving mutation of the whole list targets (`--only` limits the search, not this list, and a mutation a front end refused counts by kink-flow's resolution) . |

A mutation row is `{id, note, expect, expectation, digest, identity, removed_claims, inconsistent_pairs, typing_diagnostics, status, reason, killed_by, killer, killer_source, killer_from_cache, recorded_killer, killer_change, unusable_killer, witnesses, executed, calls, call_wall_ms, rules, action}` (version 4 added `removed_claims`, version 5 `inconsistent_pairs`, version 6 `typing_diagnostics`; version 18 named `reaching` `witnesses`):

| Field | Meaning |
| --- | --- |
| `digest` | The patch digest; null for an `invalid-mutation`, which also has `edit` (the offending edit's index or null) and `detail`. |
| `identity` | The mutation's position-free identity (tier 1's file name); null when it has none (the mutation then always runs). |
| `removed_claims` | `{removed, unsupported}`: the trusted claims the edit leaves unbacked. `removed` are absent from the mutant every program ran on (a `simplification` claim is a deleted lemma); `unsupported` are those no removal takes away, which make the mutation `unknown` (`unsupported-claims`), and each compiled equation the source reading does not explain (key `unread-equation`). Each is `{module, index, label, key, value}` (`label` null for a production) or `{inserted, key, value}` for a sentence the edit inserts. The row reads them from the deciding call's plan when it records claims (since re-pin R0-tail; the cross-check's `unread-equation` claims are known only there), and otherwise from kink-patch's withdrawal of the mutation's patch, which gives the same claims. Absent on an `invalid-mutation`; both empty on an `equivalent` row, whose mutant is the specification's theory (with reason `valid-condition` every edited equation keeps its axiom, with reason `equivalent-compilation` it compiles to the baseline's definition), so every claim of the specification holds of it and it withdraws none. |
| `inconsistent_pairs` | `[{first, second, position, reason}]`: the pairs of equations (each named by its rule label, written position or id; `position` the overlap's argument path, empty for the root) that k-rust's critical-pair check does not show to join, which make the mutation `not-admitted` (`inconsistent-mutant`); empty otherwise. Absent on an `invalid-mutation`. |
| `weakening` | Null, or for an `unkillable` mutation, or an `equivalent` one with reason `valid-condition`, `[{module, index, label, head, kind}]`, `kind` `deleted`, `narrowed` for a sentence replaced by an instance of itself (a narrower pattern or `requires`, with the same value on every instance it still covers), or `valid-condition` for a sentence whose `requires` adds only conjuncts that hold under every valuation of their variables (the same axiom; version 28); `head` null for a lemma. |
| `typing_diagnostics` | `[{module, index, label, message}]` (or `{inserted, message}`): the edited rules' errors in compilation's typing view (kink-patch `Mutant::typing_diagnostics`), empty when each types. A diagnostic only: compilation decides whether the mutant is valid, and a mutant with a typing error that compiles is run like any other. Absent on an `invalid-mutation`. |
| `status`, `reason` | The status (see the run section) and the runner's or the flow's reason. |
| `expect`, `expectation` | The mutation's `expect` (`survive`, `kill` or null), and null without it, else its check against `status` ("`MUTATIONS.toml`"): `{verdict, detail}`, `verdict` `met`, `unmet` or `inconclusive`, `detail` what the row shows against the claim (`expected to survive, killed by add`, every program of `killed_by` under `--full`; `expected to be killed, survived`; the undecided programs and their causes of a `timeout` or `unknown` row) or that a met control is vacuous, or met only within what the runs observed (a survival resting on a `horizon` or on `stop_hides_edit`, whose row keeps its action), null otherwise; both front ends print `mutation ID: DETAIL` on stderr for each unmet or inconclusive one. Since version 37. |
| `killed_by` | Under `--full`, on every row a fold decided, every killing program in `FLOW.toml`'s order, cached or live (`[]` unless the status is `killed`; version 15). Null under first-kill, which establishes one killer ("The full matrix"), and on every row no fold decided (`invalid-mutation`, `unkillable`, a corpus error, `outcome-mismatch`, `resolution-mismatch`). |
| `killer`, `killer_source`, `killer_from_cache` | The killer of a `killed` mutation under both schedules: the recorded killer while it kills, else the first killing program in C ("The corpus record"); where the kill came from: `outcome-cache` (tier 1; under `--full`, the killer's cell was cached), `record` (the recorded killer's one-program call; never under `--full`) or `search` (the canonical call); `killer_from_cache` is true for `outcome-cache` only. Null, null and false otherwise. |
| `recorded_killer`, `killer_change` | The lock's killer of the mutation, or null (always null without `--lock`), and why `killer` is not it: null when they are equal, else `no-record` (no recorded killer, and the mutation is killed), `not-in-corpus` (the recorded id is no `[[program]]`), `not-comparable` (its class is not comparable; `unusable_killer` says why), `clock-stopped` (its run was stopped by the clock, so whether it still kills is not decided on this host, and the lock keeps it), `no-longer-kills` (it ran, live or cached, and did not distinguish; its `executed` entry gives the outcome) or `not-run` (no program ran it: the status was decided before any run, as for `invalid-mutation`, `unkillable`, `baseline-findings` or a mutant that failed as a whole). |
| `unusable_killer` | `{program, class, cause, source}` when a cached kill (`source` `outcome-cache`) or the lock's record (`record`) names a program of the corpus that is not comparable now; else null. |
| `witnesses_global` | Whether the mutant's compiled edit is not site-local (step 3: an equation's left-hand side or attribute, a removed or inserted equation, a declaration, ...), so that `witnesses` is every program whatever its coverage reaches: a changed pattern can match terms no baseline run tried (version 26). Null when `witnesses` is null and on a `no-comparable-program` row, whose O is empty; `false` on a row whose site-local edit no program witnesses (`witnesses: []`). |
| `witnesses` | The comparable programs whose cached coverage witnesses the mutant's compiled edit (step 3: applied, k-rust `applied`, for an axiom whose edit is confined to its right-hand side or `ensures`; matched, k-rust `matched`, for any other axiom of a site-local edit; every program for an edit that is not site-local; and, for any edit, every program whose cached coverage is not complete; a definedness claim kink withdraws, which `removed_claims` names, adds none through coverage, step 3), in O's order: the compiled edit of this run's call, or, on a row tier 1 decided with no call, the one the mutation's outcome file keeps (`witness`, "The cache directory"). `[]` on a `no-comparable-program` row: O is empty, and no program of an empty set witnesses an edit, whatever the edit. Otherwise `null` when there is no compiled edit: the row is `unkillable`, `invalid-mutation` or a `baseline-findings` row, its mutant was refused before its claim-free side compiled, or tier 1 decided the row with no call from an outcome file whose `witness` is not read (one written without `reading` for a mutation kink withdrew only definedness claims from, "The cache directory"), which stays so while tier 1 decides it. `applied` holds every candidate a step built of the rule, defined or rolled back, so `witnesses` can list a program that `coverage`' `fired_by` (k-rust `committed`, the steps a path takes) does not: an edit can make a rolled-back candidate defined, and that program can then kill. |
| `executed` | `{program, outcome, slots, difference | failure, cause, cached, wall_ms, baseline_ms, baseline_reused}` (`difference` since version 12: the kill evidence of a distinguishing program, live or cached, null on every other compared program; below), plus `specification_diagnostics` when the mutant's run lists a contradicted-claim record and `smt_unknowns` when its count of undecided solver answers is nonzero (version 9), and `short_circuit_readings` when its list of short-circuit readings holds entries that count against it (version 15, as a `coverage` row prints them; the `cause` of a `short-circuit-reading` failure names the step), for every program whose outcome decided the status: first the cached ones (`cached: true`, in the order of step 3), then each program the mutant ran on in this command, in the runner's order, each listed once (a recorded killer that did not kill and ran again in the canonical call is listed with that later run; `calls` lists every call); under `--full` every program of O, cached and live merged in `FLOW.toml`'s order, so the row is the matrix row. `outcome` is `distinguish`, `agree`, `timeout`, `unknown`, `incomparable` or `error`; `failure` names a run that produced no value (`time-limit`, `resource-limit`, `indeterminate`, `infrastructure`) or one that is excluded (`stack-stop`, `load-stack-stop`, `contradicted-claim`, `implementation-chosen-hook`, `short-circuit-reading`, `allowance-refusal`, `equals-condition`, `implementation-chosen-value`, `unsupported-hook`). `slots` is below. `cause` is null when the outcome is `agree` or `distinguish`, else what the runner's evidence says stopped the comparison, per slot (`exit-stop, whole-term: ...`), with the budget values, followed by the mutant run's leaf census for a time limit (`; when the bound fired k-rust returned ...`) or an unknown or timed-out slot (`; the mutant's run: k-rust returned 1 leaf (depth-bound 1), the deepest at depth 200`), which tells a depth bound from an undecided end. `wall_ms` is the mutant's run of the program, `baseline_ms` the program's live baseline run in this command and `baseline_reused` whether this call reused it; all three are null on a cached entry, whose `cause` (an `unknown`'s), `smt_unknowns` and `decider_smt_unknowns` are the record's, as the live entry that wrote it gave them (version 24, CF-33d). |
| `calls` | `{programs, status}` of each runner call: `[]` when tier 1 decided, `[[k]]` when the recorded killer k killed alone, `[[k], [rest]]` when it did not, `[[rest]]` without a recorded killer to run; under `--full`, `[]` or `[[the programs with no cached outcome]]`. |
| `call_wall_ms` | The wall time of each call of `calls`, in the same order (the mutant's compile and every run of the call). |
| `rules` | Null for a `killed` mutation and for an `invalid-mutation`; otherwise each edited rule, in sentence order: `{module, index, file, label, start_line, end_line, edits, before, after}`. `before` and `after` are the rule's K text before and after the mutation's edits, sliced from the file's K view by the sentence's span (`after` is null for a deleted rule); `edits` are the indices of the mutation's edits addressed to the rule. |
| `action` | Null for `killed`; otherwise one sentence saying what the status asks (write a program, fix the mutation, fix the corpus, report it); `nothing: it survived, as its expectation states` for the `survived` row of a met control whose survival rests on no `horizon` and no `stop_hides_edit`. |

`slots` is an object keyed by oracle slot, `exit-stop` and `whole-term` (or `cells`, which has the shape of `whole-term`), each `{outcome}` (`agree`, `distinguish`, `timeout`, `unknown`, `incomparable`, `error`).
A distinguishing slot also has `sides`: for `exit-stop`, each side's exit-stop kinds, for example `{"baseline": ["normal"], "mutant": []}`
(the flow's classifier makes every ended run `normal`; an undefined step, a rule whose result is undefined such as a division by zero, is no end and has no kind, so a side whose every path takes one has `[]`, as has a mutant whose start is decided to have no value (`check`, above), and an undefined path beside the same ends changes no kind);
for `whole-term`, each side's number of final configurations, `{"baseline": {"final_configurations": 1}, "mutant": {"final_configurations": 1, "kore": [{"text", "truncated"}]}}`
(an undefined step's outcome is no configuration, so the configuration it is taken from is no final configuration, and a side whose every path takes one has `final_configurations: 0`; kink's `trust.md`, "What a kill trusts"),
where `kore`, on the killing program's entry only, holds the mutant's final configurations as KORE text, each cut to 4000 characters (`truncated: true` when cut).
A cached entry has no run at hand, and a one-sided kill (the mutant's run reached its work budget, `budget.work_factor`) has a mutant side that is `unknown`, not a value: since version 12 their distinguishing slot's `sides` are read from the entry's `difference`, in the same shape (each side's count and classes of the ends the difference compared; from a front end's evidence, each side's count of ends, and no `exit-stop` sides, which such evidence never accompanies), with `complete: false` on the `whole-term` mutant side (`mutant_complete: false` on `exit-stop`) for a one-sided kill, whose mutant ends are its run's one-sided ends (below).
No timing, census or side value enters an evidence row, a digest, a key or the killer record; the difference enters only its `killed` outcome record.

#### Kill evidence

A distinguishing program's `difference` (CF-16) says where the two sides' ends differ.
Its `format` names its shape: kink's own evidence, below, is `kink-k/1`, with cells by K label and values as K text;
a front end that reads the definition's ends at its own level renders the evidence in its format instead (next paragraph).
kink's own evidence is `{format, outside, path, baseline, mutant}`, each side `{final_configurations, complete, classes, end, value}`.
It compares the second slot's sets of ends: each side's final configurations with the `<generatedCounter>` content erased, and under `cells` each cell left out replaced by `\top` of its sort, so no difference it shows lies in a cell left out.
For a one-sided kill (`complete: false`) the mutant's set is its run's one-sided ends: the clean, ground, stuck ends of explored complete paths that the one-sided rule reads (kink-campaign `TestEvidence::one_sided_ends`).
The slot distinguishes one-sidedly exactly when one of them, erased, is outside the baseline's set, so the mutant end the difference shows is one that killed; every completion of that run has it among its ends.
The run's other explored ends are not compared.
The pair of ends is chosen deterministically:
when some mutant end is not in the baseline's set, the first such end (in the sets' term order) and its nearest baseline end (`outside: "mutant"`);
otherwise, for a complete mutant side, the first baseline end the mutant's set lacks and its nearest mutant end (`outside: "baseline"`).
The nearest end is the one with the least cell distance (the number of leaf cells and concrete-map entries in which two configurations differ), the first in term order among equals.
`path` is the first differing cell path from the top: the labels of the cells both ends hold, entering at each cell the first child in which they differ while it is the same cell on both sides,
then, while both values are concrete maps or both are concrete lists, `[key]` for the first key (in term order) whose entry differs, or `[i]` for the first index (from 0) whose element differs.
Each side's `value` is its content at the path (null for a map key that side lacks, or a list index past its end), `end` its end's `{head, class}` (as in a program's `ends`), `final_configurations` the size of its set and `classes` the classes of its ends.
When a side has no end (every path an undefined step, or a mutant with no start), its `end` and `value` are null, and the `path` is null too.
A value is one line of K text printed by krs-unparse as `krs run` prints a configuration, aliases not reversed and maps sorted (`rendering: "k"`), or KORE text when the printer warns or the term has more than 100,000 nodes (`rendering: "kore"`, the reason in `note`); each is cut to 2000 characters (a head or map key to 200), and `truncated` says whether it was.
The two values are cut around their first differing character, so the two texts shown differ: when they first differ at least 1000 characters in and one is longer than 2000, both show the 2000 characters from 1000 before that difference, and each value's `offset` is the number of characters cut before its `text` (0 otherwise).

A front end sets a renderer of kill evidence on the manifest (the library's `FlowManifest::with_end_renderer`), and the evidence of each kill is then the renderer's document in the renderer's format.
`krs kink` renders it with krs-exec's comparison of ends, `krs-difference/3`, the format in which KRS shows every difference of two ends: the differing cell by Rust field path (`cell`, `path`, `segments`), the other differing cells (`also_differ`), the compared cells, and each side (`left`, the baseline, and `right`, the mutant: `{name, ends, complete, value}`) with its value as its canonical document, or as K text where the value has none.
The renderer is given what kink's own evidence compares: both sets of projected ends, whether the mutant's is complete, and the cells left out, which hold `\top` there and so state nothing.
It chooses its pair of ends by its own order under the rule above: an end outside the other set, the mutant's first, and its nearest end in that set.
The slot compares ends by their configuration alone, whichever way a path reached them, so `krs kink`'s evidence compares no class and its sides state none (krs-exec's comparison is given each end with one class, `stuck`, which the document leaves out); under `[stop]`, each end of a program row says how the baseline's paths reached it (`halt`).
The renderer judges no kill.
Where it shows no difference, kink gives its own evidence with `note` saying why (`no krs-difference/3 evidence: ...`): a difference only in a cell the front end does not declare, an end it cannot read, or a definition it cannot compile; so a kill never loses its evidence.
A side with no end has no end a front end could show, so its evidence is kink's own, without a note.
The renderer writes kill evidence only: a program row's `ends` stay kink's K text heads under a front end too, a bounded listing for orientation, where a front end's document of an end is the whole end.
`FLOW.toml` names no renderer: under `kink-flow` the evidence is always kink's own.

A row may also carry `cache_error`.
The cause of an `unknown` slot names the possible reasons together (a path stopped at `max_depth`, an undecided end,
or a final configuration holding a collection kink cannot compare (for example one holding a `Float`), an unevaluated function or a symbolic term),
because the runner's evidence records that the mutant's value is unknown but not which of these stopped it; the leaf census that follows
(leaves per halt class: `depth-bound`, `stuck`, `indeterminate`, ...) usually says which.
A mutant's run whose end holds an application of a function whose equations the mutation edits (deletes, replaces, or edits a term or attribute of), which no equation of the mutant reduces, names the leaf's halt and depth and that application with its arguments, as K text (`its stuck leaf at depth 0 holds plus ( s(zero) , zero ), an application of the function plus, ...`): the mutant leaves its value open there (kink27 R5-WEAKENING). A cause that names such an application leads with it, and a slot the mutant's run left undecided then says only that it did not end in a value kink can compare, before the census of the run's leaves, rather than listing every way a run can end short of a value. The leaves read are the final ones whose states k-rust normalised: stuck, indeterminate, a stop's, and an undefined step's (`trivial`, its pre-step state); k-rust's states are normal forms, so an application left in any of them is one no equation reduces, and a stuck leaf holds it as surely as an indeterminate one. A stuck, indeterminate or stop leaf's state is then no value, and an undefined step's pre-step configuration is not shown to exist, which its path needs to be complete. A depth-bound, breadth-bound or work-bound leaf is not read: it is no end, or its state was never normalised. A program is undecided by such applications when every leaf of the mutant's run whose path the bridge left incomplete (kink-campaign `RunNotes::incomplete_leaves`) holds one in its state or in its path condition (kink-native `open_symbols`): in the state it makes the end no value, or keeps an undefined step's configuration from being shown to exist, and in the path condition it leaves open whether the leaf has an instance (an undefined step whose rule's result is undefined where the function's value is), so that leaf's path is incomplete by it, and an incomplete path makes every state slot undecided before any end is read; a leaf incomplete for another reason that holds none (a depth bound beside a stuck leaf, for example) keeps the program undecided by itself, so its cause can name the application while the program is not undecided by it. When every program the mutant left undecided is undecided by such applications, live or from the outcome cache (an `unknown` record keeps the fact as `open_application`), the row's reason is `open-application`. The clause names only an application of an edited function found in the state: an application of any other function is unreduced for a reason the edit does not name (it may be irreducible in the baseline as well), and the clause is absent when the open value is only read by a rule's condition (`requires p(I)`), since no state holds it.
One case has its own cause (fz26 KINK-CAUSE-SUBTERM): a slot the runner made unknown for the pair because one side's end, which is a value of
its own definition, is not data under the other side's definition (kink-campaign `judge_across`, recorded in the mutant's evidence as
`RunNotes::across`). The cause names that side (`the baseline's run ended in a value of its own definition, but that end is not data under
the mutant's definition ...`; for a pattern slot, a binding not definition-independent under the mutant's definition, or a term its relation
decisions read not definition-independent under the other side's; a state value without ends to judge is said so), and the first node of
the end, in pre-order, that fails its own test there, as a refused baseline's cause names it (see `coverage`); no leaf census follows it.

## The corpus record: `--lock FILE`

`run --lock FILE`, `coverage --lock FILE`, `compare --lock FILE` and `query --lock FILE` name the corpus record, conventionally `kink.lock`: one file, one section per command.
`[run]` is the killer record, one recorded killer per killed mutation, kept while it still kills; `[coverage]` is the coverage lock, one recorded killer per distinguished flip by the same rule, with each family's open and argued obligations; `[compare]` holds the verdicts of the corpus's other implementations, one per implementation, program and view ("Comparing implementations"); `[query]` holds each pattern's obligation, with one recorded witness per hit, kept while it still hits ("Checking a pattern").
kink-flow has no default path, since one corpus is routinely run with several mutation lists, whose rows would overwrite each other in one section; the krs front end gives `<corpus>/kink.lock` to a run of the corpus's own mutation list, to a query of its own pattern list, to `coverage` and to `compare`, unless the command names a lock.
The name is the tool's, as `Cargo.lock` is Cargo's: the file holds every command's section, so it is named for none of them, and a new name lets a front end tell the two files an earlier kink kept apart ("Old files" below).
A library run (`RunOptions::default()`, `fuzz`'s confirmation) has no lock and writes nothing outside the cache.

```toml
# kink's verdicts of a corpus, one section per command: [run] (`run` on a mutation list),
# [coverage] (`coverage`), [compare] (`compare`) and [query] (`query` on a pattern list). As a
# lock (`--lock FILE`; krs keeps <corpus>/kink.lock), each command reads, checks (--locked) and
# rewrites only its own section, and keeps the others as they are.
schema = "kink-flow-verdicts"
definition = "story-plus:main"   # a KRS flow's record; a K flow's has no such line

[run]
# The verdicts of kink's `run` command (`krs kink run`, `kink-flow run`): the next run tries
# each `killer` first, a run without --locked rewrites this section, and `run --locked` checks
# that it is current.
version = 29
profile = "z3"
z3_version = "5.3.3.0 430d19e697e2ec9bad79ff210d41b4a7a5fcfa3e 430d19e"
z3_library_sha256 = "7ca2ea1f27e40c86269d6ff7f0e82293708253cb05dbec094c90b08c4ec04d31"
work_factor = 5

[run.spec]
outcome = "admitted"

# Each [[run.mutation]] is a mutation of the list, by its id, and its verdict: killed (a
# ...
[[run.mutation]]
id = "add-becomes-sub"
status = "killed"
killer = "add"

[[run.mutation]]
id = "add-swaps-operands"
status = "survived"

[coverage]
# The verdicts of kink's `coverage` command (`krs kink coverage`, `kink-flow coverage`): the
# ...
version = 29
profile = "z3"
z3_version = "5.3.3.0 430d19e697e2ec9bad79ff210d41b4a7a5fcfa3e 430d19e"
z3_library_sha256 = "7ca2ea1f27e40c86269d6ff7f0e82293708253cb05dbec094c90b08c4ec04d31"
krs_annotation = 10

[coverage.spec]
outcome = "admitted"

[coverage.settings]
depth = 1
mcdc = [
]
work_factor = 5

# Each family lists its obligations by id: `open`, those no program covers; `argued`, those an
# ...
[coverage.rules]
open = [
]
argued = [
  { id = "rule:crate::wake", standing = "checked-on-runs" },
]

# Each [[coverage.flip]] is a condition flip: a mutant kink generates from the definition by
# ...
[coverage.flips]
run = true

[[coverage.flip]]
id = "flip--latch_1+latch_2--IntEqual"
negates = "self.a == self.b"     # the condition, as the source writes it; `toggles` for a bit of an encoding
rules = [                        # the rules the mutant edits, by their ids in the rules family
  "rule:crate::latch_1",
  "rule:crate::latch_2",
]
status = "distinguished"
killer = "irq"

[compare]
# The verdicts of kink's `compare` command (`krs kink compare`, `kink-flow compare`): a run
# ...
version = 29
profile = "z3"
z3_version = "5.3.3.0 430d19e697e2ec9bad79ff210d41b4a7a5fcfa3e 430d19e"
z3_library_sha256 = "7ca2ea1f27e40c86269d6ff7f0e82293708253cb05dbec094c90b08c4ec04d31"
protocols = ["kink-implementation/1", "kink-implementation/2"]

[compare.spec]
outcome = "admitted"

# Each [[compare.verdict]] is one view of one implementation on one program, and its verdict:
# ...
[[compare.verdict]]
implementation = "rust-cpu"
program = "cases/irq/case.toml"
view = "writes"
required = true
verdict = "equal"
request_sha256 = "039fbda42c342c04bea68bb18bca5a85541bbac54f92c7310939a7c9d4430314"
identity_sha256 = "5d1e…"

[[compare.verdict]]
implementation = "rust-cpu"
program = "cases/irq/case.toml"
view = "accesses"
required = false
verdict = "different"
difference = '{"at":"cell","cell":"bus","format":"krs-difference/3",…}'
request_sha256 = "039fbda42c342c04bea68bb18bca5a85541bbac54f92c7310939a7c9d4430314"
identity_sha256 = "5d1e…"

[[compare.verdict]]
implementation = "rust-cpu-traced"
program = "cases/loop/case.toml"
view = "boundary"
required = true
verdict = "agree-up-to"
horizon = '{"boundary":{"definition":"bound","elements":4096,"implementation":"the requested positions","limited_by":"definition"}}'
request_sha256 = "77c1…"
identity_sha256 = "5d1e…"

[query]
# The obligations of kink's `query` command (`krs kink query`, `kink-flow query`): the next
# ...
version = 29
profile = "z3"
z3_version = "5.3.3.0 430d19e697e2ec9bad79ff210d41b4a7a5fcfa3e 430d19e"
z3_library_sha256 = "7ca2ea1f27e40c86269d6ff7f0e82293708253cb05dbec094c90b08c4ec04d31"

[query.spec]
outcome = "admitted"

# Each [[query.pattern]] is a pattern of the list, by its id, and its obligation, that some
# ...
[[query.pattern]]
id = "result-above-five"
status = "hit"
witness = "nested"

[[query.pattern]]
id = "result-hundred"
status = "open"
```

The comments say what the file is to a reader who has not read this README: the first what the record is and who writes each section, the one after each section's line which command keeps it and what it does with it, and the one before a section's rows and families what each entry, list and status word is.
Each is a constant of the rendering's version, so it moves no line between runs.

**What a section is.** A section is the lines from its `[run]`, `[coverage]`, `[compare]` or `[query]` line to the next such line or the end of the file, trailing blank lines aside: the command's verdicts rendering after the record's header ("Verdicts"; `kink_flow::verdicts::lock_section`), its tables under the command's (`[run.spec]`, `[[run.mutation]]`, `[coverage.rules]`, `[[coverage.flip]]`, `[[compare.verdict]]`, `[[query.pattern]]`).
The record writes them in that order.
So a record only one command has written is that command's `--output verdicts` (for `run`, without `killed_by`), and the record is the format of recorded outputs too.

**Ownership.** Each command reads only its own section, compares only its own under `--locked`, and rewrites only its own, keeping the other sections' text byte for byte, a hand comment in them included.
So `coverage --locked` is unaffected by a stale `[run]`, and the reverse.
A file with no section for a command records nothing for it: a first `coverage` after only `run`s is no error, and its section is `created`.

**The header.** The header, before the first section, holds only what is the same for every section by construction: the comment that says what the file is, and `schema`.
Every value a verdict depends on is in each section: the rendering's `version`, the solver `profile`, the Z3 build (`z3_version`, `z3_library_sha256`), `krs_annotation` and the specification's admission (`[run.spec]`, `[coverage.spec]`).
They could be said once only if both sections were always written together, on one build; they are not.
Each command writes its section at its own time, on the build it runs on, and keeps the other as it is, so a value said once would be wrong for the section the last command did not write.
And under `--locked` a `run` on another Z3 build would move the shared line, so `coverage --locked` would be stale for a change no `coverage` made, which ownership rules out.
Each command checks the values its own section states, against its own run: two sections that agree state them twice, which is the price of each staying true of the command that wrote it.

A front end may name the definition's functions that are total on its author's word, without a check (krs: `#[k::function(total, assumed = "..")]`, `FlowManifest::with_assumed_totals`).
A backend takes an application of a total function to have a value, so every verdict of a section may rest on each, as it rests on the definition: the section states them in a table `[<command>.assumed_totals]` after its header tables and before its rows, one `"<symbol>" = "<reason>"` line per function, the symbol its K name and the reason as written.
A change of the list is then a change of the section, as a change of the definition's verdicts is: `--locked` finds the section stale (its header differs) and a command without it rewrites it.
A definition with none writes no such table, so its section is the one it was.
The list is the record's alone, for this invalidation: the verdicts rendering (`--output verdicts`) never holds it, no document prints it, a header change does not name it, and the lock's `difference` names a change of it by its line only (`{kind: "assumed_totals", line}`).

**Writing.** A command writes its section by a read-modify-write under an exclusive lock of the file's directory (`flock` on the directory, `std::fs::File::lock`): it reads the file again, keeps the other sections' text as the file now holds it, writes the record's header and every section to a temporary name in the directory, flushes it and renames it over the file, then releases the lock.
Two commands that write at once each find the other's section in the file they rewrite, so neither loses it, and a reader never sees a part-written file (`lock.rs`, `concurrent_writes_of_the_two_sections_lose_neither`).
A file that no longer decodes as a record the command may write is not overwritten (`lock.status` `not-written`, `reason` `write-failed`).
The record is created when absent, as `Cargo.lock` is: it holds the killers the next run starts from, and a run that discarded them would repeat the search.

**What it is.** The record is an input: a command reads one fact from its section, for each mutation (or flip) id the program id it names as killer, which the search tries first ("`kink-flow run`", step 5; a flip's mutant is run by `run`'s kill search under the flip's id).
Every status still comes from runs or cached outcomes; no status, cell or key is read from the record, so a hand-edited or stale record can change which program is tried first, and so the cost and the reported killer, but never a status (kink's `trust.md`).
It is also an output: after a complete run the command's section is rewritten, so it states the verdicts of the current inputs.

**The killer rule.** Let k be the section's killer of a mutation and C the search order (step 3: the witnessing programs first, then the rest, each in `FLOW.toml`'s order).
1. If k names a program of O and k kills the mutant (a cached kill, or its live run distinguishes), the killer is k.
2. Otherwise, if the status is `killed`, the killer is the first program in C that kills.
3. Otherwise there is no killer.

The row says which held: `recorded_killer` and `killer_change` ("The report"); a flip decided with no run, `unreached` or `refused`, keeps no killer, and a killer recorded for it is `not-run`.
C is the search's order, not bare `FLOW.toml` order: the search already runs the witnesses first, and bare corpus order would make the canonical search run programs that never reached an edited rule before the first one that did.
Both are functions of the inputs: the witness set is computed from the compiled edit and the result records' coverage, keyed facts, by the one predicate the live call and tier 1 share; when an edit is not site-local, C is exactly `FLOW.toml`'s order.
So each killer is a function of the section before the run, the corpus, the definition, the mutation list, the budget, the solver profile and kink's build, never of the cache, the host's clock (a killer a stopped run could change is kept as recorded: "What decides a verdict") or the order work was done in: a cold run, a warm run, any `--compile-workers` and `--no-memo` give the same killer and the same section bytes.
Rule 1 reads k's outcome, which is the same live or cached under a key that names every input; rule 2 reads the outcomes of the programs of C up to the first kill, each independent of the other programs of its call (step 3).
A recorded killer that times out is not replaced: its kill is not proved, and neither is its absence, so the row's `killer_change` is `clock-stopped` while the section keeps the recorded entry, unverified ("What decides a verdict"); so does a recorded killer whose baseline the clock stopped.
First-kill and `--full` write the same section: their statuses are equal ("The full matrix"), and both choose k when k's cell is a kill, else the first kill in C, from the same per-program outcomes.

**The `[run]` section.** There is one `killer` per `killed` mutation and none on any other status, in the list's order.
It has no `killed_by` (a full run must write the first-kill run's section), no program digest (a renamed case is a corpus edit the diff should show) and no `schedule` (its content does not depend on it).
`run` writes it when a lock is in use, the run is in search mode, it judged every mutation of the list (no `--only`, no corpus error stopped it, the specification was admitted) and `--locked` is not given; the run document's `lock.status` is `created`, `written` or `unchanged`.
Otherwise it is left as it was (`not-written`, with `reason` `only`, `verify`, `stopped`, `refused` or `write-failed`): a partial write under `--only` would mix rows judged against the current inputs with rows that were not.
`--only` and `--verify` still read it, so the recorded killers are tried first.
A run whose manifest or mutation list does not decode reads no lock and leaves it unwritten (`lock.reason` `refused`).
An interrupted run loses no work: the outcomes cached after each mutation make the next run's canonical decisions cheap and reproducible.

**The `[coverage]` section.** It gives each family's open and argued obligations, each argued one with the standing its argument rests on (`{ id, standing }`), and each flip with what it changes, its status, a refused flip's reason, a distinguished flip's killer and an argued flip's standing.
A flip is a mutant kink generates, not one a mutation list states: its id is the front end's (`flip--<rules>--<atom>`, `bitflip--<rules>--bit<k>`, more than three rules written as the first and the number of the others), which keys its recorded killer and the `[[coverage.argued]]` entry that argues it, so it stays as it is; `negates` (or `toggles`) and `rules` resolve it without the coverage document, and are functions of the definition, as the id is.
It moves only when an obligation opens or closes, an argument is added or removed or its standing moves, a flip's status moves or its killer stops killing, or the definition's text of a flipped condition changes; a case that covers nothing new leaves it as it is.
Each family's `open`, `argued` and `undecided` list one entry per line ("Verdicts"), so a case that closes obligations removes exactly their lines from the diff, and an argument added moves one line from `open` to `argued`.
The argued ids belong in it: an argued obligation leaves the open ones with no program covering it, and a section that listed only the open ones would record that change as a gap a program closed.
The standings belong in it too, each beside its id, so that an argued item is named in one place: a section that did not record them would show an argument resting on its text alone the same as one a check decided, and a lost check would move no line.
It has no `[coverage.settings] tiers`: the section is written only after a run of both tiers, and `[coverage.flips] run` says whether the flips ran.
`coverage` writes it (atomically, as above) after a run with the manifest's own settings that judged every flip: both tiers, the manifest's depth, an admitted specification, and no corpus error that stopped the search.
Otherwise it is left as it was (`not-written`, with `reason` `tier-1`, `depth`, `verify`, `stopped`, `refused` or `write-failed`): a run of other settings computes another document, which the section does not describe; those runs still read it, so the recorded killers are tried first.
A front end that derives no flips (kink-flow's own) has a complete run without them: its section lists the families' open obligations and `[coverage.flips] run = false`.
`--locked` asks whether a run with the manifest's own settings writes the committed section, so it is a usage error beside `--tier 1` or `--depth`, which run other settings.

**The `[compare]` section.** Its header names, besides the version, the profile and the Z3 build (the definition's ends are a function of the solver as every baseline is), the `protocols` its implementations' requests were written in and their answers read by (`protocols = [..]`, each once); a row's request digest names its implementation's too, since the request carries it.
It has one `[[compare.verdict]]` per (implementation, program, view) that has a verdict, keyed by its `implementation`, `program` and `view` (no `id`, since none of the three alone names the row), implementation by implementation in the manifest's order, each implementation's programs in the corpus's order and each program's views in the declaration's, so that a diff of one implementation's change is contiguous.
Each row holds `required`, the `verdict`, its `reason` (a `not-compared` verdict's reason, a `could-not-apply` verdict's own, the implementation's words), a `different` verdict's first `difference` (the document's, as canonical JSON in a literal string: a text that is a function of the difference), `request_sha256` and, where the implementation declares `identity`, `identity_sha256`: the request and the build the verdict was measured on, so a request or a build that moves shows in the diff beside any verdict that moved with it.
A failed run of an implementation has no verdict and so no row ("Comparing implementations").
`compare` writes it after a run of every implementation of the manifest whose specification was admitted and that no refusal stopped; under `--only`, which judges some of them, it is left as it was (`not-written`, reason `only`; `refused` and `write-failed` as for the other sections), so a section never mixes rows judged against the current inputs with rows that were not.
A row whose verdict rests on a run that gave no answer keeps its recorded value, in the section compared and in the section written: the implementation's run when it failed or the clock (`time_ms`) cancelled it, and the definition's baseline or depth-0 run when the clock (`budget.time_ms`) stopped it, which a faster host could have ended with any end ("What decides a verdict").
Every row of that (implementation, program) is kept, as recorded; where the lock records none, a failed run writes none and a stopped definition run writes the run's own `not-compared` rows.
`lock.clock_stopped` names each stopped run (`{program, run: "baseline"}`, `{implementation, program, run: "start" | "implementation"}`), `lock.failed` each failed run of an implementation (`{implementation, program, failure}`), and `lock.kept` each kept row the host gave another verdict (`{implementation, program, view, recorded, now}`, each side `{verdict, reason, difference}`).
Under `--locked` a section that differs in nothing else is `undecided`, exit 3, and never a difference.

**The `[query]` section.** It has one `[[query.pattern]]` per pattern of the list, in the list's order: its `id`, its `status` (`hit`, `open` or `undecided`) and, for a hit, its `witness`, the program the next query asks first ("The obligation and its witness").
It states a fact of the corpus and carries no pattern digest and no claim: a pattern's `programs` and `expect` are checked on every query and enter no lock, and the witness is asked again on every query, as a recorded killer is run again.
`query` writes it after a query of the whole list whose specification was admitted, without `--locked`; under `--only` or `--verify`, or when the pattern list or the specification is refused, it is left as it was (`not-written`, with `reason` `only`, `verify` or `refused`; `write-failed` as for the other sections).
An obligation whose value rests on a search or a baseline run the clock stopped keeps its recorded value, by the clock's rule for kills: a hit by the recorded witness rests on nothing else; another hit rests on each search the clock stopped of the recorded witness or of a program before the witness in corpus order (it could have hit); `undecided` rests on each run the clock stopped (a search could have hit, a baseline could have licensed a `no`); `open` rests on none.
The recorded value is not kept where the query decided a fact it contradicts: a hit where the lock records none, a recorded witness that is no program of the corpus, a status no query gives.
`lock.clock_stopped` names each such run (`{pattern, program, run: "search" | "baseline"}`) and `lock.kept` each kept entry this host gave another value (`{pattern, recorded, now}`, each side `{status, witness}`); under `--locked` a section that differs in nothing else is `undecided`, exit 3.
`--locked` prints one line per change: `kink.lock: above-five: witness B -> C (B: not-in-corpus)`, `kink.lock: result-hundred: open -> hit`, `kink.lock: p: added, open`.

**The definition.** The header of the record of a flow that names its definition (`[spec] krs`) states it: `definition = "PACKAGE:FACET"`.
Every section is a function of that definition, so the name is the same for every section by construction, and it is in the header, not in a section.
A command whose flow is for another definition than the one the file names is refused before anything runs, with or without `--locked` (`lock.outcome` `refused`, exit 2): its rows would replace that definition's, and the file's killers are those of another specification.
So is a command of a K flow on a record that names a definition.
A record that names none is read: it is a K flow's, or one written before version 28, whose header a command without `--locked` rewrites with the name.
`prune`, which writes no record, refuses the record of another definition as well.

**Reading.** Reading tolerates any version: `schema` must be `kink-flow-verdicts`; the command's section, where there is one, must be a table and begin with its own `[run]`, `[coverage]`, `[compare]` or `[query]` line; each row (`[[run.mutation]]`, `[[coverage.flip]]`) must have a string `id` and may have a string `killer`, and each `[[query.pattern]]` a string `id` and may have a string `witness`; and nothing else decides anything (a row's `status` and `reason`, a family's `open` and `argued` and the standings are read only to report what changed).
A version-5 lock has no `killer` lines, so it records no killer.

**`--locked`.** With `--locked` the command leaves the file unwritten (the cache is written as in any run) and compares the section it would write with the file's (under `run --only`, the selected rows and the section's header), and the record's header with the one a write gives; a file with no section for the command counts as different, as Cargo's `--locked` counts an absent file.
A difference is a finding, exit 1 (`lock.status` `stale`), as a `--verify` mismatch is: a lock is a stored record, and the command had to be asked to know the live value, so this is not the refusal (2) that comes before anything is asked.
An entry of the section (a row, an obligation, a standing) whose recorded value a run the clock stopped could have given is no difference: it is kept, in the section compared and in the section written, and `lock.status` is `undecided`, exit 3, where nothing else differs (`lock.kept`, `lock.clock_stopped`; "What decides a verdict").
Only the command's own section is kept so; the other section is neither compared nor written.
No separate check command exists: answering it is a run, and `--locked` is that run.
`kink-flow` prints one line per change on stderr: `kink.lock: add-becomes-sub: killer nested -> add (nested: not-in-corpus)`, `kink.lock: add-swaps-operands: killed -> survived`, `kink.lock: flip--b: unreached -> distinguished`, `kink.lock: rules: rule:x is open`, `kink.lock: requirements: requirement:x:held is no longer open`, `kink.lock: rules: rule:y is argued (was open)`, `kink.lock: rule:z: standing text -> unchecked` (a standing that moved, where no other line names its item), and one line per section header key that differs, `` kink.lock: [run] z3_library_sha256 differs: recorded "7ca2…", now "1f0e…" (another Z3 build) ``, or one line when the header differs in no value (the file has no section of the command, or the record's header, or a comment or spacing before the first row or family, differs).
`lock.changes` lists each row whose `(status, killer, reason)` differs, `{mutation, recorded, now}` (`{flip, ...}` for a flip; for a compare row `{implementation, program, view, recorded, now}`, each side `{verdict, reason, difference}`, so a reported view whose first difference moved is a change; either side null for a row only the other has); `lock.open_changes` each obligation whose state differs, `{family, obligation, recorded, now}` (`"open"`, `"argued"`, or null where that side lists it neither way); `lock.argument_changes` each argued item whose standing differs, `{obligation, recorded, now}` (null where that side has none).
`lock.header` says whether the record's header or the section's lines before its first row or family differ; `lock.header_changes` names each section header key whose value differs, `{key, recorded, now}` (a sub-table's key as `spec.outcome`; either side null where that side has no such key), in the section's line order and then the keys only the file has; it is empty when the file records nothing for the command or only a comment or spacing differs.
`lock.difference` names where the file's section first differs from the one the command would write, `{kind, line, recorded, now}` (`line` counted from 1 in the file), null when they are equal, when the file has no section of the command, or under `--only`.
`kind` is `order` when the section holds the same rows in another order: `line` is then the file's line of the `id` of its first row out of the rendering's order, `recorded` that line and `now` the `id` line of the row the rendering puts there, whatever comment or spacing differs before it, since the order is what a run changes.
`kind` is `text` otherwise: `line` is the first line in which the two differ, and `recorded` and `now` each side's text of that line, null past its end.
A section that differs neither in its header nor in a row's verdict (rows in another order, a comment, spacing, a key the rendering does not write) is still stale, and `kink-flow` prints that first difference on stderr: `` kink.lock: its rows are in another order than the mutation list's (first at line 9: recorded `id = "b"`, now `id = "a"`); a run writes them in the list's order ``.

**A record that does not decode.** The record is read after the manifest (and a run's list) decode, before admission.
One that is not TOML (merge-conflict markers included), has another schema, has a section of the command that is no table or does not begin with its own line, repeats an id or has a `killer` that is not a string refuses the command: exit 2, no row or family, `lock: {path, outcome: "refused", detail}`, and in the rendering a `[run.lock]` or `[coverage.lock]` table with `outcome = "refused"`.
The next step is to resolve the file, or delete it to start from the search's killers; a run then regenerates it.

**Other versions.** Under `--locked` a section of another version (its `version` is not this build's, or absent) is refused before admission, exit 2, with the detail `kink.lock: its [run] section is recorded at version 25 of the verdicts rendering, and this build writes version 26, so --locked cannot find it current; run `krs kink run --package p --definition main` without --locked once to rewrite it, and review its diff` (the command as the front end spells it).
Another version writes other bytes for the same verdicts, so the comparison could only find it stale, after a whole run; a run without `--locked` reads its killers and rewrites its section, and the diff shows what the new version changed beside any moved verdict.

**Old files.** Before version 24 each command kept its own file, the command's rendering at its top (`document = "run"` or `"coverage"`, the rows `[[mutation]]` or `[[flip]]`, the standings under `[arguments]`), which the krs front end named `<corpus>/verdicts.lock` and `<corpus>/coverage.lock`.
A file of that layout given as `--lock FILE` is read as the section of the command it names: a command without `--locked` keeps its killers and rewrites the file in the current layout, which then holds that command's section alone, as the old file held nothing else; under `--locked` it is refused as a section of another version is.
A file of the other command's is refused, since writing it would lose that command's record.
A front end that kept the two files names the old one beside the record (`FlowCommand::set_legacy_lock`; the krs front end does for a command that keeps `<corpus>/kink.lock` by default, while the old file is there).
While the record has no section for the command, the command reads the old file's recorded facts (killers, statuses, obligations, the section header), so a migration loses no killer, and its write moves them into the record; `lock.legacy` is `{path, status: "migrated", moved}`, and stderr says `kink/verdicts.lock: its killers are now in kink/kink.lock's [run] section; delete kink/verdicts.lock`.
Once the record has the section, the old file is `superseded`, and stderr says to delete it.
Under `--locked` the command is refused while the old file is there, since the committed record is not the file the check would compare: `kink/verdicts.lock: it is a lock written before version 24, which kink/kink.lock replaces with one [run] section per command, so --locked cannot find the corpus's lock current; run `krs kink run ...` without --locked once to move its killers into kink/kink.lock, then delete kink/verdicts.lock`, and, once the record has the section, `... whose verdicts kink/kink.lock's [run] section now keeps; delete kink/verdicts.lock`.
kink-flow deletes no file.

**Profiles and Z3 builds.** Each section names the `profile`; a section written under one profile is read under the other only as killers to try.
A killer that kills under Z3 and is undecided without it is `no-longer-kills`: the search finds another killer or the status moves to `unknown`, and the rewritten section shows `profile` and the moved rows (under `--locked`, a finding).
Under Z3 an outcome is also a function of the Z3 build, since whether a resource-bounded query is decided depends on the machine code that counts its units, so under the Z3 profile each section also names the build (`z3_version`, `z3_library_sha256`; "Verdicts").
A section recorded on another Z3 build is read like one of another profile: its killers are tried first, and a killer the build no longer proves is `no-longer-kills`, which the row's `killer_change` and the rewritten section header both show.
Under `--locked` such a section is stale even when every row agrees (exit 1, its `header_changes` naming the build lines).
The solver build is part of the instrument a section was measured with, as the profile is, and `--locked` asks whether this run, on this instrument, writes the committed section.
A run on another build cannot confirm that, since rows that agree on the current corpus do not make two builds interchangeable for the next edit.
Passing it would leave the repository's record naming a build no check ran on, and a row that later moves would be blamed on the corpus while the header misnamed the solver.
When every row agrees the fix is a header-only rewrite, a run without `--locked`, which review sees as exactly that; a project whose CI links another Z3 build than its developers do records the sections on the CI's build.

A corpus commits `kink.lock`, and a CI runs `run --locked` and `coverage --locked` (`krs kink run --locked`, `krs kink coverage --locked`), `compare --locked` where it declares an `[[implementation]]` (`krs kink compare --locked`), and `query --locked` where it has a pattern list (`krs kink query --locked`).

## Verdicts: `--output verdicts`

`coverage`, `run` and `compare` print, with `--output verdicts`, a TOML rendering of their document instead of the JSON, with the same exit status; `report --output verdicts` renders the stored run document.
It holds what the specification, the corpus and the budget decide and nothing that depends on the host, kink's own build identity, the cache or the order the work was done in (it names the solver: the build's solver profile and, under Z3, the Z3 build, below),
so an unchanged corpus renders the same bytes on a cold and on a warm cache.
It is the record's header and the command's section ("The corpus record"): the format of recorded outputs and, without `killed_by`, of the section `run --lock` writes, and of the one `coverage --lock` writes, so that a moved verdict shows in review; a record only one command has written is that command's rendering.

```toml
# kink's verdicts of a corpus, one section per command: [run] (`run` on a mutation list),
# ...                         (the record's comment)
schema = "kink-flow-verdicts"
definition = "story-plus:main"   # the definition a KRS flow names; no line for a K flow

[coverage]                    # or [run]: the command's section
# The verdicts of kink's `coverage` command (`krs kink coverage`, `kink-flow coverage`): the
# ...                         (the comment naming the command, and what it does with its section as a lock)
version = 29
profile = "z3"                # or "no-z3", which has no z3_ lines
z3_version = "5.3.3.0 430d19e697e2ec9bad79ff210d41b4a7a5fcfa3e 430d19e"   # Z3's own version string
z3_library_sha256 = "7ca2ea1f27e40c86269d6ff7f0e82293708253cb05dbec094c90b08c4ec04d31"   # its library file
                              # run: work_factor = 5, [budget] work_factor, the mutants' work budget
krs_annotation = 10           # coverage: a document the KRS front end annotated, its krs.version

[coverage.spec]
outcome = "admitted" # a refused specification adds its stage and reason, and nothing below

[coverage.settings]           # coverage: [coverage]'s values (no tiers: [coverage.flips] run says whether tier 2 ran)
depth = 1
mcdc = [                      # or the names, one per line, or true
]
work_factor = 5               # coverage: [budget] work_factor, the flips' work budget

# Each family lists its obligations by id: `open`, those no program covers; `argued`, those an
# ...                         (the comment saying what each list and standing is)
[coverage.rules]              # coverage: each family's open and argued obligations, by id, in item order
open = [
  "rule:calc.k:23",
]
argued = [                    # an empty array too opens and closes on lines of its own
]

[coverage.requirements]
open = [
]
argued = [                    # [[coverage.argued]] items, each with the standing its argument rests on; its text is not rendered
  { id = "requirement:CALC.div:refuted", standing = "text" },
]
undecided = [                 # only where a family has undecided items, which open leaves out
  "requirement:CALC.div:B:mcdc",
]

[coverage.syntax]
open = [
]
argued = [
]

[coverage.rule_windows]       # coverage at a depth above 1 only: every open window, on the frontier or not
open = [
  "window:CALC.seq,CALC.div",
]
argued = [
]

[coverage.syntax_paths]       # coverage at a depth above 1 only: every open path and joint field value
open = [
]
argued = [
]

# Each [[coverage.flip]] is a condition flip: a mutant kink generates from the definition by
# ...                         (the comment saying what a flip and each status is; where none ran, that none did)
[coverage.flips]              # coverage: whether the flips family ran
run = true

[[coverage.flip]]             # coverage: each flip, where they ran, in item order
id = "flip--dispatch+run+wake+halted--H"
negates = "H"                 # the condition as the source writes it; a bit flip's is `toggles = "bit 6 of argument 1"`
rules = [                     # the rules the mutant edits, by their ids in the rules family
  "rule:CALC.dispatch",
  "rule:CALC.run",
  "rule:CALC.wake",
  "rule:CALC.halted",
]
status = "distinguished"
killer = "irq"                # the recorded killer while it kills, else the first in the search's order

[[coverage.flip]]
id = "flip--refused"
negates = "matches!(x)"
rules = [
]
status = "refused"
reason = "not-judged"         # a refused flip's reason

[[coverage.flip]]
id = "flip--halted+wake--I"
negates = "I"
rules = [
  "rule:CALC.wake",
  "rule:CALC.halted",
]
status = "argued"             # an argued flip
standing = "text"             # its argument's standing

# Each [[run.mutation]] is a mutation of the list, by its id, and its verdict: killed (a
# ...                         (run: the comment saying what a row and each status is)
[[run.mutation]]              # run: each mutation it judged, in list order
id = "add-becomes-sub"
status = "killed"
killer = "add"                # the recorded killer while it kills, else the first in the search's order
killed_by = [                 # run --full only: every killer, in FLOW.toml's order
  "add",
  "nested",
  "inline",
]

[[run.mutation]]
id = "renamed-anchor"
status = "invalid-mutation"   # or "not-admitted": a mutation its author must fix
reason = "unknown-label"      # its reason, a function of the specification and the mutation

[[run.mutation]]
id = "stall-longer"
status = "survived"
horizon = [                   # [observe]: agreed only up to it, one program and channel per line
  { program = "run", channel = "clock", elements = 16, opening = "bound" },
]
```

The comments say what the rendering is to a reader who has not read this README: the record's says what the file is and who writes each section, the section's names the command whose verdicts it holds and what that command does with it as a lock (`run --lock`, `coverage --lock`), and one before a run's first `[[run.mutation]]`, a coverage section's first family and its `[coverage.flips]` says what each entry, list and status word is.
Each is a constant of the rendering's version, so it moves no line of a lock between runs.

Every array of strings or inline tables the rendering writes (`open`, `argued`, `undecided`, `mcdc`, a flip's `rules`, `horizon`, `killed_by`) has one value per line, with a trailing comma, from its key's line to a `]` on its own line, an empty array included.
A lock is reviewed as a diff, and in this layout the diff of a set that changed is exactly the lines of the values that joined or left it: closing one open obligation of many removes its line, closing the last one too, and no other line moves.
The values keep their order (item order, list order, `FLOW.toml`'s order), so a case that closes a gap removes lines and moves none.
An `argued` entry is an inline table, `{ id, standing }`, so that each argued item is written once, with what its argument rests on: a standing that moves changes that item's line alone.

A run document of a mutation list that does not decode has no `[run.spec]` but `[run.mutation_list]` with `outcome = "refused"`, and one of a lock that does not decode has `[run.lock]` (`[coverage.lock]`) with `outcome = "refused"`;
a run that a corpus error stopped ends with `[run.stopped]`, the mutation and the reason (the mutations after it have no status).
An `invalid-mutation` or `not-admitted` mutation, which its author must fix before it is judged, has its `reason`, as a refused specification has: the reason is a function of the specification and the mutation alone (the resolution, the mutant's compile, its consistency, its stop), so it is the refusal's verdict, and a lock shows which refusal moved.
A refusal's or a stop's text is not part of the rendering, since it explains a refusal rather than records a verdict: `kink-flow` prints it on stderr (`kink_flow::verdicts::refusal_details`), one line per refused specification or list, per mutation its author must fix (`mutation <id>: <status> <reason>: <detail>`), and for a stop.

A coverage rendering lists ids, which name a rule by its KRS item when a front end annotated it (`krs.item`), else by its label, else by `file:line` ("The document" under `coverage`); it lists no program and no count, so it moves only when a gap opens or closes or a flip's status or killer moves, and a case that covers nothing new renders the same bytes.
Where the flips ran, each is listed (`[[coverage.flip]]`) with the condition it negates as the source writes it (`negates`, the flip item's `text`; `toggles` for a bit of an encoding), the rules it edits by their ids in the rules family (`rules`), its status, a refused flip's reason, a distinguished flip's killer, which follows the killer rule over the coverage lock ("The corpus record"), and an argued flip's `standing`.
A family with undecided obligations lists them as `undecided`, which `open` leaves out ("Unique-cause MC/DC"): a pair the records cannot decide is another verdict than one no program shows, so a lock moves when one becomes the other.
The KRS front end's annotation has a version of its own (the document's `krs.version`), which the header renders as `krs_annotation`, because the spelling of an item follows it: from version 2 an item is spelled as a stop reads it (`crate::plus_zero`, `lang::step`), and a document with no version named it as the `// KRS` line does (`plus_zero`); version 3 adds `stop.krs.when`, the stop condition as the corpus wrote it, and spells items as version 2 does; version 4 named a `results` document's guard nodes by KRS construct, and version 5 annotates the `coverage` document that replaced it, whose item ids spell items as version 2 does.
Two renderings of the same verdicts under different annotation versions differ in that line and in the rule names only.
A run rendering names no rule, so it has no `krs_annotation` line, which could only move a lock without any verdict moving.
The reason of every status but a refusal is left out: the reason of `unknown` is the first exclusion in run order.
A status does not depend on the order or the cache while no `budget.time_ms` bound fires ("Cost model"); a `timeout` depends on the host by its nature.
A killed mutation's `killer` follows the killer rule under both schedules ("The corpus record"): a function of the lock and the inputs, so a warm run renders the bytes a cold one does.
A full run's `killed_by` is such a function too ("The full matrix"), so a first-kill and a full rendering state the same facts apart from the `killed_by` lines, and a full rendering of a run with no kill is byte-equal to the first-kill rendering.
For a first-kill run, `run --output verdicts`, `report --output verdicts` and the lock are the same bytes.
The `profile` line is there because the two profiles decide solver questions differently (without Z3 none is decided, and under Z3 within `budget.smt_resource_limit` on the Z3 build), so a class, a status and a cell can differ between them, and a diff of two renderings across profiles shows why.
The same argument applies to the Z3 build: under Z3 whether a query is decided within its units is a function of the query, the units and the machine code that counts them, so a kink build linking another Z3 can move a class, a status or a killer with the same inputs and the same profile.
Under the Z3 profile the header therefore names the build the document's verdicts were decided on (the document's `z3`, k-rust's `z3_build`), and the portable profile renders neither line.
`z3_library_sha256` is the identity: the SHA-256 of the library file Z3's code comes from, the archive (`libz3.a`) of a static link or the shared library of a dynamic one, so that it names Z3 whatever kink is built around it, and it is the digest every cache key already holds (the result key's `smt.z3`, see `coverage`).
`z3_version`, Z3's own version string (`Z3_get_full_version`), names a release, not a build (two builds of one release, from another compiler, with other flags or for another architecture, can count units differently and report the same string); it is there so that a reader of a moved header sees which release moved.
A build that cannot name its library (a shared library replaced since it was mapped, a static link whose archive the build could not name) renders `z3_version` alone, and its caches are off for the same reason.
Version 2 (CF-23) added `schedule`, `profile` and `killed_by`, and version 3 (CF-40c2) renders the status version 2 rendered `invalid` as `not-admitted`, as the run document names it since its version 18; the rendering's shape is unchanged, and a lock recorded at version 2 differs from a version 3 rendering of the same verdicts in its `version` line and in that status's name only.
Version 4 adds the header's `krs_annotation`, so that a lock whose rule names move with the KRS annotation (version 2 of it spells `plus_zero` as `crate::plus_zero`) says why; a version 3 rendering of a KRS document named its rules as the document did, without saying which annotation version that was.
Version 5 adds the `reason` of an `invalid-mutation` or `not-admitted` mutation; a version 4 rendering of such a mutation gave its status alone, so a reader learned the refusal only from `check`.
Version 6 adds each killed mutation's `killer` under both schedules and a refused lock's `[lock]` section, and drops the header's `schedule` (a first-kill rendering no longer differs from a full one in what it records but `killed_by`) and a run rendering's `krs_annotation`.
Version 7 added a `results` rendering's `[[guard]]` list: each fired or matched rule whose guard missed an outcome.
Version 8 adds the header's `z3_version` and `z3_library_sha256` under the Z3 profile; a lock recorded at version 7 under Z3 differs from a version 8 rendering of the same verdicts in its `version` line and those two lines only, and a portable one in its `version` line only.
Version 9 renders the `coverage` document, which replaced the `results` document: its settings, then each family's open obligations by id, and whether the flips ran, with no case and no program list; a run rendering is unchanged but for its `version` line, so a lock recorded at version 8 differs from a version 9 rendering of the same run in that line only.
Version 10 lists the syntax family's open obligations in a coverage rendering (`[syntax]`).
Version 11 lists each flip of a coverage rendering whose flips ran (`[[flip]]`), with its status, a refused flip's reason and a distinguished flip's killer, so that a `coverage.lock` records the flips' verdicts; every other rendering is unchanged but for its `version` line.
Version 12 gives a survivor that rests on a horizon its `horizon` (`[observe]`, "What a run observes"): each program whose channels agreed only up to its baseline's horizon, each channel and the number of elements agreed on, a function of the budget and not of the host.
Version 13 lists each family's argued obligations beside its open ones (`argued`) and gives an argued flip the status `argued`, so that a `coverage.lock` records which obligations are argued rather than covered; a run rendering is unchanged but for its `version` line, and a coverage lock recorded at version 12 with nothing argued differs from a version 13 rendering of the same coverage in that line and the empty `argued` lines only.
Version 14 gives each horizon its `opening` (`bound`, `undecided-element`, `branch`, `undecided-path` or `cycle`), so that a lock shows whether a larger budget could observe more, and gives an undistinguished flip that rests on a horizon its `horizon`; a rendering with no horizon is unchanged but for its `version` line.
Version 17 lists a coverage rendering's rule windows (`[rule_windows]`) where the document has the family, at a depth above 1, which earlier versions refused; a rendering of depth 1 is unchanged but for its `version` line.
The section lists every open window, not only the frontier's: a lock moves when any window opens or closes.
Version 18 also lists the open and argued syntax paths (`[syntax_paths]`, every open path and joint field value, on the frontier or not) where the document has the family, at a depth above 1; a rendering of depth 1 is unchanged but for its `version` line.
Version 19 (FB-38) renders the statuses, guard outcomes and requirements of a function equation that cover every application its left-hand side matches whose deciding priority group is its own, tried or not ("Guard outcomes"): a coverage lock's open rules, `[[guard]]` entries and open requirements of equations can move for that reason alone, which the `version` line then says, rather than reading as a change of the corpus; a run rendering is unchanged but for its `version` line.
Version 20 writes every array of strings or inline tables with one value per line, an empty one included (above), where version 19 wrote each on one line; the values are unchanged, so a lock recorded at version 19 differs from a version 20 rendering of the same verdicts in its layout and its `version` line only.
Version 21 (FB-39) gives a coverage rendering `[arguments]`, each argued item's standing ("Argued obligations"), so that a lock records what each argument rests on and a standing that moves makes it stale; a coverage lock recorded at version 20 differs from a version 21 rendering of the same coverage in its `version` line and the new section only, and a run rendering in its `version` line only.
Version 22 (FB-39) renders coverage document version 19: an invariant-only equation is no obligation ("Families"), so a lock whose open lists and flips move for that reason shows a new version, not a corpus change; an `[arguments]` line names the assumed findings its standing rests on (`"<id>" = "<standing>, assuming joined <name>, ..."`); and an item whose invariant is not shown to be a function is `unchecked`. A run rendering differs from version 21's in its `version` line only.
Version 23 (KINK-FINDING-NAMES) renders coverage document version 20: an `[arguments]` line names the assumed findings a standing rests on by kind, sentences and digest, so a lock whose arguments assume findings shows a new version; every other lock differs in its `version` line only.
Version 24 (FB48-NAMES, FB48-ONE-LOCK) is the corpus record's: the rendering is the record's header (a comment saying what the file is, and `schema`) and the command's section, `[run]` or `[coverage]`, which states its own `version`, `profile`, Z3 build and `krs_annotation` and holds the command's tables (`[run.spec]`, `[[run.mutation]]`, `[coverage.rules]`, `[[coverage.flip]]`, ...), where version 23 wrote one command's rendering at the top of its file with `document`; each section opens with a comment naming the command whose verdicts it holds and what that command does with it as a lock, and a comment before its rows and families says what each entry and status word is; a coverage section gives each argued item once, in its family's `argued`, with its standing (`{ id, standing }`; an argued flip's `standing` on its row), where version 23 listed the ids there and repeated them as the keys of `[arguments]`; it gives each flip the condition it negates or the bit it toggles and the rules it edits, and it no longer writes `[settings] tiers`, which `[coverage.flips] run` states.
Version 25 (FB47-VERDICTS) gives the record a third section, `[compare]` ("The corpus record"), and the record's comment names it: a `[run]` or `[coverage]` section differs from version 24's in its `version` line only, and the record in its comment.
Version 28 (FLOW-NAMES-PACKAGE) states, in the header of the record of a flow that names its definition, that definition (`definition = "PACKAGE:FACET"`; "The corpus record"), and the rendering of such a flow's document has the same header: every section differs from version 27's in its `version` line only, and the record of a K flow in nothing else.
Version 29 (IMPLEMENTATION-TRACES) lets an implementation be of a second protocol and compare traces: the header of a `[compare]` section names the protocols of its implementations (`protocols = [..]`, where it named the one, `protocol`), a trace view's row may have the verdict `agree-up-to` with its `horizon`, canonical JSON in a literal string as `difference` is, which `--locked` compares, and the section's comments say what a verdict is, a test of one build on the corpus's programs up to the horizon it names. A `[run]`, `[coverage]` or `[query]` section differs from version 28's in its `version` line only, and a `[compare]` section of implementations of the first protocol in its header only (its `version` line, its `protocols` line and its comments): every row is the bytes it was.
Under `--locked` a section of another version, or a lock before version 24, is refused, naming the command that rewrites it ("The corpus record"), so a lock recorded at an earlier version is rewritten by one run of each command without `--locked`, whose diff shows the new layout beside any moved verdict.

## `kink-flow report FLOW.toml [--cache DIR] [--output json|verdicts]`

Prints the stored run document again, byte for byte as `run` printed it.
It reads only the cache's `report.json`, whose place depends on the manifest's directory and `--cache` alone, so it loads no specification and runs nothing.
When there is none, or it is not a run document of the current version, it prints
`{schema: "kink-flow-report", version: 2, k_rust_revision, profile, z3?, outcome: "missing" | "unreadable", path, detail}`.
Version 2 adds `z3` under the Z3 profile, the Z3 build of the process that looked, as every kink-flow document names it; the portable document has no such member.

A run document is printed only when this build could have written it: when it names this kink build and semantics identity (`kink_build`, `kink`) and, under the Z3 profile, this Z3 build (`z3`).
Under Z3 a status is a function of the Z3 build that counted its solver queries' units, and a dynamically linked Z3 is outside the executable `kink_build` digests, so after its shared library is replaced the stored document is `unreadable`, with a `detail` that names both builds, until `run` decides it again.

With `--output verdicts` it prints the rendering of the stored run document ("Verdicts: `--output verdicts`"), which is what `run --output verdicts` printed, since the rendering is a function of the document alone.
When there is no stored run document to render, it prints nothing on stdout and the reason on stderr (`missing run report PATH: DETAIL`, `unreadable run report PATH: DETAIL`).
Under `--output json` that reason is the `kink-flow-report` document on stdout, as every refusal of a kink-flow command is a document.

Exit status: the status the printed run document gives, as `run` exits on it ("Exit status"); 2 when there is none, it is unreadable, the manifest does not decode, or on a usage error.

## Checking a pattern: `kink-flow query FLOW.toml [PATTERNS.toml] [--only ID]... [--verify] [--full] [--lock FILE [--locked]] [--no-explain] [--cache DIR]`

A pattern check asks, for one program of the corpus: does some run of this program, from its input, reach a configuration that matches this pattern?
The initial configuration, every configuration a run reaches and the final ones all count.
Use it to check a claim before relying on it: when you write a program meant to exercise a situation (a division by zero, a thread that writes before another reads, a loop that runs twice), write the situation as a pattern and claim the program hits it.
kink-flow runs the program and confirms or refutes the claim, so a test whose purpose was imagined rather than reached is caught.
"Every run hits" is not asked: when a program has several runs (thread interleavings, the evaluation order of `strict` operators), the answer is about some run.

The patterns asked are the corpus's: those `FLOW.toml` declares (`[[patterns]]`, "Declared patterns", above).
A pattern list named on the command line (`PATTERNS.toml`, the operand after `FLOW.toml`) replaces them, and `[[patterns]]` is then not read, as a verb's own flag replaces a front end's list; `fuzz --patterns` does the same for a pattern job.
A corpus that declares no patterns, asked without a list, is refused (`patterns: the corpus declares no patterns: ...`, exit 2).
The krs front end names its corpus's `PATTERNS.toml` as the list where `FLOW.toml` declares no `[[patterns]]`, so a corpus written before `[[patterns]]` keeps its patterns.
`--only` names a pattern of the patterns asked; an id that is none is refused (`--only: no pattern of the corpus has the id ...`).

### `PATTERNS.toml`

```toml
[[pattern]]
id = "result-three"                  # unique, non-empty
pattern = "<k> 3 </k>"               # K text, as the left-hand side of a rule is written
programs = ["add", "sub"]            # optional: the programs you claim hit it
note = "the result 3 is reached"     # optional, free text

[[pattern]]
id = "result-above-five"
pattern = "<k> I:Int </k> requires I >Int 5"
# expect = "no"                      # optional, not beside `programs`: no program hits it
# imports = ["BOOL"]                 # optional: K modules the text names beside the main module
```

- `pattern` is parsed by the specification's own grammar, as the content of a rule in the main module: write a configuration fragment, with `...` and omitted cells completed as in a rule (`<k> 1 / 0 ~> _ </k>`, `<state> ... X |-> 3 ... </state>`), variables (`I:Int`, `_`) and an optional `requires` condition over them. A rewrite (`=>`) in a pattern denotes its left side. An `ensures` is refused, and so is a variable that occurs only on a rewrite's right side.
- A `requires` that is undefined at a state (`10 /Int (I -Int 3) >Int 0` where `I` is 3) does not hold there, as for a rule's condition: that state does not match. So a pattern whose only matches make its condition undefined gets a `no`, and a claim of it is refuted, although the program does reach the configuration you meant; write the condition so that it is defined at every state it is matched against. A condition whose definedness k-rust cannot decide (a partial function with no equation for its argument) gives `unknown`.
- `programs` lists the corpus programs you claim hit the pattern (the per-input claims): each is asked, and its row says whether the claim is confirmed. Whether or not it has claims, every pattern is an obligation of the corpus (below).
- `expect = "no"` claims that no program of the corpus hits the pattern, as a mutation's `expect = "survive"` claims no program kills it: the obligation's `expectation` is `met` when every program answers a final `no`, `unmet` on a hit (exit 1) and `inconclusive` otherwise (exit 3), and the query prints `pattern ID: ...` on stderr for each that is not met. It changes no answer and enters no key, digest or lock: the lock records the fact (`open` or `hit`). A pattern with both `expect` and `programs` claims two contradicting things, and is an error of the pattern list.
- `steps` in place of `pattern` writes a chain of patterns a run passes in order ("Chains", below).
- `imports = ["BOOL"]` (optional) lists K modules the pattern's text names beside the main module. A pattern is a question about the specification's runs and no sentence of it, so which operations it may name is its own: the main module imports what its own sentences need, and a specification none of whose rules has a condition does not import `BOOL`, where `requires A andBool B` then does not parse. A pattern with `imports` is parsed as the content of a rule of a module that holds no sentence and imports the main module, the modules the main module imports and those listed; the module exists for the parse alone, and the specification, its digests and every other pattern's answers are as without it. The key enters a pattern's digest only through the target the text compiles to. An import that is no module of the definition is refused (`invalid-pattern`), and so is a pattern that names an operation of a module the main module does not import, directly or through a module it imports: the compiled definition the runs are of holds no such operation. A KRS patterns package's clauses carry their imports themselves.
- An unknown key, a value of the wrong type, a duplicate or empty id, an empty or duplicated `programs` or `imports` entry, `expect` beside `programs`, and a claimed program the manifest does not have are errors that name the key; the command then runs nothing and exits 2.

A pattern list is such a file, whatever its name: the one the command line names, or each list `[[patterns]] files` matches.

`testdata/flow/calc/PATTERNS.toml`, `testdata/flow/loop/PATTERNS.toml`, `testdata/flow/witness/PATTERNS.toml`, `testdata/flow/chain/PATTERNS.toml` and `testdata/flow/explain/PATTERNS.toml` are complete examples.

### The obligation and its witness

A pattern states "some program's run reaches a state that matches P": an existential over the corpus, of the shape of a mutant's "some program tells it apart".
A witness discharges it as a killer discharges a mutant: one program that hits it.
- **The witness rule.** Let w be the pattern's recorded witness (`[query]`, `--lock`). If w names a program of the corpus and w hits, the witness is w; otherwise it is the first program in `FLOW.toml`'s order that hits; otherwise there is none. So the witness is a function of the record and the corpus: adding a program moves no witness while w still hits, and deleting w re-opens the obligation, whose next witness is the first hitter in corpus order.
- **The status.** `hit` with a witness; `open` when every program of the corpus answered a final `no` (no program's run reaches such a state); `undecided` otherwise (no hit, and some program's answer is `unknown`, an `error` or `invalid-pattern`). An open or undecided obligation is no finding: the query states it, and you decide whether to write the program that hits it, or to state `expect = "no"`.
- **What is asked.** The pattern's claims first, then the obligation's walk: w first, then the other programs in corpus order, until the first hit, reusing every answer a claim gave rather than asking a pair twice. An obligation with no hit asks every program. `--full` asks every pair and lists each obligation's `hitters`, every program that hit in corpus order; the witness, the status and the lock are the same as without it.
- **`witness_change`** says why the witness is not the recorded one, as `killer_change` does for a killer: null when it is, `no-record`, `not-in-corpus`, `clock-stopped` (the clock stopped w's search, so whether it still hits is not decided on this host; the lock keeps it, "The `[query]` section"), `no-longer-hits` (w was asked, live or cached, and did not hit) or `not-run` (the pattern is invalid, so w's search never ran).

### Answers

The command prints one document, `{schema: "kink-flow-query", version: 12, k_rust_revision, profile, z3?, kink_build, kink, spec, stop?, observe?, programs, patterns, rows, obligations, full, counts, refuted_claims, mismatches, pattern_cache, explanations, baseline_runs, data, lock?}`.
Version 12 (CHAIN-STOPLESS-WORK) bounds every chain run by its work budget ("Chains", "What it costs"): a chain's row may be `unknown` where a version 11 run went on until it ended or `time_ms` stopped it, with a cause naming the bound and `[budget] work_factor`; such an `unknown` is cached (its row's `cached` true on the next query), a chain on a corpus without a comparable baseline is `unknown` (`no-work-bound`), and a chain's key names the bound, so every chain answer is asked again once; every single pattern's answer, row and witness is unchanged.
Version 11 names where each pattern is written: each entry of `patterns` carries `source`, `{file}` for a pattern of a pattern list (its path relative to the manifest's directory, or as the command line names a list outside it) and `{krs, item, file, line}` for one a front end compiled from a KRS patterns package; every answer, exit status, lock row and key of version 10 is unchanged.
Version 10 (FB50-EXPLAIN) explains a failed answer ("Explanations", below): every row and every obligation carries `explain`, the document carries `explanations`, and a `--verify` mismatch of a derived pattern's record names its part; every answer, exit status, lock row and key of version 9 is unchanged.
Version 9 answers chains ("Chains", below): a chain's entry in `patterns` carries its `steps`, a chain's rows name the route `chain-run`, and a chain's witness lists its `steps`; a version 8 query refused a list holding a chain.
Version 8 prints a hit's witness for a reader (below), where version 7 gave its state and bindings as KORE text cut to 4000 characters.
Version 7 (FB54-WITNESS) adds `obligations`, `full`, `lock` and each row's `clock_stopped`, and asks a pattern without `programs` until its first hit where version 6 asked every program, so `rows` holds only the pairs asked:
`programs` are the `coverage` rows (the result cache is brought up to date first),
`data` is the baseline's full critical-pair check under the premises, as in the run document (fz26 KINK-BASELINE-FINDINGS). Version 6 (KINK-FINDING-NAMES) names its findings by kind, sentences and digest, where version 5 named them by generated-K positions. `data` was added to version 1 without a new version, since it is additive and no command reads a `query` document back. Version 2 adds the refusal of a corpus with `[stop]` (stage `stop`, reason `unsupported-verb`, "Where a run ends"). Version 3 answers `no` under the Z3 profile where the search received no undecided solver answer, with a `cause` naming that count, and names the count in the `cause` of an `unknown` it withholds a `no` for (below). Version 4 adds `z3` under the Z3 profile, the Z3 build the answers were decided on, as the run document names it: whether the search's solver queries are decided within their units is a function of the build that counts them, so a `hit`, a `no` and an `unknown` are too; the portable document has no such member. Version 5 answers a corpus with `[stop]` through each program's stopped run ("A corpus with `[stop]`", below) and admits one with `[observe]`, which it ignores ("What a run observes"): the refusals at stages `stop` and `observe` are gone, the document carries `stop` as `check`, `coverage` and `run` do and `observe` (`{declaration, ignored}`, the declaration and why the query ignores it) when the manifest has them, a refused one's too, and each row names its route (`route`: `search` or `stopped-run`). A refused specification prints the document without `data` (the member is absent, not null; `spec.outcome` is `refused` and `programs`, `patterns` and `rows` are empty), and a pattern list that does not decode prints only `{schema, version, k_rust_revision, profile, z3?, pattern_list}`.
`patterns` one entry per selected pattern `{id, note, pattern, outcome: valid | invalid-pattern, detail, digest, kore, asked: claimed | corpus, expect, source}` (`kore` is the compiled target; `asked` says whether the pattern has `programs`; `source` says where it is written, `{file}` or `{krs, item, file, line}`, and is in no key); a chain's entry also carries `steps`, `[{pattern, unless, kore, unless_kore}]`, each step's text and its `unless`'s with their compiled targets, and has `pattern` and `kore` null and `digest` the chain's,
`rows` one row per (pattern, program asked) `{pattern, program, claimed, route, answer, cause, witness, cached, wall_ms, claim, clock_stopped, explain}` (`clock_stopped`: `search` where the clock stopped the search the answer rests on, `baseline` where a completed exploration's `no` failed only for the baseline run the clock stopped, or where a chain's `unknown` rests on its work budget and the clock stopped a baseline run of the command, whose polls would give another bound, else null),
`obligations` one per selected pattern `{id, status, witness, recorded_witness, witness_change, hitters, unanswered, expect, expectation, clock_stopped, explain}` ("The obligation and its witness"; `hitters` null without `--full`; `unanswered` the programs whose answer is neither a hit nor a final `no`; `clock_stopped` the stopped runs the obligation's value rests on, `{program, run}`),
and, with `--lock`, `lock` as for the other sections ("The corpus record").

| `answer` | Meaning | What to do |
| --- | --- | --- |
| `hit` | A run reaches a configuration that matches the pattern; `witness` shows it. | Nothing: the claim holds. |
| `no` | No run reaches one: the whole state space of the program was explored, within the budget, on a definition where nothing is left to the implementation, and the solver left no query of the search undecided. Under Z3 `cause` names that count (`0 undecided solver answers`); without Z3 it is null. | The program does not do what you meant: change the program, or the pattern. |
| `unknown` | No definitive answer; `cause` says why (below). | Read the cause; usually make the program terminate within the budget, or accept that the definition leaves the question open. |
| `invalid-pattern` | The pattern does not parse, sort or compile; `cause` is k-rust's message. A position in it, `pattern:LINE:COLUMN`, is a line and column of the pattern's own text with its surrounding whitespace removed, not of the pattern list's file. A pattern that does not parse and writes a cell tag (`<IF>`, `</IF>`) that is no cell of the configuration also names it: `the pattern names <IF>, which is no cell of the configuration; the configuration declares: <k>, ...` (k-rust scans a cell's tags as one terminal, so its own message names an unexpected character sequence). It never runs. | Fix the pattern. |
| `error` | The program is not admitted, or k-rust refused the search; `cause` says which. | Fix the program, or report it. |

`claim` is null for a program the corpus form asked; for a claimed program it is `confirmed` (`hit`), `refuted` (`no`) or `unconfirmed` (anything else).
**A refuted claim** (also listed in `refuted_claims`) means the program, run exactly as kink runs it, never reaches the situation you said it tests: the purpose you gave the test is not what it does.
An `unconfirmed` claim is neither confirmed nor refuted.

The witness of a hit is `{depth, state, bindings, rules, rendering, note}`, printed for you to check:
the number of rewrite steps to the matching configuration, the configuration itself, the values of the variables you wrote, and `rules`, the rewrite steps of one run from the initial configuration to it, each named by its label, else by the file and line of the rule written for it, else by its compiled id.
`state` is `{cells: [{path, named, value}]}`, the configuration's cells in pre-order, `path` the labels from the top cell to the cell (`["<generatedTop>", "<T>", "<mem>"]`).
A cell your pattern names (one it gives a content of its own: `<k> done </k>`, `<mem> 7 |-> V </mem>`, `<regs> R </regs>`; not a cell left out, nor one written as `<c> _ </c>`) is printed in full as K text, the printer kill evidence uses ("Printing"), so the part of the state the pattern is about is never cut away.
Every other cell is shortened by its structure: a list of more than 8 elements is `{collection: "list", length, last}`, its last 8 elements; a map or a set of more than 8 is `{collection, length, first}`, its first 8 entries in printed order (a map's entry `{key, value}`); each element, and any other content, is cut at 200 characters.
A printed value is `{text, rendering, truncated}`, `rendering` `kore` with a `note` where the K printer refused the term.
`bindings` is `[{variable, value}]`, each variable by the name you wrote (`N` for `N:Int`), its value printed in full, or shortened as above when it is a long collection; the variables k-rust generates to complete cells are left out, and so is every variable spelled as k-rust spells a generated one, `_Gen<n>` or `_DotVar<n>`, so a variable of your own with such a name is not shown: the witness is for display only, and no answer reads it.
`rendering` is `k`. The printing is a function of the state and the pattern: the cache record keeps the witness's facts (the whole state and bindings as KORE text), and the document prints them when it is written, so a cached hit is printed as a live one is.
Under `krs kink`, values are printed by the same printer `krs run` prints configurations with, and each cell entry also names its cell by Rust path, `krs_cell`.

**Why a no can be unknown.** A `no` is a claim about every run, so it needs more than a `hit`:
- the exploration completed: no path stopped at `budget.max_depth` (`a path reached max_depth = N`), the search finished within `budget.time_ms`, k-rust decided every step and every match (an undecided step, an undecided match, a state stopped for lack of native stack each make it incomplete), and the search left no hook application unevaluated (`unsupported-hook`: its `unsupportedHooks` and `allowanceRefusals` lists are empty; KINK-R4, below, since where such a hook is undefined the step to its state has no successor, and where it is defined its value can let a rule apply, neither of which k-rust computed; this does not rely on the baseline run below meeting the same hook);
- the program's baseline run (its `coverage` row) is `comparable`: complete, with no stack stop and nothing else that makes a run no evidence (a contradicted claim, an allowance refusal, ...);
- the definition leaves nothing to the implementation: no rule depends on a hook whose value the definition leaves open and k-rust chooses (`implementation-chosen-hook`, decision 1's census: `String2Bytes`, `KRYPTO.keccak256`, ...; an open hook k-rust cannot evaluate, such as `#getc` or `Float2String`, is judged by the baseline run's `unsupportedHooks` instead, which the comparable baseline below requires empty), and neither does the program's initial configuration; with such a value another implementation could reach the pattern, so the exploration of k-rust's choice says nothing about it;
- on a definition whose short-circuit analysis flags a rule, and wherever the program's initial configuration applies a function or operator whose value depends on whether a short-circuit operator skips an undefined operand, the search read no operand a short-circuiting backend may skip that counts (`short-circuit-reading`: its `shortCircuitReadings` list holds no such entry, judged as a run's list is; CF-03, answer schema v6, before which no `no` was given on such a definition): an empty list means every evaluation the search used, the normalization of the initial configuration included, has the same value under the skipping reading, so it explores that reading's configurations too, while an entry that counts is a place where a skipping backend may reach another one; the cause names the step;
- the search read no value the definition leaves open (`implementation-chosen-value`: its `implementationChosenValues` list is empty; kink27 R3-CENSUS-RUNLEVEL): k-rust's own classes, such as the order of `keys_list` or a `choice`, are judged per run rather than by the census, and a search lists every class value it took, the matching of the pattern included, so with one on the list another model of that value may reach the pattern;
- the search received no undecided solver answer (below, "Undecided solver answers"): the cause of an `unknown` withheld for this names the count, and under Z3 the cause of a `no` names the count that licensed it;
- the definition has data under `[spec] assume_joined` (the `data` member's `has_data`, as `run` and `coverage` require of an end): its full critical-pair check has no finding the names leave unnamed (`baseline-findings`, fz26 KINK-BASELINE-FINDINGS), and the check read the whole definition (no stop for lack of native stack, no skipped candidate pair, every executable equation read and every root pair classified; KINK-R4, before which only a finding refused a `no`): matching is syntactic, while a pair that does not join, or one the check did not read, can identify a reached configuration with an instance of the pattern in every model.

**Undecided solver answers.**
Under the Z3 profile the search asks the solver about rule conditions and their remainders, equation side conditions, definedness obligations, a state's feasibility and the match of the pattern against each state.
Every one of those queries goes through the counting solver k-rust's facade gives the operation, and kink reads the operation's count of undecided answers (k-rust's `stop::with_operation_record`, `unknown_answers`) around the search itself, not the baseline run's `smt_unknowns`.
An undecided answer is a query Z3 did not decide within `budget.smt_resource_limit` and its retries, or by its incompleteness; a decided answer (`sat`, `unsat`, a validity verdict, a model) and a failure (a query that does not translate, a script Z3 rejects, an internal error of Z3) are facts about the query, and a stop (a cancellation, a failed prelude) ends the search or leaves a state incomplete, so none of them is counted.
With the count zero, every decision of a completed search rests on decided answers or on failures.
A failure carries no information about the query, and every place a search takes a solver answer reads it so: only a decided `unsat` or refutation refutes a condition, a match or a state, and a failure leaves it undecided or open.
Without Z3 every query that needs a solver fails, always with one kind of failure (no solver), while under Z3 a query can also fail as untranslatable, as a rejected script or as an internal error of Z3; the `no` rests on k-rust reading each of those as no refutation too, which `kink/trust.md` checks site by site.
Such a `no` rests on nothing the portable profile's does not, besides Z3's decided answers and that reading of the failures only Z3 gives.
With a nonzero count the answer is `unknown`, with the count in its `cause`: the `no` would also rest on every place k-rust takes an undecided answer reading it as no information about what is reachable, which no run of the portable profile exercises, since its solver never answers `unknown`.
The count is the search's own: the program's baseline run is a separate operation.
The solver's caches hold decided answers only, so a cached answer is never undecided, and k-rust's memos of condition verdicts are cleared when the work that opened them ends, inside the search, so a verdict served that rested on an undecided answer was counted when the same search first decided it.
`kink/trust.md` ("Stack dependence", the solver paragraph) states the argument with the k-rust sites it reads.

A `hit` needs none of these. It is a run k-rust found to a configuration that exists, and k-rust's choice of an open value is one model of the definition. A hit is found even in a program that never ends, or that the budget stops: the search stops at the first match.
That choice includes the short-circuit reading. K leaves it open: `domains.md` says `andBool` and `orBool` "may be short-circuited in concrete backends", and that `#if` "does not short-circuit on symbolic backends". k-rust reads them strictly: a condition with an undefined operand is undefined, so its rule does not apply. That is one reading K allows, so a reading on the search's list that counts (`short-circuit-reading`) makes a `no` unknown but leaves a `hit` standing.
The consequence: a hit may be on a configuration that only the strict reading reaches. For example, an `owise` rule fires because another rule's condition was undefined, and a short-circuiting backend might not reach that configuration. The census (`implementation-chosen-hook`) is treated the same way: a hit stands, a `no` does not.
Two conditions make every answer unknown: the definition's load counted a stop for lack of native stack (`load-stack-stop`), or a rule or equation has a condition equating two terms (`equals-condition`, a gap of k-rust's own answers).
A match is a hit only when it is decided, and the search stops at its first match, so otherwise the answer is unknown. A match is not decided when any of these holds:
- it holds only under a condition k-rust did not decide;
- its path emitted a backend diagnostic;
- its configuration's term is not shown defined (`undefined-state`);
- the search left a hook application unevaluated (`unsupported-hook`, KINK-R4): the search response's `unsupportedHooks` (a hook k-rust does not evaluate) or `allowanceRefusals` (a `Bytes` result its memory allowance refused) list is not empty. Such an application stays in the configuration as written, and `ground_defined` counts an irreducible application of a `value-production` symbol as a value from its declaration alone, hooked or not; where the hook is undefined at its arguments, the configuration denotes nothing and the step to it has no successor, which k-rust did not compute. The lists are the search's as a whole, so an entry on another branch also makes the answer unknown.

The `undefined-state` case is a configuration holding an application of a function the definition does not declare `total` that no equation reduced, such as `f(3)` for a function with an equation for `f(0)` only. Wherever that application is undefined, such a configuration denotes nothing: there is no run to it, although k-rust's search lists it; its match states the undecided `\ceil(f(3))` as a condition (k-rust `docs/compatibility.md`, "Search results"), so it is not a decided match, and kink also checks the configuration itself. kink therefore requires the matched configuration, and with it every binding, to be shown defined by k-rust's one existence predicate, `BackendDefinition::ground_defined` (since fz26 KRUST-ANYWHERE-HEAD; it was the stored `ceil_free` attribute, every configuration of which it still accepts): the configuration is ground and k-rust's definedness walk owes nothing. Every application must be of a constructor, of a function declared total, of a `value-production` symbol (a production with `anywhere` rules, such as SIMPLE's `_[_]`) that no equation of its head can reach, which that declaration makes a value of its sort (a ceil lemma decides its application first), or of a partial function whose `\ceil` k-rust shows `\top`. k-rust shows it in two ways: by an unconditional ceil equation of the definition whose condition simplifies to `\top`; or, since k-rust 68e362935 and fdb3ac1a5 (re-read at kink27 R1-TRUST), from its source-checked observation catalog, for a compiler sort projection `project:S(E[v])` of a term on its exact image and for a field `f(p)` of a sort with one constructor `c` whose one equation `f(c(X1, ..., Xn)) = Xi` covers every element (kink-native `tests/data.rs` pins both and records why each holds). A hooked map lookup or list access k-rust leaves unevaluated owes its key membership or length bound, which `ground_defined` never discharges. Every map or set must have keys k-rust shows apart. The configuration must also hold no term-level `\and`, at its root or below: `\and(a, b)` denotes a configuration only where `a` and `b` are equal, and nothing where they differ, which kink does not decide (k-rust's `ceil_free` counts a conjunction defined only when its two sides are one defined term) (no K rule writes one on a right-hand side, so this refuses no configuration known to be reached). A configuration whose definedness kink cannot read (it does not verify or internalize on the searched definition, k-rust provides no stack for it, or k-rust panics) is not a hit either: the answer is `unknown`.
A hooked partial operation that k-rust evaluates is not such a case. k-rust evaluates `7 /Int 0`, or a lookup of a key a map does not hold, to bottom, so the step to it is undefined and has no successor: the configuration is never reached, and the answer is a correct `no`.
Constructors, functions declared total (a `total` helper with no equation for its argument included), lists, and maps or sets over domain values such as IMP's `<state>` and IMP++'s `<store>` pass. So does SIMPLE's stored `a[4]`, which neither `anywhere` rule of `_[_]` matches. A configuration holding a partial function's unevaluated call does not, unless k-rust shows that call defined in one of the two ways above, nor does an application an `anywhere` rule of its head still matches, nor a map whose keys k-rust cannot show apart. Then the claim is `unconfirmed`, never confirmed; usually the program calls a function outside the cases its equations cover.

### Explanations

A refuted claim says that the program never reaches a configuration matching the pattern, not which part of the pattern it never reaches together with the rest.
A pattern written for a program is usually off by a step or a term, not by a situation, so the query explains each failed answer by the parts of its pattern.
It asks the patterns that leave one part out, one at a time, and lists each part whose removal gives a match, with the value the part left out has where it matches.

**The parts** are read on the compiled pattern, the constraints the matcher applies, not on its text:
- each cell the pattern names, as a witness lists cells: one written with a content of its own, `<requests> ListItem(request(C, _)) _ </requests>` or `<bus> L </bus>`, but not one left out or written `...`, and not one written only around other cells, whose inner cells are the parts. A cell of multiplicity `*` is held in a collection, so the cell holding the collection is the part;
- each conjunct of the `requires`: each operand of its top-level `andBool`s, left to right, numbered from 1. The sort test the compiler adds for a cast `X:Int` holds for every value of `X`, so it is no part and is not numbered.

**Leaving a part out.**
A cell is replaced by a fresh variable, as if the pattern did not write it, and every conjunct that names a variable only that cell binds goes with it (`dropped_conjuncts`): kept, such a variable would occur in the condition alone, which the matcher cannot decide.
A conjunct is dropped, and the others stay conjoined.
Either way the result matches every configuration the pattern matches, so where it hits and the pattern does not, the configuration it hits satisfies everything but the part left out.
A result that constrains nothing (every cell's content a variable, no condition) matches every configuration: its part is `vacuous`, not asked, and never a lead.

**A chain** is explained step by step.
Its longest reached prefix comes first: steps 1 to k asked as a chain (one step as a single pattern), for k = 1, 2, ... until one is refuted, reported as `prefix`.
Then each part of step k + 1 is left out, and so is its `unless`, each asked as the prefix followed by that step without the part.
A variable an earlier step binds is carried into the step, so no conjunct naming it goes with a cell, and the steps after k + 1 are not asked, so no variable they share is broken.

**When.**
- A refuted claim (a claimed program's final `no`) is explained on its program, in its row's `explain`.
- An open obligation (every program a final `no`) is explained over the corpus, in the obligation's `explain`: each part's pattern is asked in corpus order up to its first hit, the obligation's own existential and order. An obligation whose pattern states `expect = "no"` meets its expectation and is not explained.
- An `unknown` already has its cause, and a hit, an undecided obligation and an invalid pattern are not failures of a pattern: their `explain` is null.

Explanations are on by default, since they run only where an answer failed and their answers are cached; `--no-explain` turns them off.
They change no answer, row, count, obligation, exit status, `[query]` row, key or record of the pattern: they are computed after its answers and enter only `explain`, `explanations` and the derived patterns' own records.

**The answer.**
`explain` is `{form, parts, leads}`, `form` `pattern` or `chain`; a chain's also has `prefix`, `{steps, of, program, depth, cached, undecided}` (the longest reached prefix, the program that reaches it first and the depth of its last step; `undecided` is `{step, answer, program, cause}` where a prefix's answer is neither a hit nor a final `no`, which leaves the next step unknown and no part asked), and `step`, the number of the step whose parts are listed.
Each part is `{part, kind, cell, conjunct, dropped_conjuncts, digest, outcome, cause, program, cached, witness}`:
`part` its label (`cell <requests>`, `requires conjunct 1: C:Int <=Int size ( L:List )`, `step 3's unless`, a chain's parts prefixed with their step), `kind` `cell`, `conjunct` or `unless`, `cell` the cell's label, `conjunct` the conjunct printed, `dropped_conjuncts` the labels of the conjuncts that go with a cell, and `digest` the derived pattern's digest.
`outcome` is `hit` (the first program that hits, in `program`), `no` (every program a final `no`), `unknown`, `error` or `invalid-pattern` (with the first such program and its `cause`), or `vacuous`.
A part that is `unknown` is no lead: its `cause` says why.
`witness`, on a hit, is the part's value where the derived pattern matches, `{depth, state, bindings, rendering}`: for a cell, `state.cells` holds that cell's entry, printed in full as a witness prints a cell its pattern names; for a conjunct, `bindings` holds the values of its variables.
Under `krs kink`, a cell's part also names its cell by Rust path, `krs_cell`, as a witness's cell entry does.
`leads` lists the parts that hit.
`explanations` is `{enabled, asked, from_cache, records_written}`: the (derived pattern, program) pairs this command asked, how many the cache answered and the records written.

For example, a claim of

```toml
pattern = "<k> writeByte(_:Int, _:Int) ~> pushLow(_:Int, _:Int) ... </k> <requests> ListItem(request(C:Int, _:Int)) _:List </requests> <bus> L:List </bus> requires C <=Int size(L)"
```

on a program that files its request only after the byte is written leads with `cell <requests>`, whose witness shows `<requests>` holding `.List` where the rest matches, and `cell <k>`, `cell <bus>` and `requires conjunct 1` answer `no`.
A claim of `<bus> L:List ListItem(read(7, V:Int)) </bus> requires write(7, V) in L` on a program that reads 9 where it wrote 8 leads with `requires conjunct 1`, with V = 9 and L holding `write(7, 8)`; its `cell <bus>` takes the conjunct with it and is vacuous.
`testdata/flow/explain` holds both.

**How it is asked.**
Each derived pattern is a pattern: it is asked on the command's route, by the same matcher and judge, keyed by its own digest and the key every answer has, and its `hit` or `no` is cached as every answer is, so a second query reads it from the cache.
Within a command each (derived pattern, program) is asked once, so a part shared by a claim's explanation and its obligation's is asked once.
`--verify` asks every derived pattern live too, and a record that differs is a mismatch naming the part (`explain`), exit 1, as for every record a query without `--verify` would use.

**What it costs.**
A refuted claim's explanation of a pattern of C cells and R conjuncts asks at most C + R answers, one per part (a vacuous part none).
An open obligation's asks each part over the corpus up to its first hit: at most (C + R) × N answers for N programs.
A chain of n steps adds at most n − 1 answers for its prefix on one program (n − 1 per program over the corpus), and its step's parts at most C + R + 1, its `unless` included, per program.
Each answer is a search or a run of the program, as the pattern's own is, and a cached one costs none.

### A corpus with `[stop]`

A stop is part of a case's meaning ("Where a run ends"): each path of the case ends at its last stop event, or where the definition's own run ends, whichever comes first.
A state past a path's last stop event is no state of the case, so a match there is no answer, and an exploration that reached every end of the truncated system is complete, also for a program whose untruncated run never ends.
So on a corpus with `[stop]` (route `stopped-run`) each (pattern, program) is the program's run as `run` and `coverage` make it, one execute request of every path under the state set with the stop's rules, the program's count and the stop's condition, the manifest's `max_depth`, `baseline_max_work` and `time_ms`, which also matches every state it reaches against the pattern (k-rust `match_states`, with proof agreement: a state is refuted only where both evaluation modes refute it, since a refutation in execution mode alone may rest on a value the definition leaves open that nothing records; for a pattern that evaluates nothing this costs a second match and changes no verdict): the initial configuration, every state a path stepped or a bound stopped, a terminal rule's successor, and a cut-point leaf's state, but not the successor a cut-point rule proposes.
A corpus without `[stop]` keeps the search (route `search`), its keys and its answers; a chain is answered by a run on either corpus ("Chains").

- `hit`: the run reached a state that matches, decided, shown to exist, holding no term-level `\and`, on a path whose diagnostics up to it carry nothing but values the definition leaves open (k-rust's choice is one model, and the claim is existential), and the run left no hook application unevaluated.
- `no`: the matcher refuted every state the run reached, and the run explored the truncated system to its ends: every leaf is stuck, undefined or a stop leaf (no bound, no clock, no `stop-undecided` leaf) and carries no diagnostic of its path (a rule whose condition was left unsimplified, failed to simplify or exhausted the simplification budget may have been left unapplied there), no stop was passed, nothing excludes the run (the exclusions a baseline run is judged by, the initial configuration's included), neither the run nor the matcher stopped for lack of native stack, and the run, its leaves' feasibility questions and its matcher received no undecided solver answer (under Z3 the `cause` says so). The premises the search route also needs still hold: data, and a `comparable` baseline run, which is the same request without the matching.
- `unknown` otherwise, with the first missing premise in `cause`, its name in parentheses: `passed-stop` (a step of a stop rule that had another successor, where the run goes on through every successor, so on that branch its states need not be states of the truncated system: neither a match there nor its lack is an answer), `stop-condition` (a condition that refused makes the stop undefined on the run, and one left undecided ends its path at no end of the truncated system, which loses a `no` but not a hit reached on any path), `clock`, `incomplete`, `diagnosed-leaf`, `undecided-match`, `undecided-answers` with the three counts, `execution-mode-refutation` (a refutation in execution mode alone, which proof agreement rules out), an exclusion's name, and the hit's own causes (`dirty-reach`, `term-conjunction`, `unsupported-hook`).

A hit's witness has the reached state's `depth` and `state` (printed as above), the `bindings` of a match of the pattern against that state without a condition (the kind of match the run reached it by), found by a search of depth 0 from it, which is bounded work and runs under no clock, so the bindings are a function of the state and the pattern; `{absent: reason}` where that search fails or gives no such match, which no array of bindings is (an empty array means you wrote no variable); and `rules` null: the run reports where it reached the state, not the steps of the path to it, and a search for a path could find another one, past a stop.
The run does not stop at its first match: a hit costs one truncated run, about the program's baseline run, which its stop and the budget bound.
The answer's key also holds the program's stop (`stop`, as its result key holds it) and the route's modality (`{route: "stopped-run", search_type: "all", result_modality: "state-set"}`), so an answer of one count is never read for another, and a key without a stop keeps its bytes.

### Chains

A chain asks whether some run of a program passes configurations that match several patterns, in order.

```toml
[[pattern]]
id = "doubled-unless-alarm"
steps = [
  { pattern = "<k> pick(P:Int) ... </k>" },
  { pattern = "<log> _:List ListItem(V:Int) </log> requires V ==Int P *Int 2", unless = "<alarm> true </alarm>" },
]
```

`steps` stands in place of `pattern`: a non-empty array of tables `{ pattern, unless? }`, one per step.
Each `pattern` and each `unless` is written as a single pattern is, `requires` included, and is compiled alone.
The first step has no `unless`, since no step comes before it.
A `steps` of one step without `unless` is that step's `pattern`: the same entry, digest, route, key and witness.
`id`, `programs`, `expect` and `note` mean what they mean for a single pattern.

**Meaning.**
A chain P1, [U2] P2, ..., [Un] Pn holds on a program when some path of the program's run has configurations s1, ..., sn, each at or after the one before it, and one assignment of the variables the steps share, such that:
- each si matches Pi, with Pi's `requires` true;
- for each i ≥ 2 that has an `unless` Ui, no configuration strictly between s(i-1) and si matches Ui, for any value of the variables only Ui names.

Steps are reflexive: one configuration may match consecutive steps, as `=>*` allows.
A cell a step does not name is unconstrained, not "unchanged" as on a claim's right side: steps share values only through the variables they name.
The configurations of a path are those the stopped route matches ("A corpus with `[stop]`"): the initial configuration, every configuration a path stepped or a bound stopped, and a terminal rule's successor.
A `=>` inside a step keeps its meaning in a pattern: the step denotes its left side.

**Variables.**
A variable named in one part only (a step, its body and `requires` together, or an `unless`) is local to it: bound and reported in a step's body, existential in a step's `requires` alone and in an `unless`.
A variable named in two or more parts is shared, and one value of it is carried from the part that binds it to every later part: it is bound by the body of the first step that names it, and every other part that names it comes after that body (that step's `requires`, a later step, or the `unless` of a later step).
Each occurrence of a shared variable has one sort, and a shared variable is neither a set variable nor a variable written for several cells.
A violation is `invalid-pattern`, naming each variable and the parts.

**How it runs.**
A chain is answered by the program's run on either corpus (route `chain-run`): with the corpus's stop where it has `[stop]`, and with none otherwise, so every path ends where the definition's run ends.
The run is the stopped route's request, under the manifest's `max_depth`, `baseline_max_work` and `time_ms` and the chain run's work budget (below), with proof agreement on every part.
It matches the first step at every configuration it reaches, and each later step with the values earlier steps bound substituted for the variables it shares, so a step's `requires` may name them.
Per path it keeps the partial occurrences later steps can still complete, each by the step it awaits and the values later parts need.
A single pattern keeps the search on a corpus without `[stop]`.

**Answers.**
- `hit`: some path completes the chain, each step's configuration decided, shown to exist and holding no term-level `\and`, the path's diagnostics up to the last step's configuration carrying nothing but values the definition leaves open, and the run left no hook application unevaluated. An `unless` needs no configuration shown to exist: a configuration that denotes none lies on no path.
- `no`: the stopped route's premises of a `no`, with the chain's matcher in the pattern's place (no step's or `unless`'s match left undecided, no path beyond the cap below, no stop for lack of native stack and no undecided solver answer of the matcher), and the premises every route shares: data and a `comparable` baseline run.
- `unknown` otherwise, with the first missing premise in `cause`. Beside the stopped route's causes a chain has `undecided-match` with `undecided-step at step N` (a step's match at some configuration was undecided, so the partial occurrence was not extended by it) or `undecided-unless at step N` (an `unless`'s match at a configuration between two steps was undecided, so the partial occurrence was dropped, and it never makes a hit), each with k-rust's reason and count; and `chain-partial-cap` (some path kept more partial occurrences than the cap). The cause of an undecided part whose `requires` names a variable that neither its cell patterns nor an earlier step binds says how to bind it.

A chain is one obligation of the corpus, with one `[query]` row whose witness is a program that hits it: the witness rule, `programs`, `expect = "no"`, `--full` and `--locked` treat it as they treat a single pattern ("The obligation and its witness").

**The witness** of a hit is `{depth, state, bindings, rules, rendering, note, steps}`.
`depth` and `state` are the last step's, printed with the cells that step names in full.
`bindings` holds every variable of the steps you wrote, once each.
`rules` is null: the run reports the configurations of the completion, not the rewrite steps between them.
`steps` holds each step's `{step, depth, state, bindings, rendering}`, its state printed with the cells that step names in full, and its bindings those of its own variables (a variable an earlier step bound is that step's).
The witness is the first completion the run finds in its depth-first order, and on its path the one whose last configuration comes first: a function of the definition, the program and the budget.

**What it costs.**
At each configuration the run makes one match of the first step, one per partial occurrence its path keeps, and one per `unless` such an occurrence awaits, each twice under proof agreement.
A path keeps at most 256 partial occurrences, a constant of kink that the answer's key names; beyond it the largest are evicted, an evicted occurrence never makes a hit, and a `no` becomes `unknown` (`chain-partial-cap`).
A chain whose steps share no variable keeps at most one partial occurrence per step.
The run merges two configurations only where their paths' partial occurrences agree, so it can explore more configurations than the program's run without the chain, and so more than the program's baseline run, which completed.
A chain run is therefore a run of the program other than its baseline, as a mutant's run is, and it has a mutant's work budget: at most `max(work_factor × P, P_max)` polls, `P` the polls of the program's baseline run and `P_max` the largest of the corpus's comparable programs (`budget.work_factor`), on every corpus.
A stop ends each path at its last stop event, but bounds neither a path that meets no stop event before `max_depth` nor the number of paths, so with `[stop]` too the budget is the run's counted bound of its total work when `baseline_max_work` is absent.
`baseline_max_work` still bounds the run where it is set, and the run ends at whichever bound it reaches first; both are counted.
A run a bound cut is `unknown` for the work bound (`incomplete`: a `poll-bound` leaf, whose cause names the bound and `[budget] work_factor`, as `the chain run used more than 5 × the program's baseline's 1234 polls (6170), its work budget ([budget] work_factor)`; or a `work-bound` one, naming `baseline_max_work`), not for the chain; a hit found before the cut stands.
The bound of polls stops the run at the same poll on every host, so such an `unknown` is a function of the answer's key, which names the bound, and is cached; raising `work_factor` asks it again.
A program whose baseline is not comparable has no `P`, and its bound is `P_max`: a hit within it stands, and a `no` is withheld anyway for its baseline.
A corpus none of whose programs has a comparable baseline gives no bound, and its chains are `unknown` (`no-work-bound`) without a run: a run bounded by `time_ms` alone would answer what the host allows.
Where the clock stopped a baseline run of the command, a faster host could count its polls and give another bound, so an `unknown` the budget decided has `clock_stopped` `baseline` and the lock keeps the obligation's recorded value.
The run does not stop at its first completion: a check costs about one run of the program, with its matches.

**The key** of a chain's answer is a single pattern's with `lowering` `kink-flow/chain-lowering/v1`, `pattern` the chain's digest (each part's compiled target and generated variables; not the text's layout, the id or the note), `modality` `{route: "chain-run", search_type: "all", result_modality: "state-set", partial_cap}`, `stop` the program's stop, null on a corpus without `[stop]`, and the budget's `max_polls`, the run's bound of polls.
A chain's key never equals a single pattern's, and its records are kept beside the single patterns', under the chain's digest.

### How it runs, and what it costs

Each pattern is compiled once, by k-rust's own compiler of search patterns (`kompile::compile_search_pattern`, the one `krun --pattern` uses), against the compiled definition the programs run on.
Each asked (pattern, program) is one k-rust `search_pattern_kore` from the program's initial configuration: search type all (every reachable configuration, the initial one included), state set (each distinct configuration of a depth once), at most one result, the manifest's `max_depth`, under a watchdog of `time_ms`.
k-rust's search has no work budget yet (a k-rust request, KINK-24, would make a bounded answer reproducible), so `time_ms` is what stops a program that does not end.
A check costs about one plain run of the program (release build, shared host at load 9-24; flow F-18 handoff): where the search explores every configuration it took 1.0-2.3 times the program's baseline run (`examples/imp` sum 6 ms against 3, primes 12 against 8, collatz 20 against 10; IMP++ primes 98 against 43, collatz 93 against 48, spawn 2.5-2.9 s against 2.5 s), and much less when the hit comes early (an interleaving of IMP++ spawn found at depth 39 in 0.32 s, against 2.5 s for the run).
The search keeps every configuration it reached with the trace of one run to it, which added at most 45 MiB to the process's peak (IMP++ primes 153 MiB against 109 MiB).
The admission of the specification (about 1 s per command on IMP) costs more than most checks, and a cached answer costs no search.

### The cache, `--verify` and trust

Only a `hit`, a `no` and a chain's `unknown` its work budget decided ("Chains") are cached, one record per (pattern, program), `patterns/<execution digest>/<pattern digest>/<program digest>.json` in the cache directory:
`{schema: "kink-flow-pattern", key, pattern_id, program_id, answer, witness, baseline_run_sha256, cause, record_sha256}`, a hit's `witness` its facts `{depth, state, bindings, rules}`, the state and each binding's variable and value as whole KORE text, and `cause` an `unknown`'s, null otherwise.
The key is `{schema_version: "kink-flow/pattern-answer/v10", lowering: "kink-flow/pattern-lowering/v1", k_rust_revision, kink_build, kink, execution, program, pattern, budget, modality, stop?}`, `stop` on the stopped route only ("A corpus with `[stop]`"; a chain's key, "Chains"):
the execution digest (`{kind, digest}`, the result cache's: the loaded definition without positions, so a comment or layout edit keeps every answer), the program digest (its text, start sort and variables), the pattern digest (its compiled KORE target, not its id or its text's layout), the budget as the result key holds it, the search's modality, kink's build (any rebuild misses) and its semantics identity.
A record is used only when its key is exactly the current one and its `record_sha256` recomputes; a cached `no` also only while the program's current result is `comparable` with the baseline run digest the `no` was given against.
A used record is judged again with the current command's facts (the definition's exclusions on this command's load, the initial configuration's, the baseline class, the profile), so it never answers more than a live search would.
Editing the meaning of the specification, the program, a bound of the budget (not `time_ms`: a stored answer is a hit, the `no` of a complete exploration or a chain run its bound of polls cut, none of which the clock decided) or the pattern, or rebuilding kink, recomputes the answer; any other `unknown` is recomputed every time.

A cached answer stands without a search. It rests on the integrity of the cache directory (whoever can write it can forge an answer, as for every kink cache) and on the key naming every input; not on k-rust's determinism: a `hit` and a `no` are facts about the definition and the program, which a later search can fail to re-derive (an unknown) but cannot contradict.
A cached chain `unknown` claims nothing about the chain: it withholds an answer, and that a run under the same key withholds it too rests on k-rust's count of polls being a function of the request (k-rust `docs/compatibility.md`, "Poll budget"), which `--verify` re-derives.
`--verify` searches every selected (pattern, program) live, compares each with the stored record a command without `--verify` would use (the answer, and for a hit the witness's facts: its `depth` and whole `state`, and its `bindings`, `rules` and a chain's `steps` where both sides carry them: absent bindings and the null `rules` of the stopped and chain routes are not compared, and the printing never is), lists every difference in `mismatches` (`{pattern, program, record, cached, live}`, each witness as its facts, whole KORE text, since two witnesses can differ in a cell the printing shortens; the row's `verify` is `match` or `mismatch`), writes no pattern record, and exits 1 on a difference; it also updates the results with `--verify` (which writes a result record for a program that has none).
Each live answer is judged with the program's live baseline run, not with a stored result record that `--verify` found different, so the printed answers are those of this command's own runs; a stale result record shows as a mismatch of the results, and the command exits 1.
The cache is on in both profiles: under Z3 the search's solver queries are resource-bounded, and the key's budget names the units and the Z3 build.
It is off where tier 1 is (a solver the clock bounds, a Z3 build that cannot be named) and when the executable cannot be read (`pattern_cache.enabled` false, with the reason).

What every answer trusts, besides the cache:
- k-rust's search is sound and exact for "some reachable configuration matches" under the state set (re-pin M-2 found the same distinct states and hits by stepping on IMP and IMP++; `tests/query.rs` walks every fixture program's states one step at a time and requires the same answers);
- k-rust's parser and pattern compiler decide what a pattern denotes;
- the baseline's own claims (`total`, `preserves-definedness`, lemmas) are trusted, as for every baseline run. A contradiction k-rust detects does not end its path: since k-rust KINK-18/2 a path whose decisions rest on one goes on, and carries a `contradicted-claim` record on its states and matches (k-rust `docs/compatibility.md`, "A contradicted `total` attribute is named, not repaired"); a hit needs no diagnostic on the match or its path, so a witness whose path rests on a detected contradiction is `unknown`, and a record on the baseline run, on a leaf or (since re-pin adoption A-1) only on its `contradictedClaims` list (work that ended on no leaf, the load), makes the program not comparable, so no `no` is given there. A record only on a search's `contradictedClaims` list is not read yet (re-pin adoption A-2 reads it): it rests on the baseline's claims, which are trusted;
- k-rust's `unsupportedHooks` and `allowanceRefusals` lists of a search name every hook application it left unevaluated (a hit and a no each need both empty);
- the operation record of a search counts every undecided answer the solver gave it ("Undecided solver answers", above; a no needs the count zero), and Z3's decided answers are true of the definition's translation, whose `smt-hook` and `smt-lemma` claims are trusted as the baseline's other claims are;
- k-rust's `ground_defined` decides that a matched configuration's term is defined: its definedness walk, which skips a subterm whose stored `ceil_free` attribute holds (k-rust checks that shortcut against the walk without it on generated terms, and in debug builds at every subterm it skips) and discharges an irreducible `value-production` application through k-rust's instance-normality scan, a partial application through an unconditional ceil equation, and a sort projection on its exact image or a one-constructor field through its observation catalog; the definition's `total` and `value-production` declarations and its ceil lemmas are among the trusted claims above, and so is a lemma that states a product field's equation;
- a search does not count the stops for lack of native stack it dismisses while it only refines a result (k-rust `docs/compatibility.md`, "Execute"). k-rust states at every such site a search reaches that the kept result is sound (a definedness condition left unsimplified, a fold forgone), so such a stop can leave a step or a match undecided (an unknown) but cannot make a decided match or a completed exploration false: whether an answer is definitive can depend on the host's stack, its truth cannot. A `no` also requires the baseline run's own count to be zero.

**Answers never decide a mutation.** No answer enters a result record, an outcome record, the `[run]` or `[coverage]` section of a lock or a run document (the `[query]` section records each obligation, which no other command reads), and `run` does not read the pattern cache: a kill needs the final configurations to differ, and a pattern-only difference stays unknown by design.

Exit status ("Exit status"): 0 when every asked (pattern, program) got its answer, `hit` or `no`, and every `expect` is met (an `open` or `undecided` obligation is no finding);
1 when a claim is refuted, an `expect = "no"` is unmet, `--verify` found a difference, or `--locked` found that the query would change the `[query]` section (a witness whose program is gone, a status that moved);
3 when an answer is `unknown`, an `expect` is inconclusive, or under `--locked` the only differences rest on runs the clock stopped;
2 when an answer is `invalid-pattern` or `error`, the manifest, the pattern list, the lock, the specification or a program is refused, a record or the lock could not be written, or on a usage error (an `--only` id that names no pattern, an option given twice, `--locked` without `--lock`).

## Redundant programs: `kink-flow prune FLOW.toml MUTATIONS [PATTERNS.toml] [--full] [--lock FILE] [--compile-workers N] [--progress] [--cache DIR] [--output json|text]`

`prune` reports which programs of the corpus are redundant.
It writes no lock and edits no file; it reads and fills the caches as `coverage`, `run` and `query` do, and stores no run report, so `report` and `fuzz --kill` keep reading the last `run`'s.
`--output text` prints a summary for a reader.

The report is of one flow.
A flow that names its corpus root (`[corpus] root`, "The corpus root") reads cases that other flows may read, each against the obligations of its own definition, and a case is removable from the root only when the cases kept discharge every flow's obligations.
The document of such a flow says so: `scope`, `{flow_only: true, corpus_root, detail}`, with the root as the manifest writes it, and `--output text` prints the detail as a `note:` line after its first line: the report holds for this flow alone, and a case redundant here may be the only discharger of another flow's obligation.
The document of a flow whose cases are in its own directory has no `scope`.

### The obligations

A corpus discharges existential obligations, each of the shape "some program does X":

| Family | An obligation | Its dischargers | Its unknown cells |
| --- | --- | --- | --- |
| `mutations` | each mutation a program can kill (`killed`, `survived`, `timeout`, `unknown`) | every program whose cell of the kill matrix is a proved difference (`killed_by` of `run --full`) | the programs whose executed entry is neither `agree` nor `distinguish` (the kill matrix's `undecided`) |
| `patterns` | each pattern, with or without `programs` ("The obligation and its witness") | every program whose answer is a hit (`hitters` of `query --full`) | `unanswered`: neither a hit nor a final `no` |
| `rules`, `requirements`, `syntax`, `rule_windows`, `syntax_paths` | each item the family counts, but a unique-cause requirement | when covered, the programs its covering list names (`fired_by`, `covered_by`, `reached_by`) | a requirement's `undecided_by`; a field value's binder's `truncated_by` |
| `requirements`, unique-cause level (`[coverage] mcdc`) | each unique-cause requirement | a pair of programs together ("Pair obligations" below) | the programs whose record left a combination out (`truncated_by`) or holds a combination with an undecided outcome or truth |
| `flips` | each flip kink's verdict makes one (`distinguished`, `undistinguished`, `unreached`, `unknown`) | its `killer` | its `causes` and `timed_out` programs |
| `arguments` | each argued item whose invariant evidence `holds` | the programs whose run read a step of the item's rules (`stepped_by`) | none |

Each item of the coverage families but a unique-cause requirement is covered by one program's own run or record: a rule's firing, an outcome class of a condition or of an operand, a production or field value a fired instance touched, a window one path took as consecutive steps, a syntax path one fired instance touched, a flip's killer, an argued item's stepped rule.
An unknown cell never discharges.
An obligation no program of any corpus can discharge (an `equivalent`, `unkillable`, `not-admitted` or `invalid-mutation` mutation, a refused or equivalent flip, an out-of-scope rule) is none.
A flip's kill search stops at its first killer, so its killer is its only decided discharger.

The report is computed, never read from a stored document, since a stored document can be stale: `prune` runs `coverage` (tier 2, the flips where the front end derives them, each flip's killer read from `--lock`'s `[coverage]` section), then `run`'s first-kill search of the mutation list and `query`'s walk of each pattern to its first hit, and asks each further cell of their rows only where a decision needs it ("Lazy cells" below); with `--full` it runs `run --full` and `query --full` instead.
Each runs in process, through its own command's code and caches, so the report is a function of the definition, the corpus and the counted budgets, as their verdicts are; the document's `mode` is `lazy` or `full`.
A family whose input is absent is skipped, and `families` says so (`run: false`, `reason`): `no-mutation-list` where a front end's layout has none, `no-patterns` where no pattern list is named and the manifest declares none, `not-computed` for a coverage family the document does not compute (a depth-dependent family at depth 1, the flips without a front end that derives them).

Each `families` entry of `mutations` and `patterns` names the list it read (`list`: `{path, corpus_own}`, `path` null for the patterns the manifest declares or a family with no list).
The report holds for the lists it read: with a mutation list other than the corpus's own, a program removable here may be the only killer of a mutation the corpus's own list has.
Only a front end with a corpus layout knows its corpus's own lists, so `corpus_own` is `true` or `false` under `krs kink prune` (a list `--mutations` or `--patterns` names is the corpus's own only when it is the layout's file), and null under kink-flow's own command line, which takes the mutation list as an operand; `--output text` prints a `note:` line for each list that is not the corpus's own.

### What is never prunable

- A program a claim names: a pattern's `programs`, since removing it makes the pattern list refuse (`no program of the manifest has the id`). Nothing else of the manifest, the mutation lists or the pattern lists names a program: a mutation's `expect` states a verdict, not a program.
- A program whose decided cell refutes a universal claim, since removing it would hide a finding: a killer of a mutation that expects to survive, a hitter of a pattern that expects `no`, the program whose run gave an argued item's evidence its failing state, a program whose own expectation is unmet.
- A program that is the only decided discharger of an obligation; of a pair obligation, a program without which no decided pair discharges it.
- A program whose cell on an obligation is unknown while no other program discharges that obligation: removing it could lose the only potential discharger.
- A program whose decided combination is a side of a pair obligation that no decided pair discharges without it, while another program's cell on it is unknown or its baseline undecided (`unknown-partner`): what that program holds may be the other side of a pair with it.
- A program whose baseline is `timeout` or `unknown` while some obligation has no decided discharger: kink asked it of no mutant and no pattern, so each of its cells is unknown.

So the report only ever under-states what is prunable.
`unanswered` counts the unknown cells (`cells`) and lists the programs with an undecided baseline (`undecided_cases`).

### Pair obligations

A unique-cause requirement ("Unique-cause MC/DC") is covered by two valuation combinations, one where the condition held and one where it was refuted, in which its atom has the two truths and every other atom the same decided truth.
Two programs' records may give the two, so its `covered_by` (both sides of the one `pair` the item shows) is not a list of programs each of which discharges it alone: where only `x` holds one side and only `y` the other, both are kept.
The obligation holds over a set of programs when some pair of the rule's combination rows (`guard.combinations`, every pair they give, not only the item's `pair`) has a program of its held side and a program of its refuted side in the set; one program may be on both sides.
The pairs are of decided combinations (a decided outcome, the atom two-valued, every other atom decided).
A program's cell is unknown where its record may hold a combination the rows do not show: it left one out (`truncated_by`), or one of its combinations has an undecided outcome (`undecided`, `stopped`) or an undecided truth, the atom not undefined.

The rules above read "a decided pair holds" where a single-program obligation reads "a decided discharger is kept":

- `sole-discharger`: a decided pair holds over the programs considered and none holds without the program;
- `unknown`: no decided pair holds without the program, and its cell is unknown;
- `unknown-partner` (`with`): no decided pair holds without the program, its combination is a decided side, and the programs `with`, considered, have an unknown cell or an undecided baseline: a combination one of them holds may pair with it;
- `baseline-undecided`: no decided pair holds without the program.

No unique-cause outcome refutes a universal claim: the requirement states no expectation, and `open` or `undecided` states only that no recorded pair discharges it.
Removing a program no rule keeps loses no pair that may hold: either a decided pair holds without it, or no decided pair holds and none that may hold uses it, since its cell is decided and none of its combinations can meet an unknown one.
The walk below keeps every decided pair that holds over the corpus, since a program whose removal would break the last one is its sole discharger; where none holds, it keeps every program with an unknown cell or an undecided baseline, and, where there is one, every program with a decided side.
The coverage rows are complete in both modes, so the lazy report and `--full` read the same pairs.

### Redundant alone, removable together

A program is redundant alone when no rule above keeps it against the whole corpus: every obligation it discharges has another decided discharger, and every obligation on which its cell is unknown has a decided discharger.
Two programs can each be the other's only alternative, so being redundant alone is not being removable together.
The report gives both:

- `redundant`: each program redundant alone (`{case, class, obligations, unknown, unasked, removable, kept_for, lock}`), with each obligation it is known to discharge and the other known dischargers (`obligations`, `{family, id, others, complete}`), each obligation on which its cell is known to be unknown with its known dischargers (`unknown`, `{family, id, dischargers, complete}`), a pair obligation's entry in either naming instead the pairs that hold without the program (`{family, id, pairs, complete}`, each pair `{held, refuted}` with its sides' other programs), how many obligations its own cell was not asked on (`unasked`), whether the removable set removes it, and, where it does not, what kept it when the walk reached it (`kept_for`); `complete` is whether every cell of the obligation's row was asked, so that `others` (`dischargers`) is every one;
- `removable`: one set removable together (`{order, cases, lock}`), built by walking the programs in reverse manifest order (`order` `reverse-manifest`) and removing each program the rules above, read against the programs still kept, keep nowhere;
- `kept`: each program that is not redundant alone (`{case, class, reasons}`), each reason `{reason, family, id}` with `reason` one of `claimed` (the family `patterns`), `refutes` (the claim's family, `expectations` with the program's own id for its own expectation), `sole-discharger` and `unknown`, or `{reason: "unknown-partner", family, id, with}` (a pair obligation), or `{reason: "baseline-undecided", class, obligations}`.

Every list is in manifest order.
After the walk each obligation keeps a decided discharger among the kept programs (a pair obligation, a decided pair), or every unknown cell it had.
The order is reverse manifest order because a command that names one discharger names an early program: a mutation's killer is the first killing program of the search order, whose groups are each in manifest order, and a pattern's witness the first hitter in manifest order, while no record names another.
Removing the latest programs first keeps those, so the corpus record's rows move least.
The set is a function of the corpus and of this order, maximal under the order (no kept program can then be removed), not minimum: a smallest removable set is a set cover problem, which `prune` does not attempt.

### Lazy cells

The rules above read three things of an obligation's row: whether a decided discharger other than the program judged is among the programs considered (the whole corpus for redundant alone, the programs still kept during the walk), the program's own cell, and, for a claim a cell refutes, every refuting program.
None needs every cell, so without `--full` the `mutations` and `patterns` rows are asked lazily, with every decision (`redundant`, `removable`, `kept` with its reasons) the one `--full` gives:

- The ordinary searches run first: a killed mutation's first-kill search gives one decided killer and the cells it asked before it, and a hit pattern's walk one hitter and the pairs it asked.
  Every other row (survived, unknown, open, undecided, or no obligation) is one the search asked of every program it can ask, so it is complete, as under `--full`.
- While some known discharger other than the judged program is among those considered, no other cell of the row can change the decision: the judged program is then not the only discharger, and the unknown and baseline-undecided rules apply only to an obligation with no other decided discharger there.
- When none is, the row's cells over the programs considered that were not asked are asked one at a time (a mutation's in its search order, the programs that witness its edit first; a pattern's in manifest order) until one is a decided discharger or none is left, then the judged program's own.
  So judging a killer alone asks for a second killer, and the walk asks again only where it removed the known one.
  Each cell is asked through the code its full command asks it with: a mutation's full row over the one program, under the corpus's floor of polls, served by the outcome cache when its record is current; a pattern's one row, served by the pattern cache likewise.
  `--lock`'s records only order the searches (each recorded killer and witness first); none is read as a cell.
- A mutation that expects to survive and is killed, and a pattern that expects `no` and is hit, keep every refuting program: their rows are asked whole.
- A program that is not redundant alone is kept by the walk with nothing asked: a rule of a single-program obligation only weakens as the programs considered shrink, and a pair obligation's rules keep, at each step of the walk, every program they keep against the whole corpus ("Pair obligations").

The evidence then holds the cells asked: `others` and `unknown` are the known ones, `unasked` counts the obligations a program's own cell was not asked on, and each family's and `unanswered`'s `complete` say whether every cell was asked; `limits` adds `lazy`.
A distinguished flip's row is never complete in either mode, since its kill search stops at its first killer.
`accounting.cells` gives each family's matrix size (`matrix`: the list's mutations by the comparable programs, the patterns by the programs), the cells the ordinary search held (`searched`), and those asked one at a time after it (`asked`, of which `from_cache` a cache served).

### The corpus record

`--lock FILE` names the corpus record, which `prune` reads and never writes; its `[run]` killers and `[query]` witnesses also order the lazy searches.
A removable program that the record names as a killer (`[run]`, a `[coverage]` flip), a witness (`[query]`) or the program of a compare row (`[compare]`) moves those rows when it is removed: `--locked` fails once, until a command without it records them again.
Each `redundant` entry's `lock` and each `removable.lock` entry name those rows by section (`{run, coverage, query, compare}`, null where none); the document's `lock` names the file and the sections it holds.

### Exit status

0 when the report is computed, also when unknowns made it conservative: every set it states holds, and the unknowns only keep programs, so the report is an answer, not the absence of one (3).
2 when the question could not be asked: a usage error, a list or lock that does not decode, or a family whose own command would exit 2 (a refused specification, program, mutation or pattern, a corpus or infrastructure error), named in `refused` (`{family, detail}`) with that document's `spec`.
Never 1: the report refutes nothing.

### Cost

`prune` costs a `coverage`, a first-kill `run` and a `query` (no explanation), plus the cells its decisions ask after them.
Each killed mutation asks at least one more cell, its second killer, and a mutation with one killer asks its whole row to show it; a cell a later decision needs (the walk removed the known second killer) is asked then.
Each cell asked live is one call over one program, which compiles the mutant unless more than one compile worker keeps it compiled ahead for the mutation's next cell; a cell whose outcome record is current is read with no call.
`--full` costs `run --full`'s cost model ("Cost model") and a `query --full` (every pattern of every program).
Either mode reuses every cell an earlier command cached, whatever its schedule, since an outcome record does not name the schedule, and a later lazy `prune` asks the same cells in the same order, so it runs no mutant once they are cached.
On the six-program, four-mutation corpus of `tests/prune.rs` with a fresh cache, the lazy `prune` holds the first-kill search's 9 cells and asks 6 more (the second killer of each of the three killers, and the 3 kept programs' cells that show the one killer left once the walk removed the other), 15 of the 24, and of the 12 pattern cells 9; a `prune --full` after it reads those 15 and writes the other 9.
`accounting` gives what each family read and wrote (`mutations.outcome_cache`, `patterns`, the baseline runs, `cells`); it is how the facts were obtained, not part of the report.
### Limits

`limits` lists what the report does not read: `[[implementation]]` compare evidence and a case's own expectation, which are universal per program, not existential (an unmet expectation still keeps its program, and removing a program drops its `[compare]` rows); a fuzz template list, whose templates may name a program (`program`); and that a flip's killer is its only decided discharger and the removable set is maximal, not minimum; a lazy report adds `lazy`, that its evidence holds the cells asked.

## Killing a survivor with `fuzz`

```text
kink-flow fuzz FLOW.toml TEMPLATES.toml --template ID (--kill MUTATION --mutations MUTATIONS.toml | --matched RULE | --fired RULE | --refuted RULE | --cover ITEM | --pattern ID [--patterns PATTERNS.toml]) [--cases N | --work W] [--seed S] [--max-work N] [--time-limit-ms T] [--stack-stops N] [--open-stops N] [--assume-joined NAME]... [--one-path] [--cache DIR] [--no-confirm] [--no-filter]
```

When a mutation survives or is unknown because no corpus program tells the two definitions apart, write (or pick) a program that matches the edited rule (a mutation's `witnesses` are such programs), mark its literals as holes, and let `fuzz` look for hole values that kill the mutation.
It runs a k-rust-fuzz campaign in process on kink's own two sides, confirms the candidate with kink's own code, and prints the program as a `[[program]]` fragment for `FLOW.toml`.
The same command can also look for a program that matches or fires a rule, or hits a pattern ("Covering a rule and hitting a pattern" below).
A mutation expected to survive (`expect = "survive"`, a control) is not refused: a search for its kill is the most direct attempt to refute the control's claim, so the document warns `expected-to-survive` before the search, and a witness kink's own run confirms, on the flow as it stands, is a finding (exit status 1), a program on which what the edit changes is observable.
A witness `--no-confirm` left unconfirmed, or one whose kill rests on a premise `FLOW.toml`'s `[spec] assume_joined` lacks, is only a candidate: the corpus as it stands has not been shown to distinguish the mutant, so the claim is neither refuted nor confirmed (exit status 3), and the `action` says what is left to decide.
k-rust's [docs/fuzzing.md](../../../docs/fuzzing.md) is the user guide: it walks through the three jobs on `testdata/flow/fuzz/imp` and `impu`, how to choose a template, and how to read the document; this section is the reference.

### `TEMPLATES.toml`

```toml
[[template]]
id = "primes-holes"        # unique, non-empty
program = "primes"         # a [[program]] of FLOW.toml (its text, start_sort, variables and stop_count), or:
# file = "templates/straight.imp"   # relative to this file's directory, inside it
# text = "int x; x = 5;"
# start_sort = "Pgm"       # with file or text; default: kink's (the program position of $PGM's sort)
# variables = { IN = "3" } # with file or text, as in [[program]]
# stop_count = 2           # with file or text, as in [[program]]: the stop event its runs end at

  [[template.hole]]        # krust fuzz's [[hole]] keys (crates/k-rust-fuzz/README.md, "Hole declarations")
  name = "T"
  sort = "Int"
  find = "t = 1;"
  literal = "1"
  range = { min = 0, max = 3 }
```

- Decoding is strict, as for `FLOW.toml`: an unknown key, a value of the wrong type, a duplicate id, a template with not exactly one of `program`, `file` and `text`, or a path leaving the directory is an error naming the key.
- Each `[[template.hole]]` is decoded by k-rust-fuzz's own decoder, so a hole means what it means for `krust fuzz`; its messages are prefixed with `template "ID".hole[INDEX]`. A span hole addresses the template's text (leave `program` out); a `config-var` hole makes a whole configuration variable the hole. `program = "$NAME"` puts a span hole inside the text of the template's variable `NAME` (k-rust-fuzz's witness carries each binding as instantiated, `config-vars`, and the fragment writes it). A TOML date is refused.
- Mark every data literal: in TRIAL2 the killing value was usually one nobody would have guessed (`t = 0` in `primes`). A template is not a corpus program: it gets no record, and nothing is cached for it.
- `testdata/flow/fuzz/imp` (TRIAL2's IMP thin corpus, its survivors, their templates and a pattern) and `testdata/flow/fuzz/impu` (three unmatched rules and templates that match them) are complete examples; the user guide runs every command it shows on them (`tests/guide.rs`).

### Killing a flip

`--kill FLIP` names a condition flip of `coverage`'s flips family where no list holds the id: `--mutations` names a list, whose mutation the id then is, and without it the front end's own list names the mutation only where it holds the id.
The front end derives its flips (`FrontEnd::derived`; "Flips" under `coverage` above), and the job fuzzes an admitted flip's edits as a kill job of a one-mutation list (`job.flip` true): its confirmation is kink's own `run` of the flip on the flow with the candidate alone, its template's class is read from the last run document, which has no row for a flip, and each next step that would run `run` runs `coverage`, whose flips family runs the flip's kill search.
A flip the front end's judge refused has no mutant: the job is refused at stage `mutation`, with `job.status` `refused`, the judge's reason and detail, and its next step in `action`.
An id that is neither a mutation of the list nor a derived flip is refused (`unknown-mutation`), the detail saying what the list and the derived flips hold, and why the flip is not generated where the flips' `not_generated` names the id; kink-flow's own front end derives no flip, so with no list the detail says why.
A flip that changes only sentences outside the coverage scope (claim helpers) is not generated, as `coverage` lists it, so its kill job is refused the same way once the specification is admitted.

### Covering a rule and hitting a pattern

`--matched RULE`, `--fired RULE`, `--refuted RULE`, `--cover ITEM` and `--pattern ID [--patterns PATTERNS.toml]` replace `--kill`; every other option applies, and the job runs on the baseline alone (its exclusions, its assembly, its findings).

- **A rule job** looks for hole values whose program `coverage` would list in the rule's `matched_by` (`--matched`) or `fired_by` (`--fired`), each flag named by the predicate it targets ("Coverage predicates"); before document version 6 they were `--reach RULE` and `--reach RULE --fired`. `RULE` is `FILE:LINE` (any line of an authored rule of `FILE`, a source of the specification, or a suffix of its path after a `/`), the rule's label (bare, or `MODULE.x` when the bare label names several rules), or a 64-hex compiled id. The rule's ids that k-rust's run coverage can name (the coverage domain `coverage` reads) must hold exactly one rewrite axiom, the target; equation ids of the same sentence are listed as `untargeted_ids`. Refusals before any case: `no-rule-at-line` (its detail lists the five rules of the file written nearest the line, or the files that hold rules), `unknown-label` (the labels that contain the reference or that it contains, at most five), `ambiguous-label`, `ambiguous-rule-position` (the rules named), each listed rule with its position, label and the ids a rule job can target, `unknown-rule-id`, `no-authored-rule` (a compiled id that no authored rule of the specification wrote, such as a prelude rule's: `coverage` lists programs under authored rules only), `no-coverage-signal` (a macro, alias, smt-lemma or non-executable rule), `equation-target` (a function rule) and `several-rewrite-ids`. kink counts a program in `matched_by` and `fired_by` only when its all-paths baseline run is comparable, so the hit's run of every path must be comparable too (k-rust-fuzz's `comparable` option: complete, clean, data ends); the program must end naturally. A definition with a finding no name assumes makes the job `not-comparable`, as for a kill.
- **A coverage-gap job** looks for hole values whose program covers one open obligation of `coverage`'s tier-1 families: `--cover ITEM` names it by its id (a target's `item`: `requirement:<rule>:<node>:<truth>`, `requirement:<rule>:held` or `:refuted`, `syntax:<production>`, a front end's field value, `rule:<rule>` or a heating rule's `rule:<production>:heat:<position>`), and `--refuted RULE` names `RULE` as a rule job does and covers its requirement `requirement:<name>:refuted`, the run that refutes its condition on some entry. Every open obligation's target spells its job in `fuzz`, except a unique-cause requirement (a pair of entries covers it, which no one run states) and a field value whose item names no binder. The obligation is looked up among the specification's obligations with no program (each family's universe is a function of the definition), and stated as the facts of a run's records that cover it, any one of which suffices: for a requirement, its node reached with the truth at the node's path in the written `requires`, or the condition's `held` or a refutation as the guard outcome (where a front end groups the guard, the author's condition: its last authored conjunct `true`, or an authored conjunct `false`); for a production, an operand head of a fired instance of a counted sentence, or the firing of an axiom alternative that inspects or builds it; for a field value, a fired instance's binding of the item's `binder` to one of its encodings; for a rule or a heating rule, its firing (a rewrite rule's committed step, an equation's applied instance). The campaign is a k-rust-fuzz coverage target over those facts, judged from the guard outcomes, bindings and committed transitions k-rust records, the records `coverage` reads; as for a rule job, the hit's run of every path must be comparable. Its distance is how near those records come to a fact: the guard's recorded truths against the valuation that reaches the node (the branch distance of the condition records), the bound values against the encodings, and the rule-graph distance to the fact's rule otherwise, which k-rust-fuzz's climb follows beside blind sampling (the other jobs sample blind alone). The confirmation is `coverage` on the fragment, read as the front end names the obligation: the program is comparable and the item lists it as covering (status `covered`, `not-covered` or `not-comparable`). Refusals before any case, at stage `item`: `unknown-item` (with the ids that contain the reference or that it contains), `mcdc-requirement`, `no-requirement` (`--refuted` of a rule whose condition states none), `no-obligation`, `no-binder`, `no-skeleton`, `no-syntax-facts`, `no-fact`; `--refuted`'s rule refusals are the rule job's. The document's `job.item` is `{id, family, kind, file, line, facts}`.
- **Pattern** looks for hole values whose program reaches a configuration matching the pattern named `ID`, of the list `--patterns` names, else of the patterns `FLOW.toml` declares ("Declared patterns"), as a `query` `hit`: matched at every configuration of every path (k-rust-fuzz's `at: any-state`), with every fact on which a complete search could stop refused (`query-confirmable`). The pattern is first lowered exactly as `query` lowers it; an invalid one is refused (`invalid-pattern`, with k-rust's message) before any campaign. A pattern reads no data end, so it takes no assumed name: `--assume-joined` is a usage error, and the flow's own names are not passed.
- The action names kink's confirming command: `kink-flow coverage` for a rule or coverage-gap job, and for a pattern, adding the fragment's id to the pattern's `programs` and running `kink-flow query --only ID`.

### What it runs

- **Sides.** The baseline is the admitted specification's compile, with its claims. The mutant is the claim-free, consistency-checked mutant kink's runner builds for every test of the mutation (kink-campaign `claim_free_mutant`, admitted with the flow's `[spec] assume_joined`). Both run on the backend route kink runs (`Backend::from_definition`). A mutation `run` would refuse (`invalid-mutation`, `equivalent`, `not-admitted` with its reason and `inconsistent_pairs`, unsupported claims) ends the command with that status and reason; nothing is fuzzed. So does a mutation `run` decides from its edit alone, on a baseline whose findings are all assumed (`run` step 2): `unkillable` (reason `weakening`) or `equivalent` (reason `valid-condition`) is a fact of the axioms, which no case can change, so the job is refused at stage `mutation`, reason the status, with `job.status`, `job.reason`, `job.weakening` and the row's action, exit 2.
- **Target.** The differential target on all paths (`--one-path` for one), as kink compares complete state sets: a case is a hit when the mutant reaches an end the baseline cannot or the reverse, on ends that are data.
- **Comparability is strict.** If a definition's full critical-pair check reports a finding no name assumes, the campaign is `not-comparable` and the document lists every finding (`findings`: side, name, verdict). Such a definition may identify the two ends a kill compares, so a kill there would hold in no model of it, and `run` refuses it too (`baseline-findings`). A finding is read as resolved only when you name it: the flow's `[spec] assume_joined` names are always passed, and `--assume-joined NAME` adds one for this command. A decided finding cannot be named; a genuine one can, but it is a premise known to be false, and the fragment says so.
- **Budgets.** `--cases N` (default 1000) or `--work W`, `--seed S` (default 0), the library's blind proposer. Every case runs with `[budget] max_depth`, a safety limit of `[budget] time_ms` per execution, and a work bound of `--max-work N` (default 100000). `run` bounds the mutant's run at `max(work_factor × P, P_max)` polls ("What decides a verdict"), so a kill whose mutant needs more is `unknown` there. `--time-limit-ms T` cancels the campaign's run after `T` ms (not the admission and compiles before it); a cancelled campaign is outside the determinism contract (`stopped: time-limit`). A case whose run stopped for lack of native stack (the embedded report's unjudged reason `stack-stops`) judges nothing, and no option bounds the stack: after `--stack-stops N` such cases in a row (default 25) the search ends (`stopped: stack-stops`, the embedded campaign `cancelled` by kink-flow). 25 is as many cases as the guide's trials needed to kill every killable mutation on a template whose run reached the edited rule and ended on both definitions (docs/fuzzing.md, "Choosing a template"), and none of the 25 is a case that could kill; the stop is advice, never a verdict. Of a kill job, a case whose mutant run ends holding a term not shown to exist (unjudged reason `not-ceil-free` on the mutant: an application the mutant leaves open, which no budget decides) judges nothing either: after `--open-stops N` such cases in a row (default 25, by the same argument) the search ends (`stopped: open-stops`). Both stops count cases, never time. kink-flow ends either search through the campaign's observer, which k-rust-fuzz reports as its caller's cancellation (the embedded campaign `cancelled`); the `action` says which count ended it instead. Otherwise the same inputs and seed give the same document, but for cases a clock or the stack decided: a case that `time_ms`, a solver `unknown` or a stop for lack of stack decided is outside the determinism contract (the embedded report's `totals.outside-determinism`), and since every later case depends on the cases before it, a re-run may differ from the first such case on (`totals.first-outside-determinism`, which also counts a candidate whose confirmation the clock stopped, and which the statement in `action` names); kink's confirmation runs under `time_ms` too.
- **Definition exclusions.** Before any case, kink's definition exclusions are read on both sides as kink's runner reads them (kink-native `DefinitionExclusions::of_validated`, `definition_exclusion`). One on the mutant (an edit that brings in an implementation-chosen hook, an equals condition, or a load stack stop) makes `run` report the mutation `unknown` with that reason; one on the baseline excludes every baseline run, so `run` finds no comparable program (`error`, `no-comparable-program`, each program's cause naming the exclusion). Either refuses the job with that status and reason (`job.refusal.stage: exclusions`, `job.exclusions`: each side's `{exclusion, detail}`, the detail as the check document's `spec.exclusion` gives it, or null); nothing is fuzzed. A rule the short-circuit analysis flags is none: kink's runner judges each run of such a side by its own list of short-circuit readings, so the job runs, and the witness filter keeps its static reading of the flag (below).
- **Assembly.** kink assembles every test's input from the baseline's grammar, for both sides. The campaign binds kink's stream defaults (`$IO` to `"off"`, `$STDIN` to `""`) after the template's variables, as kink does, for each stream variable the definition declares and the template leaves unbound, since k-rust-fuzz's own default binds `$STDIN` to krun's buffered `"\n"`; the printed fragment leaves these bindings out. A run of no case gives each side's initial configuration at the holes' anchors (the fuzz report identity's `initial-configuration-digest`). When the mutant's differs from the baseline's (an edit of a `[macro]` rule, or of anything the program's parse reads), the job is refused before any case (`mutant-assembly-differs`: the mutant parses the template differently from kink's input); when the baseline's differs from kink's own assembly of the template, it is refused too (`template-assembly-differs`, a defect to report). The campaign reads a configuration variable's text as krun reads `-c`, with the rule kink reads the manifest's `program.variables` with (the syntax module's grammar first wherever it has the variable's sort), so a `Word` token that the main module's scanner alone would read as another token sort is the same `Word` in the campaign and in kink. Then the candidate's program is assembled by kink exactly as a `[[program]]` (start sort, variables, the concrete-state check and the input gate), and each side's `initial_configuration` in the witness, parsed as KORE, must equal it; otherwise the candidate is not offered (`stopped: assembly-mismatch`, `candidate.assembly` says which side or kink's refusal).
- **The last run.** The last `run` document (`report.json` in `--cache DIR`, default `.kink-flow`, read as `report` reads it and only when it is of the current specification and of the corpus's programs, each id with its program digest: a row's status and `witnesses` are facts about the programs that run judged, a killer one of them) gives the template's own program class (found by its program digest) and the mutation's status and `witnesses`, each suggested as a template (`template.last_run`; `witnesses` is `null` when the last run's row is: no compiled edit of the mutation was known to it). Nothing in the cache is written.
- **Warnings** (`warnings: [{kind, detail}]`): `unusable-template` (the template's program is not `comparable` in the last run, or kink refuses the template's own input), `template-not-a-witness` (the template's program is not among the mutation's `witnesses`), `global-witnesses` (the survivor's compiled edit is not site-local, `witnesses_global`: every program, the template's among them, is a witness by default, not because its coverage reaches an edited rule, since a changed pattern can match terms no baseline run tried; given only when the template's own program's current baseline record is not `comparable` or matches none of the row's edited rules (the predicate of `coverage`'s `matched_by`, which lists comparable programs only), since its advice, to build on a program that reaches one, is otherwise already followed), `no-witness` (no comparable program witnesses the survivor's compiled edit), `witnesses-not-computed` (the last run's row of the survivor has no `witnesses`: the run neither compiled its mutant nor found its compiled edit in the outcome cache, as for a `baseline-findings` row or a row tier 1 decided from an outcome file whose `witness` it does not read, so it names no witnessing program and suggests no template; the row's reason says why), `already-killed`, `expected-to-survive` (the mutation states `expect = "survive"`: the search is not refused, since it is the most direct attempt to refute the control's claim, and a witness kink confirms, needing no premise the flow lacks, is a finding), `stack-stop` (the last run left the mutation `unknown` with reason `stack-stop`: a case on which the mutant recurses the same way is no witness, and the search ends after `--stack-stops` of them in a row; `work-budget` likewise, when the last run's reason is `work-budget`, kink's work budget having cut the mutant on every undecided program: the fuzz's own runs are not bounded by it, so a case that recurses without end stops for lack of stack and counts toward `--stack-stops`; the detail is the row's action), `open-application` (the last run left it `unknown` with reason `open-application`: a case whose mutant run ends holding the open application is no witness, and the search ends after `--open-stops` of them in a row; the detail is the row's action), `last-run-without-mutation` (the last run document is current but has no row for the mutation: it judged another list or selection, so no witness is checked and no up-front warning is given; the detail names the run of the job's own list and cache), `stale-run-document` (the last run document is of another specification, or of other programs than the corpus's, which the detail names as added, removed and changed since: `last_run` is then `{found: true, current: false}` and nothing else, so no `already-killed` names a killer the corpus no longer holds), `crash` (one per crash finding of the campaign: a k-rust or k-rust-fuzz panic or internal error during a case, kept in the embedded report's `crashes`; a crash is no kill and moves no verdict), `not-ceil-free` (one per function the embedded report names as held unevaluated in a leaf it could not judge, `not-ceil-free`, such as `plus` on a mutant whose narrowed equation leaves it open and from which kink withdrew its `total` claim; the report's statement says a warning names the function when it is known), `client-refused` (kink's rules, as the filter reads them, refused candidate hits inside the campaign, counted per cause), `witness-not-terminating` (the offered witness's run of every path was cut by a bound or a clock, so as a corpus program it may not terminate; only a pattern witness can be one), `stop-hides-edit` (a kill job's edit of a rule the stop stops before, on a template whose count is 1, "A corpus with `[stop]` or `[observe]`"), and `time-limit-scope` with `--time-limit-ms` (it bounds the campaign's run, not kink's admission, the mutant's preparation, the exclusions or k-rust-fuzz's `Campaign::new`, which builds both grammars and backends and runs both definitions' full critical-pair checks).
- **Witness filter** (fz26 FZ-COMPARABLE-B; `src/fuzz_filter.rs`). kink refuses some fuzz witnesses for reasons that depend on the input: its end check (TV-01) gives a `String` domain value a value only when its bytes are ASCII, and generated strings almost never are, so a String-hole kill used to end `unconfirmed` (TRIAL3's ASCII-STRINGS). Unless `--no-filter` is given, the campaign runs with kink's own rules as a k-rust-fuzz witness filter (crates/k-rust-fuzz/README.md, "Witness filters"), built from the loads the definition exclusions were read from and the data facts of the names kink's confirmation judges under (the flow's `[spec] assume_joined`, recomputed only when `--assume-joined` adds names). Each candidate hit and shrink candidate is judged before its confirmation and after it, in the order kink's runner judges a run: the state exclusion of the baseline side's initial configuration under each side's facts (`initial-state:<exclusion>`), each side's undefined steps under its own facts (`preserves-definedness`, `short-circuit-step`), TV-01 on every `stuck` leaf under its own definition (a `trivial` leaf needs only existence, which the fuzz's clean-leaf rule already requires, kink27 R3-UNDEF-BRIDGE, witness filter v3; `domain-value-not-ascii` for a String-like domain value that is not ASCII, `domain-value` for any other, `injection`, `not-constructor`, `overload-not-data`, `collection-untrusted`, `collection-shape`, `term-kind`, `undeclared-symbol`, `arity`), for a kill each `stuck` leaf's value under the other definition too (`cross-<test>`; an undefined step's pre-step configuration is no end and is not judged across, kink27 R1-UNDEF, witness filter v2), and nothing of the mutant run's work: kink's work budget is a bound of polls, which a case does not record, so kink's own run decides whether a kill's mutant run ends within it (witness filter v4; v3 refused a removed-end kill past a bound of states, `work-factor`). A rule job judges the baseline alone; a pattern only the state exclusion, since a query's run stops at its first match and kink's own query decides the rest. Every walk over a case's terms runs on a stack sized for them (k-rust's `with_solver_over`), and terms deeper than the largest stack the backend provides are refused `too-deep`, never an overflow of the campaign's thread. Each side's definition and solver are reached once, when the filter is built: a side that cannot be reached then, or later for any reason but stack, accepts every case for the rest of the campaign, so the judgement before a confirmation and the one after it never differ for a reason outside the case. A refused hit is no witness, and the search goes on; a hit refused only for non-ASCII String ends (every refusal of the case `domain-value-not-ascii`, so none that holds whatever the strings are) is repaired: up to two candidates replace only the non-ASCII characters of the String holes (nested ones too) by ASCII letters or digits, keeping lengths, ASCII characters and distinct strings distinct, and the first that kills the same way and passes the filter and the fuzz's confirmation becomes the witness (`repaired-from` in the embedded report). A value refused whatever it holds (a `Float` or `MInt` end) gets no candidate; a `Bytes` end is a value (kink's [`trust.md`](../../trust.md#what-a-kill-trusts), R5-BYTES-ENDS). The filter is stricter than kink where its initial-state check (on every definition) and its undefined-step check (on a definition whose short-circuit analysis flags a rule) read the analysis while kink judges each run by its own list of readings, where its work-factor check reads the fuzz's work for kink's and kink's execution request differs (both read the state set of the same request whatever its leaves since KINK-PATHSET-FALLBACK) and where it refuses a term past the backend's depth that kink's runner, judging it on no stack sized for it, may overflow on; it is laxer on a leaf that is not one decided term, on leaf diagnostics (kink makes a diagnosed leaf incomplete), on a side it cannot reach, on the mutant's single path of a `--one-path` campaign, on an added end under `work_factor`, on a `trivial` leaf kink does not show to exist, on everything after a pattern's first match, and on the run's lists of open values and of short-circuit readings, which it never sees (a flagged rule whose condition reads an undefined skipped operand does not apply, so its run ends in no `trivial` leaf of that rule), all of which kink's confirmation decides; it never makes the document claim a kill kink did not make. Its identity names its composition, the kink components it composes or assumes (`terminal_value`, `data_facts`, `definition_exclusion`, `execution_request`, `k_rust_revision`) and the flow's work budget, never `kink_build`. It keeps each side's kink load (a backend and its parsed KORE) for the whole campaign: about +90 MB of peak resident memory on TRIAL3's SIMPLE job (478 MB against 385-390 MB), not measurable on IMP. A template whose own input the filter excludes, reading it without a run's lists, is refused before any case (`initial-state-excluded`), since the filter would refuse every candidate that keeps the template's text outside its holes; with `--no-filter` kink's confirmation judges such a witness by its runs' lists.
- Nothing is written: no cache, no lock, no file under the flow's directory.

### A corpus with `[stop]` or `[observe]`

A stop is part of a case's meaning ("Where a run ends"): a state past a path's last stop event is no state of the case, and a step past it is taken by no run kink judges.
So every request of the campaign carries the corpus stop (k-rust-fuzz `CaseOptions::stop`, crates/k-rust-fuzz/README.md, "A campaign's stop"): the stop's rules, as `FLOW.toml` names them, and the template's count, its program's `stop_count`, else the template's own `stop_count` (a `file` or `text` template only), else `[stop] count`.
Each case's run, both sides of a kill, the comparability run of a rule or coverage-gap job, the replays and the shrinking all end their paths there, and a leaf at the stop is an end of the truncated system as a stuck leaf is; a case that passed a stop (a step of a named rule that had another successor) is unjudged (`passed-stop`), as `run` excludes such a run.
A rule's own early stop is not used under a stop, so `--fired` reads the firing from the truncated run's trace: a rule whose step only a path past the stop takes is fired by no case.
The confirmation runs the overlay with the same stop, and the fragment writes the template's own `stop_count` when it has one, so the corpus program judges the input the campaign judged; `template.stop_count` is the count the template's runs end at.
A kill job's mutant must have a rewrite rule of each label the stop names, or the job is refused at stage `mutant` (`job.status` `not-admitted`, reason `stop-unresolved`), as `run` does not admit such a mutant; an edit of a rule the stop stops before, on a template whose count is 1, is warned (`stop-hides-edit`), as `check --mutations` warns it.
A stop condition (`[stop] when`) is refused (stage `stop`, reason `unsupported-verb`).

The single-definition jobs admit `[observe]` and run their cases as without it (`job.observe`, `{ignored}`, the reason): no channel changes which states one definition's run reaches, which rules it fires, or where it ends.
What a channel changes is which programs the corpus counts: `coverage` counts a program a deterministic bound cuts as `comparable-prefix`, beside a `comparable` one.
A fuzz goal is a program the corpus's own judgement counts, so the confirmation of a rule or coverage-gap job accepts exactly the classes `coverage` counts, by its own predicate.
The campaign still searches for `comparable` witnesses only: k-rust-fuzz reads a rule or coverage goal at a leaf, and a path a bound cut is no hit there (`reached-cut-path`), so a program `coverage` counts only by its channels is confirmed when given, not searched for.
A kill job is refused (stage `observe`, reason `unsupported-verb`), since its campaign judges ends and a kill of such a corpus is judged by its channels.

### The document

`{schema: "kink-flow-fuzz", version: 16, k_rust_revision, profile, z3?, kink_build, kink, stop?, observe?, spec, template, job, sides, assembly, findings, assumed, attempts: [{seed, fuzz, candidate, confirmation}], program, stopped, action, warnings}`.
`k_rust_revision` is k-rust's build identity (`k_rust::build_identity`: its version and a digest of its sources), as in every kink-flow document, and the value the embedded report's `identity.k-rust-revision` records (GUIDE-USABILITY 5, within version 4); `kink.k_rust_revision`, the semantics identity's component, is the version alone, and `kink_build` pins the whole executable.
`z3`, under the Z3 profile only (version 12), is the Z3 build, `{version, library_sha256}`, as the run document names it: a confirmation is a kink run of the candidate, whose classes and kill are a function of the build that counts its solver queries' units, and a dynamically linked Z3 is outside the executable `kink_build` pins:
- `spec`: admitted, with the flow's `assume_joined`, whether the baseline has data under them (`has_data`) and its unnamed findings, as `run` reads them; or the refusal.
- `template`: its id, source, the start sort used and where it came from (`template`, `program` or `default`), its variables, its hole declarations and `last_run` (`{found, current, template: {program, class, cause}, mutation: {status, reason, witnesses}, suggested_templates}`, or `{found: false, detail}`).
- `job`: `{kind: "kill", mutation, flip, expect, outcome: fuzzed | refused, path_mode, filter: {on, id}}` (`expect`: the mutation's `expect`, or null) (`id`: the witness filter's identity, `null` with `--no-filter`), with kink's `status`, `reason`, `claims` and `inconsistent_pairs` when kink refuses the mutation, `status`, `reason` and `weakening` (the run row's) when kink decides it from its edit, and the claims the mutant withdrew otherwise. A rule job has `kind: "matched"` or `kind: "fired"` and `rule: {module, index, file, start_line, label, id, untargeted_ids}` (a refused rule has refusal stage `rule`); a coverage-gap job `kind: "cover"` or `kind: "refuted"` (with `rule`) and `item: {id, family, kind, file, line, facts}`; a pattern job `kind: "pattern"` and `pattern: {id, text, kore}`. Both have `sides.baseline` only and no `mutant_anchor`.
- `sides`: each side's compiled KORE digest and the two provenance digests of its k-rust-fuzz definition.
- `assembly`: `{kink_template: {sha256} | {refused}, baseline_anchor, mutant_anchor}`, the digests the up-front check compares.
- `findings`, `assumed`: every finding of the campaign's check, and every assumed name with where it came from (`in_flow`, `from_command_line`), whether it assumed a genuine finding, and the findings it matched.
- `attempts`: one attempt, `{seed, fuzz, candidate, confirmation}`: the k-rust-fuzz report as JSON, the candidate (the shrunk witness case, else the first, with `case`), with `assembly: {status: match | mismatch | refused, ...}`), and `confirmation`: `null` with `--no-confirm`, else kink's verdict `{case, confirmed, status, reason, cause}` with the job's `killer`, `class` or `answer`. When kink refuses the shrunk case and the first is another program, the first is confirmed too; the refused verdict is then listed in `refused_confirmations` and `candidate` is the first case.
- `program`: for a witness, `{id, fragment, file, premises, confirmed}` (`confirmed`: kink confirmed it; false with `--no-confirm`); absent when kink refused every candidate. `id` is `<template>-fz-<8 hex of kink's program digest>`. `fragment` is the `[[program]]` table as TOML: the instantiated text as `text`, the template's start sort and variables (each binding as instantiated: a `config-var` hole's value, or a span hole's value inside the binding's text). `file` suggests where to write the text instead. `premises` lists every assumed name, genuine ones flagged, and whether `FLOW.toml` names it already.
- `stopped`: `null` for a witness; `budget` (no witness, and the budget was spent: kink-flow runs the blind proposer alone, which never runs out, so k-rust-fuzz's ending with every proposer exhausted does not occur; `action` advises raising `--cases` or `--work` exactly when the statement says neither that coverage stopped growing, the embedded report's `totals.coverage-last-grew` long before its last case, nor that the mutant may not terminate on some case, `totals.diverging`, which one such case among many is enough for; otherwise it points at the template and its holes, since the statement then says more cases are unlikely to reach a new rule, or that a case may never end and no bound is suggested, although more cases with other hole values may still find a witness), `domain-exhausted` (no witness, and every assignment of the holes ran, each hole having finitely many values: more cases cannot help; the embedded report's `totals.domain`), `client-refused` (no witness in the budget, kink's rules refused candidate hits inside the campaign, and no hit the filter accepted was lost to the fuzz's confirmation: none was a witness kink's rules accept, which is no sign of survival; otherwise the job stops `budget` with the warning; the warning `client-refused` counts them per cause, and the embedded report's `client-refusals` give each cause's first case), `rejected-out`, `time-limit`, `stack-stops` (no witness: the last `--stack-stops` cases in a row each stopped for lack of native stack; `action` gives the advice of the run's `stack-stop` reason when each of them recursed on the mutant of a kill, a mutant that ends, a replacement or dropping the mutation, and never a larger budget), `open-stops` (no witness: the last `--open-stops` cases of a kill job each ended, on the mutant, holding a term not shown to exist; `action` gives the advice of the run's `open-application` reason, a program or hole range whose runs do not reach the application, a replacement or dropping the mutation, and never a larger budget; a `budget` stop every case of which was so says the same instead of advising more cases), `equivalent` (the two definitions denote one theory: equal execution digests and equal program assembly), `assembly-mismatch` (a witness kink's assembly does not reproduce: nothing offered), `unconfirmed` (kink's own code refused every candidate: nothing offered), `not-comparable`, `aborted` (`action` names the fuzz outcome's `kind`: a failed solver prelude, a solver that did not start, or backends that did not rebuild after a crash) or `refused`.
- `action`: the next step.

**Confirmation** (fz26 KF-T4). Unless `--no-confirm` is given, each candidate whose assembly matches is confirmed by kink's own code on an overlay of the flow held in memory: its `[spec]`, with the flow's `assume_joined` and the command line's `--assume-joined` names, its `[budget]`, `[coverage]` at its defaults (a rule job reads the rule's `matched_by` and `fired_by`, which no `[coverage]` value changes, so a section `coverage` would refuse does not stop it), and the fragment as the only `[[program]]`, with a fresh scratch cache under the system's temporary directory, removed on every path. A kill is confirmed when `run` kills the mutation with the fragment as killer; a rule job when `coverage` gives the fragment class `comparable` and lists it in the targeted rule's own `matched_by` (`fired_by`), the entry of the authored rule the job resolved (a listing under any other rule is `not-listed`), with status `matched` or `not-matched` (`fired` or `not-fired`); a fragment that is not comparable has status and reason `not-comparable`, since `coverage` counts it under no rule, whatever its run matched or fired. The confirmation is at the authored rule's granularity, as `coverage` lists programs: a rule given as a 64-hex id is confirmed when the program matches (fires) the authored rule that wrote the id, whichever of that rule's compiled axioms it matched; a rule that compiles to several rewrite axioms is refused when named by its position or label (`several-rewrite-ids`), and given one of its ids, `confirmed: true` says that the authored rule is listed, not that this axiom was; a pattern when `query`, asked with `programs = [fragment]`, confirms the claim. Things the fuzz does not judge decide here: kink's end check (TV-01, which refuses some domain values the fuzz's data judgement accepts), `work_factor`, the exclusions kink reads on a run. There is no seed retry (`--attempts` is a usage error). Confirmation costs one kink run of the one program (a few seconds), outside `--time-limit-ms`; a kink time-out in it depends on the host.

To use a witness, add every premise `FLOW.toml` lacks to `[spec] assume_joined` and append the fragment; then `kink-flow run` (or `coverage`, or `query` with the program claimed) decides it again on the whole corpus, and a `run --lock` of the whole list records it as the killer.
In either profile, while no `time_ms` bound fires, that command gives the verdict the confirmation gave: each program's outcome is independent of the programs run before it (under Z3 every solver query is resource-bounded, so a backend whose solver caches are warm answers it as a fresh one does), and under FirstKill a kill by the fragment is a kill of the corpus (another killing program may be named the killer).
A `time_ms` bound depends on the host in every profile, so a program near it can time out in one command and finish in the other.

Exit status ("Exit status"): 0 when the job has its answer (`stopped` is `null`, a witness, or `equivalent`, a proof that no input kills the mutation);
1 for a witness of a kill job whose mutation expects to survive (`job.expect` `survive`) that kink confirmed (`program.confirmed`) and whose kill needs no premise `FLOW.toml` lacks (every `program.premises` entry `in_flow`): it refutes the expectation, and the `action` says that the program is one on which what the edit changes is observable;
3 when the search ended without a witness kink accepts (`budget`, `domain-exhausted`, `client-refused`, `unconfirmed`, `assembly-mismatch`, `stack-stops`, `open-stops`, `time-limit` or `cancelled`): the job asks whether some input witnesses it, and the caller retries with more cases or time, other holes or another template (`domain-exhausted` says only that this template's holes hold no witness); and for any other witness of a mutation expected to survive (unconfirmed under `--no-confirm`, or resting on a premise the flow lacks), which neither refutes nor confirms the expectation;
2 when an input, the template or the mutation is refused (`refused`: the exclusions and the up-front assembly check included), the generated hole values are mostly rejected (`rejected-out`: they do not read back or violate their sort, so the holes must be fixed, and more cases cannot help), the campaign is `not-comparable` or it `aborted`, or on a usage error (a template, mutation or pattern id that names nothing, an option given twice, two jobs, `--attempts`, or `--assume-joined` with `--pattern`).
`krust fuzz` agrees on a witness (0), a refused campaign and a usage error (2); it exits 1 for every campaign that ends without a witness, where this command exits 3 for a search that has no answer, 0 for `equivalent` and 2 for `not-comparable` and an aborted campaign (docs/fuzzing.md, "`krust fuzz` on its own").

Version 3 of the document (fz26 FZ-COMPARABLE-B) adds `job.filter`, the `stopped` value `client-refused`, the warning `client-refused` and the refusal `initial-state-excluded`, and embeds fuzz reports that carry the witness filter's fields; version 2 had none of them.
Version 4 (fz26 round 4, FZ-REPLAY-WHOLE) embeds k-rust-fuzz reports of version 10: their identity records the k-rust-fuzz build (`fuzz-revision`) and the parser's diagnostic work limit, their totals the first case outside the determinism contract, the holes' finite domain, the cases in which the mutant may not terminate and the last case that reached a new rule, and every source location they name is relative to the main module's file; it adds the `stopped` value `domain-exhausted` and the warning `witness-not-terminating`. Version 5 adds the warning `reaching-not-computed`, and `template.last_run.mutation.reaching` is `null` when the last run's row is.
Version 6 (CF-40c2) names each coverage predicate as every kink-flow document does ("Coverage predicates"): the rule jobs are `--matched RULE` and `--fired RULE`, of kinds `matched` and `fired`, where version 5 had `--reach RULE [--fired]` of kind `reach`, and `job.rule` has no `mode` (version 5's k-rust-fuzz goal name, `condition-reached` or `covered`, which the kind says again and whose `covered` is not `coverage`' `covered`); a rule job's refusal has stage `rule` (was `reach`) and its confirmation status is `matched`, `not-matched`, `fired` or `not-fired` for a comparable program and `not-comparable` for any other (was `reached` or `unreached`); `template.last_run.mutation.reaching` is `witnesses`; and the warnings `reaching-not-computed`, `no-reaching-program` and `template-not-reaching` are `witnesses-not-computed`, `no-witness` and `template-not-a-witness`.
Version 7 adds the refusal of a corpus with `[stop]` (stage `stop`, reason `unsupported-verb`, "Where a run ends"), with `stopped` `refused` and its `action`.
Version 8 adds `template.last_run.mutation.witnesses_global` and the warning `global-witnesses`.
Version 9 refuses a kill job of a mutation `run` decides from its edit (stage `mutation`, reason `unkillable` or `equivalent`, with `job.weakening`) in place of the warning `unkillable`, and adds the `stopped` value `stack-stops` with `--stack-stops N`, and the warnings `stack-stop` and `not-ceil-free`. Version 10 adds the `stopped` value `open-stops` with `--open-stops N` and the warnings `open-application` and `last-run-without-mutation`, gives `global-witnesses` only where the template's program reaches no edited rule, and names the job's own list and cache in each next step that runs `run`.
Version 11 adds the kill job of a condition flip a front end derives (below): a kill job's `job.flip` says whether its mutation is one, a refused flip is refused at stage `mutation` with `job.status` `refused` and the judge's reason, and a flip's next steps that would run `run` run `coverage`.
Version 12 adds `z3` under the Z3 profile (above).
Version 13 (CS-8) adds the coverage-gap jobs `--refuted RULE` (kind `refuted`, with `job.rule`) and `--cover ITEM` (kind `cover`), with `job.item`, the refusals at stage `item`, the climb beside blind sampling, and the confirmation statuses `covered` and `not-covered`; the other jobs' documents are version 12's.
Version 14 adds a kill job's `job.expect` and the warning `expected-to-survive`, and exits 1 on a confirmed witness, needing no premise the flow lacks, of a mutation expected to survive, and 3 on any other witness of one; the other jobs' documents are version 13's.
Version 15 runs a corpus with `[stop]` and one with `[observe]` ("A corpus with `[stop]` or `[observe]`"): `stop` and `observe` are the manifest's, as the `check`, `coverage` and `run` documents carry them, the refusals at stages `stop` and `observe` are narrowed to a stop condition and to a kill job, `template.stop_count`, `job.observe`, the refusal `stop-unresolved` at stage `mutant` and the warning `stop-hides-edit` are new, and the embedded k-rust-fuzz report is version 11, whose identity records the stop.
Version 16 (KINK-FINDING-NAMES) names every finding (`findings`, `assumed`, `spec.unnamed_findings`, a witness's premises) by its kind, sentences and digest, refuses a genuine finding's name given with `--assume-joined` (`decided`), and embeds k-rust-fuzz reports of version 12.
`tests/formats.rs` ties the version to the document's keys and enumerated values and to the report version it embeds.

## Comparing implementations: `kink-flow compare FLOW.toml [--only NAME]... [--lock FILE [--locked]] [--cache DIR] [--output json|text|verdicts]`

A corpus states what its system does on each of its programs.
Another implementation of the system (an emulator, a hardware model, a port) is compared with the definition over the same programs, inputs and `[stop]` by declaring it in `FLOW.toml`; a program added to the corpus is compared with no other edit.

```toml
[[implementation]]
name = "rust-cpu"                       # unique among the implementations
protocol = "kink-implementation/2"      # optional; default "kink-implementation/1"
command = ["bin/cpu", "--kink"]         # argv: a first word with a `/` is relative to FLOW.toml's directory, else looked up on PATH
given = "start"                         # "start": the definition's start besides the inputs; "inputs": the inputs alone
omits = ["k", "ei_pending"]             # optional: the cells the implementation does not state
identity = { file = "bin/cpu" }         # optional: the file whose digest names its build
time_ms = 30000                         # optional; default budget.time_ms
views = [
  { name = "writes", views = { bus = "WritesView" }, observer = "pkg:views", required = true },
  { name = "accesses", views = { bus = "AccessesView" }, observer = "pkg:views" },
  { name = "boundary", channels = ["boundary"], required = true },   # a trace view, under the second protocol
]
```

| Key | Meaning |
| --- | --- |
| `name` | The implementation's name, which rows, `--only` and the documents use; nonempty and unique. |
| `protocol` | `kink-implementation/1` (the default) or `kink-implementation/2` (below, "Traces"). Another name refuses the command (stage `implementation`, reason `declaration`). |
| `command` | A nonempty array of nonempty strings: the executable and its arguments. It runs in the manifest's directory. |
| `given` | `start` or `inputs` (below, "The protocol"). Required. |
| `omits` | The cells the implementation does not state, by the front end's cell names (krs: Rust field paths). Every other observable cell must be in each answer, or the answer is malformed, naming the cell. A view that compares an omitted cell is `not-compared` (`omitted`). Default: none. |
| `identity` | `{ file }`, relative to the manifest's directory: the document names its SHA-256 (`implementations[].identity.sha256`), the build its answers are cached under and its lock rows name ("The record and the cache" below). Absent: the implementation runs on every command. A file that cannot be read refuses the command (stage `implementation`, reason `identity`). |
| `time_ms` | The wall clock that cancels one run of the implementation; positive. It decides no verdict (below). Default `budget.time_ms`. |
| `views` | A nonempty array of views, each `{name, required, compare, views, observer}`: `name` unique among the implementation's views; `required` a boolean, default false (a view that is reported only); `compare` the cells it compares (default: every observable cell the implementation states); `views` a function by cell, applied to both sides' values before they are compared; `observer` the definition the functions are evaluated in (default: the definition). `compare`, `views` and `observer` are the front end's, resolved as an expectation's are ("Expectations"); a view that does not resolve refuses the command (stage `implementation`, reason `declaration`). `views = [{ name = "end", required = true }]` compares every cell the implementation states. A view with `channels`, a nonempty array of channel names of the flow's `[observe]` without repeats, is a trace view (below, "Traces"): it has `name`, `required` and `channels` only, and compares no cell. A trace view under the first protocol, in a flow with no `[observe]`, with no channel, or naming a channel `[observe]` does not declare refuses the command (stage `implementation`, reason `declaration`), and so does one over a channel some component of which has no value with a document, naming the channel and the component: no implementation can state an element of it. |

No run of the definition reads an implementation, so `[[implementation]]` is in no digest or cache key of the definition's runs, and every other command ignores it.

### The protocol

The protocol is `kink-implementation/1`, a stable contract between kink and an implementation, or `kink-implementation/2`, which is the first with traces added ("Traces" below); each implementation declares its own.
kink runs the implementation's `command` once per program (in the manifest's directory), writes one JSON request on its stdin and closes it, and reads one JSON answer from its stdout.

The request is an object:

| Key | Meaning |
| --- | --- |
| `protocol` | The implementation's protocol, `"kink-implementation/1"` or `"kink-implementation/2"`. |
| `program` | The program's id, as every document names it. |
| `inputs` | The program's inputs as typed values, by input name: under krs, each typed input decoded at its parameter's declared type and written as its canonical document by the parameter's Rust name, and a program file bound to the main parameter as its value (a `Bytes` document, or `{"$text": ..}` for a text program), so the request is a function of the values, never of the files that hold them. |
| `stop` | `{count}`, the program's stop count (its `stop_count`, else `[stop] count`), when the corpus has a `[stop]`: the implementation stops where the corpus's stop is, by its own meaning of it. |
| `start` | Where `given = "start"`: the definition's start for the program, the state of its depth-0 run (its initializer evaluated), every cell stated, in the definition's cell vocabulary (krs: an end document's `cells`, by Rust field path, values as documents of the typed encoding). |

The answer is an object of `end`, and `cells` or `reason`, and no other key:

| `end` | Meaning | Also |
| --- | --- | --- |
| `stopped` | the run reached the corpus's `[stop]` | `cells`: its end's cells, in the definition's cell vocabulary |
| `final` | the run ended on its own | `cells`, as for `stopped` |
| `could-not-apply` | the implementation cannot apply the program as given | `reason`, a nonempty string |

An implementation never names a rule label or states the computation (the `k` cell): those are the definition's internals, which no other implementation knows.
kink names the definition's own end by the same words: an end some path of the program's baseline run reached at its last stop event is `stopped`, one every path reached on its own is `final`; without `[stop]` every end is `final`.
The request and the answer are extensible by new keys under a new protocol version (version 2 adds traces at `[observe]` points; inclusion for nondeterministic definitions and hardware logs are not written); version 1's answer refuses every other key, so an implementation that writes one is told so rather than silently half-read.
A request of version 1 and the reading of its answer are the same bytes and the same rules in a flow that also declares implementations of version 2.

One process runs per program: a failure is then a fact of one program, the protocol needs no framing, and the cost is one process start per program (milliseconds, against the definition's own run of the program).
The programs run one after another, in corpus order, each implementation in manifest order.

A run that does not give an answer is a failure of the implementation, not a verdict: its row has `failure`, `{kind, detail, exit_code, stderr}` (the last 2000 bytes of its stderr), and no view verdicts.
`kind` is `spawn` (the command cannot be started), `exit` (it exited with a status other than 0, or a signal ended it; an answer it printed is not read), `malformed` (its stdout is not one JSON answer, or `cells` names a cell the definition does not declare, holds a value of another type, or leaves out a cell `omits` does not name, or its `observations` is no record of the channels asked) or `timeout`.
The clock only cancels: a run that has not closed its stdout and stderr when `time_ms` has passed is killed, and is `timeout`, no answer on this host (once it has closed them, its answer is complete, and kink waits for it to exit); the clock never decides a verdict, which only an answer does.

### Traces: `kink-implementation/2`

An end view compares where a run ends.
A trace view compares what a run does on the way: the elements of the flow's `[observe]` channels ("What a run observes"), which the definition's baseline run of each program records, against the elements the implementation states for the same channels.
So a program that never ends, or that the corpus's bounds cut, is compared up to where the definition's run was cut.

What a trace verdict is:

- It is a test of one build of the implementation, on the corpus's programs, up to the horizon the verdict names.
  It says nothing of another program, of a longer run, or of another build.
- kink compares the two sides' elements at equal indices.
  That the implementation's element `k` is its state at the definition's point `k` is the implementation's claim, which kink does not check; every trace row says so (`correspondence: "implementation-claim"`).
- Nothing here relates two K definitions, and no verdict of this command is a proof.
  A wrapper around `krs run` (or another K tool) declared as an `[[implementation]]` is not a supported way to compare two definitions: the correspondence of their points would be the wrapper's claim, and the verdict would still be a test of some programs up to a horizon.

The request is version 1's, with `protocol` `"kink-implementation/2"` and, where the implementation declares a trace view and the program's baseline has one path, `observe`:

| Key | Meaning |
| --- | --- |
| `observe.channels` | One object per channel the implementation's trace views name, without repeats, in `[observe]`'s order (the point classes, then the logs). |
| `name` | The channel's name. |
| `kind` | `point` or `log`. |
| `components` | A point class: `[{name, type}]`, the keys of an element's value in the class's order (krs: a cell's Rust field path, or a component's name), each with the type its value is a document at. |
| `element` | A log: `{type}`, the type an element is a document at. |
| `stutter` | A point class: `count` or `collapse`. |
| `filtered` | A point class: whether it has a filter (`when`). Stating only the points where the filter holds is then part of the implementation's claim. |
| `points` | A point class: `{before, after}`, its rule names as the manifest holds them, each list sorted. They say where the definition reads the channel, and are in the request so that a changed declaration is another request; an answer never names a rule. |
| `at` | A log: the point classes it is read at. |
| `positions` | How many indices from 0 the answer is asked to state: the number of elements the definition's channel holds where it is open after them (its run was cut), and one more where it is closed (the closure is a position, so an implementation that goes on can show its element there). Under `collapse` it counts collapsed elements. |

The horizon is the definition's: `[budget] max_depth` and `baseline_max_work` cut its run and `[stop]` ends it, and `positions` tells the implementation the result in elements, never in steps.
The implementation stops once every channel has its positions, or when it ends.

The answer is an object of `end`, `cells`, `reason` and `observations`, and no other key:

| `end` | Meaning | Also |
| --- | --- | --- |
| `stopped`, `final` | as in version 1 | `cells`, required where the implementation declares an end view and read where stated; `observations`, where the request has `observe` |
| `horizon` | it stated the positions asked and has not ended; only to a request with `observe` | `observations`, and no `cells`: it has no end |
| `could-not-apply` | as in version 1 | `reason`, and neither `cells` nor `observations` |

`observations` is there exactly when the request has `observe` and the answer is not `could-not-apply`.
It is a `krs-observations/1` document, the format `krs run --output observations` prints, read exactly: `{schema, channels: [{name, kind, elements, closed, open}]}`, the channels being exactly those asked, once each.

- Each element is `{index, depth, rule, side, value}`: `index` its position, `depth` the implementation's own count (cycles, instructions; it is shown in a difference and never compared), `rule` and `side` present and null (they name points of the definition), and `value` the element's value.
  An element the implementation cannot state has `undecided`, a string saying why, in place of `value`; under `collapse` the channel is known only up to such an element.
- A point's `value` is an object of exactly the class's components by name; a log's is its element.
- A channel ends `closed: "end"` (the run ended; `"undefined"` where its last step is undefined) with `open: null`, or `closed: null` with `open: {index, reason}`, `index` the number of elements stated: nothing is stated from there on.

Under krs, a value is a document of the typed encoding at its component's type, in any of the value's spellings: kink decodes each stated value at that type and writes its canonical document before it compares, so two elements are equal exactly when their values are (a map written as an object or as pairs, an integer as a number or as `{"$int": ..}`).
A value of another type, a component missing or unknown, a non-null `rule` or `side`, or a channel of another kind makes the answer `malformed`, named by its place (`channels[0].elements[3].value.pc`).
A `collapse` channel is collapsed after that, as the definition's is: an element equal to the last one kept is dropped, so an implementation may state such a channel at a finer granularity than the definition's, provided it only repeats contents.

**Choosing the points.**
A trace view tests something only where the two systems have a common notion of "the same moment".
Name point classes whose rules are boundaries in both systems (an instruction boundary, a frame end), not rules of the definition's own bookkeeping: where the definition takes two steps for what the implementation does in one, a `count` class over both rules has an element the implementation has no state for, and the first-difference report shows the offset at once.
Where the two differ only in how often a content repeats, use `stutter = "collapse"`.
Where the interesting behaviour is a sequence of events (bus writes, output), observe it as a log channel: its elements are the appended items, which do not depend on where either system is sampled.

### Verdicts

Each (implementation, program, view) has one verdict:

| Verdict | Meaning |
| --- | --- |
| `equal` | Every end of the definition agrees with the answer: the same word, and the same values of the compared cells (through the view's functions); `omitted` lists the cells left out because the implementation omits them. A trace view: on every channel of the view both sides close after the same elements, by the same closure. A channel both sides close with no element is compared at that closure, and agrees. |
| `agree-up-to` | A trace view only: nothing differs, and on some channel a side states nothing past the elements that agree. `horizon` names each such channel, `{elements, limited_by, definition, implementation}`: the number of elements that agree; `limited_by` `definition` where the definition's channel is open there (`definition`: why, `bound`, `cycle` or another opening of its record) or `implementation` where the definition states a further position and the answer does not; `implementation`: the answer's own `open.reason`, or null. It is never spelled `equal`. |
| `different` | They differ, first at `difference`: the word (`{format: "kink-end/1", at: "end", definition, implementation}`; an end view answered `horizon` on a program the definition ends differs so), else the front end's first difference of the compared cells (krs: `krs-difference/3`, its sides `definition` and `implementation`). A trace view: `{format: "kink-trace/1", channel, kind, index, path, definition, implementation, correspondence}`, the first index at which both sides hold a decided element or a closure and the two differ, where several channels differ the one the definition's run reached first. `kind` is `value` (two elements; `path` the place inside the value, `acc`, `regs.a`) or `closure` (one side ends where the other goes on). `definition` is `{element, rule, side, steps}`, the point the definition read it at (krs: the rule as a `krs run` report names it; `rule` and `side` null for a log item read at no point) and the steps its run took to it, or `{closed, rule: null, side: null, steps: null}` where its channel closes there; `implementation` is `{element, count}`, `count` its own `depth`, or `{closed, count: null}`. |
| `could-not-apply` | The implementation's own answer; `detail` is its reason. |
| `definition-refused` | An end view of a program every end of whose baseline is at a declared `refused` end ("Declared ends"), whatever the implementation answered: the definition states no end of the program to compare an answer with, only that it refuses it. Where the baseline also has an end of another class, the view is compared with the ends as before, since a refusal on one path does not answer for another. `detail` names the first refused end and its reason. It mirrors `could-not-apply`, the implementation's refusal, and is an answer as that is. A trace view is compared as before: the elements before the end are behaviour the definition states. A lock row's `reason` is the detail, and a section with such a row adds a legend line for it. |
| `not-compared` | The view is not compared; `reason` says why: `definition` (the program's baseline is not `comparable`: it has no end; for an implementation of version 2 only a baseline that is `timeout`, `unknown` or an error), `no-end` (an end view of an implementation of version 2 on a program whose baseline the bounds cut, `comparable-prefix`), `several-paths` (a trace view of a program whose baseline has several paths: its record holds no one sequence of elements), `observed-nothing` (a trace view no channel of which was compared at any index: a comparison of nothing is no agreement), `omitted` (the view compares a cell the implementation omits), `left-out` (a cell the corpus's ends leave out, `[result]` or an unobservable cell), `several-ends` (the definition's run has several ends that the view tells apart, or ends both at the stop and on its own: one answer against several ends is inclusion, which this command does not decide), `undecided` (a view's evaluation stopped before it ended, or the clock stopped the depth-0 run that gives the start: no answer on this host; for a trace view, an element before any difference is not decided on one side, an `undecided` element of the answer or an element of the definition that is undecided or has a part with no document), `unreadable` (the definition's start, an end or an input has no document). |

### Exit status

Only a required view decides the status; every other verdict is reported.
Each (implementation, program) row joins its required views' statuses: `equal` and `could-not-apply` 0 (an answer: the implementation states that it does not apply the program), `definition-refused` 0 (an answer: the definition states that it refuses the program), `different` 1, `not-compared` 3 for `several-ends`, `several-paths`, `observed-nothing`, `undecided` and a `definition` that is `timeout`, `unknown` or `comparable-prefix`, else 2; and, for an implementation with a required view, its failure: 3 for `timeout`, else 2.
`agree-up-to` is 0 where every horizon is the definition's (`limited_by: "definition"`): the answer agrees with everything the definition states.
It is 3 where some horizon is the implementation's: the definition states a position the answer does not, so an answer of fewer positions than asked never passes a required view.
A `no-end` end view is 0 where the same implementation declares a required trace view, which then carries the program, and 3 otherwise.
The command exits with the join of its rows and of its lock ("Exit status"; `stale` 1, `undecided` 3, a lock that does not decode or cannot be written 2), 2 for a refusal: a front end with no cell vocabulary (`unsupported-front-end`: kink-flow's own, which reads K terms; run `krs kink compare`), a manifest with no `[[implementation]]` (`no-implementation`), an `--only` name it does not declare (`unknown-implementation`), a declaration the definition refutes (`declaration`), an unreadable `identity` file (`identity`), and a refused specification.

### The document

`schema` `kink-flow-compare`, `version` 3, `protocol`, the builds (`k_rust_revision`, `profile`, `kink_build`, `z3`), `spec`, `refusal` (`{stage, reason, detail}` or null), `implementations` (each declaration as written, its `identity` with `sha256`), `programs` (each program's baseline `{id, class, cause, cached, cache_error}`), `stop` and `result.not_compared` (the cells the ends leave out), `rows` and `summary`.
Each row is one (implementation, program): `{implementation, program, required, request_sha256, answer: {end, reason}, cached, failure, wall_ms, clock_stopped, views}`, `request_sha256` the SHA-256 of the request's canonical JSON, `cached` whether the answer was read from the cache (its `wall_ms` is then null), `clock_stopped` the run the clock stopped that the row rests on (`baseline`, `start`, `implementation`, or null), and each entry of `views` `{view, required, verdict, difference, reason, detail, omitted, status}`.
Each program's baseline is `{id, class, cause, cached, not_cached, cache_error}`.
`summary` counts the verdicts (`verdicts`, and `required`, of the required views) and the `failures`.
`lock`, with `--lock`, is the lock's state as `run`'s and `coverage`'s is ("The corpus record"), with `failed`.
`--output text` prints one line per verdict (`IMPLEMENTATION PROGRAM VIEW (required|reported): VERDICT`, with where a difference is or why a view is not compared) and per failure, then the counts; `--output verdicts` prints the record's header and the `[compare]` section the run would write.
Version 2 adds `lock`, a row's `cached` and `clock_stopped`, and a program's `not_cached`.
Version 3 adds the second protocol.
Where a selected implementation declares it, the document has `protocols`, the protocols of the selected implementations, in place of `protocol`, and `evidence: "testing"`, and both members of `summary` count `agree-up-to`; a document of implementations of the first protocol alone has none of the three and is version 2's but for its `version`.
A trace view's entry also has `horizon` (null but for `agree-up-to`) and `correspondence`; an end view's entry has neither key.
An `agree-up-to` entry's `status` is its own, 0 or 3 ("Exit status").
A text line of a trace view ends with `(testing: that element k is the definition's point k is NAME's claim)`.
A value run that does not reproduce the recorded baseline refuses the command (stage `compare`, reason `trace-capture`).

### The record and the cache

With `--lock FILE` the verdicts are the corpus record's `[compare]` section ("The corpus record"): one `[[compare.verdict]]` per (implementation, program, view), with `required`, the verdict, its reason, a different view's first difference, an `agree-up-to` view's `horizon`, `request_sha256` and the implementation's `identity_sha256`, under a header that names the `protocols` of its implementations.
The record is read before anything runs, and the command follows the rule of `run` and `coverage`: a run of every implementation without `--locked` rewrites the section (`created`, `written` or `unchanged`), keeping the other sections byte for byte; `--only` and a refusal leave it unwritten.
A verdict is a function of the definition, the corpus, the request and the implementation's answer, so the section states what the current inputs give, and a moved verdict shows in review.

Under `--locked` the command writes nothing and compares the section it would write with the file's: a row whose verdict, reason, first difference or horizon differs (`kink.lock: rust-cpu cases/loop/case.toml boundary: agree-up-to: its horizon moved: recorded ..., now ...`), a reported view's included, is a lock difference (`lock.status` `stale`, exit 1, one line per change on stderr: `kink.lock: rust-cpu cases/irq/case.toml accesses: different: its first difference moved: recorded ..., now ...`, `kink.lock: rust-cpu cases/irq/case.toml writes: equal -> different`), and so is a row only one side has (`added, equal`, `removed, was different`), a moved digest, or another order or text, which the first difference names.
A run of an implementation that gave no answer, because it failed (`spawn`, `exit`, `malformed`) or the clock cancelled it (`timeout`), decides no verdict, and neither does a definition run the clock stopped: the rows of that (implementation, program) keep their recorded values, so the run is never a lock difference and never rewrites a row, and under `--locked` a section that differs in nothing else is `undecided`, exit 3, not decided on this host, as the clock's rule is for `run` ("What decides a verdict").
stderr names each such run (`kink.lock: rust-cpu cases/irq/case.toml: the clock (time_ms) cancelled the implementation's run: its rows are not decided on this host`).

An implementation that declares `identity` has its answers cached in the result cache (`--cache DIR`, `implementation-answers/`): the stdout of a run that exited 0 with an answer the protocol reads is stored under the protocol, the digest of the `identity` file, the `command` and the request's digest, and a later run with the same four reads it instead of starting the implementation (`cached: true`).
A request of version 2 holds the channels asked, with their components and points, and each channel's `positions`, so a changed `[observe]` or a moved horizon is another request, which no cached answer answers.
The definition's side of a trace view is the values of the elements its record holds digests of, which a value run reads: one more run of the program's baseline, whose record must be the recorded one.
A completed value run is cached too (`definition-traces/`), under the program's result key and the names of the channels asked, in the order asked.
The result key names the definition, the program, the budget, `[stop]` and `[observe]` ("Programs and the result cache"), so a change of any of them, or another set of channels, is another key, which no stored entry answers.
An entry names the digest of the observation record its run reproduced and carries a digest of itself.
It is read only for that record, and only where it holds the channels asked, each with the end the record gives it, one element per element of the record, and a value exactly where the record holds a digest.
Any other entry is a miss: the value run is made, and its values replace the entry.
A value run that gave no values (it was refused, the clock stopped it, or its record is not the recorded one) is never stored.
Neither is one of a program whose baseline result is not cached, nor any where the result cache is off.
An entry holds each element as the front end's document of it (under `krs kink`, the JSON value), with its depth and its point.
kink's own contents are KORE terms, which have no text form an entry and its reader agree on: a value run that holds one is not stored, so a corpus without a front end's functions makes that value run on every `compare`.
No document, verdict, lock row or exit status depends on whether the values were read or computed, and no key of the document says which.
A cached answer trusts that the same binary, given the same request, gives the same answer.
The cache holds answers, not verdicts: each run reads the answer again by the protocol and compares it again with the definition's ends under the views as they are then, since a request with `given = "inputs"` does not name the definition, so a definition, a `[result]` or a view that changed is never answered from the cache, and `--locked` checks the verdicts the current definition gives.
A failure or a cancelled run is never cached: it is no answer, and a host on which the implementation answers must not be told otherwise.
Without `identity` nothing names the build that answered, so the implementation runs on every command.
The lock is not the cache: a lock row states a verdict, which also depends on the definition's ends, and a cache in the lock would make `--locked` compare a row with itself.

## Front ends

kink-flow's manifest, command layer and documents are a library (`kink_flow`) for two front ends: kink-flow's own command line over a K specification, and the krs front end (`krs kink <verb>`, in krs-cli), which builds a KRS package, keeps the K it emits as `definition.k` in the corpus directory and runs kink-flow's commands over that K.
The krs front end's commands, its corpus layout (`<package>/kink/`) and what it adds to the documents (a `krs` object on every rule, the `definition` object) are stated in KRS's workflow reference (`docs-site/src/pages/reference/workflow.mdx`, "The corpus loop").
Both decode `FLOW.toml` with `ManifestFile::decode` and run the engine unchanged, so a KRS corpus has the K corpus's admission, kill definition, caches, documents and statuses.

- `ManifestFile` is a decoded `FLOW.toml` whose `[spec]` is a `SpecDecl`: `K` (as written) or `Krs`.
  `ManifestFile::bind` gives the `FlowManifest` every command runs on; a front end binds a KRS declaration to the `SpecSection` of the K it emitted (the declaration's `assume_joined` is kept), and a K declaration binds to itself.
  A front end then sets on it what only it knows: how typed inputs are read (`with_input_decoder`) and which sentences are claim helpers (`with_claim_helpers`, by module and label, and `is_claim_helper(module, label)` to ask; every coverage family's scope, `coverage` above).
- `report::stored_report(directory, options, spelling)` is `report` for the corpus whose manifest is in `directory`, so a front end prints the stored run document without building the specification.
- `FlowCommand::parse(verb, files, options)` reads a verb's options exactly as `kink-flow <verb>` does, the corpus's files given by the front end (`CommandFiles`: kink-flow's operands, or the front end's layout), and `dispatch(manifest, command, front)` runs it on the large stack kink's definitions need.
- `FrontEnd` is what a front end adds: `spelling`, how next steps spell its commands, with whatever selects its corpus (the trait `CommandSpelling`; kink-flow's own is `KinkFlowSpelling`); `refused`, the mutations its own checks refused, each with an `InvalidReason::External { name, next }`; `annotate`, applied to every document before it is printed and, for `run`, before each write of the report; and `derived`, the condition flips it derives for `coverage`'s flips family (`flips::Derived::Flips` with a `DerivedList`), or why it derives none (`Derived::None`, kink-flow's own: `flips::DERIVES_NONE`).
  `coverage` reads the rules' items as `annotate` names them before it deduces which flips are unreached, so a front end's match (`krs.matched_by`) decides a match occurrence.
  A refused mutation's `run` row has status `invalid-mutation`, the front end's reason, detail and next step (`action`), and nothing is resolved, compiled or run for it, so no outcome record or memo record is written; `check --mutations` adds the refusal to its row, and a `fuzz` kill job of it is refused.
- `check_corpus_mutations` and `check_mutations_document` let a front end add its findings (`Finding::refused` for a refusal) and its own row keys (`MutationCheckRow::extra`, rendered after kink-flow's keys) between the check and its document.
- `visit_rules` visits every object of a document that names a sentence of the baseline (a `module` and an `index`; in `spec.exclusion`, the `authors` of each compiled sentence), with the sentence and its label, so a front end can add its own names to every rule a document names.
  A rule named only by a compiled id or as text (a specification diagnostic's `rule_id`, a query witness path's `rules`) names no baseline sentence and is not visited.
- `verdicts` is the rendering above.
