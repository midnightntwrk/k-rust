# The entry schema

An entry is one point of K's or KORE's meaning: a K text, the ruling on it, the reason of the ruling, and what each implementation was observed to do on the text.
The ruling is derived from the K and KORE texts. Every implementation (kompile, a backend, `kore.k` as krust runs it, KCore) is evidence, and none of them is the ruling.
`tools/check.py` checks that an entry's record is consistent with itself (section 5).

## 1. Layout

Two kinds, one schema.

| kind | directory | what it is |
| --- | --- | --- |
| `case` | `cases/<id>/` | an executable entry: an object definition `def.k` and an initial term `pgm`; the ruling is the set of final configurations of the search |
| `text` | `texts/<id>/` | a text-ruling entry: a K text, a hand-written KORE text, or a hook declaration quoted from `domains.md`; the ruling is a statement about the text |

- An id is `cNN-name` for a case and `tNN-name` for a text entry. A number is never reused.
- An entry is cited as `kk:<id>`, for example `kk:c44-ensures-priority`, wherever it is cited: in another entry, a ticket, a finding.

Files of an entry:

| file | written by | content |
| --- | --- | --- |
| `entry.toml` | by hand | section 2. **No tool writes or changes it.** |
| the K text | by hand | `def.k` and `pgm` for a case; `<id>.k` or `<id>.kore` for a text entry; none for a hook entry that quotes a declaration |
| `evidence.json` | `tools/case.py` only | section 4 |
| `kompile.txt`, `kore.txt` | `tools/case.py` only | kompile's command, release, exit code and messages, with the entry's directory and K's paths replaced by names and the process numbers kore-exec prints by `PID`; the sentences the text adds to an empty module (those of the main module that come from no builtin file of K and that the main module of an empty module does not hold), each after a line `//@ N`, N its index among the main module's sentences, without their `Source` and `Location` attributes and with the variables kompile generates renumbered, so that no absolute path is committed. A rebuild of the same text need not write the same `kore.txt`: kompile writes the disjuncts of an `[owise]` premise in an order that depends on the absolute path of the text it kompiles (seen on c48), and a rebuild in another directory that reorders them changes the file, its hash in `evidence.json`, and the lines a `kompiled` locator names. No `kore.txt` where kompile refused the text |
| `pgm.kore`, `kore.pgm`, `symbols.json` | `tools/case.py`, cases only | the initial term's KORE, the encoded program for `kore.k`, and the encoder's numbering |


## 2. `entry.toml`

The example is an unsettled case, which uses every field of a case. Its content is an illustration of the form, not a ruling.

```toml
id = "c44-ensures-priority"
kind = "case"                      # case | text
subject = "A rule whose ensures is false, beside an overlapping rule of larger priority number."
retro = ["R3"]                     # optional: rows of the retrospective this entry answers
rests_on = ["kk:t05-rule-ensures-result", "kk:t03-applied-rule-blocks"]

[text]                             # what the ruling is about
files = ["def.k", "pgm"]           # case: def.k and pgm. text: one K or KORE file
# or, for a hook entry with no K text:
#   declaration = { source = "domains", locator = "domains.md:LINE", quote = "syntax ..." }
kompile = "accepts"                # accepts | rejects | not-run (a declaration quoted alone)

[ruling]
status = "unsettled"               # settled | unsettled
reason = """
The derivation, in sentences: which sentence gives which step. No implementation is named in it."""
interpreter = "applied-blocks"     # unsettled case only: the reading kore.k computes, or "outside"
separates = ["undefined-result-does-not-block", "ensures-false-not-applied"]

[[ruling.basis]]                   # at least one; each is a sentence of a text
source = "manual"                  # manual | tutorial | domains | builtin-module | kore-syntax | prelude | kompiled | matching-logic
locator = "docs/user_manual.md:LINE (K 7.1.337)"
quote = "the sentence, verbatim"

[[reading]]                        # unsettled only: at least two
name = "applied-blocks"
statement = "A rule has applied once its left side matches and its requires holds; an empty result is still an application."
finals = ["b(1)"]                  # or answer = "prose" where no single ground answer exists
consequence = "a(0) has no successor and is not final."

[[reading]]
name = "empty-result-does-not-block"
statement = "A rule that gives no successor has failed in the sense of the manual sentence on owise."
finals = ["b(1)", "c(0)"]
consequence = "The rule of priority 60 steps a(0) to c(0)."

[[disposition]]                    # one per implementation result that is not the ruling
implementation = "llvm"
is = "difference"                  # difference | reading:<name> | coincides:<name>
reason = "Why the result is not the ruling, or no reading."
```

### 2.1 The fields

| field | where | required | meaning |
| --- | --- | --- | --- |
| `id` | top | yes | the directory's name |
| `kind` | top | yes | `case` or `text` |
| `subject` | top | yes | one or two sentences: what the entry is about |
| `retro` | top | no | row ids of the retrospective |
| `rests_on` | top | no | the entries (`kk:<id>`) whose readings the reason uses |
| `origin` | top | no | text entry: the fixture its K text was copied from |
| `files` or `declaration` | `[text]` | exactly one | the entry's K text, or a quoted declaration with `source`, `locator`, `quote` |
| `kompile` | `[text]` | yes | `accepts`, `rejects`, or `not-run` |
| `frontend`, `frontend_difference` | `[text]` | no | `as-ruled`, `differs` or `manual-silent`: how the sentences kompile writes stand against the manual; `differs` needs `frontend_difference`, a sentence saying where |
| `status` | `[ruling]` | yes | `settled`, `unsettled` |
| `reason` | `[ruling]` | yes | the derivation of the ruling from the basis and from `rests_on` |
| `[[ruling.basis]]` | `[ruling]` | at least one | `source`, `locator`, `quote` |
| `finals` | `[ruling]` | settled case | the final configurations, as terms in the syntax of `def.k`; `[]` means there is none |
| `finals_canonical` | `[ruling]`, `[[reading]]` | no | finals in the canonical text of `tools/korek.py`, where `kast` cannot parse them from `def.k`'s syntax; then in place of `finals` |
| `statement`, `form` | `[ruling]` | settled text entry | section 3 |
| `[ruling.kore]` | `[ruling]` | no | the ruling on the written KORE sentences: `statement`, and its own `[[ruling.kore.basis]]` |
| `interpreter` | `[ruling]` | unsettled case | the name of the reading `kore.k` computes, or `"outside"` |
| `separates` | `[ruling]` | no, unsettled case | the mutations of `MUTATIONS.toml` that tell the readings apart |
| `[[reading]]` | top | unsettled: at least two | `name`, `statement`, `consequence`, and `finals` (or `finals_canonical`) or `answer` |
| `[[disposition]]` | top | one per implementation result that is not the ruling | `implementation`, `is`, `reason` |
| `[[observe]]` | top | no | `file` (`kore.txt` or `kompile.txt`) and one of `contains`, `absent`: a substring that must, or must not, occur in that file |
| `[[note]]` | top | no | `implementation`, `text`: an observation of an implementation that is no disposition. Never part of the reason |

### 2.2 Rules on the fields

- **`reason` and `ruling.basis`.** The reason is a derivation from the sentences in `ruling.basis` and from the entries in `rests_on`. It names no backend, no krust, no KCore and no document of an implementation. A `quote` is verbatim, with the file and line in the pinned K release. The sources are K's manual (`manual`), K's tutorial, `k-distribution/k-tutorial/` (`tutorial`), `domains.md` (`domains` for its prose, `builtin-module` for the K text of the builtin modules), `kore-syntax.md` (`kore-syntax`), the KORE prelude (`prelude`), and matching logic where the text defines it (`matching-logic`).
- **`source = "kompiled"`** names a sentence by its place in `kore.txt`. It supports a statement about what the written KORE sentences mean (`[ruling.kore]`, with `matching-logic` or `kore-syntax` beside it), never a statement about what the K text means: kompile is an implementation, and its output is an observation of one release.
- **`rests_on`.** A case rests on several readings at once (strict evaluation, when a rule applies, what a priority does). Those readings are text entries, and a case cites them instead of restating them. A `settled` entry rests only on `settled` entries. An entry that rests on an `unsettled` entry is `unsettled`, and its readings are named after that entry's.
- **`unsettled`.** Where the text is silent, the entry has no answer of its own and at least two readings. Each reading has a name, a statement, an answer and a consequence. A reading without a single ground answer carries `answer` in prose instead of `finals`.
- **A value the text leaves open.** Where the text states that a value exists and not which (a `total` function no equation covers, `kk:t14-total-no-equation`) or not whether one exists (`kk:t13-fn-no-equation`), the readings that each fix the value are joined by a reading `rest` that keeps the choice open per interpretation, with a prose `answer`: the result in each interpretation. A result given per interpretation, each reading's result under the condition that selects it, is that reading (`reading:rest`, c11, c42).
- **`interpreter`.** `kore.k` computes something at an unsettled case. The entry says which reading that is, or `"outside"` when what `kore.k` computes is no reading of the text; `"outside"` needs a disposition for `kore.k`, and only then has `kore.k` one.
- **`disposition`.** How an implementation's result stands against the ruling, with its reason. At a settled entry the one form is `difference`: the result is not the ruling. At an unsettled entry:
  - `difference`: the result is no reading;
  - `reading:<name>`: the result is that reading and cannot be compared mechanically (finals under conditions that cover several readings);
  - `coincides:<name>`: the finals equal that reading's, reached by a route that is not the reading. The equality must hold.
- The implementations are named `haskell`, `llvm`, `kcore`, and `kore.k` for the interpreter as krust runs it.

## 3. The ruling of a text entry

A settled text entry has `statement`, in prose, and `form`:

| `form` | the statement says | further fields |
| --- | --- | --- |
| `means` | what the sentence or the construct denotes | none |
| `same-text` | the construct changes no sentence: the text equals another entry's | `other = "kk:tNN-..."` |
| `differs-in` | the construct changes these sentences against another entry | `other`, `sentences` |
| `no-sentence` | the construct gives no sentence of its own | none |
| `rejected` | there is no text: the frontend refuses the K text | none |
| `no-model` | the sentences as written have no model at the stated point | none |
| `hook-value` | the value of a hook at stated arguments | `hook`, `points` (argument and value pairs, or `unstated`) |

- A `hook-value` entry quotes the `domains.md` sentence in `ruling.basis` and needs no K text. A point the prose leaves open makes the entry `unsettled`, with the candidate values as readings.
- `rejected`, `same-text` and `differs-in` are statements about what the frontend delivers.

## 4. `evidence.json`

Written by `tools/case.py`, never by hand.

```json
{
  "inputs":  {"answer": "<sha256>", "def.k": "<sha256>", "pgm": "<sha256>"},
  "kompile": {"release": "K v7.1.337", "command": "kompile --backend haskell ...", "exit": 0,
              "kore.txt": "<sha256>", "message": null},
  "ruling_canonical": {"settled": ["inj{SortS,SortKItem}(Lblb...(1))"],
                       "readings": {"applied-blocks": ["..."], "empty-result-does-not-block": ["...", "..."]}},
  "implementations": {
    "haskell": {"version": "K v7.1.337: kompile --backend haskell; krun --search (kore-exec 0.1.155)", "finals": ["..."]},
    "llvm":    {"version": "...", "finals": ["...", "..."]},
    "kcore":   {"version": "kcore-spec <commit>, kcore oracle", "finals": ["..."], "imported_from": "<file sha256>"}
  }
}
```

- `inputs` holds the SHA-256 of each file of `[text].files`, and `answer`.
- `inputs.answer` is the hash of the answer fields alone, so that a change of a reason, a basis or a disposition leaves the evidence current. It is the SHA-256 of the UTF-8 text of this JSON value, with sorted keys, no space after `,` and `:`, and characters outside ASCII written as themselves (`check.answer_hash`):

  ```json
  {"finals": <[ruling].finals or null>, "finals_canonical": <[ruling].finals_canonical or null>,
   "kompile": <[text].kompile>,
   "readings": [{"finals": <or null>, "finals_canonical": <or null>, "name": <name>}, ...]}
  ```

  with the readings in the order of `entry.toml`.
- `kompile` is absent for an entry that has no K text to kompile (a KORE text, a quoted declaration). Its `exit` is 0 exactly when `[text].kompile` is `accepts`; `message` is kompile's output where it refused the text, else `null`. `kore.txt` is the hash of the entry's `kore.txt`, absent where kompile wrote none.
- `ruling_canonical` (a case only) is the hand-written `finals` (`settled`), and each reading's (`readings`, by name; a reading with a prose `answer` has no key), in the canonical text `tools/korek.py` prints. It is a translation of the ruling and changes no word of it. `tools/case.py` parses each term with `kast` against the kompiled `def.k`: the term the `<k>` cell holds, for a configuration of one cell; the top cell, for one of several. Where `kast` does not parse the terms (a cell collection of several instances, or of none), the entry carries `finals_canonical` in place of `finals`, taken as written.
- A row of `implementations` holds `version` and `finals` (canonical texts, sorted), or `error` where the implementation failed. `kcore` is optional, added by `tools/case.py --import kcore=FILE` with `imported_from`, the SHA-256 of FILE. A row is kept only while the K text it was computed from is unchanged. For a text entry the rows hold what was observed of each implementation on the text, and there may be none.
- `kore.k`'s result is not stored: `tools/check.py` runs it and treats it as one more implementation.

## 5. What `tools/check.py` checks

An entry fails for one of three causes.

1. **Schema fault.** `entry.toml` does not parse; a field of section 2.1 is missing, has a value outside its list, or is not one of the fields; no `ruling.basis`, or one without `locator` and `quote`; an unsettled entry with fewer than two readings, or a reading without an answer and a consequence; a settled entry resting on an entry that is not settled; `rests_on` naming no entry; an unsettled case without `interpreter`; a word of an implementation in `reason` (`haskell`, `llvm`, `krust`, `kcore`, `backend`, `compatibility.md`); `[text].kompile` against the exit code in `evidence.json`; an `[[observe]]` pointer that does not hold.
2. **Stale.** A hash in `evidence.json` is not the present one (the answer, a file of the K text, `kore.txt`), the canonical text of the ruling is missing, or there is no `evidence.json`.
3. **Unrecorded or outlived difference**, for each implementation result of a case, `kore.k`'s included:
   - settled: the result equals `ruling_canonical.settled`, or a disposition names the implementation. Equal and named fails: a disposition does not outlive its difference.
   - unsettled: the result equals one reading's finals and no disposition names the implementation; or a disposition names it, and then `difference` requires that the result equal no reading, and `coincides:<name>` that it equal that reading's finals. `reading:<name>` is not compared.
   - `kore.k` at an unsettled case: its result equals the finals of the reading `interpreter` names (not compared where that reading's answer is prose); or `interpreter` is `"outside"` and a disposition names `kore.k`.
   - a disposition names an implementation of which no result is recorded.

An implementation that differs from the ruling under a disposition is not a failure, whichever implementation it is.
A text entry is checked for causes 1 and 2.
What the script does not check: that a `quote` stands at its `locator`, that the reason follows from the basis, and the rule on `source = "kompiled"`.

It prints one line per entry, its status and, for a case, how each implementation stands (`=`, `reading:<name>`, `coincides:<name>`, `differs`), then a summary: the entries that pass, how many are settled and unsettled, and per implementation the number of recorded differences, `kore.k`'s apart. `kore.k`'s count is the list of cases where the catalogue's interpreter does not compute the settled ruling or computes no reading of the text: work for `kore.k`, not a fault of the entry.

## 6. The ruling hash

A reader of the catalogue that rests on an entry (a `rows.toml` row of kcore-spec) records which ruling it read by the entry's ruling hash. `tools/check.py --ruling-sha ID...` prints it, one line `ID SHA` per id (`kk:ID` or `ID`). It is the SHA-256 of the UTF-8 text of this JSON value, serialized as `inputs.answer` is (`check.ruling_hash`):

```json
{"reading": <the [[reading]] blocks, in order, or []>, "ruling": <the [ruling] table, with its [ruling.kore] and [[ruling.basis]]>}
```

The dispositions, notes, `[[observe]]` pointers, `subject`, `rests_on` and `[text]` are outside it: a change of those leaves a citing row current, and a change of the ruling, of a quoted sentence or of a reading marks it stale.
