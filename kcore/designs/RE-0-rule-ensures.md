# FD-E: OD-7 decided, and the design of `ensures` on `Rule`

Fable design agent, 2026-11-14. Read-only; nothing was built or run.
Lean read at the released tree `kcore-merge` (`c68b1a1a`); the experiment at `kcore-reader`.
Section 7 lists what was not read.

---

## 1. OD-7: decision

**R-block stands.** A rule that matches with its `requires` true applies, whatever its right side or
`ensures` gives, and a rule that applies blocks the larger priority numbers.
`NotApplies`, `RuleReqFails` and `applies` keep their text.

### 1.1 The reason, from K's text

`OD7-blocking.md` opens with "K's text does not say". For the `ensures` case that is too weak: three
quoted sentences of K4, read together, do say.

| Sentence | Place | What it fixes |
|---|---|---|
| "If the requires clause does not evaluate to `true`, then the rule does not apply." | UM:1153-1157 | The only stated cause of a matching rule not applying is its `requires`. |
| "It *may* cause the entire term to become undefined, but the backend will not stop itself from applying the rule in this case." | UM:1159-1164 | A rule whose `ensures` empties the result **applies**. |
| "the second rule above will only be tried after the first rule has been shown not to apply" | UM:1722-1724 | The larger priority number is reached only where the smaller one does not apply. |

So, at a configuration where A matches, `requires` is true and `ensures` is false: A applies (second
sentence), hence it has not been "shown not to apply", hence B is not tried (third sentence). That is
R-block, and the configuration is "applies, undefined" (U), in the text's own words.

Two limits of this reading, stated plainly:

- UM:1722-1724 stands in a section whose only example is a function. K4(a) found no sentence that
  separates rewrite rules from function equations, so the sentence is read for both.
- UM:1166-1173 lists "build `alpha(RHS #And ENS)` and check if it's satisfiable" as a step of applying.
  It does not say that failing that check makes the rule "not apply", and UM:1159-1164 says the
  opposite for `ensures`.

For a right side that is undefined without an `ensures` (`X /Int 0`), no sentence speaks. The text
names the end state `RHS #And ENS` (UM:1166-1167), one pattern; `rhsE_eq` shows the `ensures` case is
the undefined-right-side case with `defA := defA && E`. A reading that blocked for one and skipped for
the other would make `Step` depend on how an empty right side is written. One reading covers both.

### 1.2 The reason, from Lean

Checked against the statements in `BlockingNoResult.lean` (they say what the findings file says).

| | R-block | R-skip |
|---|---|---|
| Model, sound, complete, unique step (`theory_model`, `sound_complete`, `sound_complete_unique`) | yes | yes |
| Competitor in B's axiom | A's left side and `requires`: the left side of A's own `\rewrites` (`block_comp_lhs_req`, `rfl`) | must name `⌈rhsA⌉` (`skip_needs_rhs`): the left side of no axiom of the text |
| Functions (`f_d0`, `fblock_iff`, `fskip_iff`) | the text's equations plus closure have exactly this model | contradicts the text's own equation for A |
| U (applies, no result) | exists exactly at `Q` true, right side empty (`block_U_iff`) | never (`skip_no_U`) |
| `ensures` | a right-side fact; differs from the conjunct reading at c44, and in N/U at c43 | equals the conjunct reading (`ensures_skip_eq_conj`) |

**Provable under R-block, not under R-skip:** `applies c r'` is the left side of r''s axiom; rules and
function clauses block by one criterion (left side and `requires`); at fd0 the function text's value;
`a` is U at d0.

**Provable under R-skip, not under R-block:** no configuration is U; `ensures` is a `requires`
conjunct with no loss; at d0 `a → c`; the theory entails `TextG` at d0.

### 1.3 Why the `TextG` result does not decide

`d0_textG` (R-skip entails `TextG` at d0, R-block contradicts it) reads as a point for R-skip. It is
not one. `TextG` gives B the axiom `a → •c` with no premise: it is the text with the `priority`
attribute deleted. `prio_beyond_text` shows both readings contradict `TextG` as soon as A has a
successor. So `TextG` measures how often a reading lets the priority act, and any reading of the
priority loses against it. The manual says the priority "*must*" be respected (UM:1404-1414), so
`TextG` is not the text either.

### 1.4 Cost

| | R-block | R-skip |
|---|---|---|
| Cone definitions changed | none | `RuleReqFails` or `NotApplies`, `applies` or `prioRuleK`, and through it `Γstep` |
| Proofs redone | none | every proof that reads `applies` or `NotApplies` (`FaithfulNeg`, `FaithfulStep`, the executors' `step_iff`) |
| Rules against functions | one criterion | two criteria, or a function reading that contradicts kompile's equations |
| `kcore agree` | c44 stays `{b(1)}` | c44 becomes `{b(1), c(0)}`; the 10 `trivial-result` texts get `a → c` |

### 1.5 Reversal

Reverse to R-skip if any of these is found:

1. A sentence of K's manual, or of kompile's KORE, saying that a rule whose right side or `ensures`
   is unsatisfiable "does not apply" or "fails" **for the purpose of priority**.
2. kompile writing, for an `[owise]` or `priority(N)` **function** equation, a negated competitor that
   contains the competitor's right side or `ensures`. K4 found no corpus text with a non-trivial
   competitor `ensures`. Experiment to run (orchestrator): kompile
   `rule f(X) => 1 ensures X >Int 0` beside `rule f(_) => 2 [owise]` and read the `\not(\or(…))`.
3. A later kompile writing a competitor premise on rewrite axioms that names the right side.

Recorded as evidence only: Haskell backend 0.1.155 gives c43 `{b(1)}`, c44 `{b(1)}` (R-block's
results); LLVM backend (K 7.1.337) does not check `ensures`.

---

## 2. FD-E: the kernel change

Principle: Γ's rule axiom becomes the text's axiom with its right side verbatim, plus the two
premises KCore already adds (negated competitors, definedness of the right side). `ensures` is part
of the right side; it is never part of "applies".

### 2.1 `Rule` (Core.lean:132)

```lean
structure Rule where
  vars : List Srt
  lhs : Term
  req : Option Term
  rhs : Term
  ens : Option Term
  prio : Nat
```

- Type `Option Term`, as `req`: `none` is the text's `\top`, `some E` its `\equals{Bool,S}(E, true)`.
- No default value. Every producer states it. (Generated packages read the text with
  `definition_of`, so no generated file writes a `Rule` literal.)
- `Clause` gets no field: an `ensures` on a function equation is outside this design (section 6).

### 2.2 `Step` (Step.lean)

```lean
  | rule {x y : Config c} (r : Rule) (mem : r ∈ c.rules) (σ : Subst)
      (hσ : c.WellSorted r.vars σ)
      (hmatch : PatVal c σ r.lhs x.val)
      (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
      (heval : EvalTerm c σ r.rhs (some y.val))
      (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
      (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val) : Step c x y
```

- One premise, `hens`, between `heval` and `hprio`.
- `RuleReqFails` and `NotApplies`: **text unchanged**. They read `lhs` and `req`. This is OD-7.
- The file's header comment gains one sentence: the right side is `rhs` where the `ensures`
  evaluates to `true`; neither is read by `NotApplies`.

### 2.3 Γ's rule axiom (Faithful.lean:533)

```lean
def prioRuleK (c : Semantics) (r : Rule) : Kore.Pattern :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  let right : Kore.Pattern := .and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]
  let rightDef : Kore.Pattern := .ceil C C right
  if comps.isEmpty then
    .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)), rightDef]) right
  else .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
      .not C (anyOfC C comps), rightDef]) right
```

- `right` is `rhs ∧ (E = true)`, or `rhs ∧ ⊤` without an `ensures`. Today's right side is already
  `.and C [rhs, .top C]`, so with `ens = none` the right side is today's text.
- The premise is `⌈right⌉` in place of `⌈rhs⌉`. With `ens = none` it is `⌈rhs ∧ ⊤⌉`, equal to
  `⌈rhs⌉` in every model but not by `rfl`. That is accepted: the headline proofs are redone anyway.
- Chosen over two equivalent shapes (premise `⌈rhs⌉ ∧ (E = true)` with right side `rhs`; a `match`
  on `ens`): this one is the text's right side verbatim, so the "Γ and the text" table (OD-8) needs
  one row: "premise `⌈right side⌉` added". The lemma it needs (the value of `rhs ∧ π` for a
  predicate `π`) is needed for the right side under every shape.
- `applies` (Statements.lean:112): **text unchanged**.
- `ruleItems`, `ΓRules`, `stepClosureItem`, `Γstep`: text unchanged; they read `prioRuleK`.

### 2.4 `ruleSorted` (Tie.lean:73)

One conjunct, after the `requires` one:

```lean
  reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.ens &&
```

The same conjunct in `ruleOK` and `ruleOKAll` (DefinitionWf.lean:934, 943; not cone), with
`ruleSorted_of_all`'s projection adjusted. Variables: `binds` still asks that the left side binds
every variable, so an `ensures` with a variable of its own is refused by `coreOK`, as a right side is.

### 2.5 Outside the cone, required by the field

| Place | Change | Why |
|---|---|---|
| `Emit.lean:219-220` (the rule's axiom) | right side `.and C [rhs, reqPat C ens]` | Otherwise `d.emit` of a definition with an `ensures` is a text without it, and a tie would relate the definition to the wrong text. (Finding 1.) |
| Executors: `Exec.lean:340`, `CollExec.lean:408, 421`, `Cert.lean:147, 195, 596-603` | after `b == some true` and a value of `rhs`, evaluate `ens`; not `some true` gives no successor. The "applies, no result" test (`CollExec.lean:421`) becomes `b == some true && (rhs has no value ∨ ens not true)` | `step_iff` and the N/U split |
| `Symbolic.lean:62` | the mirrored step characterization gains the `ens` conjunct | it restates `Step.rule` |
| `Lazy.lean:110` | occurrences of `r.ens` (a site of its own, or the `requires` site) | today the `ensures` is walked inside `req` |
| `Features.lean:95, 112` | `r.ens.toList` among the rule's terms; a feature flag `ensures` | account |
| `FireTac.lean:505` | `Rule.mk` arity 5 → 6 | (Finding 4.) |
| `ModelUndefRhsWitness.lean:39` | `ens := none` | literal |
| `Determinism.lean:240` `sameRule` | compare `ens` too | (Finding 5.) |

### 2.6 The reader (Parse.lean:1034-1150, 1832, 2334-2339; Account.lean:209-228)

- `ruleBodyAs` loses its `ensRes` flag and both branches: the `ensures` is read with `term N vs c`
  after the `requires` and stored in `ens`. `req` is the `requires` as written (plus `keyCut`'s
  conjuncts, as today).
- Removed: `ensGuard`, `ensGuardFirst`, `ensGuardList`, `ruleOfEnsRes`, `ensuresResultIdx`, the second
  pass in `coreOf` (2334-2339), `hasEnsures` if nothing else uses it, the refusal `ensuresBlocking`,
  the read-as class `ruleEnsuresAsRequires` (1832), `Account.ruleEnsuresResult`.
- **The conjunct reading (c43's) is removed everywhere, not kept as a fallback.** A rule with an
  `ensures` is now read as written, with no "read in another form" note.
- The reading no longer needs `Map:lookup`, `|->` or an injection into KItem in the right side, so
  nothing is refused for lack of something to guard.
- `ensGuard*` and its lemmas move to the bridging test (2.7); the library no longer holds them.

### 2.7 Bridging theorems (new file `test/EnsBridge.lean`; `test/EnsGuard.lean` folded into it)

Two encodings exist today; each gets a statement against the field. Let `c` hold rules with fields.

**B-guard** (today's reading of the 10 texts, c44, `ensrule-overlap`, `ensrule-prio`).
`guardOf r := { r with rhs := g, ens := none }` where `ensGuardFirst E r.rhs = some g`; `c_g` is `c`
with each such rule replaced. Under EnsGuard's hypotheses (`Map:lookup`, `|->`, `_andBool_` are hooks
and no constructors in `c`; `E`'s result unique):

    ∀ x y, Step c x y ↔ Step c_g x y
    ∀ r x, NotApplies c r x ↔ NotApplies c_g (guardOf r) x        -- by rfl: lhs and req are equal

So the guard encoding and the field give the same steps, the same N and the same U. From
`guard_true`, `guard_some`, `guard_no_value`.

**B-conj** (today's reading of every other rule with an `ensures`: c43, 13 corpus texts, mir).
`conjOf r := { r with req := conj r.req r.ens, ens := none }`, `conj none e = e`,
`conj (some q) (some e) = some (.app boolAnd [q, e])`; `c_j` likewise. With `_andBool_` a hook and no
constructor:

    (1) ∀ x y, Step c x y → Step c_j x y                          -- the field never adds a step
    (2) Apart c → ∀ x y, Step c_j x y → Step c x y
    (3) ∀ r x, NotApplies c r x → NotApplies c_j (conjOf r) x
    (4) NotApplies c_j (conjOf r) x → ∀ σ, WellSorted → PatVal c σ r.lhs x →
          RuleReqFails c σ r ∨ ∃ t v, r.ens = some t ∧ EvalTerm c σ t v ∧ v ≠ some (bool true)

`Apart c`: for every rule `r` with `r.ens.isSome` and every `r''` with `r.prio < r''.prio`, no value
is matched by both left sides. (`Det.overlap_sound_term` gives it from the reader's `overlap`.)
(3) and (4) are OD-6's "`NotApplies` differs exactly where `ensures` fails"; the converse of (4)
needs every term to have a result (FnHyp's first conjunct) and may be stated with that hypothesis.
(1) is the direction that makes today's corpus results an upper bound of the new ones.

No Γ-level bridge is needed: each side has `sound_hyp` and `complete_hyp`, so equal `Step` gives equal
forced successors.

### 2.8 Proofs to redo

Every `.rule r hr σ hσ hpv hreq heval hprio` and every destructuring of a step gains one component
(about 15 sites). The content is in four places; the rest is plumbing.

| Proof | What is new |
|---|---|
| Soundness of a step (`StepSound`, `FaithfulStage2-4`, `FaithfulStep`) | the premise `⌈rhs ∧ (E = true)⌉` holds, and `•(rhs ∧ (E = true))` is `•rhs`: from `hens`, by the lemma that turns `EvalTerm t (some true)` into `Γ ⊧ t = true` (already proved for `hreq`, at the same sort `C`) |
| Model exists (`ModelRules`, `ModelStep`, `ModelPat`) | in the standard model the axiom's premise gives `E = true`, hence `EvalTerm E (some true)`: the `requires` direction, reused |
| Completeness (`FaithfulComplete`) | a closure disjunct `∃x̄. L ∧ y ∈ (rhs ∧ (E = true))` gives `hens` and `heval` |
| Executors (`StepIff`, `StepIffWf`, `DetSound`, `Cert`, `CollExecSound`, `CollExecStepIff`, `CollExecFinal`) | the evaluator's `ens` test against `hens` |

`FaithfulNeg` (the competitors) should need no change in content: `applies` and `NotApplies` are
untouched. If it does, that is a stop condition (section 4).

Plumbing only, expected: `SubjectReduction`, `Runs`, `Invariant`, `NICells`, `SymbolicLemmas`,
`Params`, `Determinism`, `Fire`, `CoreChecked`, `TablesChecked`.

### 2.9 Expected effects (to be measured, not asserted)

| | Today | With the field |
|---|---|---|
| c43, KCore | `a(0)` is N; finals `{a(0), b(1)}` | `a(0)` is U; finals `{b(1)}` |
| c43 against haskell 0.1.155 | differ | agree |
| c44, KCore | `{b(1)}` by the guard | `{b(1)}` by the field |
| c43, c44 against llvm | differ | differ (that backend does not check `ensures`) |
| `kcore agree` totals (README: 67 agree / 5 differ / 14 no-reference / 2 not-runnable) | | 68 / 4 / 14 / 2 |
| Corpus read clean / `coreOK` | 353 / 353 | 353 / 353; no verdict changes |
| Texts whose `Rule` values change | | the 13 conjunct-read texts, the 10 guard-read texts, mir, the three `f2-examples/ensrule*` |
| Every other text | | same rules with `ens := none` |
| `read ruleEnsuresAsRequires` count | > 0 | class gone |
| mir | conjunct, no overlapping larger priority | same successors (B-conj (1), (2)); a failing `ensures` moves a configuration from N to U; hand-written `User` proofs that destructure a step of that rule need the extra component |
| `test/EnsuresRule.lean` | three verdicts with the `read ruleEnsuresAsRequires` note; `rules_shape` on `req.isSome` | notes empty; shapes restated on `ens`; the five step / no-step theorems keep their statements |
| Tie | "a definition read with an `ensures` is never tied" (RD-3 §12.3) | may now be tied, since `Emit` writes the `ensures`; not required by this change |

---

## 3. What the release gate must accept

**Byte-identical** (the pins): the statements of `sound_hyp`, `complete_hyp`, `SoundC`, `CompleteC`,
`StepIs`, `FnHyp`, `Semantics.coreOK`.

**Cone declarations whose text changes: exactly four.**

| Declaration | Allowed change |
|---|---|
| `KCore.Rule` | one field, `ens : Option Term`, between `rhs` and `prio` |
| `KCore.Step` | one premise, `hens`, as in 2.2 |
| `KCore.Faithful.prioRuleK` | `right` and `⌈right⌉` as in 2.3, and its doc comment |
| `KCore.Semantics.ruleSorted` | one `reqOK … r.ens` conjunct, and its doc comment |

**Byte-identical although their meaning follows the four:** `RuleReqFails`, `NotApplies`, `applies`,
`anyOfC`, `reqPat`, `ruleItems`, `ΓRules`, `Γ`, `stepClosureItem`, `Γstep`, `sortedOK`.
Any other line of the cone diff is a failure of the gate, as is any new cone declaration.
`core-manifest.toml`: layer `signature` ("rules with priorities" gains "and an `ensures`"), layer
`step` (`teaches` and "what Step.lean reads of rules"), `cone_size`, `changed`.

---

## 4. Opus briefs

Two briefs, in order. E2 starts from E1's commit. Neither is a parallel lane of the other.

### Brief E1: the field in the kernel, the reader still writing `ens := none`

Workspace and build copy: named by the orchestrator. Cone definitions this brief may change: the four
of section 3, to the texts of 2.1-2.4, and nothing else.

- **Unit 1. Definitions and the headline.** `Rule.ens`; `Step.rule`'s `hens`; `prioRuleK`;
  `ruleSorted`, `ruleOK`, `ruleOKAll`; `Emit`'s rule axiom; every `Rule` literal gets `ens := none`,
  the reader included (it keeps today's conjunct and guard readings in this brief). Re-prove in import
  order up to `Sound.lean`: `sound_hyp` and `complete_hyp` with their statements.
- **Unit 2. Executors.** `Exec`, `CollExec`, `Cert` evaluate `ens` (2.5); `step_iff` in each form and
  the stuck / final characterizations re-proved.
- **Unit 3. The remaining importers and tests.** The plumbing files of 2.8, `Lazy`, `Features`,
  `Symbolic`, `FireTac`, `sameRule`; `test/EnsuresRule.lean` and the tests that destructure a step
  still pass unchanged (the reader's output differs only by `ens := none`). One new test,
  `test/EnsField.lean`: a hand-written two-rule semantics (`a => b ensures false` at 50, `a => c` at
  200) with `coreOK` by `decide`, `∀ y, ¬ Step c A y`, `¬ NotApplies c r50 a`, and a one-rule variant
  with `ensures true` stepping.

Validation: library modules changed and their importers by `test/lake-serial.sh`; the named tests;
native `kcore gen --core` over the corpus with verdicts and generated files compared (expected: no
difference, since the reader's readings are unchanged). Not run: `run.sh`, `final.sh`, the judge,
KEVM, mir, package rebuilds.

Stop and report, with a proposal, if:

1. A headline statement's text would change, or a cone declaration outside the four, or one of the
   four beyond 2.1-2.4. In particular if `NotApplies`, `RuleReqFails` or `applies` would have to read
   `ens`.
2. `KoreAML.closureDisjunct`, `tableOf`, or any translation in `Kore/` needs a change to accept a
   right side whose second conjunct is not `\top`.
3. The model's existence or completeness needs a new conjunct of `coreOK` or a stronger `FnHyp`.
4. `FaithfulNeg`'s statements need more than renaming.
5. A corpus text changes verdict or generated files.
6. Unit 1 is not through `Sound.lean` after the four content proofs of 2.8 are done and the rest is
   not plumbing: report which lemma is missing, do not restructure.

Report: the cone diff (expected: four declarations), which modules were rebuilt, the corpus
comparison, and the hand-written `User` modules that destructure a `Step` (they will break at the
release build).

### Brief E2: the reader reads the field; bridging; agreement

- **Unit 1. Reader.** 2.6 in full. Account: the class and the listing removed or replaced by a count
  of rules with an `ensures`. `test/EnsuresRule.lean` restated per 2.9.
- **Unit 2. Bridging.** `test/EnsBridge.lean` with B-guard and B-conj (1)-(4) as stated in 2.7;
  `test/EnsGuard.lean`'s lemmas move there with the `ensGuard*` definitions. Standard axioms only.
- **Unit 3. Agreement and corpus.** `kcore agree` on the cases; c43's expectation updated; the corpus
  account; the list of texts whose rules changed, checked against 2.9; `test/README.md`'s numbers.

Stop and report if:

1. A corpus text loses `coreOK` or is newly refused.
2. c44's finals are not `{b(1)}`, or c43's are not `{b(1)}` with `a(0)` U.
3. A text outside the list of 2.9 changes its generated files.
4. B-guard's `Step` equivalence needs a hypothesis beyond EnsGuard's, or B-conj (1) fails: either
   would mean a text read today meant something else than stated, and the corpus results of the
   earlier release must be re-read.
5. B-conj (2) needs more than `Apart` and the `_andBool_` hypothesis.
6. A cone declaration changes (none may in E2).

Wave end (integration lane, not E2): release run with the Fable gate of section 3, mir and KEVM
rebuilt, the manifest edits, S27's doc comments and the OD-8 table riding on the same release.

---

## 5. Findings

| # | Place | Claim | Evidence | Sure | Settles it |
|---|---|---|---|---|---|
| 1 | `Emit.lean:219-220` | The emitted rule axiom writes `\top` for the `ensures`. Once `Rule` has `ens`, an unchanged `Emit` drops it, and a tie would relate a definition with an `ensures` to a text without one. | `.rewrites C (.and C [lhs, reqPat …]) (.and C [Term.kore c vs r.rhs, .top C])` | shown by reading | E1 unit 1 changes it; a round-trip test on `ensrule.kompile.kore` |
| 2 | `OD7-blocking.md` §2, `d0_textG` | The result that R-skip entails the guarded text at d0 does not favour R-skip: `TextG` is the text without its priority, and both readings contradict it wherever A fires. | `TextG` gives B `Valid R (· = .a) rhsB`; `prio_beyond_text` | shown by reading | nothing to run; the findings file could say it in one line |
| 3 | `OD7-blocking.md` "what K's text says" | The file says the text does not decide; UM:1153-1157, 1159-1164 and 1722-1724 together state R-block for `ensures`. | section 1.1 | shown by reading; rests on reading "applies" in the three sentences as one notion | owner may reject that reading; the Lean results alone still give 1.2-1.4 |
| 4 | `FireTac.lean:505` | The tactic matches `Rule.mk` at arity 5 and will silently take the other branch at 6. | `if r.isAppOfArity ``Rule.mk 5 then pure r else kdeep r` | shown by reading; the effect of the other branch is suspected | E1 unit 3; a package that uses the tactic |
| 5 | `Determinism.lean:240` | `sameRule` compares `vars`, `lhs`, `rhs` and neither `req` nor `ens`. Whether its use stays correct when two rules differ only in `ens` depends on what its lemma claims. | the definition | suspected | read its soundness lemma in E1 unit 3 |
| 6 | the brief's reading set | `RD-3-wasm-mir.md` is not in `kcore-merge`'s findings; it was read from `kcore-reader`. | `ls` | shown | none needed |
| 7 | K4(c)(iii), `OD7-blocking.md` "Not covered" | No text shows what kompile writes for a function competitor with a non-trivial `ensures`; OD-7's function argument rests on `requires` only. | K4: "Not found: a corpus text with an `[owise]` function equation whose competitor has a non-trivial `ensures`" | shown | the kompile experiment of 1.5 item 2 |

## 6. Left open by this design

- `ensures` on a function equation: no `Clause` field, no reading decided. What the reader does with
  one today was not read.
- Whether to tie definitions with an `ensures` now that `Emit` writes it.
- A witness (`ModelEnsWitness`) that the axiom without `⌈right⌉` has no model at a false `ensures`,
  beside `ModelUndefRhsWitness`: optional; `ensures_text_no_model` shows it on the toy.

## 7. Not read

- The proofs themselves (`Faithful*`, `Model*`, `StepIff*`, `CollExec*`, `Cert`): section 2.8 is from
  `grep` of where `r.req`, `r.rhs` and a step's components are read, not from the proofs.
- `Kore/Translate.lean`, `closureDisjunct`, `tableOf`: whether they accept the new right side is stop
  condition 2 of E1, not a checked fact.
- `FaithOK.lean`, `NameCodes.lean`: whether a `coreOK` conjunct walks a rule's terms and so must walk
  `ens`.
- `kcore agree`'s code, `test/agree.jsonl`, the harness's N/U computation: the numbers of 2.9 are
  from `test/README.md:283-297`.
- mir's and KEVM's packages and `User` modules; `TICKETS-2026-11-11.toml`; REVIEW-SYNTH beyond OD-6,
  OD-7, S6, S18 and step 4.
