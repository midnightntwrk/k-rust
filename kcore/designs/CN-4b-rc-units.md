# CN-4b: the ten R-c rows of CN-4 §7, each decided

**Amendments after REVIEW-CN4b (orchestrator, 2026-11-16; they override the body below).** findings/REVIEW-CN4b.md (cold; BAND and the CE fix's inductive shape kernel-checked, the defects argued) found HO-1, HO-2, row 4 (B), FL, BAND and UNIT sound, and SV-D not judgeable before its probe. All of the following are accepted:
- **CE-1 (severe).** With CE's `Eval` side as written, `sound_at`, `complete_at` and `famEx_closed` are false as pinned. Counterexample: `f() => g(?Z:Int)` with `post := Z ∈ lp()`, `lp() => lp()`; the design's own `f(X) => ?B:Bool` fixture fails too. A clause with `exs` has a result only where an extension exists, every value extension has `post` decided, and each gives the one result or none. Spelled as three constructors (`clause` with `exs = []`, `clauseEx`, `exNone`) plus `InstIs`; the kernel accepted this inductive shape. Where instances differ the function has no result, so §1.5's rows "two results, ¬FnDet" become "no result".
- **CE-2.** `Coherent.of_fnDet` stays provable for a clause whose existential variable stands in a pattern: use `AgreeOff (cl.exs.filter (!cl.leftVars.contains ·))`.
- **CE-3.** In §1.5 and §1.6, "no theorem is stated" means no `…_hyp` theorem.
- **SV-D.** Read only where no clause of larger priority exists; otherwise refused `setVariable`. Without this, `f(@S,@S) => @S` beside `f(X,Y) => X [owise]` gives `Γ ⊧ f(a,b) = a`, which the text does not state. It stays fixture-first; the probe's sentences decide the rest.
- **Row 6 (B), `\in` form, the "g constant" sub-case.** Class R-c naming `SetLawAt`, not R-a: the second model falsifies the sentence, so no pair of models exists.
- **Row 4 (B).** The wording is "sound and complete".
- **UNIT.** CN-4 §6 item 2 reads "an associativity or idempotence law the text writes for it is a premise of the theory".
- **SV-1 beside `[owise]` (findings/SV1-OWISE-decision.md).** The reason given under "Strongest attack (SV-1)" is false: kompile 7.1.337 writes the `[owise]` exclusion of `f(@S, @S) => r` as `∃G. X0 ∈ G ∧ X1 ∈ G`, G an element variable, which is `X0 = X1`; so the `[owise]` sentence states `f(a, b) = q` at every a ≠ b, the first sentence states `f(a, b) = r` there, and where r and q differ at two distinct elements the text has no model. The conclusion stands for another reason: the first sentence is read exactly (`setvar_in_drop`); `Γ` reads the `[owise]` equation with the premise it gives every clause of priority 200, that no executable clause of a smaller priority applies as read, which is narrower than the text's, so the text's sentence entails `Γ`'s (named weakening `owiseDisjunctNarrower`). `Γ` states `f = r` at every pair and leaves out the `[owise]` sentence's value off the diagonal; the account notes, conditionally, that the text has no model. The reader accepts for such an equation the disjunct with one bound variable at both positions (with the note) and the one with two distinct variables (exact, no note); any other is `exclusionShape`. §4's table row 1 gains "beside an `[owise]` equation: read, with that note". §13's `setVariable` row is unchanged: a set variable in an `[owise]` equation's exclusion is its case (i) ("an exclusion", as the reader's detail already says), and one in an `[owise]` equation's own arguments is refused as a shape `setvar_in_drop` does not state. This entry does not touch the SV-D entry above: SV-D is the direct form with the set variable on the right, refused beside a clause of larger priority because the clause read there (the diagonal) is a weakening and `Γ` would state the value off it; SV-1 is the `\in` form with the set variable on no right side, read exactly, so a clause of larger priority beside it is narrowed and nothing is stated that the first sentence does not state. The attack's text is replaced by:
  **Strongest attack (SV-1).** `rule f(@S, @S) => r`, `rule f(_, _) => q [owise]`. The text states both values off the diagonal (the `[owise]` exclusion is the diagonal), so the reading cannot be the text. It is the text's first sentence, exact, and a weakening of the second that the second entails; the mirror reading (the first at equal arguments, the second as written) weakens an exact sentence and is the singleton reading CN-4 §6 item 4 refuses. What `Γ` leaves out, `f(a, b) = q` for a ≠ b, is stated by the text beside `f(a, b) = r`; the account says so.
- **CE-5.3 (findings/CE-fixes-inj-decision.md, 2026-11-17; orchestrator chose variant N).** `fixesBy` gains `| .inj _ _ (.var j) => j == i` after its `.var` line (one injection; nested injections not read) and `Cond.fixes`' `.mem` arm becomes `fixesBy ok i t u`; the side condition is `c.subsorts.contains (a, b)`, which `condOK` already decides, so the arm carries no test. `inj_value` is the landed `inj_back`. No pair fails under `coreOK`; a hand-built pair with a collection or domain-value upper sort is R-c naming the missing `cons-fun` and `cons-inj` of `inj Sort{a} Sort{b}`. Section 6 of the decision lists the CE-4, CE-PARTITION, rows.toml and REVIEW-EX-CE §2.2 wording that reads as amended there.
- **CE-5.1/5.2 (findings/CE-fixes-confined-scoped-decision.md, 2026-11-17).** `Clause.fixedExs` admits a confined existential variable with `j != i`; the `Cond.fixes` arm for `.ex` overrides the bound index in `ok` and admits a bound variable fixed by its body only where its sort has a value. "No premise on B's sort" is false (`vac_some`): the row "s has no value" is class R-a with the two models of the decision. Section 8 of the decision lists the CN-4b lines, the CE-4 wording and REVIEW-EX-CE text that quote the old arity; they read as amended there. Variant B (widening `Cond.bound`'s `.ex` arm) waits on CE.decision-bound-fixed.
- **CE-4-and-eq (findings/REVIEW-andAsEnsures.md, section Fix; orchestrator chose (a), 2026-11-16).** N4 applies to every `\and` of terms at a term position of an equation's right side, with or without a binder (fresh Z in `exs`, `Z ∈ t₁ ∧ … ∧ Z ∈ tₙ` in `post`); hoist's `.same` is not applied to an equation and its `.isTrue` is unchanged. For a rule's right side, `t #And u` reads `rhs = C[t]`, `ens = t ==K u`, a named weakening the text entails (findings/REV-rule-and-terms-decision.md); the exact reading through `Rule.post` is REV-rule-and-in's.
- **CE-4 (partition rows P2, P3, P5; findings/CE-PARTITION-decision.md; orchestrator chose (a) with (a′), 2026-11-16).** The reader normalizes an equation's right side, each step an equality in every interpretation: N1 an `\exists` under applications and injections is hoisted to the top (`app_exists`); N2 an `\exists` in a conjunct of an `\and` at a term position is hoisted (`and_exists`); N3 an `\exists` in an alternative of an `\or` at a term position is hoisted where its sort has a value on the built definition (`or_exists`), and is otherwise refused R-c naming `Cond.fixes`; N1 to N3 precede the tests. N4 is CE's arm, entered where EX does not read the equation: where the equation has a binder, an `\and` of terms at a term position becomes its variable conjunct V with `V ∈ tⱼ` in `post`, or a fresh Z with `Z ∈ t₁ ∧ … ∧ Z ∈ tₙ` (`var_and_mem`, `mem_and`, `cut_identity`). (Under choice (a′) of section 3, EX's E2 reads the first form for its own variable.) Bound variables are renamed apart from every name of the axiom. Hoisting stops at `\not`, `\implies`, `\iff`, `\forall`, `\mu`, `\nu`: those keep their own rows. A binder inside a predicate conjunct is not touched. `existentialEquation s` is class R-a only for a variable that N1 and N2 alone put at the top and that no conjunct equates with a term; a variable that fails `clausesPlain` after N3, over a confined existential variable, or under an injection is refused with class R-c naming `Cond.fixes`, `Clause.fixedExs` or `fixesBy`, and the detail says which. §13, row `manyValuedRightSide`: its shape column reads "`\top`; `\not`" as now; add "an `\exists` under `\not` (P1)". Row `existentialEquation s`: the "Kind and reason" cell gains the R-c cases above. REVIEW-EX-CE §1.4's table: rows P2, P3 and P5 go; a row P0 "normalize (CE-4)" stands before P1; P1b and P6 are unchanged. Under choice (a) of section 1, E1 reads "after CE-4's N1, its right side … is one `\exists` at the top".

Design agent (Fable), 2026-11-16.
CN-4b decides the ten rows that `designs/CN-4-constructs.md` §7 lists as "R-c rows that CN-4 keeps or creates without a unit", and CX-V D11.
It adds units to CN-4 and edits no line of that file. It does supersede some of CN-4's sentences for the briefs named here: section 12 lists each. Where a unit replaces a refusal row of CN-4 §5, section 13 gives the row to put.
Rows 1 and 2 share one section (one unit), and so do rows 4 and 5.
CN-4 §0 (rules every brief carries) holds for every unit here.

**What was run.** One scratch file, kernel-checked from kcore-theory's package root at `8c2f206a`, axioms `propext` only: `<scratchpad>/cn4b/Band.lean` (row 9: `nf_left`, `nf_right`, `nf_idem`, `nf_nf`, `nf_mem`, `nf_single`, `nf_ne_nil`, and two `decide` examples).
Every other Lean block is **to run**, under CN-4's rule: where one does not elaborate or a stated lemma is not provable, the lane stops and reports; it does not respell, pin less or move a hypothesis.
No kompile was run: every probe is brief P's, and each unit is written for both outcomes.
No unit here has had a counterexample pass by another agent. Each section ends with the strongest attack I tried.

**Marks.** COLD-REVIEW as in CN-4. **(A)**: a unit. **(B)**: a refusal on first principles, with the text and the two models.

## 0. Table

| # | Row of CN-4 §7 | Decision | Unit | Owner (brief) | Predecessors | COLD-REVIEW |
|---|---|---|---|---|---|---|
| 1 | `#Or` on a non-total function's right side; more than 8 alternatives | A | CE | brief CE, alone against lanes R and F | e3, F2, R3 (the `Holds` lemma), R4, F9; brief P (`e3-ml-eq-rhs-or-total`) | yes |
| 2 | existential equation at a confined sort, beyond F4's shape | A | CE | brief CE | as row 1; brief P (`e3-eq-exists-bool`) | yes (with 1) |
| 3 | `openRight` (ii): a variable under a collection's symbols | A | HO-1 | lane R (R4) | R3 | yes |
| 4 | a function-overloaded symbol in a pattern | A, with a part B | CUT (reader), HO-2 (arm) | lane P (P3); lane R (R4); brief CE for the clause side | R3, F3, e3 (`Clause.pre`); HO-2 after HO-1 | yes (HO-2) |
| 5 | `openGeneratorPattern` (ii) | A if kompile writes the text, else no text | CUT | lane P (P3) | R3, V2; brief P (`e2-open-mixed`) | no |
| 6 | a non-linear set variable | A in three forms, a part B | SV-1, SV-R, SV-D | lane P (P3) | brief P (the set-variable probes); SV-R after R3; SV-D after FL | SV-D only |
| 7 | `overloadAxiom`, the larger symbol a function | A | OVF | lane F (F9), reader only | F3; brief P (`e5-ovl-fn-fn`) | no |
| 8 | `lawAxiom` (i) | A | FL | lane F (F9) | INT-C; brief P (`e2-fn-assoc`) | yes |
| 9 | `openLaw (assoc, idem)` | A | BAND | lane V (V13) | V2 | yes |
| 10 | `openLaw (unit)` | A | UNIT | lane V (V13) | V2, FL; brief P (`e2-unit-ctor`) | yes (with 8) |
| D11 | overlap of two entries of one value | decided: no value | none (fixture line) | lane V (V1-c1 fixture) | none | no |

No row ends as a whole (B). Rows 4 and 6 each keep a part that is a first-principles refusal; both parts fall under reasons CN-4 §5 already has (`openRequires`, `setVariable`), and their models are given here.
No decision moves the text of `SoundC`, `CompleteC`, `ExactC`, `FnHyp`, `coreOK`, `OpenLaws`, `sound_hyp`, `complete_hyp`, `exact_hyp`, `consistent_of`. One pinned definition is added (`FnLaws`, with `LawAt`). The bodies of `Eval`, `FnSolves`, `Coherent`, `rulesPlain`, `clausesPlain`, `paramsPlain`, which pinned statements name, change for the new shapes only (rows 1 to 4, 9, 10).

## 1. Rows 1 and 2, unit CE: a clause with existential variables — COLD-REVIEW

### 1.1 The construct, from the sentences

Row 1. `f(P̄) => t₁ #Or … #Or tₙ` is the sentence `premise → f(X̄) = ⋁ₖ tₖ ∧ ⌈E⌉`. Where f has no `functional` sentence the text has a model in which `f(x)` is every element of each defined side. F6's clauses state `f = tₖ` for each defined side, which that model refutes. So the reading has to state the union and nothing more.
Row 2. `f(P̄) => rhs[?Y] ensures E[?Y]` is `premise → f(X̄) = ∃Y:S. (rhs ∧ ⌈E = true⌉)`: the union over the elements of S. At a confined S those elements are the values.
Both are one shape: **the right side is a union over existentially bound variables**, since in every interpretation `C[φ] ≡ ∃Z. C[Z] ∧ Z ∈ φ` (application distributes over union; the device R3 uses for rules). `t₁ ∨ t₂` at a term position is `∃Z. Z ∧ (Z ∈ t₁ ∨ Z ∈ t₂)`.

The fields exist since U0 and are inert: `Clause.exs`, `Clause.post`. CE admits them. It is the repair CX-F finding 4 proposed and CN-4 F4 called "right as a theory and not taken"; CN-4 F4 and F6 named it as their reversal.
F4 and F6 stay as they are for the shapes they read (a total function; at most 8 alternatives): their clauses are plain `pre` clauses, which every consumer reads. CE reads what they refuse.

### 1.2 What can be an existential variable of a clause

A rule's existential variable is decided by values in two ways: held under constructors of the successor, or confined. A function's value is not a given value, so the first way does not exist: `f() => c(?Z:Int)` has the value `c(j)` at an element j that is no value's, and that stays `existentialEquation Int`, R-a.
There is one other way: the predicate equates the variable with a term over the other variables. `Z ∈ t` at values of t's variables holds only at the value of t, or nowhere. That is what the `#Or` reading produces.

```lean
-- FaithOK.lean (to run)
/-- The condition, where it holds, equates the variable i with a term whose variables `ok` admits. -/
def Cond.fixes (ok : Nat → Bool) (i : Nat) : Cond → Bool
  | .mem _ (.var j) t => j == i && (varOccs t).all ok
  | .and p q => p.fixes ok i || q.fixes ok i
  | .or p q => p.fixes ok i && q.fixes ok i
  | _ => false

/-- The existential variables the predicate fixes, in rounds: by a term over the variables that are
not existential and the existential ones fixed in an earlier round. -/
def Clause.fixedExs (cl : Clause) : List Nat :=
  (List.range cl.exs.length).foldl (fun acc _ =>
    cl.exs.filter fun i => acc.contains i ||
      cl.post.fixes (fun j => !cl.exs.contains j || acc.contains j) i) []
```

### 1.3 The texts (all lane F's; each is e3's text with the change stated)

```lean
-- Evaluation.lean, before the block (to run)
/-- σ' is σ off the indices `is`. -/
def AgreeOff (is : List Nat) (σ σ' : Subst) : Prop := ∀ i, i ∉ is → σ'.lookup i = σ.lookup i
/-- The variables of a clause that its right side does not bind. -/
def Clause.univ (cl : Clause) : List Nat := (List.range cl.vars.length).filter (!cl.exs.contains ·)

-- in the block: the three edits and one new relation
    | clause …                                  -- e3's premises, then:
        (hrhs : EvalTerm c σ cl.rhs r) (hens : …)
        (hpost : Holds c cl.vars.length σ cl.post true)
        (hex : cl.exs = [] ∨ r.isSome = true) : Eval c f vs r
    | ensFails … (hex : cl.exs = []) … : Eval c f vs none      -- otherwise e3's text
    /-- A clause with existential variables decides and none of its instances gives a value. -/
    | exNone {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause} {σ : Subst}
        (hfn : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses) (hne : cl.exs ≠ [])
        (hσ : c.WellSortedAt cl.vars cl.univ σ) (hmatch : PatVals c σ cl.pats vs)
        (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
        (hpre : Holds c cl.vars.length σ cl.pre true)
        (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c vs cl')
        (hall : ∀ σ', AgreeOff cl.exs σ σ' → c.WellSorted cl.vars σ' → InstFails c σ' cl) :
        Eval c f vs none
  /-- The instance of the clause's right side at σ gives nothing. -/
  inductive InstFails (c : Semantics) : Subst → Clause → Prop where
    | ens {σ cl t w} (ht : cl.ens = some t) (he : EvalTerm c σ t w) (hw : w ≠ some (bool true)) :
        InstFails c σ cl
    | post {σ cl} (h : Holds c cl.vars.length σ cl.post false) : InstFails c σ cl
    | rhs {σ cl} (h : EvalTerm c σ cl.rhs none) : InstFails c σ cl
```

What they state: for a clause with `exs`, the function's values at `vs` are the values of the instances, over value extensions of the match on `exs`, whose `ensures` and `post` hold and whose right side has a value; it has no value where the clause decides and every extension fails. For a clause with `exs = []` every text is e3's (`hex` holds by `Or.inl rfl`; `hpost` is `Holds.top`, since `clausesPlain` below asks `post = .top` of it).
`hall` is a Π ending in `InstFails`, as `Fails.intro`'s premise ends in `ReqFails`: strictly positive.

```lean
-- EvalFunctional.lean / FnSolves.lean (to run)
/-- The instance of the clause at σ gives the value v. -/
def Clause.Gives (c : Semantics) (cl : Clause) (σ : Subst) (v : GroundTerm) : Prop :=
  EvalTerm c σ cl.rhs (some v) ∧ (∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) ∧
    Holds c cl.vars.length σ cl.post true

/-- A result of the clause at the match σ. Without `exs`: e3's two cases. With `exs`: a value some
extension gives, or none where every extension fails. -/
def Clause.Res (c : Semantics) (cl : Clause) (σ : Subst) (r : Option GroundTerm) : Prop :=
  (cl.exs = [] ∧ (((∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true))) ∧ EvalTerm c σ cl.rhs r) ∨
      ∃ t w, cl.ens = some t ∧ EvalTerm c σ t w ∧ w ≠ some (bool true) ∧ r = none)) ∨
  (cl.exs ≠ [] ∧ ((∃ σ' v, AgreeOff cl.exs σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v ∧ r = some v) ∨
      (r = none ∧ ∀ σ', AgreeOff cl.exs σ σ' → c.WellSorted cl.vars σ' → InstFails c σ' cl)))
```

- `Coherent c cl cl'`: its premises unchanged; its conclusion becomes
  `(cl.exs = [] ∧ cl'.exs = [] ∧ (the landed first disjunct)) ∨ ∀ r r', cl.Res c σ r → cl'.Res c σ' r' → r = r'`.
  For two clauses without `exs` it is the landed proposition (`Res` unfolds to the landed two cases).
- `FnSolves c`: the right side of its `↔` becomes `∃ σ', AgreeOff cl.exs σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v`.
- `Clause.AppliesAt`: its first conjunct `c.WellSorted cl.vars σ` becomes `c.WellSortedAt cl.vars cl.univ σ` (the same proposition where `exs = []`, by a lemma the unit proves). An existential variable is in no pattern, `requires` or `pre` (`clauseSorted` below), so whether the clause applies does not read it. `Eval.clause` keeps `WellSorted cl.vars σ`: its σ is an instance.
- `Clause.DecidesAt`, `Clause.Decides`, `Fails`, `ReqFails`, `PrioDecided`, `exclusion`: unchanged.
- `clauseEquation`, `competingEquation`: the right side is under the binder, as `ruleRight`'s:

```lean
-- Faithful.lean (to run): the pair (right side, ensures part) both equations pass to `eqnSentence`
def clauseRhs (c : Semantics) (f : Fn) (cl : Clause) : Kore.Pattern × Kore.Pattern :=
  let vs := canonVars c cl.vars
  let S := srtOf c f.result
  if cl.exs.isEmpty then (Term.kore c vs cl.rhs, reqPat S (cl.ens.map (Term.kore c vs)))
  else ((cl.exs.filterMap (vs[·]?)).foldr (fun v p => .exist S v.kore p)
      (.and S ([Term.kore c vs cl.rhs, reqPat S (cl.ens.map (Term.kore c vs))] ++ Cond.conj c vs S cl.post)),
    reqPat S none)
```

- `clauseSorted` gains `&& cl.exs.all (· < cl.vars.length) && nodupB cl.exs && cl.exs.all (fun i => !cl.leftVars.contains i) && condOK c cl.vars cl.post`.
- `clausesPlain` (CE's body; HO-2 later widens the `conf` of its last conjunct, section 3.3):

```lean
def Semantics.clausesPlain (c : Semantics) : Bool := c.fns.all fun f => f.clauses.all fun cl =>
  let conf := fun i => (cl.vars[i]?.map c.confined).getD false
  (!cl.exs.isEmpty || cl.post.isTop) &&
  cl.exs.all (fun i => conf i || cl.fixedExs.contains i) &&
  (!cl.reqOpen || cl.reqClosed || cl.openCondVars.all conf)
```

`readsConfined` is true of a definition with such a clause (an existential variable is in `cl.opens`), so `Γcl` holds `boolClosed` where Bool holds only literals; no text of `readsConfined` or `Γcl` changes.

**The lemma the unit rests on** (to run, beside R3's `Holds` lemma): for a clause with `clauseSorted` and the conjuncts above, a substitution σ of values on `cl.univ`, and a model of `Γc`: an element valuation that extends σ and satisfies `ens` and `post` and gives the right side an element gives each existential variable a value's element. Cases: confined (`confined_value`); fixed (`Z ∈ t` with t's variables at values is, by `ΓDomains`, `ΓFns` and `ΓFallback`, the membership in a value's element or in ⊥).
From it: `Eval … (some v)` by an instance is entailed as `den v ⊆ f(vs)`, with equality under `FnDet`; `exNone` is entailed as `f(vs) = ⊥`.

### 1.4 The reader

- An `\or` at a term position of an equation's right side, where F6 does not read the equation (f not `total`, or more than 8 alternatives): each maximal `\or{s}(t₁, …, tₙ)` becomes a fresh variable Z:s in `exs`, with the conjunct `Z ∈ t₁ ∨ … ∨ Z ∈ tₙ` in `post`. An `\or` inside an alternative is read the same way; the inner variable is fixed in an earlier round. No distribution is done, so the count of alternatives is not bounded: the "more than 8" refusal goes, for a total function too.
- An `\exists` on an equation's right side, where F4 does not read it: the variables in `exs`, in the text's order of nesting. Each must be confined or fixed; otherwise `existentialEquation s` (CN-4 §5's case (i), R-a, unchanged).
- `\top` and `\not` at a term position stay `manyValuedRightSide`, R-a (unchanged: `Z ∈ ¬φ` fixes nothing).
- Tie: for `\or`, the lemma `C[φ] ≡ ∃Z. C[Z] ∧ Z ∈ φ` (entailed each way, every interpretation); for `\exists`, the clause equation is the translated sentence.

### 1.5 Fixtures and expectations

| Fixture | Text | If kompile writes the sentence | If kompile rejects |
|---|---|---|---|
| `e3-ml-eq-rhs-or-total`, the variant without `total` (brief P has it) | `h(X) => f(X) #Or g(X)`, h, f, g functions, none total | one clause, `exs = [Z]`, `rhs := Z`, `post := or (mem Z f(X)) (mem Z g(X))`. Where f and g agree or one is undefined: `Eval h [x]` has that one value and no other result. Where neither is defined: `Eval h [x] none` by `exNone`, and no rest is read. Where they differ: two results, `¬ FnDet`; `Γ`'s sentence is the text's and has the model with both elements; `FnDet` is listed as owed and false at that point, no theorem is stated | row R-b; the reader arm for `\or` is not built |
| new `e3-ml-eq-rhs-or-many` | `k(X) => 1 #Or 2 #Or … #Or 9`, k `total` | read by CE (F6 refuses nine); nine results, `¬ FnDet`, and the text has no model (k is total); with every alternative `X` instead: `Eval k [x] (some x)` alone, `FnHyp` holds | R-b |
| `e3-eq-exists-bool` without `total` | `syntax Bool ::= f(Bool) [function]`, `rule f(X) => ?B ensures ?B ==Bool notBool X` | `exs = [B]`; `Eval f [true] (some false)` and no other result (B := `true` is an instance that gives nothing, not a result `none`); `FnHyp` holds | R-b |
| new `e3-eq-exists-ctor` | `syntax Col ::= "r" \| "g"`, `syntax Col ::= pick(Col) [function]`, `rule pick(X) => ?C ensures ?C =/=K X` | Col is confined; `Eval pick [r] (some g)` alone | R-b |
| the same with no `ensures` | `rule f(X) => ?B` | two results; `¬ FnDet`; the text has the model with both, `Γ` the same sentence | |
| the Int form | `?Z *Int 2 ==Int X` | refused `existentialEquation Int` (Z neither confined nor fixed) | |

Kernel test (hand-built, the semantics of CX-F's `ExEnsFails.lean`, `f() => ?B ensures ?B`): `Eval c fl [] (some (bool true))`, `¬ Eval c fl [] none`, and `FnDet` at `fl`.

### 1.6 Pins, ownership, stop rules

Declarations: the `Eval` block, `Coherent`, `FnSolves`, `Clause.AppliesAt`, `clauseEquation`, `competingEquation`, `clauseSorted`, `clausesPlain` (all lane F's by CN-4 §4.1); new `Cond.fixes`, `Clause.fixedExs`, `Clause.univ`, `AgreeOff`, `Clause.Gives`, `Clause.Res`, `InstFails`, `clauseRhs`.
Pins: no `rfl` pin holds these bodies. `consistent_of` names `FnSolves`; `FnHyp` names `ClausesAgree` and `MatchIndependent`, which read `Coherent`; `Coherent.of_fnDet` is pinned as a statement and stays provable (each `Res` is an `Eval` result where the clause decides). For a clause with `exs = []` every changed proposition is equivalent to e3's; the unit proves each equivalence as a lemma (`coherent_iff_noExs`, `fnSolves_iff_noExs`). Nothing is weakened: the hypotheses are the landed ones on every semantics the landed `clausesPlain` admits.
Who re-proves what reads them: CE runs **alone against lanes R and F**, as e3 does, because it changes the `Eval` block and `FnSolves`. Its brief holds, for its duration, lane R's proofs that read them (`sound_at`, `complete_at`, `exact_hyp`, `consistent_of`, `has_model_choice`, the model's function cases and its uses of `eval_of_decides`) and every mutual induction over the block; it changes no statement of them.
Stop rules: positivity fails; a `…_plain` lemma is not provable at its pinned type; `Coherent.of_fnDet`, `fnDet_of_coherent` or `fnSolves_of_total` needs more than the texts above; the lemma of 1.3 needs a premise beyond `coreOK`, the clause hypothesis of `sound_at`, and results existing for the terms of `post`.
Reversal: an owner ruling that `function{}()` states "at most one element" (CN-4 F6's): then `Γ` gains that item, F6's clauses are exact everywhere, and CE is needed for row 2 only.

### 1.7 Strongest attack

An open universal variable beside the existential one, at an unconfined sort, which B1b admits on a right side: `f() => ?B ensures ?B ==Bool (Y >Int 0)`, Y:Int bound by no pattern. A model with an element h of Int that is no value's reads the instance at Y := h, where the union may be anything. If that instance could give `f()` a value no value instance gives, `Eval` would be unsound.
It fails. Every instance is an equation of the one application `f()`. The instance at Y := 1 states `f() = true` and at Y := 0 `f() = false`: `Eval` has both, `FnDet` is false, the text has no model, nothing is claimed. Where the value instances agree, one of them fixes `f()` to a value's element in every model, and the instance at h must agree or the model is none.
Second attack, CX-F's own: B := `false` giving `none`. Closed by `hex` on `ensFails` and by `exNone` asking every extension.
Not attacked to the end: `fnSolves_of_total` and the model's `eval_of_decides` under the new `FnSolves` (proof bodies were not read).

## 2. Row 3, unit HO-1: a variable held under a collection's symbols — COLD-REVIEW

**Decision: (A).** CN-4 R-D4 wrote "no such model was shown and none was excluded (`ΓColls`'s axioms were not read)". They are read now, and the lemma that excludes the model is landed.

`ΓColls` states, at all elements of the sorts: a map's unit splits only into units, an entry is not the unit, an entry is atomic (`elem(a', b') = concat(elem(a, b), r)` gives `a = a'`, `b = b'`, `r = unit`), and an entry of a union is an entry of one part; the same for lists and sets (kcore-theory `Faithful.lean`, `mapCollAxioms`, `listCollAxioms`, `setCollAxioms`).
From them the tree proves (kcore-theory `FaithfulCollPat.lean`, `head_back`): if a value's element is what a collection pattern symbol gives on elements of its argument sorts, those elements are values' elements. That is the constructor case of R1b unit 1 for the unit, element and concatenation symbols of a map, list or set collection.

**Fix.** A wider occurrence test for the right side, beside `ctorOccs`; `ctorOccs` and `Cond.bound` keep their texts.

```lean
-- FaithOK.lean, after `Semantics.confined` (to run; `isCollPat` is Evaluation.lean's: the file is the lane's to choose)
mutual
  /-- The variables a term holds under constructors, injections and the symbols under which a
  value's element has values' elements as arguments (`holds`). -/
  def heldOccs (c : Semantics) : Term → List Nat
    | .var i => [i]
    | .app f ts => if c.isCtor f || c.holds f then heldOccsList c ts else []
    | .inj _ _ t => heldOccs c t
    | .as t i => heldOccs c t ++ [i]
    | .dv _ _ => []
  def heldOccsList (c : Semantics) : List Term → List Nat
    | [] => []
    | t :: ts => heldOccs c t ++ heldOccsList c ts
end
/-- HO-1: the unit, element and concatenation symbols of a map, list or set collection. -/
def Semantics.holds (c : Semantics) (f : Sym) : Bool := patternHooks.contains f || c.isCollPat f
```

`rulesPlain`'s first arm reads `(heldOccs c r.rhs).contains i` in place of `(ctorOccs c r.rhs).contains i`. R1b unit 1 is restated over `heldOccs` and gains the case, by `head_back`. No range-map symbol is in `patternHooks` or `collPatternHooks` (CN-4 V6), so none is passed.
`ctorOccs_subset_heldOccs` (to run) keeps every landed use of arm A.

**Fixtures.**

| Fixture | Text | Expectation |
|---|---|---|
| `e3-vars-map` (brief P has it) | `<m> K \|-> ?V:Int </m>` on a right side, K bound | read, no `openRight`. With the cell holding nothing else: `Step` to the configuration with `k \|-> i` for every Int i; `Γc ⊧ den x ⇒ •famEx`; by `ExactC` no other value is a successor |
| new `e3-vars-map-rest` | `<m> M => (?K:Int \|-> 0) M </m>` | `Step` to `(k \|-> 0) m` exactly for the values k that are no key of m; at a k that is a key the concatenation has no value and `⌈right⌉` fails, in `Step` and in every model |
| new `e3-vars-set`, `e3-vars-list` | `SetItem(?V:Int) S`, `ListItem(?V:Int) L` | as above (`setK_back`, `listK_back`) |
| new `e3-vars-update` | `<m> M => M [ 0 <- ?V:Int ] [ 0 <- 1 ] </m>` | refused `openRight Int`, case (i): `_[_<-_]` is a hooked function, not a collection pattern symbol, and the successor does not hold V |
| a range map | `<r> [0, 1) r\|-> ?V:Int </r>` | refused `openRight Int`: no range-map symbol is passed (`collAxioms … .rangeMap = []`) |

If kompile rejects `?V` under a map entry, the row is R-b and the arm still stands for a universal open variable (`K |-> V` with V bound nowhere).

**Pins and owner.** `rulesPlain` is lane R's; `heldOccs`, `holds` are new. No pin text moves; `coreOK` admits more rules, which is what a COLD-REVIEW reads. Stop rule: R1b unit 1 over `heldOccs` needs more of the symbol than `head_back` gives (report the symbol kind).
Reversal: none wanted; the refusal returns for a kind whose `…_back` lemma fails.
`openRight` (ii) leaves CN-4 §5; case (i) stays.

**Strongest attack.** An entry at an element that is no value's standing for a value's entry: a model with an element j of the key sort and `elem(j, 0)` interpreted as the element of the value `1 |-> 0`, so that `(?K |-> 0) M` at K := j is a value's element and the step is to a value no value of K gives. It fails by `mapElemAtomAx`, which is stated for all elements: `elem(1, 0) = concat(elem(j, 0), unit)` gives `j = 1`. The proof is the landed `map_elemK`.
Second: a cell map, whose symbols are parameters with a collection `impl`. `head_back` covers the definition's own collections (`HeadReading` over `c.allColls`).

## 3. Rows 4 and 5, units CUT and HO-2: a symbol on a left side that is no constructor

### 3.1 CUT (reader; no cone)

Two symbols may stand on a kompiled left side without being constructors: an overloading symbol with a function overload (row 4; CN-4 F2 refuses it by `ovlPatsOK`), and an open generator (row 5; `patCtxAll` holds no `raw` parameter).
For both, `C[g(P̄)] ≡ ∃V. C[V] ∧ V ∈ g(P̄)` in every interpretation. So the reader reads the subterm `g(P̄)`, at sort s, as a fresh variable V:s, and adds the conjunct `mem s (.var V) (g(P̄))` to the `pre` of the rule or clause (to the `body` of an `exMatch` for a pattern there). This is CN-4 R-D2's cut with `mem`. Its term is evaluated by `EvalTerm`: for a function-overloaded symbol by F1's case (a covered application is the injected function value, an uncovered one the raw application), for an open generator by `paramVal`.
`ovlPatsOK` and `patCtxAll` keep their texts: the pattern no longer holds the symbol. The variables of P̄ that the left side holds nowhere else become open, and `rulesPlain` and `clausesPlain` decide them.
The tie is by equality on translated patterns (the lemma above). Nested occurrences are cut outermost first, the inner symbol staying in the term.
A clause's cut is a `Clause.pre`, so it needs e3 (section 12 on e3's gate).
**The `exMatch` case is not built.** `Cond.bound` asks each binder of an `exMatch` to be in `ctorOccs` of its pattern or confined, and neither text changes here. After a cut the binders under the symbol are no longer in the pattern, so only confined ones would pass, and the refusal would come from `ruleSorted` or `clauseSorted`, not from the arms below. No reader arm produces an `exMatch` today (CN-4 R-D6), so no kompiled text has the shape; a hand-built one is kept out by `ovlPatsOK` and `patCtxAll` as today. It is the one place HO-2 does not reach; the reversal is a reader arm that produces such a pattern, and then `Cond.bound` gains `heldOccs` and `memHeld` in a unit that names it.

What the arms then admit, with no change to them:
- every variable of P̄ of a confined sort: admitted (arm B, and the competition conjunct by `openCondVars.all conf`);
- a rule with no rule of larger priority, each variable of P̄ held under constructors by the right side: admitted (arm A);
- anything else: `openRequires s`, the detail naming the variable and the symbol.

Row 5 is the first line whenever it arises: case (ii) is "its sort is confined", so the generator takes arguments of confined sorts. Such a generator is not recursive, so its argument sorts differ from its result sort: the text of brief P's probe `e2-open-mixed`.

| Fixture | If kompile writes an open generator across sorts | If it does not (it keeps `constructor`, or rejects) |
|---|---|---|
| `e2-open-mixed` with `syntax KItem ::= c(B) \| d(A)`, `rule <k> c(X & Y) => d(X) </k>`, A ::= `x` \| `y` | read: `c(V) => d(X)`, `pre := mem B V (and(X, Y))`. For every H with `OpenLaws` and `OpenTotal`: `Step c(v) d(a)` exactly for the values a, b of A with `paramVal and [a, b] = some v`. At `HookParams.none`: `c(and(x, y))` steps to `d(x)` only. At the H with `app and [y, x] = some (.ctor and [x, y])`: it steps to `d(x)` and to `d(y)`. Beside an `[owise]` rule: still admitted (X, Y confined) | no kompiled text has case (ii). The row says so; the decided condition (`patCtxAll` holds no `raw` parameter) keeps a hand-built one out; nothing is built for row 5 |

### 3.2 Row 4, the part that is (B)

A variable under a function-overloaded symbol, a covering sort unconfined, in a rule that competes with a larger one, in a clause, or absent from the successor: `openRequires s`, R-a. The text and the two models:

```k
syntax Exp ::= Int | dbl(Exp) [overload(dbl)]
syntax Int ::= dbl(Int) [function, total, overload(dbl)]
rule dbl(I:Int) => 2 *Int I
rule <k> run(dbl(E:Exp)) => done(0) </k>
rule <k> run(E:Exp) => done(1) </k> [owise]
```

At `run(3)` no value e has `dbl(e)` equal to `3`: an uncovered application is raw, a covered one is `2 *Int i`. So at values the first rule does not apply and `Step` is to `done(1)`.
Model 1: the value model. Model 2: the values and one more element h of Int with `2 *Int h = 3` (`ΓDomains` states the hook's graph at values only), so `dblExp(inj h) = inj(dblInt(h)) = inj 3` by the overload equation and the function's equation, both stated for all elements. In model 2 the first rule applies at `run(3)`, the `[owise]` premise is false, and the one successor is `done(0)`.
Both are models of every sentence of the text. They agree at the values and disagree on the step. No `Step` on values is sound for both. Without the `[owise]` rule the same h gives `run(3)` the value successor `done(0)` in model 2 and none in model 1.

### 3.3 HO-2: the arm for confined covering sorts — COLD-REVIEW

Where every function overload takes arguments of confined sorts, 3.2's model does not exist, and the variable's own sort may still be unconfined (`Gas` is recursive in `ovlfun.k`; `N` has one value). Then the cut variable is decided by values:
- at uncovered arguments the symbol is injective and apart from the other generators (F1's `injUncItem`, `distUncItem`), so an application that is a value's element has values' elements as arguments;
- at arguments covered by a constructor overload, the overload equation and that constructor's items give the same;
- at arguments covered by a function overload, the arguments are elements of confined sorts, so values' (`confined_value`).

```lean
-- FaithOK.lean (to run); replaces HO-1's `holds`
/-- An overloading symbol each function in whose overload closure takes arguments of confined sorts. -/
def Semantics.ovlHeld (c : Semantics) (f : Sym) : Bool :=
  c.isOvl f && (c.fnOverloads f).all fun fn => fn.args.all c.confined   -- `fnOverloads`: lane's to spell
def Semantics.holds (c : Semantics) (f : Sym) : Bool :=
  patternHooks.contains f || c.isCollPat f || c.ovlHeld f

/-- The top-level conjuncts of a condition. -/
def Cond.conjuncts : Cond → List Cond
  | .and p q => p.conjuncts ++ q.conjuncts
  | p => [p]
/-- The variable i is held by a cut: a conjunct `V ∈ t`, V among `bound`, t holding i (`heldOccs`). -/
def memHeld (c : Semantics) (bound : List Nat) (pre : Cond) (i : Nat) : Bool :=
  pre.conjuncts.any fun
    | .mem _ (.var v) t => bound.contains v && (heldOccs c t).contains i
    | _ => false
```

`rulesPlain` (R3's final body) reads `let conf := fun i => (r.vars[i]?.map c.confined).getD false || memHeld c (varOccs r.lhs) r.pre i`, nothing else changed. `clausesPlain`'s last conjunct reads `cl.openCondVars.all fun i => conf i || memHeld c (varOccsList cl.pats) cl.pre i` (edited in brief CE, which follows R4).
`Rule.needsWitness` and `Clause.needsWitness` (pinned) keep their texts: a rule with a cut has a condition that holds a bound variable, so `reqClosed` is false and `needsWitness` is false.
Lemma (to run): in a model of `Γc`, a valuation under which the left side holds at a value and `pre` holds gives every `memHeld` variable a value's element. It is R1b unit 1 over `heldOccs` at the term of the cut, the bound variable being a value's by the left side.
An ordinary overloading symbol (no function overload) passes `ovlHeld` by the empty `all`; its case is the second bullet alone.

| Fixture | Text | Expectation |
|---|---|---|
| `e5-ovl-fun-lhs` (brief P has it) | `ovlfun.k` with `rule <k> run(cap(G:Gas)) => done(G) </k>`; N has the value `z`, `capN(z) = z` | CUT alone: read, `run(V) => done(G)`, `pre := mem Gas V capGas(G)`; admitted (arm A). `Step run(inj z) done(inj z)` (G := `inj z`, covered: `capGas(inj z) = inj(capN(z))`); `Step run(capGas(inf)) done(inf)` (uncovered); no step from `run(inf)`. `complete_hyp`'s conclusion, which CX-F finding 2 showed false for the pattern reading, holds |
| the same beside `rule <k> run(G:Gas) => done(inf) </k> [owise]` | | with HO-2: admitted (`capGas` is `ovlHeld`: its one function overload takes N, confined). `run(inj z)` steps to `done(inj z)` only; `run(inf)` to `done(inf)`. Without HO-2: `openRequires Gas` |
| new `e5-ovl-fun-lhs-int` | 3.2's text | refused `openRequires Exp`, naming E and `dbl`, whose overload takes Int; alone and with `=> done(E)`: admitted by arm A |
| `e5-ovl-fun-keep` with the rule `run(cap(G)) => done(G)` | `capN(z) => inf` | `run(inf)` steps to `done(inj z)`: the covered application is `inf` |

If kompile rejects a function-overloaded symbol on a left side, rows 4's reader arm is not built and the row is R-b.

**Pins and owners.** CUT: lane P (P3), reader; `functionInPattern` (ii) leaves CN-4 §5. HO-2: `rulesPlain` lane R (R4); `clausesPlain` in brief CE (after R4); `heldOccs`'s `holds` lane R. No pin text moves.
Stop rules: the HO-2 lemma needs injectivity or totality of the symbol at a covered argument (F1's reversal: report); `ovlCoherent` admits two function overloads covering one argument list.
Reversal for HO-2: a text where `ovlHeld` holds and a model gives a cut variable an element that is no value's; then `ovlHeld` goes and the shape is `openRequires`.

**Strongest attack.** A result-keeping overload whose function value is a raw application of the larger symbol: `rule cap(z) => cap(inf)`, so `capGas(inj z) = capGas(inf)` (CX-F finding 3's second text). The cut term `cap(G)` at the value `capGas(inf)` then has two preimages, `inf` and `inj z`, and injectivity of `capGas` would make them equal.
It fails as an attack on HO-2: F1 (b) states injectivity at uncovered arguments only, so `Γ` has a model; both preimages are values; `Step` has both successors and each is entailed alone. The lemma needs "values' elements", not uniqueness.
Second: an element of `Gas` that is no value's and is covered. It would be `inj(n)` for an element n of N, and N is confined.
Not attacked to the end: `distLbItem` where the overloading symbol's sort has an injection with a lower bound (CN-4 R1b's open point; the same stop rule).

## 4. Row 6: a set variable outside `[simplification]`

**Decision: (A) by form, fixture-first; one part (B).** The row turns on the sentence kompile writes. Brief P's probes `e3-setvar-linear` and `e3-setvar-nonlinear` record it for a function rule; one probe is added for a rewrite rule (`e3-setvar-rewrite`: `rule <k> c(@S, @S) => d(@S) </k>`). A text kompile rejects is R-b.

| Sentence the probe shows | Decision | Reading |
|---|---|---|
| function rule, `\in` form, the set variable in no right side, `requires` or `ensures`: `X0 ∈ @S ∧ X1 ∈ @S → f(X0, X1) = r` | A, unit SV-1, reader only | each `\in` conjunct over the set variable is dropped: the clause `f(A, B) => r`, A and B two variables |
| function rule, `\in` form, the set variable on the right: `X0 ∈ @S ∧ X1 ∈ @S → f(X0, X1) = r[@S]` | B: `setVariable`, R-a | below |
| rewrite rule, the set variable under applications only, on both sides | A, unit SV-R, reader only, after R3 | each left occurrence a fresh variable Aᵢ; each right occurrence a fresh `?Zⱼ` with `post := ⋁ᵢ mem Zⱼ Aᵢ` |
| rewrite rule, the set variable in a `requires`, an `ensures`, or under a connective | B: `setVariable`, R-a | below |
| function rule, direct form: `f(@S, @S) = r[@S]` | A, unit SV-D — COLD-REVIEW, built only if the probe shows this form | the clause on the diagonal, and the sentence at sets of values as a named obligation |

**SV-1, why exact.** `∀S. (x₀ ∈ S ∧ x₁ ∈ S → φ)` with S not in φ is `φ`: some set holds both elements. So the non-linearity of the K rule states nothing in this form, and the clause with two distinct variables is the sentence, in every interpretation. Expectation for `f(@S, @S) => r`: `Eval f [a, b] (some r)` for all values a, b, equal or not. (Evidence to record with the fixture, not a reason: what the Haskell backend 0.1.155 does at `f(a, b)`, a ≠ b.)

**SV-R, why exact.** With the set variable under applications only, both sides grow with S. The sentence at S says: every configuration in `L[ā]`, ā drawn from S, has a successor in `R[S]`. A configuration matched with ā is covered by the instance at every S that holds ā; of those the one at `S = {ā}` says most, since `R[{ā}] ⊆ R[S]`, and it entails the others. So the sentence is `∀ā. L[ā] → •R[{ā}]`, and `R[{ā}]` is `∃Z̄. R[Z̄] ∧ ⋀ⱼ ⋁ᵢ Zⱼ ∈ Aᵢ`. `rulesPlain` then decides the `?Zⱼ` (arm A where the right side holds them under constructors).
Expectation for `c(@S, @S) => d(@S)`: at `c(a, b)`, `Step` to `d(a)` and to `d(b)`; `famEx` is `d(a) ∨ d(b)`; neither alone is entailed where a ≠ b (`has_model_choice`).

**The (B) parts.**
- `\in` form with the set variable on the right, text `rule f(@S, @S) => @S`: the sentence gives `f(x, x)` the value `S` for every S holding x. At a sort with two elements a, b it states `f(a, a) = {a}` and `f(a, a) = {a, b}`: no model. `Γ` with it has none, against "`Γ` has no contradictions"; a weaker reading (at the least set) is the reading CN-4's `[goal]` item 4 excludes. For a right side that happens to be the same at every set (`g(@S)` with g constant), the sentence is true in a model where g is constant on all elements and false in one that agrees at the values and has an element h with another `g(h)`: its truth reads the sort's extent. R-a, CN-4 F7's reason, unchanged.
- a set variable in a `requires`, text `rule <k> c(@S) => d </k> requires p(@S)`: `⌈p(S) = true⌉` holds where some element of S has `p` true and none has it false. At `c(a)` with `p(a)` undefined, the instance at `S = {a, b}` steps where `p(b) = true`. So `c(a)` steps exactly if some element b of the sort has `p(b) = true`. Model 1: the values, none with `p` true. Model 2: one more element h with `p(h) = true`. They agree at the values and disagree on the step from `c(a)`. R-a at every unconfined sort; at a confined sort it is R-c in name only, since no fixture has it (reversal: a definition that needs it; then it is a `Cond.ex` over the sort).

**SV-D, the design if the direct form appears.** `∀S. f(S, S) = r[S]` states, at singletons, `f(a, a) = r[a]`; at a larger S it bounds the off-diagonal values and does not fix them. KCore already reads a function where no clause applies as the interpretation's value (`Eval.rest`, `fnRest`, `ΓFallback`). So:
- the clause `f(X, X) => r[X]` (a named weakening the sentence entails: its instances at singletons);
- off the diagonal the clause fails and the value is the rest, as for any partial function;
- the sentence at sets of values is a named obligation on the interpretation, outside `Γ`, in the manner of `FnLaws` (section 6):

```lean
-- to run, only if built. A sentence `lhs[@S] = rhs[@S]`: `occL`, `occR` are the variables that
-- stand for the occurrences of the set variable, of sort `s`.
structure SetLaw where
  vars : List Srt
  s : Srt
  occL : List Nat
  occR : List Nat
  lhs : Term
  rhs : Term
/-- The sentence at every finite set S of values: the values of the left side with its occurrences
drawn from S are the values of the right side with its occurrences drawn from S. -/
def SetLawAt (c : Semantics) (l : SetLaw) : Prop :=
  ∀ (S : List GroundTerm), (∀ a ∈ S, c.sortOf a = some l.s) → ∀ σ₀ v,
    (∃ σ, AgreeOff l.occL σ₀ σ ∧ c.WellSorted l.vars σ ∧ (∀ i ∈ l.occL, ∃ a ∈ S, σ.lookup i = some a) ∧
        EvalTerm c σ l.lhs (some v)) ↔
    (∃ σ, AgreeOff l.occR σ₀ σ ∧ c.WellSorted l.vars σ ∧ (∀ i ∈ l.occR, ∃ a ∈ S, σ.lookup i = some a) ∧
        EvalTerm c σ l.rhs (some v))
```

This is why the form is not (B): the two models CX-F finding 7 describes (off the diagonal `f(a, b) = ⊥` in one, `r[a]` in the other) are two interpretations, and KCore states its theorems for each. CN-4 F7's objection ("nothing can state no result and no premise") is met by the rest, which is neither: it is the interpretation's value, and the obligation says which interpretations the text admits.
It is marked COLD-REVIEW and is to be re-designed with the fixture's sentence in hand; the block above fixes the reading, not the proof route.

**Strongest attack (SV-1).** A second clause that the diagonal reading would leave room for: `rule f(@S, @S) => 1`, `rule f(X, Y) => 2 [owise]`. Under SV-1 the first clause applies everywhere and the `[owise]` clause nowhere, which looks like more than the text says. It is what the text says: the first sentence's premise holds at every pair, and the `[owise]` sentence negates the existence of a match of the first, which exists at every pair. The attack fails; the K author's intent and the sentence differ, which the fixture records.
**Strongest attack (SV-R).** A set variable under a function on the right (`=> d(g(@S))`): still monotone, and `?Z` under g is not under constructors, so `rulesPlain` prints `openRight` (i). Under a complement on either side the sentence is not monotone; the reader refuses it there (the table's fourth line).

## 5. Row 7, unit OVF: an overload axiom whose larger symbol is a function

**Decision: (A), reader only, no cone change.** The sentence `f(inj x̄) = inj(g(x̄))`, f a function, is "one more equation of that function, outside its clauses" (CN-4 F3). The landed block has exactly that: an `aside` clause blocks no clause and is excluded by none of a larger priority.

**Reading.** One clause of f: `pats := [inj{sᵢ', sᵢ}(Xᵢ)]` (a plain variable where the sorts are equal), `rhs := inj{r', r}(g(X̄))`, `req`, `ens` none, `aside := true`, `prio := 0`.
- `prio := 0`: `Eval.clause`'s `hprio` reads the clauses of a smaller priority, and there is none, so the clause decides wherever it matches; `prioEquation` gives it `clauseEquation`, with no negated competitor: `X̄ ∈ p̄ → f(X̄) = rhs`, which the overload sentence entails and is entailed by.
- `aside := true`: no other clause's premise negates it (`lowerClauses` filters it), as no `[owise]` sentence kompile writes for f negates the overload axiom.
- Where it and another clause of f both apply, `ClausesAgree` asks that they agree (an `aside` clause of a smaller priority competes with every clause). Where they do not, the text has no model and `ClausesAgree` is owed and false: a property of the text, as e5-owise-nonexec.
- `Eval.rest` asks every clause to fail, the `aside` one included, so the rest is not read at covered arguments.
The pair is not registered in `c.ovls`: f is a function, `isOvl` is false of it, and its applications are evaluated by `Eval`.

| Fixture | Text | If kompile writes the `symbol-overload` axiom | If it writes none, or rejects |
|---|---|---|---|
| new `e5-ovl-fn-fn` | `syntax Exp ::= Int \| "e"`, `syntax Exp ::= neg(Exp) [function, overload(neg)]`, `syntax Int ::= neg(Int) [function, total, overload(neg)]`, `rule neg(I:Int) => 0 -Int I`, `rule neg(e) => e` | read; `Eval negExp [inj 3] (some (inj -3))` by the `aside` clause; `Eval negExp [e] (some e)`; the two clauses of `negExp` meet at no argument, so `ClausesAgree`; `FnHyp`; `Consistent` | none written: the row has no sentence and says so; rejected: R-b |
| the same with `rule neg(_:Exp) => e [owise]` | | at `inj 3` two results, `inj -3` and `e`; `¬ FnDet`; `ClausesAgree` owed and false; the text has no model (its `[owise]` sentence and its overload sentence both hold at `inj 3`) | |
| the larger symbol a function, the smaller a constructor | `syntax Int ::= s(Int) [overload(s)]`-like, if kompile accepts | the same reading; `rhs` is a constructor term | |

Decided condition: none needed (`aside` clauses are admitted by the landed `clausesPlain`). Owner: lane F (F9), reader. Pin: none. `overloadAxiom` leaves CN-4 §5.

**Strongest attack.** The priority. If the `aside` clause had the default priority 50, a user clause of priority 40 that applies at a covered argument would make the `aside` clause's `hprio` fail there, and its equation in `Γ` would carry the negation of that clause: `Γ` would state less than the sentence and `Eval` would lose the overload's value. With `prio := 0` nothing is below it. The attack fails; the reader arm must write 0 and not the default (kernel test: a clause of priority 0 beside the `aside` clause, both applying, are of one priority and compete, so `ClausesAgree` reads the pair).
Second: `[owise]`'s premise. If kompile's `[owise]` sentence for f did negate the overload axiom, `aside` would be the wrong reading (the clause would be a competitor of priority below 200). The fixture's second text shows the sentence; the expectation above is for the premise that lists the rules of f only.

## 6. Row 8, unit FL: a law axiom on a function — COLD-REVIEW

**The construct.** `[assoc]`, `[unit]`, `[idem]` on a `function` production that is no collection's concatenation: the text holds `\equals(f(f(K1, K2), K3), f(K1, f(K2, K3)))` and the like, for every element. (`comm` has no sentence.) The function's value is given by its clauses and, where none applies, by the interpretation (`fnRest`).

**Two readings pass.** Both are sound; the choice is the orchestrator's, and (a) is recommended.

| | (a) outside `Γ`, a named obligation | (b) inside `Γ`, a hypothesis of `consistent_of` |
|---|---|---|
| `Γ` | unchanged; asserts less than the text (no more) | holds the translated sentence |
| Obligation | `FnLaws c ls`, outside `FnHyp`, a hypothesis of the package statements where `ParamsTotal` and `OpenTotal` sit | a conjunct of `FnHyp` and a hypothesis of `consistent_of` |
| Pins | one added (`FnLaws`, `LawAt`); none moves | `FnHyp`, `consistent_of` move |
| Provable | every headline as today; under the obligation the exhibited models satisfy the law's sentence (`consistent_with_laws`) | the same, and `Γ ⊧ law` at elements that are no value's, which a symbolic consumer can use |
| Not provable | `Γ ⊧ f(f(a, b), d) = f(a, f(b, d))` for terms that are not values | nothing more |

**(a), the fix.**

```lean
-- Faithful.lean, after `OpenTotal` (to run)
/-- An equation between two terms that the text states for every element. -/
structure LawEq where
  vars : List Srt
  lhs : Term
  rhs : Term
/-- The law at values: under every well-sorted substitution the two sides have the same results. -/
def LawAt (c : Semantics) (l : LawEq) : Prop :=
  ∀ σ, c.WellSorted l.vars σ → ∀ r, EvalTerm c σ l.lhs r ↔ EvalTerm c σ l.rhs r
/-- The interpretation satisfies, at values, the laws the text writes. -/
def FnLaws (c : Semantics) (ls : List LawEq) : Prop := ∀ l ∈ ls, LawAt c l

/-- Under the obligation the theory with the laws' sentences has a model. -/
theorem consistent_with_laws {c : Semantics} (h : c.coreOK = true) (hd : FnDet c) (hs : FnSolves c)
    (ho : OpenLaws c) {ls : List LawEq} (hl : FnLaws c ls) (hsort : ∀ l ∈ ls, lawSorted c l = true) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧ ∀ l ∈ ls, I ⊧ᴵ lawPattern c l
```

Beside it, `law_model_choice`: `has_model_choice`'s statement with the conjunct `∀ l ∈ ls, I ⊧ᴵ lawPattern c l` added to what it concludes of its model, under `hl` and `hsort`. Its text is the lane's to write from the pinned statement, which was not read here; the laws' sentences do not read the transition, so the proof is `consistent_with_laws`'s.
`Definition.laws : List LawEq` is filled by the reader (beside `totalParams`; `Semantics` gains no field). `lawSorted` (both sides sorted at one sort in `rhsCtx`, each variable occurring) and `lawPattern` (the translated sentence) are the lane's to spell. The package states each theorem with `FnLaws (d.sem.withHooks H) d.laws` among its hypotheses, for every H.
The account lists `FnLaws` among the owed facts, one entry per law. Where no term of the law reads the rest (the function's clauses cover every argument), the fact does not depend on H and is proved once or shown false by an instance. Where it reads the rest, it is a condition on H, and the package exhibits one H that meets it or lists the witness as owed: the library has no generic witness, since the clauses may contradict the law.

**Reason.** The sentence reads H through the function's rest: it is a sentence of the class HOOK-READING §0.4 names, "an interpretation the text admits is one under which every sentence of the text that reads H holds at values". (a) puts it where CN-4 V1 put an open generator's `functional` sentence, for V1's reason: inside `Γ` it needs a hypothesis of `consistent_of`. With (a) no pinned theorem is false without the obligation; the obligation narrows the interpretations the package speaks of to the text's, and `consistent_with_laws` shows the text's fuller theory has the model the statements are about.
Exactness is not lost: a model of the text is a model of `Γc ∪ Γstep`, and the exhibited model is a model of the text.

| Fixture (new, brief P) | Text | If kompile writes the axiom | If it rejects the attribute on a function |
|---|---|---|---|
| `e2-fn-assoc` | `syntax Int ::= pl(Int, Int) [function, total, assoc]`, `rule pl(A, B) => A +Int B` | sentence classed `fnLaw (assoc)`, "stated at values, under `FnLaws`"; `LawAt` holds at every H (no rest is read), owed and dischargeable from Int addition | R-b |
| `e2-fn-assoc-bad` | the same with `A -Int B` | `¬ LawAt`, kernel-checked at (1, 2, 3); ~~the account says the text has no model~~ (superseded by F9.FL-account-wording: the account prints the law's entry `FnLaws owed, open`; see section 12); no statement is made | |
| `e2-fn-assoc-rest` | `syntax Int ::= pk(Int, Int) [function, assoc]`, no rule | `LawAt` is "H's value at `pk` is associative on Int": true at `HookParams.none` (both sides undefined) and at H := addition; false at H := subtraction | |
| `e2-fn-idem`, `e2-fn-unit` | `[idem]`, `[unit(…)]` on a function | the same class, with the idempotence and unit sentences | |

Declarations: new `LawEq`, `LawAt`, `FnLaws`, `consistent_with_laws`, `law_model_choice`; `Definition.laws`. Owner: lane F (F9); the reader's classification is lane P's (P3). Pin: `LawAt` and `FnLaws` are added to Pins.lean by `rfl`; `[goal]`: section 12. `lawAxiom` (i) leaves CN-4 §5; (ii) stays.
Stop rule: `consistent_with_laws` needs a hypothesis beyond those written.
Reversal: the owner prefers (b).

**Strongest attack.** A law that fixes a value the clauses leave open, so that `Γ` without the law and the text disagree at values: `syntax Int ::= mx(Int, Int) [function, idem]` with the one rule `mx(X, Y) => X requires X >Int Y`. At `(2, 2)` no clause applies, the text's law says `mx(2, 2) = 2`, and `Γ(H)` says it is H's value. At an H that answers 7, `Γ(H)` states what the text refutes, and `Step` through `mx(2, 2)` goes wrong.
It fails against the unit and would succeed without the obligation: `LawAt` at that H is false (`EvalTerm mx(2, 2)` is `some 7`, the right side `some 2`), so no statement is made there. At `HookParams.none` it is false too (no value against `some 2`): for this text the admitted interpretations are those with `mx(a, a) = a`, and the package must exhibit one. This is the case the account must print as "a condition on the interpretation"; an account that printed `FnLaws` as discharged at `HookParams.none` would be the defect.

## 7. Row 9, unit BAND: an open generator with `assoc` and `idem` — COLD-REVIEW

**Decision: (A).** Nothing in `Γ` stands against the two axioms together (CX-V: no injectivity or distinctness item names an open generator), and `consistent_of` takes `OpenLaws`, whose two conjuncts are read separately. The one thing missing was an interpretation that satisfies both, to show the class is inhabited.

**The witness.** `lawHooks` at a `raw` parameter with `assoc` and `idem`: flatten both arguments, keep the first occurrence of each atom, nest to the right (a one-atom list is the atom).
Kernel-checked on lists (`cn4b/Band.lean`): with `nf` the first-occurrence form, `nf (nf u ++ v) = nf (u ++ v)`, `nf (u ++ nf v) = nf (u ++ v)`, `nf (w ++ w) = nf w`, `nf (nf w) = nf w`, `x ∈ nf w ↔ x ∈ w`, `nf [a] = [a]`, `nf w ≠ []` for `w ≠ []`.
From these: a value headed by the generator is the nesting of a form (kept raw exactly when `lawHooks` returns it, by `nf_nf`); `OpenAssoc` by `nf_left` and `nf_right`; `OpenIdem` by `nf_idem` and `nf_nf`; `OpenTotal` by `nf_ne_nil` and the atoms' sorts.

**It is not the free interpretation.** `nf [1, 2, 1] = nf [1, 2]` (checked): the witness satisfies `x | y | x = x | y`, which the two laws do not entail. It does not make the generator commutative (`nf [1, 2] ≠ nf [2, 1]`, checked).
HOOK-READING §1 asks of `lawHooks` that it show the class of admitted interpretations inhabited, "the witness that the class is inhabited, not the meaning of the generator". Any interpretation of the laws does that. HOOK-READING §4's sentence "a fixture expectation that holds only at the free interpretation is written as holding at `lawHooks`" becomes, in V13's brief and for every generator: "an expectation that holds at `lawHooks` and that the text does not state is written as holding at `lawHooks`". For a generator with `assoc` alone or `idem` alone `lawHooks` stays the free interpretation.
Reversal: the owner wants the free band exhibited. Then `nf` is the Green–Rees form (the least prefix and suffix that hold every atom, recursively); the statements below keep their texts, the four list lemmas are re-proved for it, and a raw `x | y` is no longer its own form.

**Fix.**
- `paramsPlain` (CN-4 V8's body) loses `!(k.assoc && k.idem) &&`.
- `openLaws_lawHooks`, `openTotal_lawHooks` and the `example` of CN-4 4.7 lose the hypothesis `hl`.
- `consItemsK` writes both axioms, as it writes each alone.

| Fixture (new, brief P) | Text | If kompile writes both axioms and no `constructor` | Otherwise |
|---|---|---|---|
| `e2-band-ctor` | `syntax Exp ::= "x" \| "y" \| Exp "\|" Exp [assoc, idem]` | for every H with `OpenLaws` and `OpenTotal`: `x \| x` is `x`; `(x \| y) \| (x \| y)` is `x \| y`; the package's `Consistent`, sound, complete and exact statements hold. At `lawHooks`: `x \| y` and `y \| x` are two values; `(x \| y) \| x` is `x \| y` (true of this interpretation; the text does not state it). At `HookParams.none`: `OpenIdem` fails at `x` | the symbol keeps `constructor`: `lawAxiom` (ii), R-a (CN-4 V7 case 3). Rejected: R-b |

Declarations: `paramsPlain`, `lawHooks` (lane V's). Pin: none moves; `coreOK` admits a parameter it refused. Owner: lane V (V13). `openLaw (assoc, idem)` leaves CN-4 §5.
Stop rule: `consistent_of` at a `c` with such a parameter needs more than `OpenLaws` (then the value model fails one of the two axioms: report which).

**Strongest attack.** Idempotence at a compound value, the case that defeats "merge equal adjacent arguments": `(x | y) | (x | y)` flattens to `x y x y`, which has no equal neighbours, so the adjacent merge returns a value other than `x | y` and `OpenIdem` fails. With the first-occurrence form it is `x y`: `nf_idem`, checked for every word.
Second: `Γ(H)` without a model at an admitted H. The axioms are two equations; the value model satisfies each by its conjunct of `OpenLaws`; no item states an open generator injective or apart. Not attacked to the end: the proof of `consistent_of` was not read, so "the conjuncts are used separately" is from the statements (`OpenAssoc`, `OpenIdem`), and the stop rule covers it.

## 8. Row 10, unit UNIT: a unit law on an open generator — COLD-REVIEW (with FL)

**Decision: (A), by FL.** The unit sentences `f(K, u) = K` and `f(u, K) = K` are equations between terms that read the interpretation through `paramVal`: `LawEq`s. With reading (a) of section 6 they are stated at values under `FnLaws`, outside `Γ`, and need no conjunct of `OpenLaws` (which is pinned by `rfl`).
This treats the unit law of an open generator unlike its associativity and idempotence, which are axioms of `Γ` (reading U1-3). The difference is the pin: `OpenLaws` is closed. What (a) gives up is `Γ ⊧ f(t, u) = t` for a term t that is no value; at values it follows from the graph `ΓDomains` writes, at every admitted H.
The other reading, for the orchestrator: `OpenLaws` gains `OpenUnit`, `consItemsK` writes the unit axioms, and the pins of `OpenLaws` and (through its content) `FnHyp` move. It makes the three laws alike and `Γ` as strong as the text there.

**Fix.**
- `ParamSig` gains `unit : Option Sym := none`: the nullary symbol of the two unit sentences. Only `lawHooks` and `paramsPlain` read it; `Γ` does not.
- `paramsPlain` asks, of a `raw` parameter with `unit = some u`: the signature is `[s, s] → s`, and u is a nullary constructor of s.
- `lawHooks` at such a parameter: the unit is flattened to no atom; with `assoc`, the form of the flattened arguments (with `idem`, section 7's), nested, the empty list being u; without `assoc`, `f(u, a)` and `f(a, u)` are a, anything else as before.
- The reader puts the two sentences in `Definition.laws`.

```lean
-- to run (lane V, V13)
theorem unitLaws_lawHooks (c : Semantics) (h : c.coreOK = true) (H : HookParams) :
    ∀ k ∈ c.params, k.raw = true → ∀ u, k.unit = some u →
      LawAt (c.withHooks (lawHooks c H)) (unitLawL c k u) ∧ LawAt (c.withHooks (lawHooks c H)) (unitLawR c k u)
```

A unit that is no constructor (a function constant), or a text with one of the two sentences only: the sentences are still `LawEq`s and the obligation is stated; `unit` stays `none`, the library has no witness, and the package lists the witness as owed. Nothing is refused for it.

| Fixture | Text | Outcome of the probe | Expectation |
|---|---|---|---|
| `e2-unit-ctor` (brief P has it) | `syntax Exp ::= ".E" \| "x" \| Exp "+" Exp [assoc, unit(.E)]` | kompile rejects | R-b |
| | | the symbol keeps `constructor` | `lawAxiom` (ii), R-a: `.E + .E = .E` against the distinctness of `+` and `.E` |
| | | an open generator with the two unit sentences | read. For every H with `OpenLaws`, `OpenTotal` and `FnLaws`: `x + .E` is `x`. At `lawHooks`: `(x + .E) + x` is `x + x`, a value; `.E + .E` is `.E`. At `HookParams.none`: `LawAt` of the right-unit law fails at `x` (`x + .E` is a raw value other than `x`) |

Declarations: `ParamSig` (Core.lean; no lane's in CN-4 §4.1: assigned to lane V in V13, a field with a default, as U0 added `raw`, `assoc`, `idem`), `paramsPlain`, `lawHooks`. Pin: none moves. `openLaw (unit)` leaves CN-4 §5.
Stop rule: the generated text of a package without an open generator changes through the new field (then the field's default is not printed as nothing: report, change nothing).

**Strongest attack.** The unit beside idempotence and the no-junk sentence: is `.E` still a value at `lawHooks`, and is every value of the sort still built from generators? `.E` is a constructor constant, so a value at every H; flattening sends it to no atom and the empty list back to it, so `lawHooks` returns a value of the sort at every argument list (`OpenTotal`). An interpretation that sent `x + .E` to `.E` would satisfy neither sentence; the obligation excludes it.
Second: under reading (a), a symbolic consumer that rewrites `K + .E` to `K` for a variable K. It cannot from `Γ`. That is the cost named above, and the reason reading (b) is offered.

## 9. CX-V D11: overlapping entries of one value

**The prose** (K 7.1.337, `k-distribution/include/kframework/builtin/domains.md`):
- 498-500: "The `RangeMap` sort represents a map whose keys are stored as ranges, bounded inclusively below and exclusively above. Contiguous or overlapping ranges that map to the same value are merged into a single range."
- 502-504: "You can construct a new `RangeMap` consisting of range/value pairs of two RangeMaps. If the RangeMaps have overlapping ranges an exception will be thrown during concrete execution."
- 600-602: "This function is total, which is distinct from range map concatenation, a partial function only defined on range maps with non overlapping ranges."

**Decision.** `rmConcat` keeps the landed value: **no value** at `([0,3) r|-> a) ([2,5) r|-> a)`. The fixture `e6-rangemap` asserts it (`¬⌈…⌉`), in place of asserting nothing.

**Reason.** 498-500 is a sentence about the sort: which descriptions are values of it. It names no operation. 502-504 and 600-602 are the two sentences about concatenation, and both say "overlapping ranges" with no exception for equal values; 600-602 says the function is "only defined on range maps with non overlapping ranges". `[0,3)` and `[2,5)` overlap whatever they map to.
498-500 has content without concatenation. "Contiguous" ranges of one value do reach concatenation, which is defined there, and the landed table merges them (the fixture's `find_range(merged, 4) = [0,5)`). "Overlapping" ranges of one value reach a range map through an operation that is defined at an overlap. That there is one is inferred, not read: line 600 calls some function "total" at "parts where ranges are overlapping", and CX-V lists `updateRangeMap` among the symbols the text declares `functional`. So no sentence is left without a case, and no prose stands against prose: this is not a third prose-against-declaration case.
Both readings satisfy the text's three law sentences (the union of two partial functions that agree where they overlap is associative where defined, with the empty map its unit), so the laws do not choose; the prose does.
The standing of "no value" against "silent" at an overlap is the ruling CX-V D11 reports (600-602 over 503-504; the TICKETS entry itself was not read) and is not reopened.

**Reversal.** An owner reading that 498-500 governs concatenation. Then `rmConcat` at entries that agree on their overlap is the merged map, the fixture's line flips, and the three laws are re-checked at values (they hold, by the argument above).
Owner: lane V (the fixture line, in V1-c1 or at its next brief). Declarations: none.

## 10. What the units share

- **The cut and the union are one identity**, `C[φ] ≡ ∃V. C[V] ∧ V ∈ φ`: R3 uses it on a rule's right side, CE on an equation's right side, CUT on a left side, SV-R for a set variable. One tie lemma, stated once (lane R, R3), serves all four.
- **Laws at values, outside `Γ`**: FL's `LawEq` serves rows 8 and 10, and SV-D's `SetLaw` is its form for a set variable. All three are conditions on the interpretation in HOOK-READING's sense.
- **"Decided by values" has four arms now**: under constructors and collection symbols of a value (`heldOccs`), confined, held by a cut (`memHeld`), fixed by a membership (`Cond.fixes`). Each has one lemma that turns an element valuation into a value substitution.

## 11. DAG additions

After CN-4's INT-C. Waves as in CN-4 §4.2; no two briefs that run in parallel own one cone declaration.
The new briefs are R4, F9, CE, V13 and P3. F9 and V13 are numbered past CN-4's decision names (F1 to F8, V1 to V12), so that "F4" and "V4" keep meaning CN-4's decisions.

```
INT-C ──┬─ R4 [HO-1, HO-2] ──┐
        └─ F9 [FL, OVF] ─────┴─ CE (alone against lanes R and F) ─ INT-D ──┬─ V13 [BAND, UNIT] ──┐
                                                                           └─ P3 [CUT, SV, rows] ┴─ INT-E
```

| Brief | Owner | Units | Predecessors |
|---|---|---|---|
| R4 | lane R | HO-1 (`heldOccs`, `holds`, R1b unit 1 restated, `rulesPlain`'s arm A); HO-2 (`ovlHeld`, `memHeld`, `rulesPlain`'s `conf`) | INT-C (R3's final `rulesPlain`; F3's `funUncItem`, `injUncItem`, `distGuarded`) |
| F9 | lane F | FL (`LawEq`, `LawAt`, `FnLaws`, `consistent_with_laws`); OVF (reader) | INT-C; brief P's probe for OVF |
| CE | lane F's declarations and, for its duration, lane R's proofs that read `Eval` and `FnSolves` (1.6) | CE (section 1); then `clausesPlain`'s `memHeld` (3.3) | R4, F9, e3, F2; brief P's probes for CE |
| V13 | lane V | BAND; UNIT | INT-D (FL, for UNIT); V2 |
| P3 | lane P | CUT; SV-1; SV-R; SV-D only if the probe shows the direct form; the reader's classification of law axioms on functions (`fnLaw`); the rows of section 13 in `rows.toml` | INT-D; brief P's probes |

CE is not run beside R4: lane R re-proves `sound_at`, `exact_hyp` and the model's rule cases there, and CE changes the block they read.

Additions to brief P's probe table (CN-4 §4.6), each the K text, `kore.txt` or `kompile.txt`, and the account: `e3-ml-eq-rhs-or-many`, `e3-eq-exists-ctor`, `e3-vars-map-rest`, `e3-vars-set`, `e3-vars-list`, `e3-vars-update`, `e5-ovl-fun-lhs-int`, `e5-ovl-fn-fn`, `e3-setvar-rewrite`, `e2-fn-assoc` (with `-bad`, `-rest`), `e2-fn-idem`, `e2-fn-unit`, `e2-band-ctor`, and `e2-open-mixed` extended with the rule of 3.1.

Ownership added to CN-4 §4.1: lane R, in R4: `heldOccs`, `holds`, `ovlHeld`, `memHeld`. Lane F, in F9: `LawEq`, `LawAt`, `FnLaws`. Brief CE: every declaration of 1.6. Lane V, in V13: `ParamSig.unit`, `paramsPlain`, `lawHooks`. `ctorOccs`, `Cond.bound`, `OpenLaws`, `Clause`, `Fn`, `ΓFallback` stay with no lane and no unit edits them.

Most likely to break elsewhere: every mutual induction over the `Eval` block (CE adds a constructor and a relation one unit after e3 did); proofs that destructure `Coherent`'s conclusion; proofs that unfold `rulesPlain`'s `conf`; any package or test that prints a `ParamSig` literal with positional fields.

## 12. `[goal]` and decision texts that change

- `[goal].statement`, after CN-4 §6's item on an open generator: add "A law the text writes for a function, and a unit law it writes for an open generator, are stated at values: the package's statements are for every interpretation under which they hold there, FnLaws, a named obligation, and under it the exhibited model satisfies the law's sentence (CN-4b FL)."
- CN-4 §6 item 4's last sentence ("A sentence over a set variable read at singletons is not among them: it is refused") stays true for the `\in` form with the variable on the right. If SV-D is built it gains: "except the direct form of a function equation, read on the diagonal with the sentence at sets of values a named obligation".
- HOOK-READING §4's sentence, as CN-4 4.7 carries it: "holds only at the free interpretation" becomes "holds at `lawHooks` and is not stated by the text" (section 7); the obligations it names gain `FnLaws` where the text has a unit law.
- `scoreboard_columns`, "owed facts": the names gain `FnLaws`.

**Sentences of CN-4 that these units supersede.** Lanes are briefed from CN-4, so each brief named in section 11 carries this list; until that brief runs, CN-4's sentence holds.
- F4 (§3.3): "there is **no** `Clause.exs` unit. `clausesPlain` keeps `cl.exs.isEmpty` for good": superseded by CE. F4's and F6's own readings stand.
- F8 (§3.3) and §4.9: "`Clause.post` and `Clause.exs` are not admitted": superseded by CE (F8 named this as its reversal).
- F6 (§3.3): "more than 8 alternatives is refused `manyValuedRightSide` (cost)" and "otherwise it is refused `manyValuedRightSide`": after CE those equations are read by CE.
- F2 (§3.3) and F7: `functionInPattern` for a function-overloaded symbol, `setVariable` for every set variable: after P3, section 13's rows.
- F3 (§3.3): "an overload axiom whose larger symbol is itself a function stays refused `overloadAxiom`": superseded by OVF.
- R-D4 (§3.2): the R-c row of `openRight`: superseded by HO-1. R1d's final `rulesPlain` and R3's: `ctorOccs` becomes `heldOccs`, `conf` gains `memHeld` (R4).
- V8 (§3.4): `paramsPlain`'s body: after V13 it has no `!(k.assoc && k.idem)` and gains the `unit` conjunct. V7's "with both laws the generator is refused `openLaw (assoc, idem)`": superseded by BAND.
- §4.7: the hypothesis `hl` of `openTotal_lawHooks`, `openLaws_lawHooks` and the `example`: dropped in V13.
- §4.9, the gate of e3 ("a clause `pre` is produced by F6 and F4 only; if both probes are rejected, e3 and F2 are not built"): CUT on a clause pattern is a third producer of `Clause.pre`, and CE needs the block e3 builds. The gate becomes: e3 is not built only if the probes of F6, F4, CE (`\or` and `?B` on a non-total function) and CUT on a clause pattern (`e5-ovl-fun-lhs` and `e2-open-mixed` with a function clause over the pattern) are **all** rejected. If e3 is not built, CE and the clause side of CUT and HO-2 are not built either, and their rows are R-b.

**Sentences of this document superseded since.**
- Section 6's table, row `e2-fn-assoc-bad`: "the account says the text has no model": superseded by F9.FL-account-wording. The account cannot decide `LawAt` (a statement over all values), so it never prints a law false or a text without a model; it prints the law's entry `FnLaws owed, open`, and `Bad.not_lawAt` (test/FnLawFixtures.lean) states the failure in Lean. The law sentence's tie direction is hypothesis: owed as `FnLaws`, never refused or claimed by the reader.

## 13. CN-4 §5: rows to replace and to add

Rows that go: `openLaw (assoc, idem)`; `openLaw (unit)`; `overloadAxiom`.
Rows that change (the cells not listed keep CN-4's text):

| `RefusalReason` | Shape | Applies where | Decided condition | Kind and reason |
|---|---|---|---|---|
| `openRight s` | a variable no left side binds, or an existential one, of sort s, that the right side, `ensures` or `post` holds under no constructor and no collection symbol of a map, list or set, and that no condition holds | s unconfined | `rulesPlain` (`heldOccs`) | R-a: `c() => d(f(?Z:Int))` has a value successor through an element that is no value's. A range-map symbol holds nothing: R-a, V6's reason |
| `existentialEquation s` | `\exists` on an equation's right side binding a variable of sort s | s unconfined, and the predicate does not equate the variable with a term over the other variables | `clausesPlain` (the `exs` conjunct) | R-a: the function's value ranges over elements the text does not name |
| `manyValuedRightSide` | on an equation's right side: `\top`; `\not` | always | none needed: `Term` has no connective | R-a: the value is a sort's extent or a complement in it |
| `setVariable` | a set variable outside a `[simplification]` axiom: (i) in a function equation of the `\in` form, on the right side or in a `requires` or `ensures`; (ii) in a rewrite axiom, in a `requires` or `ensures` or under a connective that is no application | always | none needed: `Term` has no set variable | (i) R-a: the sentence states the function's value at every set holding the arguments; with `=> @S` it has no model at a sort with two elements, and otherwise its truth reads every subset of the sort. (ii) R-a: the instance at a larger set is not entailed by the instance at a smaller one, so the sentence reads every subset of the sort (`c(@S) => d requires p(@S)`: the step from `c(a)` turns on whether some element b has `p(b) = true`) |
| `functionInPattern` | (i) a rule's left side, a clause's pattern or an `exMatch` pattern that applies a function, a parameter that is no open generator, or a hooked symbol that is no collection pattern symbol; (ii) an `exMatch` pattern that applies a function-overloaded symbol or an open generator | always | (i) `patCtxAll` in `ruleSorted`, `clauseSorted`, `condOK`; (ii) `overloadsOK` (`ovlPatsOK`) and `patCtxAll`, which keep their texts: a hand-built semantics with either symbol in any pattern is refused by them | (i) in a rewrite rule: R-b if the probe `e3-rule-lhs-fun` is rejected, else read as the cut (R-D2). (ii) no reader arm produces the pattern; R-c naming `Cond.bound` (3.1). In a rule's left side or a clause's pattern the reader reads the two symbols as the cut (CUT), and the pattern the semantics holds has neither |
| `openRequires s` | CN-4's shape; and a variable under a function-overloaded symbol or an open generator of a rule's left side or a clause's pattern (the cut's term) | CN-4's; for the cut: s unconfined, and for a function-overloaded symbol some function overload takes an argument of an unconfined sort | `rulesPlain`, `clausesPlain` (`memHeld`) | R-a: CN-4's reason; for the cut, section 3.2's text (`dbl`, `2 *Int h = 3`) |
| `openGeneratorPattern s` | an open generator binding a variable in a left side | its sort is recursive or reaches an unconfined sort | `patCtxAll` holds no `raw` parameter (unchanged); for the cut the reader writes, `rulesPlain`, `clausesPlain` | R-a: CN-4's reason (i). Case (ii) is read as the cut where kompile writes an open generator across sorts; otherwise no kompiled text has it |
| `lawAxiom` | an `[assoc]`, `[unit]` or `[idem]` axiom on a symbol that kept `constructor` | always | none needed: nothing is added to `Γ` | R-a: CN-4's reason (ii). An axiom on a `function` production is read (`fnLaw`, stated at values under `FnLaws`) |

Rows to add to "Not refused, a property of the text" (CN-4 §5, the closing list):
- an equation with `\or` or `\exists` on its right side whose instances give more than one value: `FnDet`, `MatchIndependent`; the text gives the function each of them;
- an interpretation, or a function's own clauses, under which a law the text writes for a function or a unit law for an open generator fails at values: `FnLaws`; no statement is made there;
- an overload sentence of a function that disagrees with a clause of that function: `ClausesAgree`.

## 14. Not decided, not read, to run

**Needs a probe (brief P), each written above for both outcomes.** Whether kompile writes `\or` and `?B` on a non-total function's right side; `?V` under a map entry; a function-overloaded symbol on a left side; an open generator across sorts; the three set-variable sentences; a `symbol-overload` axiom whose larger symbol is a function; `[assoc]`, `[idem]`, `[unit]` on a `function` production; `[assoc, idem]` and `[unit]` on a production that is no collection's.
**Left to the orchestrator.** FL's reading (a) against (b) (section 6), and with it row 10's; the first-occurrence witness against the Green–Rees form (section 7).
**To run.** Every Lean block but `Band.lean`. In particular: the lemma of 1.3; R1b unit 1 over `heldOccs` (both cases); `consistent_with_laws`, `law_model_choice`; `unitLaws_lawHooks`; `openLaws_lawHooks` without `hl`; the kernel test of 1.5 on CX-F's `ExEnsFails` semantics.
**Read.** MAIN: `designs/CN-4-constructs.md`, `findings/CX-R.md`, `CX-F.md`, `CX-V.md`, `HOOK-READING-decision.md`, `designs/CX-COMMON.md`, TICKETS `[goal]`; of `N1-decision.md` and `NONEMPTY-decision.md` sections 0 to 3 (N1) and 0 to 3 with the Q4 table (NONEMPTY), not their kernel-check sections. domains.md lines 498-504 and 600-602 only.
kcore-symbolic `1fbee135`: Core.lean (`Cond`, `Clause`, `Fn`, `ParamSig`, `HookParams`), Evaluation.lean (`isCollPat`, `isOvl`, `fnRest`, `PatVal`, the `Eval` block, `Holds`'s first constructors), Faithful.lean (`ΓDomains`, `ΓFallback`, the collection axioms' statements, `clauseEquation` to `ΓFns`, `ruleRight`, `OpenDecided` to `OpenLaws`), EvalFunctional.lean (`Clause.DecidesAt` to `MatchIndependent`, `FnDet`, `FnSolves`), ClausesAgree.lean (`ClausesAgree`), test/Pins.lean (a search for `OpenLaws`, `FnSolves`, `Coherent`).
kcore-theory, read while its working copy was empty on `8c2f206a` (it has since moved to `f4447328`; `ctorOccs` and `head_back` were re-read at `8c2f206a` through `jj file show`, the others were not): FaithOK.lean (`ctorOccs`), FaithfulCollPat.lean (the statements of `map_splitK`, `map_elemK`, `mapK_back`, `head_back`), Tie.lean (`rulesPlain`), Statements.lean (`readsConfined`, `needsWitness`), DefinitionWf.lean (`condVars` to `reqClosed`), Kore/Gamma.lean (`liesP`, `uncoveredP`, `distUncItem`), Faithful.lean (`distGuarded`, `consItemsK`), Kore/Build.lean (`equationAx`). kcore-reader `4c16f70f`: ParamsTotal.lean (`totalParams`, `ParamsTotal`).
**Not read.** Every proof body, so each "provable" above is from statements; `condOK`, `Cond.conj`, `Cond.kore`, `premise`, `norm`, `ovlOver`, `ovlCoherent` (their uses only); the model files; Parse.lean, Account.lean; CN-2's d1 block; any fixture file (sentences are taken from CN-4 and the CX files). No kompile run. Other implementations: none consulted.
