/-
  Clauses with a variable their patterns do not bind, at the lemmas that read them. Run from the
  package root: `lake env lean test/OpenClauses.lean`. Kernel-checked (`decide +kernel`).

  The semantics is the reader's for `f2-examples/opencl.kompile.kore` (`opencl.k`): Int, Bool, a
  sort S whose generator `c(Empty)` takes a sort without a value (so S is not confined), the total
  predicate `isC`, and the functions `f()` (no equation) and `g(Int)` (`g(_) => 0 [owise]`). The
  clauses below are written by hand over that vocabulary, as `test/OpenRules.lean` writes its rules
  (the reader reads such clauses from their own texts: `test/B1bClauses.lean`); each is one arm of
  the conjunct of `clausePlainOpen` on open condition variables:
  - `clH`, `f() => 0 requires 1 ==Int 2 *Int H`, H:Int (`f2-examples/openh.k`): closed conditions
    over an unconfined sort, `needsWitness`;
  - `clG`, `g(X) => 1 requires isC(H)`, H:S (`f2-examples/clgenless.k`'s `f(_) => 1 requires
    isC(H:S)`), beside `g`'s `[owise]` clause: closed conditions over S, `needsWitness`;
  - `clB`, `g(X) => 1 requires B`, B:Bool: an open condition variable of a confined sort;
  - `clP`, `g(X) => 1 requires X ==Int 0`: no open condition variable.

  `exclEmptyCl_of` and `exclEmptyCl_core` (a clause that fails has an empty exclusion in every
  model of `Γc`) are instantiated at each: the decided facts on the clause hold, `CondDecided` is
  asked where `needsWitness` holds (`clH`, `clG`), and that the definition reads a confined sort
  only at `clB`, whose open condition variable is of one. `CondDecided` stays a premise at `clH` and
  `clG`: neither is `Witnessed` (no Int value solves `1 = 2 * H`; S has no value) nor shown
  `Refuted` (Int and S are not confined); `test/OpenRulesCore.lean` instantiates the premise at
  `clW`, which is `Witnessed`, in a semantics with `coreOK`. In `c2` (the text with `clG` among `g`'s
  clauses) `clause_den4Cl` and `eval_den4Cl` are instantiated with the context `coreOK` gives as
  hypotheses; `c2` meets `coreOK` (`clauseSorted` asks of H only that it occur), which gives the
  clause facts (`clauseOpenFacts_of_sortedOK` at `c2`);
  `readsConfined_of_coreCl`, `Γc_coreCl` and `openDecided_of_coreCl` at the text's semantics.
  `cBH` (the text with `clB` among `g`'s clauses and `f` the function of `clH`) meets `coreOK` and
  reads a confined sort, and `exclEmptyCl_of` is instantiated at `clB` and `clH` as clauses of it:
  the confined-sort premise is decided; `clH`'s `CondDecided` stays a hypothesis, the fact the
  text owes (no value witnesses it, `test/ClauseOpenCond.lean`, and nothing here refutes it).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace OpenClauses

definition_of defn from "f2-examples/opencl.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def i (n : Int) : Term := .dv Srt.int (.int n)

/-- The symbols and sorts the clauses name. -/
example : c.symName 391 = "Lblf" ∧ c.symName 389 = "Lblg" ∧ c.symName 390 = "LblisC" ∧ c.symName 387 = "Lblc" ∧
    c.sortName 32 = "S" ∧ c.sortName 33 = "Empty" ∧ c.symName intEq = "Lbl'UndsEqlsEqls'Int'Unds'" ∧
    c.symName intMul = "Lbl'UndsStar'Int'Unds'" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- S is not confined; Bool is. -/
example : c.confined 32 = false ∧ c.confined Srt.int = false ∧ c.confined Srt.bool = true := by decide +kernel

/-- `g`'s clauses in the text: `g(_) => 0 [owise]`. -/
noncomputable def gText : List Clause := (c.fns.map (·.clauses)).getD 0 []

example : (c.fns.map (·.label)).getD 0 0 = 389 ∧ gText.length = 1 := by decide +kernel

/-- `f() => 0 requires 1 ==Int 2 *Int H` -/
def clH : Clause :=
  { vars := [Srt.int], pats := [], req := some (.app intEq [i 1, .app intMul [i 2, .var 0]]), rhs := i 0, ens := none }
/-- `g(X) => 1 requires isC(H)` -/
def clG : Clause := { vars := [Srt.int, 32], pats := [.var 0], req := some (.app 390 [.var 1]), rhs := i 1, ens := none }
/-- `g(X) => 1 requires B` -/
def clB : Clause := { vars := [Srt.int, Srt.bool], pats := [.var 0], req := some (.var 1), rhs := i 1, ens := none }
/-- `g(X) => 1 requires X ==Int 0` -/
def clP : Clause := { vars := [Srt.int], pats := [.var 0], req := some (.app intEq [.var 0, i 0]), rhs := i 1, ens := none }

def fH : Fn := { label := 391, args := [], result := Srt.int, clauses := [clH] }
noncomputable def gG : Fn := { label := 389, args := [Srt.int], result := Srt.int, clauses := clG :: gText }
noncomputable def gB : Fn := { label := 389, args := [Srt.int], result := Srt.int, clauses := clB :: gText }
noncomputable def gP : Fn := { label := 389, args := [Srt.int], result := Srt.int, clauses := clP :: gText }

/-- Each clause has `clauseSortedOpen` and `clausePlainOpen`, and `clauseSorted`, which asks of H and
B only that they occur in the clause (the patterns of the first three do not bind them). -/
theorem sorted :
    (c.clauseSortedOpen fH (c.fns.map Fn.sig) clH = true ∧ c.clausePlainOpen clH = true ∧
      c.clauseSorted fH (c.fns.map Fn.sig) clH = true) ∧
    (c.clauseSortedOpen gG (c.fns.map Fn.sig) clG = true ∧ c.clausePlainOpen clG = true ∧
      c.clauseSorted gG (c.fns.map Fn.sig) clG = true) ∧
    (c.clauseSortedOpen gB (c.fns.map Fn.sig) clB = true ∧ c.clausePlainOpen clB = true ∧
      c.clauseSorted gB (c.fns.map Fn.sig) clB = true) ∧
    (c.clauseSortedOpen gP (c.fns.map Fn.sig) clP = true ∧ c.clausePlainOpen clP = true ∧
      c.clauseSorted gP (c.fns.map Fn.sig) clP = true) := by
  decide +kernel

/-- The arms: `clH` and `clG` have closed conditions over an unconfined open variable
(`needsWitness`); `clB`'s open condition variable is of a confined sort; `clP` has none. -/
theorem arms :
    (clH.openCondVars = [0] ∧ clH.reqClosed = true ∧ clH.needsWitness c = true) ∧
    (clG.openCondVars = [1] ∧ clG.reqClosed = true ∧ clG.needsWitness c = true) ∧
    (clB.openCondVars = [1] ∧ clB.openCondVars.all (fun i => (clB.vars[i]?.map c.confined).getD false) = true ∧
      clB.needsWitness c = false) ∧
    (clP.reqOpen = false ∧ clP.needsWitness c = false) := by
  decide +kernel

/-- Which open condition variables are of a confined sort. -/
theorem conf :
    clH.openCondVars.any (fun i => (clH.vars[i]?.map c.confined).getD false) = false ∧
    clG.openCondVars.any (fun i => (clG.vars[i]?.map c.confined).getD false) = false ∧
    clB.openCondVars.any (fun i => (clB.vars[i]?.map c.confined).getD false) = true ∧
    clP.openCondVars.any (fun i => (clP.vars[i]?.map c.confined).getD false) = false := by
  decide +kernel

/-- The lemma at each clause, in every model of `Γc`: `CondDecided` asked of `clH` and `clG`, that the definition reads a confined sort of `clB` only. -/
example {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Faithful.Γc c)
    (hH : clH.CondDecided c) (hG : clG.CondDecided c) (hrc : c.readsConfined = true) :
    Faithful.ExclEmptyCl c I fH clH ∧ Faithful.ExclEmptyCl c I gG clG ∧ Faithful.ExclEmptyCl c I gB clB ∧
      Faithful.ExclEmptyCl c I gP clP :=
  ⟨Faithful.exclEmptyCl_of coreOK hI Faithful.fns_headsOK sorted.1.1 sorted.1.2.1 rfl
      (fun h' => by rw [conf.1] at h'; cases h') (fun _ => hH),
   Faithful.exclEmptyCl_of coreOK hI Faithful.fns_headsOK sorted.2.1.1 sorted.2.1.2.1 rfl
      (fun h' => by rw [conf.2.1] at h'; cases h') (fun _ => hG),
   Faithful.exclEmptyCl_of coreOK hI Faithful.fns_headsOK sorted.2.2.1.1 sorted.2.2.1.2.1 rfl
      (fun _ => hrc) (fun h' => by rw [arms.2.2.1.2.2] at h'; cases h'),
   Faithful.exclEmptyCl_of coreOK hI Faithful.fns_headsOK sorted.2.2.2.1 sorted.2.2.2.2.1 rfl
      (fun h' => by rw [conf.2.2.2] at h'; cases h') (fun h' => by rw [arms.2.2.2.2] at h'; cases h')⟩

/-- The text with `clB` among `g`'s clauses and `f` the function of the clause `clH`. -/
noncomputable abbrev cBH : Semantics :=
  { c with fns := gB :: c.fns.drop 1 ++ [fH], params := c.params.filter (·.sig.name != 391) }

/-- **`cBH` has `coreOK` and reads a confined sort**; `clB` and `clH` are clauses of it with the
facts `exclEmptyCl_of` reads; `clH` needs a witness, `clB` does not. -/
theorem coreBH : cBH.coreOK = true ∧ cBH.readsConfined = true ∧
    (cBH.clauseSortedOpen gB (cBH.fns.map Fn.sig) clB = true ∧ cBH.clausePlainOpen clB = true) ∧
    (cBH.clauseSortedOpen fH (cBH.fns.map Fn.sig) clH = true ∧ cBH.clausePlainOpen clH = true) ∧
    clB.needsWitness cBH = false ∧ clH.needsWitness cBH = true ∧
    clH.openCondVars.any (fun i => (clH.vars[i]?.map cBH.confined).getD false) = false := by
  decide_cheap

/-- **`exclEmptyCl_of` at `clB` and `clH`, clauses of `cBH`**, in every model of `Γc cBH`: that
`cBH` reads a confined sort is decided; `clH`'s owed `CondDecided` is the one hypothesis. -/
example {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Faithful.Γc cBH)
    (hH : clH.CondDecided cBH) :
    Faithful.ExclEmptyCl cBH I gB clB ∧ Faithful.ExclEmptyCl cBH I fH clH :=
  ⟨Faithful.exclEmptyCl_of coreBH.1 hI Faithful.fns_headsOK coreBH.2.2.1.1 coreBH.2.2.1.2 rfl
      (fun _ => coreBH.2.1) (fun h' => by rw [coreBH.2.2.2.2.1] at h'; cases h'),
   Faithful.exclEmptyCl_of coreBH.1 hI Faithful.fns_headsOK coreBH.2.2.2.1.1 coreBH.2.2.2.1.2 rfl
      (fun h' => by rw [coreBH.2.2.2.2.2.2] at h'; cases h') (fun _ => hH)⟩

/-- `exclEmptyCl_core` at `clG`, from `Fails` alone: where `clG` fails at `[w]`, its exclusion is
empty at every valuation giving `X0` w's element. -/
example {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Faithful.Γc c)
    (hG : clG.CondDecided c) {w : GroundTerm} (hw : c.sortsOf [w] = some [Srt.int])
    (hf : Fails c [w] clG) : True := by
  have := @Faithful.exclEmptyCl_core c M _ I (by decide +kernel) coreOK (by decide +kernel) hI gG clG _ Faithful.fns_headsOK
    sorted.2.1.1 sorted.2.1.2.1 rfl (fun h' => by rw [conf.2.1] at h'; cases h') (fun _ => hG) [w] hw hf
  trivial

/-! ## A clause that decides: `clause_den4Cl` -/

/-- The text's semantics with `g`'s clauses `clG` and the `[owise]` clause: `clG` is a clause of the
semantics, of a smaller priority than the `[owise]` clause, which negates it. -/
noncomputable abbrev c2 : Semantics := { c with fns := gG :: c.fns.drop 1 }

theorem hfn2 : c2.lookupFn 389 = some gG := by rfl

/-- The `[owise]` clause of `g`. -/
noncomputable def clO : Clause := gText.getD 0 { vars := [], pats := [], req := none, rhs := .var 0, ens := none }

theorem gG_clauses : gG.clauses = [clG, clO] := by rfl

/-- The facts on the two clauses `clause_den4Cl` reads: each variable occurs in the clause, `\top`
predicates, the sorts; `clO` is not `aside` and of a larger priority than `clG`. -/
theorem den_facts :
    c2.clauseSortedOpen gG (c2.fns.map Fn.sig) clG = true ∧ c2.clausePlainOpen clG = true ∧
    c2.clauseSortedOpen gG (c2.fns.map Fn.sig) clO = true ∧ c2.clausePlainOpen clO = true ∧
    clG.aside = false ∧ clG.prio < clO.prio ∧ clO.prio = 200 := by
  decide +kernel

/-- `clause_den4Cl` at `clG` (an open condition variable; no clause of a smaller priority) and at
the `[owise]` clause, whose competitor `clG` has an empty exclusion where it fails, in every model
of `Γ` with the context `coreOK` gives a semantics. -/
example {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Faithful.Γ c2)
    (hnn : Faithful.NamesNumbered c2) (hsc : SortCtx c2) [OvlOK c2]
    (hph : Faithful.patHooksApart c2 = true) {ws : List GroundTerm} (hws : c2.sortsOf ws = some gG.args)
    (hE : Faithful.ExclEmptyCl c2 I gG clG) (hF : Fails c2 ws clG) (hM : Faithful.ModelFailsCl c2 I clG ws) :
    True := by
  obtain ⟨hpG, hoG, hrG, hhG, heG⟩ := Semantics.clauseSortedOpen_parts den_facts.1
  obtain ⟨hexG, hpostG, -, -⟩ := Semantics.clausePlainOpen_partsP den_facts.2.1
  have hpreG : clG.pre = .top := rfl
  obtain ⟨hpO, hoO, hrO, hhO, heO⟩ := Semantics.clauseSortedOpen_parts den_facts.2.2.1
  obtain ⟨hexO, hpostO, -, -⟩ := Semantics.clausePlainOpen_partsP den_facts.2.2.2.1
  have hpreO : clO.pre = .top := rfl
  have hmemG : clG ∈ gG.clauses := by rw [gG_clauses]; exact List.mem_cons_self ..
  have hmemO : clO ∈ gG.clauses := by rw [gG_clauses]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hlowG : ∀ cl' ∈ gG.clauses, cl'.aside = false → cl'.prio < clG.prio → False := by
    rw [gG_clauses]; intro cl' hcl' _ hlt
    rcases List.mem_cons.mp hcl' with rfl | hcl'
    · exact Nat.lt_irrefl _ hlt
    · rw [List.mem_singleton.mp hcl', den_facts.2.2.2.2.2.2] at hlt; exact absurd hlt (by decide)
  have hlowO : ∀ cl' ∈ gG.clauses, cl'.aside = false → cl'.prio < clO.prio → cl' = clG := by
    rw [gG_clauses]; intro cl' hcl' _ hlt
    rcases List.mem_cons.mp hcl' with rfl | hcl'
    · rfl
    · rw [List.mem_singleton.mp hcl'] at hlt; exact absurd hlt (Nat.lt_irrefl _)
  have := fun {σ' : Subst} {r : Option GroundTerm} (hσ' : c2.WellSorted clG.vars σ') (hm : PatVals c2 σ' clG.pats ws)
      (hr : ∀ v, r = some v → c2.sortOf v = some gG.result) ihright ihreq =>
    Faithful.clause_den4Cl (r := r) hI hnn hsc hph hfn2 hmemG hws hσ' hm hpG (by rw [hpreG, Semantics.condOK]) hpostG hexG hoG hrG hhG heG hr ihright ihreq
      (fun hpt => by rw [hpreG] at hpt; simp [Cond.isTop] at hpt)
      (fun cl' hcl' ha hlt => (hlowG cl' hcl' ha hlt).elim)
  have := fun {σ' : Subst} {r : Option GroundTerm} (hσ' : c2.WellSorted clO.vars σ') (hm : PatVals c2 σ' clO.pats ws)
      (hr : ∀ v, r = some v → c2.sortOf v = some gG.result) ihright ihreq =>
    Faithful.clause_den4Cl (r := r) hI hnn hsc hph hfn2 hmemO hws hσ' hm hpO (by rw [hpreO, Semantics.condOK]) hpostO hexO hoO hrO hhO heO hr ihright ihreq
      (fun hpt => by rw [hpreO] at hpt; simp [Cond.isTop] at hpt)
      (fun cl' hcl' ha hlt => by
        rw [hlowO cl' hcl' ha hlt]
        exact ⟨by rw [hpreG, Semantics.condOK], hpG, fun t ht => Faithful.varOccs_lt t (hrG t ht), hE, hF, hM⟩)
  trivial

/-! ## `readsConfined_of_coreCl`, `Γc_coreCl`, `openDecided_of_coreCl` -/

/-- The text's clauses open no variable and need no witness. -/
theorem noOpens : (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.opens = []) ∧
    (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = false) := by
  decide +kernel

/-- The text's rules bind their variables in their left sides. -/
theorem rulesBindC : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true := by
  decide +kernel

/-- The text's rules have `\top` predicates. -/
theorem rulesTopC : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top :=
  Semantics.rulesTop_of_isTop (by decide +kernel)

example : c.readsConfined = false := Semantics.readsConfined_of_coreCl (hpreTop := by decide +kernel) coreOK rulesBindC rulesTopC noOpens.1
example : Faithful.Γc c = Faithful.Γ c := Γc_coreCl (hpreTop := by decide +kernel) coreOK rulesBindC rulesTopC noOpens.1
example : OpenDecided c :=
  openDecided_of_coreCl coreOK rulesBindC fun fn hfn cl hcl hw => absurd hw (by rw [noOpens.2 fn hfn cl hcl]; decide)

/-! ## L3 at the fourth stage: `eval_den4Cl` -/

/-- Its clause hypothesis holds for every semantics `sortedOK` accepts none of whose clauses binds a
variable by `\exists`, and at the open clause `clG`
of `c2` (from the decided facts). -/
example : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∃ L, HeadsOK c L ∧ Faithful.ClauseOpenFacts c fn L cl :=
  Faithful.clauseOpenFacts_of_sortedOK (hpreTop := by decide +kernel)
    (Semantics.fnsNoExs_of_all (by decide +kernel)) (Semantics.coreOK_parts coreOK).1
example : Faithful.ClauseOpenFacts c2 gG (c2.fns.map Fn.sig) clG := Faithful.clauseOpenFacts_of (by decide +kernel) den_facts.1 den_facts.2.1 rfl

/-- `c2`, whose clause `clG` has a variable its patterns do not bind, meets `coreOK`, which gives the
clause facts of every clause of `c2`. -/
theorem coreOK2 : c2.coreOK = true := by decide_cheap
example : ∀ fn ∈ c2.allFns, ∀ cl ∈ fn.clauses, ∃ L, HeadsOK c2 L ∧ Faithful.ClauseOpenFacts c2 fn L cl :=
  Faithful.clauseOpenFacts_of_sortedOK (hpreTop := by decide +kernel)
    (Semantics.fnsNoExs_of_all (by decide +kernel)) (Semantics.coreOK_parts coreOK2).1

/-- `eval_den4Cl` at `g` in `c2`, whose clause `clG` has an open condition variable. -/
example {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Faithful.Γ c2)
    (hnn : Faithful.NamesNumbered c2) (hsc : SortCtx c2) [OvlOK c2] (hph : Faithful.patHooksApart c2 = true)
    (hcls : ∀ fn ∈ c2.allFns, ∀ cl ∈ fn.clauses, ∃ L, HeadsOK c2 L ∧ Faithful.ClauseOpenFacts c2 fn L cl)
    (hneg : ∀ fn ∈ c2.allFns, ∀ cl ∈ fn.clauses, Faithful.ClauseNeg c2 fn cl → Faithful.ExclEmptyCl c2 I fn cl)
    {ws : List GroundTerm} {r : Option GroundTerm} (hE : Eval c2 389 ws r) (hws : c2.sortsOf ws = some gG.args)
    (e : ML.Valuation M) (m : M) :
    (KoreAML.den (Faithful.symApp c2 389 (GroundTerm.koreList c2 ws))).interpret I e m ↔ Faithful.Res c2 I e r m :=
  Faithful.eval_den4Cl hI hnn hsc hph hcls hneg hE hfn2 hws e m

/-- info: 'OpenClauses.sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sorted

/-- info: 'KCore.Faithful.exclEmptyCl_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Faithful.exclEmptyCl_of

end OpenClauses
