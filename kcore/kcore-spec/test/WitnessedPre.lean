/-
  The fixture e3-witnessed-pre: `syntax S ::= "a" | c(Empty) | "d"` (`syntax Empty`, no
  production), `isC(S)` total with `isC(c(_)) => true`, `isC(d) => true` and `isC(a) => false`,
  and `f(Int)` with `rule f(_) => 1 requires isC(H:S #And d) [unboundVariables(H)]`. The text is
  `f2-examples/e3-witnessed-pre.kompile.kore`.
  Run from the package root: `lake env lean -j1 test/WitnessedPre.lean`.

  The requires' conjunction under `isC` is cut (`andUnderAppCut`): the clause of `f` has the
  `requires` `isC(H)` and the premise predicate `H ∈ d`, both closed over H, which no argument
  binds. S keeps the generator `c` over Empty, a sort without a value, so S is not confined and the
  clause needs a witness with a predicate in its premise (`shape`); the reader reads it
  (`clauseRefusal_none`; the account: `CondDecided open, over VarH:S`; `owedClauses = [(0, 0)]`).

  - `coreOK` holds (`coreOK`).
  - The clauses that compete are coherent (`coherent`): the deciders name no agreement fact, and
    the one match-independence fact they name, `f`'s clause, holds because its right side has no
    variable. No termination fact is read.
  - The clause is `Witnessed` at H := d (`witnessed`, by `Clause.witnessed_of_coherent`; the
    predicate is not `\top`, so `Clause.witnessed_of_top` does not apply): `isC(d)` is `true` by
    `isC(d) => true`, and `H ∈ d` is true at H := d; under `coherent` neither has another result.
  - So the clauses' hypothesis of the pinned statements holds (`hc`), the rules' side is vacuous (no
    rule needs a witness), `OpenDecided` holds (`openDecided`), and the pinned `sound_at` is
    instantiated with no hypothesis left (`sound_at_wp`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.WitnessedPre

open KCore ML Faithful KoreAML

definition_of defn from "f2-examples/e3-witnessed-pre.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def fS : Sym := 390
def isCS : Sym := 391
def dS : Sym := 388
def cS : Sym := 387
def aS : Sym := 386
def sS : Srt := 32

theorem names : c.symName fS = "Lblf" ∧ c.symName isCS = "LblisC" ∧ c.symName dS = "Lbld" ∧
    c.symName cS = "Lblc" ∧ c.symName aS = "Lbla" ∧ c.sortName sS = "S" ∧ c.sortName 33 = "Empty" := by
  decide +kernel

/-! ## The clauses -/

/-- `f(X) => 1 requires isC(H) ∧ H ∈ d`, X:Int, H:S -/
def clG : Clause :=
  { vars := [Srt.int, sS], pats := [.var 0], req := some (.app isCS [.var 1]), rhs := .dv Srt.int (.int 1),
    ens := none, pre := .mem sS (.var 1) (.app dS []) }
def fG : Fn := { label := fS, args := [Srt.int], result := Srt.int, clauses := [clG] }
/-- `isC(c(_)) => true` -/
def ic1 : Clause := { vars := [33], pats := [.app cS [.var 0]], req := none, rhs := .dv Srt.bool (.bool true), ens := none }
/-- `isC(a) => false` -/
def ica : Clause := { vars := [], pats := [.app aS []], req := none, rhs := .dv Srt.bool (.bool false), ens := none }
/-- `isC(d) => true` -/
def icd : Clause := { vars := [], pats := [.app dS []], req := none, rhs := .dv Srt.bool (.bool true), ens := none }
def fIsC : Fn := { label := isCS, args := [sS], result := Srt.bool, clauses := [ica, ic1, icd], total := true }

theorem text : c.fns = [fG, fIsC] := by rfl

theorem coreOK : c.coreOK = true := by decide_cheap

/-- **The shape**: the clause's conditions are closed over H, of the unconfined sort S, and it has a
predicate in its premise. -/
theorem shape : clG.openCondVars = [1] ∧ clG.reqClosed = true ∧ c.confined sS = false ∧
    clG.needsWitness c = true ∧ clG.pre.isTop = false := by
  decide +kernel

/-- **The reader reads the clause**: `Parse.clauseRefusal` refuses it nowhere. -/
theorem clauseRefusal_none : Parse.clauseRefusal c clG ["X0", "H"] = none := by decide +kernel

theorem lookupF : c.lookupFn fS = some fG := by rfl
theorem lookupIsC : c.lookupFn isCS = some fIsC := by rfl

def dv : GroundTerm := .ctor dS []

theorem sorts : c.sortOf dv = some sS := by decide +kernel

theorem syms : c.isCtor dS = true ∧ c.isCtor isCS = false ∧ isHook isCS = false ∧ c.isParam isCS = false := by
  decide +kernel

theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = [(fS, 0)] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [(0, 0)] := by decide +kernel

/-! ## The clauses that compete are coherent -/

/-- The clause of `f` is match independent: its right side has no variable. -/
theorem matchG : MatchIndependent c clG := by
  have hx : clG.exs = [] := rfl
  refine (matchIndependent_iff_noExs hx).mpr fun vs σ σ' _ _ _ _ _ _ _ => .inl
    ⟨hx, hx, rfl, rfl, fun i hi => ?_, fun t ht => by cases ht⟩
  cases hi

open Det in
/-- **The clauses that compete are coherent**: from `coreOK`, the agreement the deciders confirm (they
name no function) and the match independence of the clause they name (`matchG`). No termination
fact and no fact on the clauses' predicates is read. -/
theorem coherent : CoherentAll c := by
  obtain ⟨hok, -, hha, hp, hids⟩ := Semantics.coreOK_parts coreOK
  have hsr := NamesApart.srReady_of hp hids hok
    (NamesApart.rangeKeys_genWf_of_faithCore (Semantics.coreOK_parts coreOK).2.1) (Semantics.coreOK_ovls coreOK)
  have hmc : Exec.MatchCtxO c := ⟨NamesApart.subsorts_trans_of hids hok,
    NamesApart.subsorts_irrefl_of hids hok, NamesApart.patHooks_of hha hids, Semantics.coreOK_ovls coreOK⟩
  have hnoEx : c.FnsNoExs := Semantics.fnsNoExs_of_all (by decide +kernel)
  have hag := clausesAgree_of_IO hok hnoEx hsr hmc (fun f hf => by
    rw [agree_named] at hf; exact absurd hf List.not_mem_nil)
  have hmi := matchIndependentAll_of_L hok hnoEx hmc (fun p hp fn hfn cl hcl => by
    rw [match_named, List.mem_singleton] at hp
    subst hp
    rw [lookupF] at hfn
    cases hfn
    simp only [fG, List.getElem?_cons_zero, Option.some.injEq] at hcl
    subst hcl
    exact matchG)
  exact coherentAll_of_parts hmi fun f fn hfn => by
    obtain ⟨hmem, -⟩ := lookupFn_spec hfn
    rcases List.mem_append.mp hmem with hu | hp
    · exact hag fn hu
    · exact sortPreds_agree hp

/-! ## The clause is `Witnessed` at H := d -/

/-- **`isC(d)` is `true`**, by `isC(d) => true`: no clause of a smaller priority. -/
theorem isC_d : Eval c isCS [dv] (some (bool true)) :=
  .clause (cl := icd) (σ := []) lookupIsC (by simp [fIsC]) (fun i s hs => by simp [icd] at hs)
    (.cons (.ctor syms.1 .nil) .nil) (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fIsC, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl | rfl <;> exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- `H ↦ d`. -/
def σd : Subst := [(1, dv)]

/-- The `requires` `isC(H)` at H := d: `true`. -/
theorem req_d : EvalTerm c σd (.app isCS [.var 1]) (some (bool true)) :=
  .call (vs := [dv]) syms.2.1 syms.2.2.1 (.cons .var .nil) rfl isC_d syms.2.2.2

/-- The predicate `H ∈ d` at H := d: true. -/
theorem pre_d : Holds c clG.vars.length σd clG.pre true := by
  have h := Holds.mem (c := c) (n := clG.vars.length) (σ := σd) (s := sS) (EvalTerm.var (i := 1))
    (EvalTerm.ctor (ts := []) syms.1 .nil)
  have e : ((σd.lookup 1).isSome &&
      sameResult (σd.lookup 1) ((allSome ([] : List (Option GroundTerm))).map (GroundTerm.ctor dS))) = true := by
    decide +kernel
  rw [e] at h
  exact h

/-- **The clause of `f` is `Witnessed`** at H := d, by `Clause.witnessed_of_coherent`: its
`requires` `isC(d)` is `true` and its predicate `d ∈ d` true, and under `coherent` neither has
another result. -/
theorem witnessed : clG.Witnessed c := by
  refine Clause.witnessed_of_coherent coherent (σ := σd) (fun j hj s hs => ?_) (fun t ht => ?_) pre_d
  · have hj1 : j = 1 := by
      have : clG.condVars = [1, 1] := by decide +kernel
      rw [this] at hj; simpa using hj
    subst hj1
    cases (show some sS = some s from hs)
    exact ⟨dv, rfl, sorts⟩
  · cases ht
    exact ⟨req_d, fun r hr => EvalTerm.functional coherent hr req_d⟩

/-- **The clauses' hypothesis of the pinned statements**: the one clause needing a witness is
`Witnessed`, so its `CondDecided`, which the account lists as owed, holds. -/
theorem hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c := by
  refine openClauses_of_owed fun p hp fn hfn cl hcl => ?_
  rw [owed_clauses, List.mem_singleton] at hp
  subst hp
  rw [text] at hfn
  cases hfn
  cases hcl
  exact .inl witnessed

/-- No rule needs a witness. -/
theorem rules_decided : ∀ r ∈ c.rules, r.needsWitness c = true → r.CondDecided c :=
  openRules_of_owed (by rw [owed_rules]; intro i hi; cases hi)

/-- **`OpenDecided`.** -/
theorem openDecided : OpenDecided c := ⟨rules_decided, hc⟩

/-! ## Soundness at this text with no hypothesis left -/

/-- **The pinned `sound_at` at e3-witnessed-pre, with no hypothesis left**: the clause side by `hc`,
the rule side vacuous. -/
theorem sound_at_wp (x y : Config c) (r : Rule) (σ : Subst) (hs : StepBy c r σ x y) :
    (Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ))) ∧ (Γc c ⊧ (den c y.val ⇒ famEx c r σ)) :=
  sound_at c coreOK x y r σ hs (fun r' hr' _ hw _ => rules_decided r' hr' hw) hc

end KCore.WitnessedPre

/-- info: 'KCore.WitnessedPre.coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.WitnessedPre.coherent
/-- info: 'KCore.WitnessedPre.witnessed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.WitnessedPre.witnessed
/-- info: 'KCore.WitnessedPre.openDecided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.WitnessedPre.openDecided
/-- info: 'KCore.WitnessedPre.sound_at_wp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.WitnessedPre.sound_at_wp
