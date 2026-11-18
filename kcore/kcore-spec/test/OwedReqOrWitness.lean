/-
  The owed `CondDecided` of fixture e3-ml-req-or-unheld (`f2-examples/mlrequnheld.kompile.kore`):
  `rule <k> go(X) => done ... </k> requires X >Int 0 #Or Y:Int >Int 2 [unboundVariables(Y)]`,
  read as two rules by the split of the `#Or` (`requiresOrSplit`). Run from the package root:
  `lake env lean -j1 test/OwedReqOrWitness.lean`. Kernel-checked (`decide +kernel`).

  - The rule 1, `<k> go(X) => done ... </k> requires Y >Int 2`, is the one owed (`owed_rules`):
    its `requires` is closed over Y:Int, which the left side does not bind, and Int is not
    confined. No clause is owed (the text has no function with equations).
  - It is `Witnessed` at Y := 3 (`witnessed1`: `3 >Int 2` evaluates to `true`), so `OpenDecided c`
    holds (`owed`): the hypothesis set the generated package states is discharged here, and with
    it the pinned `sound_at` (`sound_at_owed`) and `SoundC c` (`sound`) hold with no hypothesis
    left.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace OwedReqOrWitness

definition_of defn from "f2-examples/mlrequnheld.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def gtInt : Sym := 21
def kCell : Sym := 383
def symDone : Sym := 385
def symGo : Sym := 386

theorem names_ok : c.symName gtInt = "Lbl'Unds-GT-'Int'Unds'" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName symDone = "Lbldone" ∧ c.symName symGo = "Lblgo" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

noncomputable def r1 : Rule := c.rules[1]'(by decide +kernel)

theorem r1_vars : r1.vars = [Srt.int, Srt.k, 19, Srt.int] := rfl
theorem r1_req : r1.req = some (.app gtInt [.var 3, .dv Srt.int (.int 2)]) := rfl
theorem r1_pre : r1.pre = .top := rfl

/-- **The owed conditions**: the rule 1 (the disjunct `Y >Int 2`), and no clause. -/
theorem owed_rules : c.owedRules = [1] := by decide +kernel
theorem owed_clauses : c.owedClauses = [] := by decide +kernel

/-- Y := 3, the other variables at values of their sorts. -/
def σ3 : Subst := [(0, int 1), (1, .ctor dotk []), (2, .ctor counterLabel [.dv Srt.int (.int 0)]), (3, int 3)]

theorem σ3_sorted : c.WellSorted [Srt.int, Srt.k, 19, Srt.int] σ3 := fun j s hs => by
  match j, hs with
  | 0, hs => cases hs; exact ⟨_, rfl, sortOf_int 1⟩
  | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
  | 2, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
  | 3, hs => cases hs; exact ⟨_, rfl, sortOf_int 3⟩

/-- The text has no function: the functions are the generated sort predicates. -/
theorem clauseCtx : Exec.ClauseCtx c := by
  have hf : c.fns = [] := by decide +kernel
  intro fn hfn'
  rcases List.mem_append.mp hfn' with hfn | hfn
  · rw [hf] at hfn; cases hfn
  · exact ⟨[], fun k hk => (nomatch hk), fun cl hcl =>
      let ⟨h1, h2, h3, h4, h5, h6⟩ := sortPreds_ctx hfn cl hcl
      ⟨h1, h2, h3, h4, h5, h6, Semantics.sortPreds_pre hfn cl hcl, Semantics.sortPreds_exs hfn cl hcl,
        Semantics.sortPreds_post hfn cl hcl⟩⟩

theorem sortCtx : SortCtx c := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSound_of_core coreOK
  haveI : OvlOK c := hno
  exact sortCtx_of_all hok hsr (OvlOK.ovlCase hno)

theorem matchCtx : Exec.MatchCtx c := Exec.matchCtx_of (by decide +kernel)

/-- `3 >Int 2` is `true`. -/
theorem req3 : EvalTerm c σ3 (.app gtInt [.var 3, .dv Srt.int (.int 2)]) (some (bool true)) :=
  Exec.evalT_sound sortCtx clauseCtx matchCtx 10 (by decide +kernel) (headsOK_fns c) σ3_sorted
    (s := Srt.bool) (by decide +kernel)

/-- **The rule 1 is `Witnessed`**, Y := 3. -/
theorem witnessed1 : r1.Witnessed c :=
  ⟨σ3, fun i _ s hs => σ3_sorted i s (by rw [← r1_vars]; exact hs),
   fun t ht => by rw [r1_req] at ht; cases ht; exact req3,
   by rw [r1_pre]; exact .top⟩

/-- **The owed fact holds**: the one owed rule is `Witnessed`, and no clause is owed. -/
theorem owed : OpenDecided c :=
  ⟨openRules_of_owed (by
      rw [owed_rules]
      intro j hj r hr
      cases List.mem_singleton.mp hj
      cases (show some r1 = some r from (rfl : c.rules[1]? = some r1).symm.trans hr)
      exact Or.inl witnessed1),
   openClauses_of_owed (by rw [owed_clauses]; intro p hp; cases hp)⟩

/-- **The pinned `sound_at` with no hypothesis left**: its `hw` and `hc` from `owed`. -/
theorem sound_at_owed (x y : Config c) (r : Rule) (σ : Subst) (hs : StepBy c r σ x y) :
    (Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ))) ∧ (Γc c ⊧ (den c y.val ⇒ famEx c r σ)) :=
  sound_at c coreOK x y r σ hs (fun r' hr' _ hw _ => owed.1 r' hr' hw) owed.2

/-- The generated `Obl`: no fact about a function or the interpretation is named. -/
theorem obl_nil : FnFacts c [] [] :=
  FnFacts.of_nil (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem rightHeld : c.RightHeld := Semantics.rightHeld_of_valued (by decide +kernel)

/-- **Soundness of the text's semantics**, from the generated hypothesis set discharged at `owed`. -/
theorem sound : SoundC c := sound_fn c [] [] coreOK rightHeld ParamsTotal.nil (obl_nil.obligations owed)

end OwedReqOrWitness

/-- info: 'OwedReqOrWitness.witnessed1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OwedReqOrWitness.witnessed1
/-- info: 'OwedReqOrWitness.owed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OwedReqOrWitness.owed
/-- info: 'OwedReqOrWitness.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OwedReqOrWitness.sound
