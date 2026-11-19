/-
  The fixture e2-cool-eq: `syntax KResult ::= Int`, `f(Int)` a function with `rule f(X) => X [cool]`,
  which kompile writes `f(X) => X requires true andBool isKResult(HOLE:K)` (sentence 204). The text
  is `f2-examples/e2-cool-eq.kompile.kore`. Run from the package root:
  `lake env lean -j1 test/CoolEqWit.lean`.

  HOLE is bound by no argument, and K is not confined, so the clause of `f`, whose closed `requires`
  holds HOLE, owes its `CondDecided` (the account: `CondDecided open, over VarHOLE:K`;
  `owedClauses = [(0, 0)]`). Every statement is for every interpretation H.

  - The clause is `Witnessed` at HOLE := `kseq(inj{Int,KItem}(0), dotk)` (`witnessed`): the
    equation `isKResult(kseq(inj{KResult,KItem}(V), dotk)) = true` of the sort predicate (sentence
    233) gives `isKResult` of it the result `true` (`kr_hole`), Int being below KResult, so the
    `requires` evaluates to `true` (`req_true`), and to nothing else, `f` and `isKResult` having
    one result (`fnDet`: no equations of one priority compete, and the clause of `f` is match
    independent, `matchCool`: its right side is X, which the argument fixes).
  - So the clauses' hypothesis of the pinned statements holds (`hc`), and with the rules' side
    vacuous (the text has no rule needing a witness) `OpenDecided` holds (`openDecided`), `FnHyp`
    holds (`fnHyp`) and `Γc` with the step's closure has a model (`consistent`).
  - `f(3) = 3` (C7 form (a), from sentences): `Eval` gives it by the clause at X := 3, HOLE := the
    witness (`eval_f3`), so every model of `Γc` reads it (`f3_c`, by `eval_den4ClPre` with the
    clauses' hypothesis), and `Pre`, the function sentences as written with the families of the
    reading and `Γcl` (`boolClosed`), entails it (`f3_is_3`); `Pre` with the step's closure has a
    model (`pre_model`). The sentences that determine it are the equation of `f` (204: its HOLE is
    universal over the whole sentence, so the sentence holds at HOLE := the witness) and the
    equation of `isKResult` at a K whose one item is a KResult (233).
  - `sound_at_wit`: the pinned `sound_at` with no hypothesis left, the clause side by `hc`.

  The clauses are written by hand and shown to be the reader's (`text`, `lookupKR`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.CoolEqWit

open KCore ML Faithful KoreAML

definition_of defn from "f2-examples/e2-cool-eq.kompile.kore"
user_axioms U from "f2-examples/e2-cool-eq.kompile.kore" module "E2-COOL-EQ"
kore_term kore from "f2-examples/e2-cool-eq.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fS : Sym := 385
def krS : Sym := 382
def andS : Sym := 4
def krSort : Srt := 32

theorem names : c.symName fS = "Lblf" ∧ c.symName krS = "LblisKResult" ∧ c.symName andS = "Lbl'Unds'andBool'Unds'" ∧
    c.sortName krSort = "KResult" := by
  decide +kernel

/-! ## The clauses -/

/-- `f(X) => X requires true andBool isKResult(HOLE)`, X:Int, HOLE:K -/
def clCool : Clause :=
  { vars := [Srt.int, Srt.k], pats := [.var 0],
    req := some (.app andS [.dv Srt.bool (.bool true), .app krS [.var 1]]), rhs := .var 0, ens := none }
def fCool : Fn := { label := fS, args := [Srt.int], result := Srt.int, clauses := [clCool] }

/-- `isKResult(kseq(inj{KResult,KItem}(V), dotk)) = true`, V:KResult -/
def kr1 : Clause :=
  { vars := [krSort], pats := [.app kseq [.inj krSort Srt.kitem (.var 0), .app dotk []]], req := none,
    rhs := .dv Srt.bool (.bool true), ens := none }
/-- otherwise `false` -/
def kr2 : Clause :=
  { vars := [Srt.k], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool false), ens := none, prio := 200 }
def fKR : Fn := ⟨krS, [Srt.k], Srt.bool, [kr1, kr2], true⟩

/-- The reader's function `f` is `fCool`; `isKResult` is the generated sort predicate `fKR`. -/
theorem text : c.fns = [fCool] := by rfl
theorem lookupKR : c.lookupFn krS = some fKR := by rfl

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem fnsH (H : HookParams) : (cH H).fns = [fCool] := text
theorem lookupFH (H : HookParams) : (cH H).lookupFn fS = some fCool := by
  rw [Semantics.lookupFn_withHooks]; rfl
theorem lookupKRH (H : HookParams) : (cH H).lookupFn krS = some fKR := by
  rw [Semantics.lookupFn_withHooks]; exact lookupKR
theorem sortOfH (H : HookParams) (v : GroundTerm) : (cH H).sortOf v = c.sortOf v := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]

/-- The clause of `f` needs a witness: its condition holds HOLE only, of K, which is not confined. -/
theorem needs : clCool.needsWitness c = true ∧ c.confined Srt.k = false ∧ clCool.condVars = [1] := by
  decide +kernel

/-- `kseq(inj{Int,KItem}(0), dotk)`: a K whose one item is an Int, so a KResult. -/
def hole : GroundTerm := .ctor kseq [.inj Srt.int Srt.kitem (.dv Srt.int (.int 0)), .ctor dotk []]
def i3 : GroundTerm := .dv Srt.int (.int 3)

theorem sorts : c.sortOf hole = some Srt.k ∧ c.sortOf i3 = some Srt.int := by decide +kernel

theorem syms (H : HookParams) : (cH H).isCtor kseq = true ∧ (cH H).isCtor dotk = true ∧
    (cH H).isCtor krS = false ∧ isHook krS = false ∧ (cH H).isParam krS = false ∧
    (cH H).isCtor andS = false ∧ isHook andS = true :=
  (by decide +kernel : c.isCtor kseq = true ∧ c.isCtor dotk = true ∧ c.isCtor krS = false ∧ isHook krS = false ∧
    c.isParam krS = false ∧ c.isCtor andS = false ∧ isHook andS = true)

/-! ## `isKResult(hole)` is `true`, and the clause is `Witnessed` at HOLE := hole -/

/-- V := `inj{Int,KResult}(0)`, the match of `kr1` at `hole`. -/
def σV : Subst := [(0, .inj Srt.int krSort (.dv Srt.int (.int 0)))]

theorem σV_sorted (H : HookParams) : (cH H).WellSorted kr1.vars σV := fun i s hs => by
  cases i with
  | zero =>
    cases (show some krSort = some s from hs)
    exact ⟨_, rfl, by rw [sortOfH]; decide +kernel⟩
  | succ i => cases (show (none : Option Srt) = some s from hs)

theorem kr1_match (H : HookParams) : PatVals (cH H) σV kr1.pats [hole] :=
  .cons (.ctor (syms H).1
    (.cons (PatVal.inj (w := .inj Srt.int krSort (.dv Srt.int (.int 0))) (.var rfl))
      (.cons (.ctor (syms H).2.1 .nil) .nil))) .nil

/-- **`isKResult(hole)` is `true`**, by `kr1`: no clause of a smaller priority. -/
theorem kr_hole (H : HookParams) : Eval (cH H) krS [hole] (some (bool true)) :=
  .clause (lookupKRH H) (List.mem_cons_self ..) (σV_sorted H) (kr1_match H) (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      rcases List.mem_cons.mp hcl' with rfl | hcl'
      · exact absurd hlt (by decide)
      · rw [List.mem_singleton.mp hcl'] at hlt; exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- `isKResult(HOLE)` under a σ giving HOLE the value `hole`: `true`. -/
theorem call_kr (H : HookParams) {σ : Subst} (h1 : σ.lookup 1 = some hole) :
    EvalTerm (cH H) σ (.app krS [.var 1]) (some (bool true)) :=
  .call (vs := [hole]) (syms H).2.2.1 (syms H).2.2.2.1 (.cons .var .nil) (by rw [h1]; rfl) (kr_hole H)
    (syms H).2.2.2.2.1

/-- The `requires` under a σ giving HOLE the value `hole`: `true andBool true`, so `true`. -/
theorem req_true (H : HookParams) {σ : Subst} (h1 : σ.lookup 1 = some hole) :
    EvalTerm (cH H) σ (.app andS [.dv Srt.bool (.bool true), .app krS [.var 1]]) (some (bool true)) :=
  .hook (syms H).2.2.2.2.2.1 (syms H).2.2.2.2.2.2 (.cons .dv (.cons (call_kr H h1) .nil))
    (fun vs hvs => by cases hvs; exact Semantics.hookRes_of_value (by decide +kernel)) (fun h => by cases h)

theorem clCool_exs : clCool.exs = [] := by decide +kernel

/-- **The clause of `f` is match independent, for every H**: its right side is X, and two matches
at one argument list give X the argument. -/
theorem matchCool (H : HookParams) : MatchIndependent (cH H) clCool := by
  refine (matchIndependent_iff_noExs clCool_exs).mpr fun vs σ σ' ha ha' _ _ _ _ _ => .inl
    ⟨clCool_exs, clCool_exs, rfl, rfl, fun i hi => ?_, fun t ht => by cases ht⟩
  have hi0 : i = 0 := by simpa [clCool, varOccs] using hi
  subst hi0
  have hp := ha.2.1
  have hp' := ha'.2.1
  cases hp with
  | cons h1 hn =>
    cases hn
    cases hp' with
    | cons h1' hn' =>
      cases hn'
      cases h1 with
      | var h => cases h1' with
        | var h' => rw [h, h']

def callOrder : List Nat := [fS]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
/-- The clause of `f` is the one clause whose match independence no decider shows. -/
theorem match_named : c.matchObligationsL = [(fS, 0)] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
/-- The clause of `f` is the one whose condition is owed. -/
theorem owed_clauses : c.owedClauses = [(0, 0)] := by decide +kernel

/-- The facts the deciders leave, for every H: the match independence of `f`'s clause. -/
theorem facts (H : HookParams) : FnFacts (cH H) callOrder [] := by
  refine ⟨fun g hg => ?_, fun g hg => ?_, fun g hg => ?_, fun p hp fn hfn cl hcl => ?_, openLaws_of_plain noRaw⟩
  · rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks, term_named] at hg
    exact absurd hg List.not_mem_nil
  · rw [Semantics.totalObligationsRP_withHooks _ H _ _, total_named] at hg
    exact absurd hg List.not_mem_nil
  · rw [Det.Semantics.agreeObligationsI_withHooks, agree_named] at hg
    exact absurd hg List.not_mem_nil
  · rw [Det.Semantics.matchObligationsL_withHooks, match_named, List.mem_singleton] at hp
    subst hp
    rw [lookupFH H] at hfn
    cases hfn
    simp only [fCool, List.getElem?_cons_zero, Option.some.injEq] at hcl
    subst hcl
    exact matchCool H

/-- **`f` and `isKResult` have one result, for every H**: from the deciders' facts, without the owed
condition (termination, agreement and match independence; `TiePair.fnModel_noTotal`). -/
theorem fnDet (H : HookParams) : FnDet (cH H) :=
  (TiePair.fnModel_noTotal (c := cH H)
    (hpreTop := by simp only [Semantics.clausesPreTop_withHooks]; decide +kernel)
    (hnoEx := (Semantics.fnsNoExs_withHooks _ _).mpr (Semantics.fnsNoExs_of_all (by decide +kernel))) (ord := callOrder) (coreOKH H)
    (fun g _ => (Semantics.rightHeld_withHooks (Semantics.rightHeld_of_valued (by decide +kernel)) H noRaw).heldOwed g)
    (facts H).1 (facts H).2.2.1 (facts H).2.2.2.1).1

/-- **The clause of `f` is `Witnessed`, for every H**, at HOLE := `hole`: its `requires` is `true`
and nothing else. -/
theorem witnessed (H : HookParams) : clCool.Witnessed (cH H) := by
  refine ⟨[(1, hole)], fun j hj s hs => ?_, fun t ht => ?_, .top⟩
  · rw [needs.2.2] at hj
    cases List.mem_singleton.mp hj
    cases (show some Srt.k = some s from hs)
    exact ⟨hole, rfl, by rw [sortOfH]; exact sorts.1⟩
  · cases ht
    exact ⟨req_true H rfl, fun r hr => EvalTerm.functional_of_fnDet (fnDet H) hr (req_true H rfl)⟩

/-- **The clauses' hypothesis of the pinned statements, for every H**: the one clause needing a
witness is `Witnessed`, so its `CondDecided`, which the account lists as owed, holds. -/
theorem hc (H : HookParams) :
    ∀ fn ∈ (cH H).fns, ∀ cl ∈ fn.clauses, cl.needsWitness (cH H) = true → cl.CondDecided (cH H) := by
  refine openClauses_of_owed fun p hp fn hfn cl hcl => ?_
  rw [Semantics.owedClauses_withHooks, owed_clauses, List.mem_singleton] at hp
  subst hp
  rw [fnsH] at hfn
  cases hfn
  cases hcl
  exact .inl (witnessed H)

/-- No rule needs a witness. -/
theorem rules_decided (H : HookParams) :
    ∀ r ∈ (cH H).rules, r.needsWitness (cH H) = true → r.CondDecided (cH H) :=
  openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi)

/-- **`OpenDecided`, for every H.** -/
theorem openDecided (H : HookParams) : OpenDecided (cH H) := ⟨rules_decided H, hc H⟩

/-- **`FnHyp`, for every H.** -/
theorem fnHyp (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil
    ((facts H).obligations (openDecided H))

/-- **`Γc` with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHyp H)

/-! ## `f(3) = 3` (C7 form (a)) -/

/-- `X ↦ 3`, `HOLE ↦ hole`. -/
def σ3 : Subst := [(0, i3), (1, hole)]

theorem ws3 (H : HookParams) : (cH H).WellSorted clCool.vars σ3 := fun i s hs => by
  match i, hs with
  | 0, hs => cases (show some Srt.int = some s from hs); exact ⟨i3, rfl, by rw [sortOfH]; exact sorts.2⟩
  | 1, hs => cases (show some Srt.k = some s from hs); exact ⟨hole, rfl, by rw [sortOfH]; exact sorts.1⟩
  | _ + 2, hs => cases (show (none : Option Srt) = some s from hs)

/-- **`f(3)` is 3, for every H**, by the clause at X := 3, HOLE := `hole`. -/
theorem eval_f3 (H : HookParams) : Eval (cH H) fS [i3] (some i3) :=
  .clause (cl := clCool) (σ := σ3) (lookupFH H) (List.mem_singleton_self _) (ws3 H) (.cons (.var rfl) .nil)
    (fun t ht => by cases ht; exact req_true H rfl) .top
    (fun cl' hcl' _ hlt => by rw [List.mem_singleton.mp hcl'] at hlt; exact absurd hlt (by decide))
    rfl .var (fun _ ht => by cases ht) .top

/-- `⟦f(3)⟧`. -/
noncomputable abbrev f3 (H : HookParams) : P := TiePair.app (cH H) fS [i3]

/-- **Every model of `Γc` reads `f(3)` as 3, for every H**: `Eval`'s result, the clauses'
hypothesis (`hc`) giving the exclusions of the competing clauses. -/
theorem f3_c (H : HookParams) : Γc (cH H) ⊧ (f3 H ≡ den (cH H) i3) := by
  intro M _ I hIc e m
  have hI : I ⊧ᴵP Γ (cH H) := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, -, hph, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hpreR := HoldsShape.preReadAll_of_core (coreOKH H) hIc
  have hnoEx : (cH H).FnsNoExs := (Semantics.fnsNoExs_withHooks c H).mpr (Semantics.fnsNoExs_of_all (by decide +kernel))
  have hneg := neg_of_coreCl hIc (Semantics.sortedOKCl_of_sortedOK_noExs hok hnoEx) hsr
    (Semantics.coreOK_parts (coreOKH H)).2.1 hph (hc H) hpreR
  have h0 := eval_den4ClPre hI hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK_noExs hok hnoEx))
    hneg hpreR (eval_f3 H) (lookupFH H)
    (sortsOf_cons.mpr ⟨_, _, by rw [sortOfH]; exact sorts.2, sortsOf_nil, rfl⟩)
  rw [KoreAML.interp_equal (defOK hI)]
  intro a
  exact h0 e a

/-! ## The premises of the derivation -/

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- Their indices: 204 is `f(X) => X requires true andBool isKResult(HOLE)`; the last two are
`isKResult`'s, 233 at `kseq(inj{KResult,KItem}(V), dotk)` (`kr1`) and 232 its `[owise]` sibling. -/
theorem fnText_index : fnText.map (·.index) =
    [204, 223, 231, 230, 229, 228, 237, 236, 239, 238, 235, 234, 212, 211, 222, 221, 218, 217, 220, 219,
     225, 224, 227, 226, 214, 213, 216, 215, 233, 232] := by
  decide +kernel

noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence**, pattern for pattern or with
one variable renamed (`TiePair.sameB`; kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- The function sentences as written, the text's rule items (none), the families of the reading,
and `Γcl` (`boolClosed`, a family of the reading of a definition that reads a confined sort). -/
def Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats ∪ Γcl (cH H)

/-- **Every premise of `Γc` is a consequence of `Pre`.** -/
theorem gamma_from (H : HookParams) : ∀ φ, Γc (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases h with h | h
  · exact TiePair.gamma_from (shapeH H) φ h (I := I) fun ψ hψ => hI ψ (Or.inl hψ)
  · exact hI φ (Or.inr h)

/-- **`Pre` with the step's closure has a model, for every H**: every model of `Γc` with it is one. -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) := by
  obtain ⟨M, hM, I, hI⟩ := consistent H
  have hΓ : I ⊧ᴵP Γ (cH H) := fun φ h => hI φ (Or.inl (Or.inl h))
  refine ⟨M, hM, I, fun φ h => ?_⟩
  rcases h with (h | h) | h
  · rcases h with ((h1 | h1) | h1)
    · rcases h1 with ht | ⟨x, rfl⟩
      · exact TiePair.entailed (shapeH H) φ ht hΓ
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))))))
    · exact hΓ _ (Or.inl (Or.inr h1))
    · rcases h1 with (((h1 | h1) | h1) | h1) | h1
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h1))))))
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1))))))
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1)))))
      · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inr h1))))
      · exact hΓ _ (Or.inr h1)
  · exact hI _ (Or.inl (Or.inr h))
  · exact hI _ (Or.inr h)

/-- The cut: what `Γc` entails, `Pre` entails. -/
theorem cutC (H : HookParams) {ψ : P} (hψ : Γc (cH H) ⊧ ψ) : Pre H ⊧ ψ :=
  fun hT => hψ fun φ hφ => gamma_from H φ hφ hT

/-- **`f(3) = 3`, derived from `Pre`, for every H**: the sentence of `f(X) => X` (204) holds HOLE
universal over K, so it holds at HOLE := `hole`, where the equation of `isKResult` (233) makes the
`requires` true; `Pre` with the step's closure has a model (`pre_model`). -/
theorem f3_is_3 (H : HookParams) : Pre H ⊧ (f3 H ≡ den (cH H) i3) := cutC H (f3_c H)

/-! ## Soundness at this text with no hypothesis left -/

/-- **The pinned `sound_at` at e2-cool-eq, for every H, with no hypothesis left**: the clause side
by `hc`, the rule side vacuous. -/
theorem sound_at_wit (H : HookParams) (x y : Config (cH H)) (r : Rule) (σ : Subst) (hs : StepBy (cH H) r σ x y) :
    (Γc (cH H) ⊧ (den (cH H) x.val ⇒ KoreAML.sNext (famEx (cH H) r σ))) ∧
      (Γc (cH H) ⊧ (den (cH H) y.val ⇒ famEx (cH H) r σ)) :=
  sound_at (cH H) (coreOKH H) x y r σ hs (fun r' hr' _ hw _ => rules_decided H r' hr' hw) (hc H)

end KCore.CoolEqWit

/-- info: 'KCore.CoolEqWit.witnessed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CoolEqWit.witnessed
/-- info: 'KCore.CoolEqWit.hc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CoolEqWit.hc
/-- info: 'KCore.CoolEqWit.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CoolEqWit.consistent
/-- info: 'KCore.CoolEqWit.pre_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CoolEqWit.pre_model
/-- info: 'KCore.CoolEqWit.f3_is_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CoolEqWit.f3_is_3
/-- info: 'KCore.CoolEqWit.sound_at_wit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CoolEqWit.sound_at_wit
