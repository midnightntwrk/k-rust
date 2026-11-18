/-
  The fixture e2-clause-genless-wit: `syntax S ::= "a" | c(Empty) | "d"` (`syntax Empty`, no
  production), `isC(S)` total with `isC(c(_)) => true`, `isC(d) => true` and
  `isC(_) => false [owise]`, and `f(Int)` with `rule f(_) => 1 requires isC(H:S) [unboundVariables(H)]`
  beside `rule f(_) => 0 [owise]`. The text is `f2-examples/e2-clause-genless-wit.kompile.kore`.
  Run from the package root: `lake env lean -j1 test/ClauseGenlessWit.lean`.

  S keeps the generator `c` over Empty, a sort without a value, so S is not confined and the first
  clause of `f`, whose closed `requires` holds H:S, owes its `CondDecided` (the account:
  `CondDecided open, over VarH:S`; `owedClauses = [(0, 0)]`). Every statement is for every
  interpretation H.

  - The clause is `Witnessed` at H := d (`witnessed`): `isC(d) => true` gives `isC(d)` the result
    `true` (`isC_d`), and no other, `f` and `isC` having one result (`fnDet`: their competing
    equations are those of `isC` at `c(_)` and at `d`, whose right sides are both `true`, and the
    first clause of `f` is match independent, `matchG`).
  - So the clauses' hypothesis of the pinned statements holds (`hc`), and with the rules' side
    vacuous (no rule needs a witness) `OpenDecided` holds (`openDecided`), `FnHyp` holds (`fnHyp`)
    and `Γc` with the step's closure has a model (`consistent`).
  - `f(0) = 1` (C7 form (a), from sentences): `Eval` gives it by the first clause at H := d
    (`eval_f0`), so every model of `Γc` reads it (`f0_c`, by `eval_den4ClPre` with the clauses'
    hypothesis), and `Pre`, the function sentences as written with Γ's rule item, the families of
    the reading and `Γcl` (`boolClosed`), entails it (`f0_is_1`); `Pre` with the step's closure has
    a model (`pre_model`). The sentences that determine it are the first equation of `f` (its
    sentence holds H universal over S, so it holds at H := d) and `isC(d) => true`.
  - `sound_at_wit`: the pinned `sound_at` with no hypothesis left, the clause side by `hc`.

  The clauses are written by hand and shown to be the reader's (`text`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.ClauseGenlessWit

open KCore ML Faithful KoreAML

definition_of defn from "f2-examples/e2-clause-genless-wit.kompile.kore"
user_axioms U from "f2-examples/e2-clause-genless-wit.kompile.kore" module "E2-CLAUSE-GENLESS-WIT"
kore_term kore from "f2-examples/e2-clause-genless-wit.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fS : Sym := 390
def isCS : Sym := 391
def cS : Sym := 387
def dS : Sym := 388
def sS : Srt := 32

theorem names : c.symName fS = "Lblf" ∧ c.symName isCS = "LblisC" ∧ c.symName cS = "Lblc" ∧
    c.symName dS = "Lbld" ∧ c.sortName sS = "S" ∧ c.sortName 33 = "Empty" := by
  decide +kernel

/-! ## The clauses -/

/-- `f(X) => 1 requires isC(H)`, X:Int, H:S -/
def clG : Clause :=
  { vars := [Srt.int, sS], pats := [.var 0], req := some (.app isCS [.var 1]), rhs := .dv Srt.int (.int 1),
    ens := none }
/-- `f(_) => 0 [owise]` -/
def clO : Clause := { vars := [Srt.int], pats := [.var 0], req := none, rhs := .dv Srt.int (.int 0), ens := none, prio := 200 }
def fG : Fn := { label := fS, args := [Srt.int], result := Srt.int, clauses := [clG, clO] }
/-- `isC(c(_)) => true` -/
def ic1 : Clause := { vars := [33], pats := [.app cS [.var 0]], req := none, rhs := .dv Srt.bool (.bool true), ens := none }
/-- `isC(d) => true` -/
def icd : Clause := { vars := [], pats := [.app dS []], req := none, rhs := .dv Srt.bool (.bool true), ens := none }
/-- `isC(_) => false [owise]` -/
def ic2 : Clause := { vars := [sS], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool false), ens := none, prio := 200 }
def fIsC : Fn := { label := isCS, args := [sS], result := Srt.bool, clauses := [ic1, icd, ic2], total := true }

theorem text : c.fns = [fG, fIsC] := by rfl

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem fnsH (H : HookParams) : (cH H).fns = [fG, fIsC] := text
theorem lookupFH (H : HookParams) : (cH H).lookupFn fS = some fG := by
  rw [Semantics.lookupFn_withHooks]; rfl
theorem lookupIsCH (H : HookParams) : (cH H).lookupFn isCS = some fIsC := by
  rw [Semantics.lookupFn_withHooks]; rfl
theorem sortOfH (H : HookParams) (v : GroundTerm) : (cH H).sortOf v = c.sortOf v := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]

def dv : GroundTerm := .ctor dS []
def i0 : GroundTerm := .dv Srt.int (.int 0)
def i1 : GroundTerm := .dv Srt.int (.int 1)

theorem sorts : c.sortOf dv = some sS ∧ c.sortOf i0 = some Srt.int ∧ c.sortOf i1 = some Srt.int := by
  decide +kernel

theorem syms (H : HookParams) : (cH H).isCtor dS = true ∧ (cH H).isCtor isCS = false ∧ isHook isCS = false ∧
    (cH H).isParam isCS = false :=
  (by decide +kernel : c.isCtor dS = true ∧ c.isCtor isCS = false ∧ isHook isCS = false ∧ c.isParam isCS = false)


/-! ## `isC(d)` is `true`, and the clause is `Witnessed` at H := d -/

/-- **`isC(d)` is `true`**, by `isC(d) => true`: no clause of a smaller priority. -/
theorem isC_d (H : HookParams) : Eval (cH H) isCS [dv] (some (bool true)) :=
  .clause (cl := icd) (σ := []) (lookupIsCH H) (by simp [fIsC]) (fun i s hs => by simp [icd] at hs)
    (.cons (.ctor (syms H).1 .nil) .nil) (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fIsC, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl | rfl <;> exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- `H ↦ d`. -/
def σd : Subst := [(1, dv)]

/-- `isC(H)` under a σ giving H the value d: `true`. -/
theorem req_at (H : HookParams) {σ : Subst} (h1 : σ.lookup 1 = some dv) :
    EvalTerm (cH H) σ (.app isCS [.var 1]) (some (bool true)) :=
  .call (vs := [dv]) (syms H).2.1 (syms H).2.2.1 (.cons .var .nil) (by rw [h1]; rfl) (isC_d H) (syms H).2.2.2

theorem req_d (H : HookParams) : EvalTerm (cH H) σd (.app isCS [.var 1]) (some (bool true)) := req_at H rfl

/-- The first clause of `f` is match independent: its right side has no variable. -/
theorem matchG (H : HookParams) : MatchIndependent (cH H) clG := by
  have hx : clG.exs = [] := rfl
  refine (matchIndependent_iff_noExs hx).mpr fun vs σ σ' _ _ _ _ _ _ _ => .inl
    ⟨hx, hx, rfl, rfl, fun i hi => ?_, fun t ht => by cases ht⟩
  cases hi

def callOrder : List Nat := [isCS, fS]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = [(fS, 0)] := by decide +kernel
theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem owed_clauses : c.owedClauses = [(0, 0)] := by decide +kernel

/-- The facts the deciders leave, for every H: the match independence of `f`'s first clause. -/
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
    simp only [fG, List.getElem?_cons_zero, Option.some.injEq] at hcl
    subst hcl
    exact matchG H

/-- **`f` and `isC` have one result, for every H**: from the deciders' facts, without the owed
condition (termination, agreement and match independence; `TiePair.fnModel_noTotal`). -/
theorem fnDet (H : HookParams) : FnDet (cH H) :=
  (TiePair.fnModel_noTotal (c := cH H)
    (hpreTop := by simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) (ord := callOrder) (coreOKH H)
    (fun g _ => (Semantics.rightHeld_withHooks (Semantics.rightHeld_of_valued (by decide +kernel)) H noRaw).heldOwed g)
    (facts H).1 (facts H).2.2.1 (facts H).2.2.2.1).1

/-- **The first clause of `f` is `Witnessed`, for every H**, at H := d: its `requires` `isC(d)` is
`true` and nothing else. -/
theorem witnessed (H : HookParams) : clG.Witnessed (cH H) := by
  refine ⟨σd, fun j hj s hs => ?_, fun t ht => ?_, .top⟩
  · have hj1 : j = 1 := by
      have : clG.condVars = [1] := by decide +kernel
      rw [this] at hj; exact List.mem_singleton.mp hj
    subst hj1
    cases (show some sS = some s from hs)
    exact ⟨dv, rfl, by rw [sortOfH]; exact sorts.1⟩
  · cases ht
    exact ⟨req_d H, fun r hr => EvalTerm.functional_of_fnDet (fnDet H) hr (req_d H)⟩

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


/-! ## `f(0) = 1` (C7 form (a)) -/

/-- `X ↦ 0`, `H ↦ d`. -/
def σG : Subst := [(0, i0), (1, dv)]

theorem ws_G (H : HookParams) : (cH H).WellSorted clG.vars σG := fun i s hs => by
  match i, hs with
  | 0, hs => cases (show some Srt.int = some s from hs); exact ⟨i0, rfl, by rw [sortOfH]; exact sorts.2.1⟩
  | 1, hs => cases (show some sS = some s from hs); exact ⟨dv, rfl, by rw [sortOfH]; exact sorts.1⟩
  | _ + 2, hs => cases (show (none : Option Srt) = some s from hs)

/-- **`f(0)` is 1, for every H**, by the first clause at X := 0, H := d. -/
theorem eval_f0 (H : HookParams) : Eval (cH H) fS [i0] (some i1) :=
  .clause (cl := clG) (σ := σG) (lookupFH H) (by simp [fG]) (ws_G H) (.cons (.var rfl) .nil)
    (fun t ht => by cases ht; exact req_at H rfl) .top
    (fun cl' hcl' _ hlt => by
      simp only [fG, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl <;> exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- `⟦f(0)⟧`. -/
noncomputable abbrev f0 (H : HookParams) : P := TiePair.app (cH H) fS [i0]

/-- **Every model of `Γc` reads `f(0)` as 1, for every H**: `Eval`'s result, the clauses'
hypothesis (`hc`) giving the exclusions of the competing clauses. -/
theorem f0_c (H : HookParams) : Γc (cH H) ⊧ (f0 H ≡ den (cH H) i1) := by
  intro M _ I hIc e m
  have hI : I ⊧ᴵP Γ (cH H) := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, -, hph, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hpreR := HoldsShape.preReadAll_of_core (coreOKH H) hIc
  have hneg := neg_of_coreCl hIc (Semantics.sortedOKCl_of_sortedOK hok) hsr
    (Semantics.coreOK_parts (coreOKH H)).2.1 hph (hc H) hpreR
  have h0 := eval_den4ClPre hI hnn hsc hph (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok))
    hneg hpreR (eval_f0 H) (lookupFH H)
    (sortsOf_cons.mpr ⟨_, _, by rw [sortOfH]; exact sorts.2.1, sortsOf_nil, rfl⟩)
  rw [KoreAML.interp_equal (defOK hI)]
  intro a
  exact h0 e a

/-! ## The premises of the derivation -/

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- Their indices: 216 is `f(_) => 1 requires isC(H:S)`, 215 its `[owise]` sibling, 225, 226 and
224 are `isC(c(_)) => true`, `isC(d) => true` and `isC(_) => false [owise]`. -/
theorem fnText_index : (fnText.map (·.index)).take 5 = [216, 215, 225, 226, 224] := by decide +kernel

noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence**, pattern for pattern or with
one variable renamed (`TiePair.sameB`; kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- The function sentences as written, Γ's rule item, the families of the reading, and `Γcl`
(`boolClosed`, a family of the reading of a definition that reads a confined sort). -/
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

/-- **`f(0) = 1`, derived from `Pre`, for every H**: the sentence of `f(_) => 1 requires isC(H:S)`
(216) holds H universal over S, so it holds at H := d, where `isC(d) => true` (226) makes the
`requires` true; `Pre` with the step's closure has a model (`pre_model`). -/
theorem f0_is_1 (H : HookParams) : Pre H ⊧ (f0 H ≡ den (cH H) i1) := cutC H (f0_c H)

/-! ## Soundness at this text with no hypothesis left -/

/-- **The pinned `sound_at` at e2-clause-genless-wit, for every H, with no hypothesis left**: the
clause side by `hc`, the rule side vacuous. -/
theorem sound_at_wit (H : HookParams) (x y : Config (cH H)) (r : Rule) (σ : Subst) (hs : StepBy (cH H) r σ x y) :
    (Γc (cH H) ⊧ (den (cH H) x.val ⇒ KoreAML.sNext (famEx (cH H) r σ))) ∧
      (Γc (cH H) ⊧ (den (cH H) y.val ⇒ famEx (cH H) r σ)) :=
  sound_at (cH H) (coreOKH H) x y r σ hs (fun r' hr' _ hw _ => rules_decided H r' hr' hw) (hc H)

end KCore.ClauseGenlessWit

/-- info: 'KCore.ClauseGenlessWit.witnessed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClauseGenlessWit.witnessed
/-- info: 'KCore.ClauseGenlessWit.hc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClauseGenlessWit.hc
/-- info: 'KCore.ClauseGenlessWit.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClauseGenlessWit.consistent
/-- info: 'KCore.ClauseGenlessWit.f0_is_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClauseGenlessWit.f0_is_1
/-- info: 'KCore.ClauseGenlessWit.pre_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClauseGenlessWit.pre_model
/-- info: 'KCore.ClauseGenlessWit.sound_at_wit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClauseGenlessWit.sound_at_wit
