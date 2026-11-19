/-
  The tie (C14) of the reading `setVarInDropped` on its construct fixture e3-setvar-nonlinear:
  `rule f(@S, @S) => r()`, an equation whose two arguments are memberships in one set variable,
  read as the clause with two distinct variables. The text is
  `f2-examples/svnonlinear.kompile.kore` (the kompiled text of
  `test/constructs/fixtures/e3-setvar-nonlinear`, as test/SetVarOwise.lean reads it).
  Run from the package root: `lake env lean -j1 test/NoteSetVarIn.lean`. Every statement is on the
  literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  Layer 1. `wf_defn`, `coreOK` (kernel); `defs_attrsAgree`; `account`: the function equations and
  the constructor sentences are sentences of the user module, apart, with the count of the rest.

  Layer 2. The equation (sentence 99) is the one function equation whose translation is not Γ's
  item pattern for pattern: kompile writes `X0 ∈ @S ∧ X1 ∈ @S → f(X0, X1) = r`, the set variable
  `@S` free, and Γ's item is `X0 ∈ V0 ∧ X1 ∈ V1 → f(X0, X1) = r`, `V0` and `V1` element variables.
  The sentence's translation and Γ's item are the translations of the two literal axioms `nsvAxS`
  and `nsvAxG` (`w_text`, `aW_at`; kernel), and the two hold in the same models of definedness, of
  the definition of `\ceil` and of the sort constant `SortExp` (`w_iff`, by `nsv_iff`: each says
  `f(X0, X1) = r` at every pair of elements of `SortExp`, the sentence by `KCore.setvar_in_drop`).
  Those two signature items are items of Γ (`sig_ceil`, `sig_exp`), so Γ entails the sentence
  (`fns_entailed`, every function equation, for every H), and the sentence with them entails Γ's
  item (`w1`). The other function equations (the sort predicates') are Γ's items (`shape`).
  Constructor sentences: `cons_entailed`. `consistent` for every H.

  The expectations (C7 form (a), from sentences): `PreW H` is every function equation as written
  (sentence 99 among them), Γ's rule items and the families; it has a model (`preW_model`).
  `f_a_b`: `f(a, b) = r`, at two distinct values. `f_a_a`: `f(a, a) = r`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.NoteSetVarIn

open KCore ML Faithful KoreAML

section Bridge
open Kore (KSort Pattern)

variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-! ## The two forms of the equation, on the translated patterns

The sentence `X0 ∈ @S ∧ X1 ∈ @S → f(X0, X1) = r` (`svinAx`, KcoreSpec/SetVarIn.lean) and Γ's item
`X0 ∈ V0 ∧ X1 ∈ V1 → f(X0, X1) = r` (`nsvItem`) each hold exactly where `f(X0, X1) = r` holds at
every pair of elements of `SortExp` (`NsvRead`): the sentence by `KCore.setvar_in_drop` (the set
`{x₀, x₁}` holds both elements), the item by `nsv_evar_in_drop` (`V0` at `x₀`, `V1` at `x₁`). -/

theorem nsv_upd2 {e : Valuation M} {v₀ v₁ x : EVar} {a₀ a₁ : M} (h0 : x ≠ v₀) (h1 : x ≠ v₁) :
    Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ x = e.evalEvar x := by
  rw [Function.update_noteq h1, Function.update_noteq h0]

theorem nsv_upd_self {α β : Type} [DecidableEq α] (f : α → β) (x : α) : Function.update f x (f x) = f := by
  funext y
  by_cases h : y = x
  · subst h; exact Function.update_same _ _ _
  · exact Function.update_noteq h _ _

theorem nsv_upd2_fst {e : Valuation M} {v₀ v₁ : EVar} {a₀ a₁ : M} (hv : v₀ ≠ v₁) :
    Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ v₀ = a₀ := by
  rw [Function.update_noteq hv, Function.update_same]

theorem nsv_upd2_snd {e : Valuation M} {v₀ v₁ : EVar} {a₀ a₁ : M} :
    Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ v₁ = a₁ := Function.update_same _ _ _

/-- **Memberships in two distinct element variables that stand nowhere else are dropped.** A sentence
`Q ∧ (x₀ ∈ v₀ ∧ (x₁ ∈ v₁ ∧ T)) → φ` of the result sort `R` holds at a point for every pair of
elements `v₀`, `v₁` of the sort `S` exactly where `Q ∧ T → φ` holds there, when `v₀` and `v₁` are
distinct, neither is `x₀` or `x₁` or free in `S`, `R`, `Q`, `T`, `φ`, and `x₀`, `x₁` are elements
of `S`. -/
theorem nsv_evar_in_drop [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {e : Valuation M} {S R Q T φ : P} {σ ρ : M} {x₀ x₁ v₀ v₁ : EVar}
    (hS : ∀ a, S.interpret I e a ↔ a = σ) (hR : ∀ a, R.interpret I e a ↔ a = ρ)
    (hσ : IsSort I σ) (hρ : IsSort I ρ)
    (h₀ : Inh I σ (e.evalEvar x₀)) (h₁ : Inh I σ (e.evalEvar x₁))
    (hv : v₀ ≠ v₁) (h00 : x₀ ≠ v₀) (h01 : x₀ ≠ v₁) (h10 : x₁ ≠ v₀) (h11 : x₁ ≠ v₁)
    (hS0 : S.isFreeEvar v₀ = false) (hS1 : S.isFreeEvar v₁ = false)
    (hR0 : R.isFreeEvar v₀ = false) (hR1 : R.isFreeEvar v₁ = false)
    (hQ0 : Q.isFreeEvar v₀ = false) (hQ1 : Q.isFreeEvar v₁ = false)
    (hT0 : T.isFreeEvar v₀ = false) (hT1 : T.isFreeEvar v₁ = false)
    (hφ0 : φ.isFreeEvar v₀ = false) (hφ1 : φ.isFreeEvar v₁ = false) (m : M) :
    (∀ a₀ a₁ : M, Inh I σ a₀ → Inh I σ a₁ →
      (sImp R (sAnd Q (sAnd (sIn S R (.evar x₀) (.evar v₀)) (sAnd (sIn S R (.evar x₁) (.evar v₁)) T)))
        φ).interpret I ⟨Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁, e.evalSvar⟩ m) ↔
    (sImp R (sAnd Q T) φ).interpret I e m := by
  have inv : ∀ {ψ : P}, ψ.isFreeEvar v₀ = false → ψ.isFreeEvar v₁ = false → ∀ (a₀ a₁ b : M),
      ψ.interpret I ⟨Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁, e.evalSvar⟩ b ↔
        ψ.interpret I e b := fun {ψ} g0 g1 a₀ a₁ b =>
    (interp_evarAt_svin (I := I) (e := ⟨Function.update e.evalEvar v₀ a₀, e.evalSvar⟩) (a := a₁) g1 b).trans
      (interp_evarAt_svin (I := I) (e := e) (a := a₀) g0 b)
  have hS' := fun a₀ a₁ b => (inv hS0 hS1 a₀ a₁ b).trans (hS b)
  have hR' := fun a₀ a₁ b => (inv hR0 hR1 a₀ a₁ b).trans (hR b)
  have hin0 : ∀ a₀ a₁ : M, (sIn S R (.evar x₀) (.evar v₀)).interpret I
      ⟨Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁, e.evalSvar⟩ m ↔ (e.evalEvar x₀ = a₀ ∧ Inh I ρ m) := by
    intro a₀ a₁
    rw [interp_sIn_evar_svin hD hc (hS' a₀ a₁) (hR' a₀ a₁) hσ hρ
      (by show Inh I σ (Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ x₀); rw [nsv_upd2 h00 h01]; exact h₀) m]
    show (Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ x₀ =
      Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ v₀ ∧ _) ↔ _
    rw [nsv_upd2 h00 h01, Function.update_noteq hv, Function.update_same]
  have hin1 : ∀ a₀ a₁ : M, (sIn S R (.evar x₁) (.evar v₁)).interpret I
      ⟨Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁, e.evalSvar⟩ m ↔ (e.evalEvar x₁ = a₁ ∧ Inh I ρ m) := by
    intro a₀ a₁
    rw [interp_sIn_evar_svin hD hc (hS' a₀ a₁) (hR' a₀ a₁) hσ hρ
      (by show Inh I σ (Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ x₁); rw [nsv_upd2 h10 h11]; exact h₁) m]
    show (Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ x₁ =
      Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁ v₁ ∧ _) ↔ _
    rw [nsv_upd2 h10 h11, Function.update_same]
  have hinh : ∀ a₀ a₁ : M, (inhOf R).interpret I
      ⟨Function.update (Function.update e.evalEvar v₀ a₀) v₁ a₁, e.evalSvar⟩ m ↔ Inh I ρ m :=
    fun a₀ a₁ => interp_inhOf_of (hR' a₀ a₁)
  simp only [interp_sImp, interp_sAnd, hinh, interp_inhOf_of hR]
  constructor
  · intro h
    have := h _ _ h₀ h₁
    rw [hin0, hin1, inv hQ0 hQ1, inv hT0 hT1, inv hφ0 hφ1] at this
    exact ⟨this.1, fun ⟨hq, ht⟩ => this.2 ⟨hq, ⟨rfl, this.1⟩, ⟨rfl, this.1⟩, ht⟩⟩
  · rintro ⟨hm, hf⟩ a₀ a₁ _ _
    rw [hin0, hin1, inv hQ0 hQ1, inv hT0 hT1, inv hφ0 hφ1]
    exact ⟨hm, fun ⟨hq, _, _, ht⟩ => hf ⟨hq, ht⟩⟩

def nsvRv : Kore.SortVar := ⟨⟨⟨"R"⟩⟩⟩
def nsvV0 : Kore.EVar := ⟨⟨⟨"VarV0"⟩⟩, svinExp⟩
def nsvV1 : Kore.EVar := ⟨⟨⟨"VarV1"⟩⟩, svinExp⟩

/-- Γ's axiom of the clause read from `rule f(@S, @S) => r()`: two distinct element variables. -/
def nsvItem : Pattern :=
  .implies svinR
    (.and svinR [.top svinR,
      .and svinR [.in svinExp svinR (.var (.evar svinX0)) (.var (.evar nsvV0)),
        .and svinR [.in svinExp svinR (.var (.evar svinX1)) (.var (.evar nsvV1)), .top svinR]]])
    svinEq

def nsvAxS : Kore.Axiom := ⟨[nsvRv], svinAx, []⟩
def nsvAxG : Kore.Axiom := ⟨[nsvRv], nsvItem, []⟩
def nsvCtxG : Ctx := ⟨tableOf [nsvRv] nsvItem, []⟩

/-- `nsv_evar_in_drop` at Γ's item. -/
theorem nsv_item_drop [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    {e : Valuation M} {σ ρ : M}
    (hS : ∀ a, (trSort nsvCtxG.vars svinExp).interpret I e a ↔ a = σ)
    (hR : ∀ a, (trSort nsvCtxG.vars svinR).interpret I e a ↔ a = ρ)
    (hσ : IsSort I σ) (hρ : IsSort I ρ)
    (h₀ : Inh I σ (e.evalEvar (nsvCtxG.vars.ev (evarKey svinX0))))
    (h₁ : Inh I σ (e.evalEvar (nsvCtxG.vars.ev (evarKey svinX1)))) (m : M) :
    (∀ a₀ a₁ : M, Inh I σ a₀ → Inh I σ a₁ →
      (tr nsvCtxG nsvItem).interpret I
        ⟨Function.update (Function.update e.evalEvar (nsvCtxG.vars.ev (evarKey nsvV0)) a₀)
          (nsvCtxG.vars.ev (evarKey nsvV1)) a₁, e.evalSvar⟩ m) ↔
    (tr nsvCtxG svinRead).interpret I e m :=
  nsv_evar_in_drop hD hc hS hR hσ hρ h₀ h₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) m

/-- The element variables of the sort variable `R` and of `X0`, `X1`, in the sentence's table. -/
def nsvKR : EVar := svinCtx.vars.ev (.sortVar "R")
def nsvK0 : EVar := svinCtx.vars.ev (evarKey svinX0)
def nsvK1 : EVar := svinCtx.vars.ev (evarKey svinX1)

/-- The sentence with its memberships dropped, at every valuation meeting the guards of `R`, `X0`
and `X1`: `f(X0, X1) = r` at every pair of elements of `SortExp`. -/
def NsvRead (I : Interpretation KoreAML.Sym M) (σ : M) : Prop :=
  ∀ e : Valuation M, IsSort I (e.evalEvar nsvKR) → Inh I σ (e.evalEvar nsvK0) → Inh I σ (e.evalEvar nsvK1) →
    ∀ m, Inh I (e.evalEvar nsvKR) m → (tr svinCtx svinRead).interpret I e m

theorem nsv_imp_inh {t : VarTable} {R : KSort} {prem φ : Pattern} {e : Valuation M} {b : M}
    (h : (tr ⟨t, []⟩ (.implies R prem φ)).interpret I e b) : (inhOf (trSort t R)).interpret I e b := by
  simp only [tr, interp_sImp] at h; exact h.1

theorem nsv_trSort_exp {σ : M} (hσ1 : ∀ a, I.evalSymb (.sort "SortExp") a ↔ a = σ) (t : VarTable)
    (e : Valuation M) (a : M) : (trSort t svinExp).interpret I e a ↔ a = σ := by
  have : trSort t svinExp = sym (.sort "SortExp") := by simp [svinExp, trSort, trSortApp]
  rw [this]; exact hσ1 a

theorem nsv_trSort_R (t : VarTable) (e : Valuation M) (a : M) :
    (trSort t svinR).interpret I e a ↔ a = e.evalEvar (t.ev (.sortVar "R")) := by
  have : trSort t svinR = .evar (t.ev (.sortVar "R")) := by simp [svinR, trSort, sortVarKey]
  rw [this, interp_evar]

theorem nsv_freeS : (nsvAxS.sortVars.map sortVarKey ++ freeOf [] nsvAxS.pattern).eraseDups =
    [.sortVar "R", evarKey svinX0, svarKey svinS, evarKey svinX1] := by decide
theorem nsv_freeG : (nsvAxG.sortVars.map sortVarKey ++ freeOf [] nsvAxG.pattern).eraseDups =
    [.sortVar "R", evarKey svinX0, evarKey nsvV0, evarKey svinX1, evarKey nsvV1] := by decide

/-- **The sentence holds exactly where `f(X0, X1) = r` holds at every pair of elements of `SortExp`.** -/
theorem nsv_sentence_iff [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {σ : M}
    (hσ1 : ∀ a, I.evalSymb (.sort "SortExp") a ↔ a = σ) (hσ : IsSort I σ) :
    (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", nsvAxS⟩).pat) ↔ NsvRead I σ := by
  constructor
  · intro h e hR0 h0 h1 m hm
    refine (setvar_in_drop_e3 hD hc (nsv_trSort_exp hσ1 _ e) (nsv_trSort_R _ e) hσ hR0 h0 h1 m).mp fun A hA => ?_
    refine (trAxiom_at hD h (svarAt_svin e (svinCtx.vars.sv (svarKey svinS)) A) (fun k hk b => ?_) m).mpr ?_
    · rw [nsv_freeS] at hk
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact (interp_guard_sortVar hD).mpr hR0
      · exact (interp_guard_evar hD).mpr ((interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mpr h0)
      · refine (interp_included hD).mpr fun a ha => (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mpr (hA a ?_)
        change Function.update e.evalSvar (svinCtx.vars.sv (svarKey svinS)) A (svinCtx.vars.sv (svarKey svinS)) a at ha
        rwa [Function.update_same] at ha
      · exact (interp_guard_evar hD).mpr ((interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mpr h1)
    · show (inhOf (trSort _ svinR)).interpret I _ m
      exact (interp_inhOf_of (nsv_trSort_R _ _)).mpr hm
  · intro hMid e m
    unfold trAxiom
    dsimp only
    rw [interpret_impl]
    intro hgd
    have hg : ∀ k ∈ [VarKey.sortVar "R", evarKey svinX0, svarKey svinS, evarKey svinX1],
        (guardOf (tableOf nsvAxS.sortVars nsvAxS.pattern) k).interpret I e m := fun k hk =>
      conjList_mem hgd _ (List.mem_map.mpr ⟨k, by rw [nsv_freeS]; exact hk, rfl⟩)
    have hR0 : IsSort I (e.evalEvar nsvKR) := (interp_guard_sortVar hD).mp (hg _ (by decide))
    have h0 : Inh I σ (e.evalEvar nsvK0) :=
      (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mp ((interp_guard_evar hD).mp (hg (evarKey svinX0) (by decide)))
    have h1 : Inh I σ (e.evalEvar nsvK1) :=
      (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mp ((interp_guard_evar hD).mp (hg (evarKey svinX1) (by decide)))
    have hX : ∀ a, e.evalSvar (svinCtx.vars.sv (svarKey svinS)) a → Inh I σ a := fun a ha =>
      (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mp ((interp_included hD).mp (hg (svarKey svinS) (by decide)) a ha)
    rw [interp_equal hD]
    intro b
    show (tr svinCtx svinAx).interpret I e b ↔ (inhOf (trSort svinCtx.vars svinR)).interpret I e b
    refine ⟨nsv_imp_inh, fun hb => ?_⟩
    have hb' : Inh I (e.evalEvar nsvKR) b := (interp_inhOf_of (nsv_trSort_R _ _)).mp hb
    have := (setvar_in_drop_e3 hD hc (nsv_trSort_exp hσ1 _ e) (nsv_trSort_R _ e) hσ hR0 h0 h1 b).mpr
      (hMid e hR0 h0 h1 b hb') _ hX
    have he : svarAt_svin e (svinCtx.vars.sv (svarKey svinS)) (e.evalSvar (svinCtx.vars.sv (svarKey svinS))) = e := by
      cases e; simp [svarAt_svin, nsv_upd_self]
    rw [he] at this; exact this

theorem nsv_keys : nsvCtxG.vars.ev (.sortVar "R") = nsvKR ∧ nsvCtxG.vars.ev (evarKey svinX0) = nsvK0 ∧
    nsvCtxG.vars.ev (evarKey svinX1) = nsvK1 ∧ tr nsvCtxG svinRead = tr svinCtx svinRead := by decide

/-- **Γ's item holds exactly where `f(X0, X1) = r` holds at every pair of elements of `SortExp`.** -/
theorem nsv_item_iff [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {σ : M}
    (hσ1 : ∀ a, I.evalSymb (.sort "SortExp") a ↔ a = σ) (hσ : IsSort I σ) :
    (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", nsvAxG⟩).pat) ↔ NsvRead I σ := by
  obtain ⟨kR, k0, k1, kT⟩ := nsv_keys
  have hne : nsvCtxG.vars.ev (.sortVar "R") ≠ nsvCtxG.vars.ev (evarKey nsvV0) ∧
      nsvCtxG.vars.ev (.sortVar "R") ≠ nsvCtxG.vars.ev (evarKey nsvV1) ∧
      nsvCtxG.vars.ev (evarKey svinX0) ≠ nsvCtxG.vars.ev (evarKey nsvV0) ∧
      nsvCtxG.vars.ev (evarKey svinX0) ≠ nsvCtxG.vars.ev (evarKey nsvV1) ∧
      nsvCtxG.vars.ev (evarKey svinX1) ≠ nsvCtxG.vars.ev (evarKey nsvV0) ∧
      nsvCtxG.vars.ev (evarKey svinX1) ≠ nsvCtxG.vars.ev (evarKey nsvV1) ∧
      nsvCtxG.vars.ev (evarKey nsvV0) ≠ nsvCtxG.vars.ev (evarKey nsvV1) := by decide
  obtain ⟨nR0, nR1, n00, n01, n10, n11, nv⟩ := hne
  constructor
  · intro h e hR0 h0 h1 m hm
    rw [← kR] at hR0 hm; rw [← k0] at h0; rw [← k1] at h1
    rw [← kT]
    refine (nsv_item_drop hD hc (nsv_trSort_exp hσ1 _ e) (nsv_trSort_R _ e) hσ hR0 h0 h1 m).mp fun a₀ a₁ ha₀ ha₁ => ?_
    refine (trAxiom_at hD h _ (fun k hk b => ?_) m).mpr ?_
    · rw [nsv_freeG] at hk
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · exact (interp_guard_sortVar hD).mpr
          ((congrArg (IsSort I) (nsv_upd2 (e := e) (a₀ := a₀) (a₁ := a₁) nR0 nR1)).mpr hR0)
      · exact (interp_guard_evar hD).mpr ((interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mpr
          ((congrArg (Inh I σ) (nsv_upd2 (e := e) (a₀ := a₀) (a₁ := a₁) n00 n01)).mpr h0))
      · exact (interp_guard_evar hD).mpr ((interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mpr
          ((congrArg (Inh I σ) (nsv_upd2_fst (e := e) (a₀ := a₀) (a₁ := a₁) nv)).mpr ha₀))
      · exact (interp_guard_evar hD).mpr ((interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mpr
          ((congrArg (Inh I σ) (nsv_upd2 (e := e) (a₀ := a₀) (a₁ := a₁) n10 n11)).mpr h1))
      · exact (interp_guard_evar hD).mpr ((interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mpr
          ((congrArg (Inh I σ) (nsv_upd2_snd (e := e) (a₀ := a₀) (a₁ := a₁) (v₀ := nsvCtxG.vars.ev (evarKey nsvV0)) (v₁ := nsvCtxG.vars.ev (evarKey nsvV1)))).mpr ha₁))
    · show (inhOf (trSort _ svinR)).interpret I _ m
      exact (interp_inhOf_of (nsv_trSort_R _ _)).mpr
        ((congrArg (fun r => Inh I r m) (nsv_upd2 (e := e) (a₀ := a₀) (a₁ := a₁) nR0 nR1)).mpr hm)
  · intro hMid e m
    unfold trAxiom
    dsimp only
    rw [interpret_impl]
    intro hgd
    have hg : ∀ k ∈ [VarKey.sortVar "R", evarKey svinX0, evarKey nsvV0, evarKey svinX1, evarKey nsvV1],
        (guardOf (tableOf nsvAxG.sortVars nsvAxG.pattern) k).interpret I e m := fun k hk =>
      conjList_mem hgd _ (List.mem_map.mpr ⟨k, by rw [nsv_freeG]; exact hk, rfl⟩)
    have hR0 : IsSort I (e.evalEvar (nsvCtxG.vars.ev (.sortVar "R"))) := (interp_guard_sortVar hD).mp (hg _ (by decide))
    have h0 : Inh I σ (e.evalEvar (nsvCtxG.vars.ev (evarKey svinX0))) :=
      (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mp ((interp_guard_evar hD).mp (hg (evarKey svinX0) (by decide)))
    have h1 : Inh I σ (e.evalEvar (nsvCtxG.vars.ev (evarKey svinX1))) :=
      (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mp ((interp_guard_evar hD).mp (hg (evarKey svinX1) (by decide)))
    have hv0 : Inh I σ (e.evalEvar (nsvCtxG.vars.ev (evarKey nsvV0))) :=
      (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mp ((interp_guard_evar hD).mp (hg (evarKey nsvV0) (by decide)))
    have hv1 : Inh I σ (e.evalEvar (nsvCtxG.vars.ev (evarKey nsvV1))) :=
      (interp_inhOf_of (nsv_trSort_exp hσ1 _ _)).mp ((interp_guard_evar hD).mp (hg (evarKey nsvV1) (by decide)))
    rw [interp_equal hD]
    intro b
    show (tr nsvCtxG nsvItem).interpret I e b ↔ (inhOf (trSort nsvCtxG.vars svinR)).interpret I e b
    refine ⟨nsv_imp_inh, fun hb => ?_⟩
    have hb' : Inh I (e.evalEvar (nsvCtxG.vars.ev (.sortVar "R"))) b := (interp_inhOf_of (nsv_trSort_R _ _)).mp hb
    have hr : (tr nsvCtxG svinRead).interpret I e b := by
      rw [kT]; exact hMid e (kR ▸ hR0) (k0 ▸ h0) (k1 ▸ h1) b (kR ▸ hb')
    have := (nsv_item_drop hD hc (nsv_trSort_exp hσ1 _ e) (nsv_trSort_R _ e) hσ hR0 h0 h1 b).mpr hr _ _ hv0 hv1
    have he : (⟨Function.update (Function.update e.evalEvar (nsvCtxG.vars.ev (evarKey nsvV0))
        (e.evalEvar (nsvCtxG.vars.ev (evarKey nsvV0)))) (nsvCtxG.vars.ev (evarKey nsvV1))
        (e.evalEvar (nsvCtxG.vars.ev (evarKey nsvV1))), e.evalSvar⟩ : Valuation M) = e := by
      cases e; simp [nsv_upd_self]
    rw [he] at this; exact this

/-- **The sentence and Γ's item hold in the same models** of definedness, of the definition of
`\ceil` and of the sort constant `SortExp`. -/
theorem nsv_iff [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (hE : I ⊧ᴵ (sortConstantItem ⟨"SortExp", [], false⟩).pat) :
    (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", nsvAxS⟩).pat) ↔ (I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", nsvAxG⟩).pat) := by
  obtain ⟨σ, hσ1, hσ⟩ := sortConst_of hD hE
  exact (nsv_sentence_iff hD hc hσ1 hσ).trans (nsv_item_iff hD hc hσ1 hσ).symm

end Bridge

kore_term kore from "f2-examples/svnonlinear.kompile.kore"
definition_of defn from "f2-examples/svnonlinear.kompile.kore"
user_axioms U from "f2-examples/svnonlinear.kompile.kore" module "E3-SETVAR-NONLINEAR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The axioms of the user module, in text order. -/
noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "E3-SETVAR-NONLINEAR")

theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The attributes of the text agree with `defn` (`attrsAgree`). -/
theorem defs_attrsAgree : attrsAgree kore defn = true := by decide +kernel

/-! ## The function equations -/

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

theorem fnText_index : fnText.map (·.index) = [99, 118, 126, 125, 124, 123, 130, 129, 132, 131, 128, 127, 105, 104, 117, 116, 113, 112, 115, 114, 120, 119, 122, 121, 109, 108, 111, 110, 107, 106] := by
  decide +kernel

kernel_rfl fnText_W : fnText[0]? = some U.ax99

/-! ### The equation over the set variable -/

/-- **Γ's axiom of `f`'s equation is `nsvAxG`**: the clause with two distinct variables (kernel). -/
theorem aW_at : (TiePair.fnAxioms c)[0]? = some nsvAxG := by decide +kernel

/-- Γ's item of it. -/
noncomputable def gW : P := (trAxiom [] [] ⟨0, "kernel", nsvAxG⟩).pat

theorem gW_at : (TiePair.gammaPats c)[0]? = some gW := TiePair.gammaPats_at aW_at

/-- **The text's sentence 99 is `nsvAxS`**, the axiom with the two memberships in the set variable
`@VarS` (kernel), **and so is its translation.** -/
theorem w_ax : U.ax99.ax.sortVars = nsvAxS.sortVars ∧ U.ax99.ax.pattern = nsvAxS.pattern := by decide +kernel
theorem w_text : (trS U.ax99).pat = (trAxiom [] [] ⟨0, "kernel", nsvAxS⟩).pat := by decide +kernel

/-- **The sentence is not Γ's item pattern for pattern.** -/
theorem w_differs : gW ≠ (trS U.ax99).pat := by decide +kernel

/-- **Sentence 99 and Γ's item hold in the same models** of definedness, of the definition of
`\ceil` and of the sort constant `SortExp`. -/
theorem w_iff {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hc : I ⊧ᴵ ceilDefItem.pat) (hE : I ⊧ᴵ (sortConstantItem ⟨"SortExp", [], false⟩).pat) :
    (I ⊧ᴵ (trS U.ax99).pat) ↔ (I ⊧ᴵ gW) := by
  rw [w_text]; exact nsv_iff hD hc hE

/-- The two signature items `w_iff` reads. -/
noncomputable def sigPats : List P := [ceilDefItem.pat, (sortConstantItem ⟨"SortExp", [], false⟩).pat]

/-- **W1**: the sentence, with the definition of `\ceil` and the sort constant `SortExp`, entails
Γ's item. -/
theorem w1 : TiePair.Texts ((trS U.ax99).pat :: sigPats) ⊧ gW :=
  fun {M} _ {I} hI => (w_iff (TiePair.defOK_texts hI)
    (hI _ (Or.inl (by simp [sigPats]))) (hI _ (Or.inl (by simp [sigPats])))).mp
    (hI _ (Or.inl (List.mem_cons_self ..)))

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- **The two signature items are items of Γ** (`ΓSig`; kernel for the sort constant). -/
theorem sig_exp : (sigItems c).any (fun it => decide (it.pat = (sortConstantItem ⟨"SortExp", [], false⟩).pat)) = true := by
  decide +kernel

theorem sig_pats (H : HookParams) : ∀ φ ∈ sigPats, ΓSig (cH H) φ := by
  intro φ hφ
  simp only [sigPats, List.mem_cons, List.mem_nil_iff, or_false] at hφ
  refine Or.inl (Or.inl ?_)
  rw [sigItems_withHooks]
  rcases hφ with rfl | rfl
  · exact ⟨_, sig_ceilDef, rfl⟩
  · obtain ⟨it, hit, h⟩ := List.any_eq_true.mp sig_exp
    exact ⟨it, hit, of_decide_eq_true h⟩

/-- The premise set's equations with Γ's item for sentence 99. -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 0 gW

/-- **Each of Γ's equations but item 0 is the translation of its text sentence** (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for every function equation, sentence 99 among them**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp had
  by_cases hJ : j = 0
  · subst hJ
    rw [fnText_W] at hj; cases hj
    have hg : gW ∈ TiePair.gammaPats (cH H) := by
      rw [TiePair.gammaPats_withHooks]; exact List.mem_of_getElem? gW_at
    obtain ⟨it, hit, hit'⟩ := List.mem_map.mp hg
    have hs : ∀ φ ∈ sigPats, I ⊧ᴵ φ := fun φ hφ =>
      hI _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (sig_pats H φ hφ)))))))
    exact (w_iff (defOK hI) (hs _ (by simp [sigPats])) (hs _ (by simp [sigPats]))).mpr
      (hit' ▸ hI _ (TiePair.mem_Γ_fns (Or.inl ⟨it, hit, rfl⟩)))
  · refine TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (i := j) ?_) hI
    unfold textPats
    rw [List.getElem?_set_ne (Ne.symm hJ), List.getElem?_map, hj]; rfl

/-! ## The constructor sentences -/

noncomputable def consText : List AxiomDecl := U.all.filter fun ad => tieConsB c ad.ax

theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **E for the constructor sentences**: Γ entails each, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.mem_filter.mp had).2) ad.index ad.module hI

/-! ## The account -/

noncomputable def tiedIdx : List Nat := fnText.map (·.index) ++ consText.map (·.index)

/-- **The account**: the function equations and the constructor sentences are sentences of the
user module, each once and none in both classes, with the sizes of the two classes and of the
rest (not tied here). -/
theorem account : tiedIdx.Nodup ∧ tiedIdx.all (fun i => (U.all.map (·.index)).contains i) = true ∧
    (U.all.map (·.index)).Nodup ∧
    (fnText.length, consText.length, U.all.length - tiedIdx.length) = (30, 31, 84) := by decide +kernel

/-! ## The facts the deciders leave -/

/-- `f`, the definition's function, and the three constructors of `Exp`. -/
def f : Sym := 388
def ca : GroundTerm := .ctor 385 []
def cb : GroundTerm := .ctor 386 []
def r : GroundTerm := .ctor 387 []

theorem names : c.symName f = "Lblf" ∧ c.symName 385 = "Lbla" ∧ c.symName 386 = "Lblb" ∧
    c.symName 387 = "Lblr" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem hfn : c.lookupFn f = some fn := rfl
theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem hfnH (H : HookParams) : (cH H).lookupFn f = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
theorem hvsH (H : HookParams) {x y : GroundTerm} (h : c.sortsOf [x, y] = some fn.args) :
    (cH H).sortsOf [x, y] = some fn.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact h

theorem eval_of {x y : GroundTerm} {k : Nat} {v : Option GroundTerm} (hs : c.sortsOf [x, y] = some fn.args)
    (h : Cert.evalFC c k f [x, y] = some v) (H : HookParams) : Eval (cH H) f [x, y] v :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn hs h

def callOrder : List Nat := [388]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H** (C14 closure (a)). -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## The expectations (C7 form (a), from sentences) -/

noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- Every function equation as written. -/
noncomputable def writtenPats : List P := fnText.map (trS · |>.pat)

/-- **The premises of the derivations**: every function equation as written (sentence 99 among
them), Γ's rule items (none: the text has no rule), and the families. -/
noncomputable abbrev PreW (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) writtenPats

/-- A model of `PreW H` is a model of `Pre H`: sentence 99 gives Γ's item (`w_iff`), the two
signature items being of the families (`ΓSig`). -/
theorem pre_of_written {H : HookParams} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP PreW H) : I ⊧ᴵP Pre H := fun φ hφ => by
  rcases hφ with ((hφ | ⟨x, rfl⟩) | hφ) | hφ
  · rcases List.mem_or_eq_of_mem_set hφ with hφ | rfl
    · exact hI _ (Or.inl (Or.inl (Or.inl hφ)))
    · have hs : ∀ ψ ∈ sigPats, I ⊧ᴵ ψ := fun ψ hψ =>
        hI _ (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (sig_pats H ψ hψ))))))
      have hD : DefOK I := defOK_of fun x => hI _ (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩)))
      exact (w_iff hD (hs _ (by simp [sigPats])) (hs _ (by simp [sigPats]))).mp
        (hI _ (Or.inl (Or.inl (Or.inl (by
          unfold writtenPats; exact List.mem_map.mpr ⟨U.ax99, List.mem_of_getElem? fnText_W, rfl⟩)))))
  · exact hI _ (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩)))
  · exact hI _ (Or.inl (Or.inr hφ))
  · exact hI _ (Or.inr hφ)

/-- **`PreW` with the step's closure has a model, for every H**: Γ's model, which satisfies
sentence 99 (`fns_entailed`). -/
theorem preW_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (PreW H ∪ Γstep (cH H)) := by
  obtain ⟨M, hM, I, hI⟩ := consistent H
  have hΓ : I ⊧ᴵP Γ (cH H) := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  refine ⟨M, hM, I, fun φ hφ => ?_⟩
  rcases hφ with (((hφ | ⟨x, rfl⟩) | hφ) | hφ) | hφ
  · unfold writtenPats at hφ
    obtain ⟨ad, had, rfl⟩ := List.mem_map.mp hφ
    exact fns_entailed H ad had hΓ
  · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))))))
  · exact hΓ _ (Or.inl (Or.inr hφ))
  · rcases hφ with (((h1 | h1) | h1) | h1) | h1
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h1))))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1))))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1)))))
    · exact hΓ _ (Or.inl (Or.inl (Or.inl (Or.inr h1))))
    · exact hΓ _ (Or.inr h1)
  · exact hI _ (Or.inr hφ)

/-- What `Pre H` entails, `PreW H` entails. -/
theorem written_cut {H : HookParams} {ψ : P} (h : Pre H ⊧ ψ) : PreW H ⊧ ψ :=
  fun hI => h (pre_of_written hI)

noncomputable abbrev fAt (H : HookParams) (x y : GroundTerm) : P := TiePair.app (cH H) f [x, y]

/-- **`f(a, b) = r`, derived from the sentences as written**, for every H: the two arguments are
distinct values, and sentence 99 states the equation at every pair of elements of `SortExp`. -/
theorem f_a_b (H : HookParams) : PreW H ⊧ (fAt H ca cb ≡ den (cH H) r) :=
  written_cut (TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_of (k := 10) (by decide +kernel) (by decide +kernel) H) (hfnH H)
    (hvsH H (by decide +kernel)))

/-- **`f(a, a) = r`, derived from the sentences as written**, for every H. -/
theorem f_a_a (H : HookParams) : PreW H ⊧ (fAt H ca ca ≡ den (cH H) r) :=
  written_cut (TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_of (k := 10) (by decide +kernel) (by decide +kernel) H) (hfnH H)
    (hvsH H (by decide +kernel)))

end KCore.NoteSetVarIn

#check @KCore.NoteSetVarIn.wf_defn
#check @KCore.NoteSetVarIn.defs_attrsAgree
#check @KCore.NoteSetVarIn.account
#check @KCore.NoteSetVarIn.nsv_evar_in_drop
#check @KCore.NoteSetVarIn.nsv_iff
#check @KCore.NoteSetVarIn.aW_at
#check @KCore.NoteSetVarIn.w_ax
#check @KCore.NoteSetVarIn.w_text
#check @KCore.NoteSetVarIn.w_differs
#check @KCore.NoteSetVarIn.w_iff
#check @KCore.NoteSetVarIn.w1
#check @KCore.NoteSetVarIn.sig_pats
#check @KCore.NoteSetVarIn.shape
#check @KCore.NoteSetVarIn.fns_entailed
#check @KCore.NoteSetVarIn.cons_entailed
#check @KCore.NoteSetVarIn.consistent
#check @KCore.NoteSetVarIn.preW_model
#check @KCore.NoteSetVarIn.f_a_b
#check @KCore.NoteSetVarIn.f_a_a
#print axioms KCore.NoteSetVarIn.wf_defn
#print axioms KCore.NoteSetVarIn.defs_attrsAgree
#print axioms KCore.NoteSetVarIn.account
#print axioms KCore.NoteSetVarIn.nsv_evar_in_drop
#print axioms KCore.NoteSetVarIn.nsv_iff
#print axioms KCore.NoteSetVarIn.aW_at
#print axioms KCore.NoteSetVarIn.w_ax
#print axioms KCore.NoteSetVarIn.w_text
#print axioms KCore.NoteSetVarIn.w_differs
#print axioms KCore.NoteSetVarIn.w_iff
#print axioms KCore.NoteSetVarIn.w1
#print axioms KCore.NoteSetVarIn.sig_pats
#print axioms KCore.NoteSetVarIn.shape
#print axioms KCore.NoteSetVarIn.fns_entailed
#print axioms KCore.NoteSetVarIn.cons_entailed
#print axioms KCore.NoteSetVarIn.consistent
#print axioms KCore.NoteSetVarIn.preW_model
#print axioms KCore.NoteSetVarIn.f_a_b
#print axioms KCore.NoteSetVarIn.f_a_a
