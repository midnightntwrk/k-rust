/-
  The value `first(and(x, g)) = x` of `f2-examples/e8-llvm-e2-open-mixed-clause.kompile.kore`
  (fixture e8-llvm-e2-open-mixed-clause: `A ::= x | y`, `B ::= A & A`, `&` declared `functional`
  and no constructor, `rule first(X & _) => X`), from two sentences of the text as written. Run
  from the package root: `lake env lean -j1 test/OpenFirstAndText.lean`.

  The premises (`PreFA H`): sentence 56, `and`'s functional sentence
  (`∃ Val:B. Val = and(K0, K1)`), sentence 100, the equation of `first` with the argument's
  membership (`X0 ∈ and(X, _Gen0) → first(X0) = X`), definedness, and the signature `ΓSig`, of
  which the proof reads that A and B each denote one sort, the item of `⌈_⌉{s,s'}`, and the arities
  of `and` (A × A to B) and `first` (B to A). Neither sentence is read through Γ; no item of Γ
  outside `ΓSig` is a premise, in particular not `and`'s graph at H, which `ΓDomains` holds.
  `ΓSig (c.withHooks H)` names H, and nothing the proof reads of it depends on H.

  `first_and_x`: for all elements x, g of A, `first(and(x, g))` is x. Sentence 56 at
  `K0 := x, K1 := g` makes `and(x, g)` one element w of B (`and_one`, with `and`'s arity);
  sentence 100 at `X0 := w, X := x, _Gen0 := g`, whose premise `w ∈ and(x, g)` then holds, gives
  that `first(w)` is x (`first_at`, with `first`'s arity).

  The equation is stated from the two sentences, not over `Γc (c.withHooks H)`: sentence 56 is no
  item of Γ (owed as `OpenTotal`).

  `pre_model`: `PreFA H` has a model, for every H, so `first_and_x` is not vacuous. A model of Γ at
  an H that gives `and` a value at every pair of values of A is one (`gamma_pre`), and `Γc` with the
  step's closure has a model at `lawHooks c H` (`NonVacFA.consistentFA`); `PreFA H` reads nothing of
  H (`preFA_hooks`). `pre_model_firstDet`: at an H where `and` determines its first argument and is
  total at values, every model of `Γc (c.withHooks H)` is one.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.OpenFirstAndText

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e8-llvm-e2-open-mixed-clause.kompile.kore"
definition_of defn from "f2-examples/e8-llvm-e2-open-mixed-clause.kompile.kore"
user_axioms U from "f2-examples/e8-llvm-e2-open-mixed-clause.kompile.kore" module "E2-OPEN-MIXED-CLAUSE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The sorts A and B, `and` and `first`, as the reader numbers them. -/
def aSrt : Srt := 33
def bSrt : Srt := 32
def andS : Sym := 389
def firstS : Sym := 388

theorem names : c.sortName aSrt = "A" ∧ c.sortName bSrt = "B" ∧ c.symName andS = "Lbland" ∧
    c.symName firstS = "Lblfirst" := by decide +kernel

/-- The patterns the translation writes for the sorts and the two symbols. -/
def sA : P := sym (.sort "SortA")
def sB : P := sym (.sort "SortB")
def andP : P := sym (.symbol "Lbland")
def firstP : P := sym (.symbol "Lblfirst")
def vP (n : Nat) : P := .evar ⟨n⟩

/-! ### The two sentences as the translation writes them -/

/-- Sentence 56: `R` is variable 1, `Val` 2, `K0` 3, `K1` 4; the guards are R's, K0's, K1's. -/
def pat56 : P :=
  conjList [sortGuard ⟨1⟩, (⟨3⟩ : EVar) ∈∈ inhOf sA, (⟨4⟩ : EVar) ∈∈ inhOf sA] ⇒
    (sExists ⟨2⟩ sB (sEquals sB (vP 1) (vP 2) (andP ⬝ vP 3 ⬝ vP 4)) ≡ inhOf (vP 1))

/-- Sentence 100: `R` is variable 1, `X0` 2, `VarX` 3, `_Gen0` 4. -/
def pat100 : P :=
  conjList [sortGuard ⟨1⟩, (⟨2⟩ : EVar) ∈∈ inhOf sB, (⟨3⟩ : EVar) ∈∈ inhOf sA, (⟨4⟩ : EVar) ∈∈ inhOf sA] ⇒
    (sImp (vP 1) (sAnd (sTop (vP 1)) (sAnd (sIn sB (vP 1) (vP 2) (andP ⬝ vP 3 ⬝ vP 4)) (sTop (vP 1))))
      (sEquals sA (vP 1) (firstP ⬝ vP 2) (sAnd (vP 3) (sTop sA))) ≡ inhOf (vP 1))

theorem s56_pat : (trS U.ax56).pat = pat56 := by decide +kernel
theorem s100_pat : (trS U.ax100).pat = pat100 := by decide +kernel

/-! ### The premises -/

/-- Sentences 56 and 100 as written, definedness, and the signature. -/
def PreFA (H : HookParams) : Premises KoreAML.Sym :=
  TiePair.Texts [(trS U.ax56).pat, (trS U.ax100).pat] ∪ ΓSig (cH H)

/-- The arity items of `and` and `first`. -/
def andSig : CtorSig := ⟨andS, [aSrt, aSrt], bSrt⟩
def firstSig : CtorSig := ⟨firstS, [bSrt], aSrt⟩

theorem andSig_kernel (H : HookParams) : andSig ∈ kernelSyms (cH H) :=
  (by decide +kernel : andSig ∈ kernelSyms c)
theorem firstSig_kernel (H : HookParams) : firstSig ∈ kernelSyms (cH H) :=
  (by decide +kernel : firstSig ∈ kernelSyms c)

theorem and_arity_c : (symArityItem c andSig).pat = (andP ⬝ inhOf sA ⬝ inhOf sA ⊆⊆ inhOf sB) := by
  decide +kernel
theorem first_arity_c : (symArityItem c firstSig).pat = (firstP ⬝ inhOf sB ⊆⊆ inhOf sA) := by
  decide +kernel
/-- The arity item of a symbol does not read the hook interpretation. -/
theorem symArityItem_withHooksFA (c : Semantics) (H : HookParams) (k : CtorSig) :
    symArityItem (c.withHooks H) k = symArityItem c k := rfl

theorem and_arity (H : HookParams) : (symArityItem (cH H) andSig).pat = (andP ⬝ inhOf sA ⬝ inhOf sA ⊆⊆ inhOf sB) := by
  rw [symArityItem_withHooksFA]; exact and_arity_c
theorem first_arity (H : HookParams) : (symArityItem (cH H) firstSig).pat = (firstP ⬝ inhOf sB ⊆⊆ inhOf sA) := by
  rw [symArityItem_withHooksFA]; exact first_arity_c

theorem a_numbered (H : HookParams) : aSrt < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : aSrt < nRegSorts + c.sortNames.length)
theorem b_numbered (H : HookParams) : bSrt < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : bSrt < nRegSorts + c.sortNames.length)

/-! ### Reading the premises in a model -/

section model
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- An element of `f(a)` and of `f(a, b)`. -/
def App1F (I : Interpretation KoreAML.Sym M) (f : P) (a m : M) : Prop :=
  ∃ s, f.interpret I ⟨fun _ => a, fun _ _ => False⟩ s ∧ I.evalApp s a m
def App2F (I : Interpretation KoreAML.Sym M) (f : P) (a b m : M) : Prop :=
  ∃ s, App1F I f a s ∧ I.evalApp s b m

theorem sym_closed (σ : KoreAML.Sym) (e e' : Valuation M) (m : M) :
    (sym σ).interpret I e m ↔ (sym σ).interpret I e' m := (Closed.sym σ).interp e e' m

theorem interp_app1F (σ : KoreAML.Sym) {φ : P} {e : Valuation M} {a : M} (hφ : ∀ b, φ.interpret I e b ↔ b = a)
    (m : M) : (sym σ ⬝ φ).interpret I e m ↔ App1F I (sym σ) a m := by
  unfold App1F
  rw [interp_app]
  constructor
  · rintro ⟨s, z, hs, hz, hm⟩
    rw [(hφ z).mp hz] at hm
    exact ⟨s, (sym_closed σ e _ s).mp hs, hm⟩
  · rintro ⟨s, hs, hm⟩
    exact ⟨s, a, (sym_closed σ _ e s).mp hs, (hφ a).mpr rfl, hm⟩

theorem interp_app2F (σ : KoreAML.Sym) {φ ψ : P} {e : Valuation M} {a b : M}
    (hφ : ∀ z, φ.interpret I e z ↔ z = a) (hψ : ∀ z, ψ.interpret I e z ↔ z = b) (m : M) :
    (sym σ ⬝ φ ⬝ ψ).interpret I e m ↔ App2F I (sym σ) a b m := by
  unfold App2F
  rw [interp_app]
  constructor
  · rintro ⟨s, z, hs, hz, hm⟩
    rw [(hψ z).mp hz] at hm
    exact ⟨s, (interp_app1F σ hφ s).mp hs, hm⟩
  · rintro ⟨s, hs, hm⟩
    exact ⟨s, b, (interp_app1F σ hφ s).mpr hs, (hψ b).mpr rfl, hm⟩

variable [Inhabited M]

/-- What a model of `PreFA H` gives the proof: definedness, the item of `⌈_⌉{s,s'}`, A and B each
one sort, the two sentences, and the two arities. -/
theorem facts (H : HookParams) (hI : I ⊧ᴵP PreFA H) :
    DefOK I ∧ (I ⊧ᴵ ceilDefItem.pat) ∧
    (∃ σA, (∀ z, I.evalSymb (.sort "SortA") z ↔ z = σA) ∧ IsSort I σA) ∧
    (∃ σB, (∀ z, I.evalSymb (.sort "SortB") z ↔ z = σB) ∧ IsSort I σB) ∧
    (I ⊧ᴵ pat56) ∧ (I ⊧ᴵ pat100) ∧
    (I ⊧ᴵ (andP ⬝ inhOf sA ⬝ inhOf sA ⊆⊆ inhOf sB)) ∧ (I ⊧ᴵ (firstP ⬝ inhOf sB ⊆⊆ inhOf sA)) := by
  have hD : DefOK I := TiePair.defOK_texts fun φ hφ => hI φ (Or.inl hφ)
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => hI φ (Or.inr hφ)
  have hA := sortConst_of hD (hSig _ (Or.inl (Or.inl ⟨_, sig_sortConst (a_numbered H), rfl⟩)))
  have hB := sortConst_of hD (hSig _ (Or.inl (Or.inl ⟨_, sig_sortConst (b_numbered H), rfl⟩)))
  have ha := hSig _ (Or.inl (Or.inl ⟨_, sig_arity (andSig_kernel H), rfl⟩))
  have hf := hSig _ (Or.inl (Or.inl ⟨_, sig_arity (firstSig_kernel H), rfl⟩))
  rw [and_arity] at ha
  rw [first_arity] at hf
  have h56 : I ⊧ᴵ (trS U.ax56).pat := hI _ (Or.inl (Or.inl (.head _)))
  have h100 : I ⊧ᴵ (trS U.ax100).pat := hI _ (Or.inl (Or.inl (.tail _ (.head _))))
  rw [s56_pat] at h56
  rw [s100_pat] at h100
  exact ⟨hD, hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩)), hA, hB, h56, h100, ha, hf⟩

variable (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {σA σB : M}
  (hA : ∀ z, I.evalSymb (.sort "SortA") z ↔ z = σA) (hσA : IsSort I σA)
  (hB : ∀ z, I.evalSymb (.sort "SortB") z ↔ z = σB) (hσB : IsSort I σB)
include hD hc hA hσA hB hσB

/-- The valuation of the sentences' variables: 1 (R) `r`, 2 `w`, 3 `a`, every other `g`. -/
def valFA (r w a g : M) : Valuation M :=
  ⟨fun x => match x with | ⟨1⟩ => r | ⟨2⟩ => w | ⟨3⟩ => a | _ => g, fun _ _ => False⟩

omit [Inhabited M] hD hc hσA hB hσB in
theorem sA_at (e : Valuation M) (z : M) : sA.interpret I e z ↔ z = σA := hA z
omit [Inhabited M] hD hc hσA hA hσB in
theorem sB_at (e : Valuation M) (z : M) : sB.interpret I e z ↔ z = σB := hB z

/-- **Sentence 56 at elements a, g of A**: `and(a, g)` is one element w of B. -/
theorem and_one (h56 : I ⊧ᴵ pat56) (hAr : I ⊧ᴵ (andP ⬝ inhOf sA ⬝ inhOf sA ⊆⊆ inhOf sB)) {a g : M}
    (ha : Inh I σA a) (hg : Inh I σA g) :
    ∃ w, Inh I σB w ∧ ∀ m, App2F I andP a g m ↔ m = w := by
  have h1 := h56 (valFA σA a a g) a
  unfold pat56 conjList conjList conjList at h1
  rw [interpret_impl] at h1
  have hinA : ∀ (e : Valuation M) z, (inhOf sA).interpret I e z ↔ Inh I σA z :=
    fun e z => interp_inhOf_of (sA_at hA e)
  have hinB : ∀ (e : Valuation M) z, (inhOf sB).interpret I e z ↔ Inh I σB z :=
    fun e z => interp_inhOf_of (sB_at hB e)
  have h2 := h1 (by
    rw [interpret_conj, interpret_conj]
    refine ⟨?_, ?_, ?_⟩
    · unfold sortGuard; rw [interp_member hD, interp_sortsDomain]; exact hσA
    · rw [interp_member hD, hinA]; exact ha
    · rw [interp_member hD, hinA]; exact hg)
  rw [interp_equal hD] at h2
  have h3 := (h2 a).mpr (by
    rw [interp_inhOf_of (σ := σA) (fun z => by unfold vP; rw [interp_evar]; rfl)]; exact ha)
  rw [interp_sExists] at h3
  obtain ⟨w, hw, heq⟩ := h3
  rw [interp_member hD, hinB] at hw
  simp only [Function.update_same] at hw
  let e2 : Valuation M := ⟨Function.update (valFA σA a a g).evalEvar ⟨2⟩ w, (valFA σA a a g).evalSvar⟩
  have e21 : e2.evalEvar ⟨1⟩ = σA := by simp [e2, Function.update, valFA]
  have e22 : e2.evalEvar ⟨2⟩ = w := by simp [e2]
  have e23 : e2.evalEvar ⟨3⟩ = a := by simp [e2, Function.update, valFA]
  have e24 : e2.evalEvar ⟨4⟩ = g := by simp [e2, Function.update, valFA]
  have hv : ∀ (n : Nat) (z : M), (vP n).interpret I e2 z ↔ z = e2.evalEvar ⟨n⟩ := fun n z => interp_evar
  change (sEquals sB (vP 1) (vP 2) (andP ⬝ vP 3 ⬝ vP 4)).interpret I e2 a at heq
  rw [interp_sEquals hD hc (sB_at hB e2) (fun z => by rw [hv, e21]) hσB hσA] at heq
  have happ : ∀ m, (andP ⬝ vP 3 ⬝ vP 4).interpret I e2 m ↔ App2F I andP a g m :=
    interp_app2F _ (fun z => by rw [hv, e23]) (fun z => by rw [hv, e24])
  refine ⟨w, hw, fun m => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · have hmB : Inh I σB m := by
      have := hAr e2 m
      rw [interp_included hD] at this
      refine (hinB e2 m).mp (this m ?_)
      rw [interp_app]
      obtain ⟨s, ⟨s0, hs0, hs0a⟩, hsm⟩ := hm
      exact ⟨s, g, interp_app.mpr ⟨s0, a, (sym_closed _ _ e2 s0).mp hs0, (hinA e2 a).mpr ha, hs0a⟩,
        (hinA e2 g).mpr hg, hsm⟩
    have := (heq.2 m hmB).mpr ((happ m).mpr hm)
    rwa [hv, e22] at this
  · rw [hm]
    exact (happ w).mp ((heq.2 w hw).mp ((hv 2 w).mpr e22.symm))

/-- **Sentence 100 at an element w of `and(a, g)`**: `first(w)` is a. -/
theorem first_at (h100 : I ⊧ᴵ pat100) (hFr : I ⊧ᴵ (firstP ⬝ inhOf sB ⊆⊆ inhOf sA)) {a g w : M}
    (ha : Inh I σA a) (hg : Inh I σA g) (hw : Inh I σB w) (haw : App2F I andP a g w) :
    ∀ m, App1F I firstP w m ↔ m = a := by
  let e : Valuation M := valFA σA w a g
  have hv : ∀ (n : Nat) (z : M), (vP n).interpret I e z ↔ z = e.evalEvar ⟨n⟩ := fun n z => interp_evar
  have e1 : e.evalEvar ⟨1⟩ = σA := rfl
  have e2 : e.evalEvar ⟨2⟩ = w := rfl
  have e3 : e.evalEvar ⟨3⟩ = a := rfl
  have e4 : e.evalEvar ⟨4⟩ = g := rfl
  have hinA : ∀ (e : Valuation M) z, (inhOf sA).interpret I e z ↔ Inh I σA z :=
    fun e z => interp_inhOf_of (sA_at hA e)
  have hinB : ∀ (e : Valuation M) z, (inhOf sB).interpret I e z ↔ Inh I σB z :=
    fun e z => interp_inhOf_of (sB_at hB e)
  have hR : ∀ z, (vP 1).interpret I e z ↔ z = σA := fun z => by rw [hv, e1]
  have hinR : ∀ z, (inhOf (vP 1)).interpret I e z ↔ Inh I σA z := fun z => interp_inhOf_of hR
  have h1 := h100 e a
  unfold pat100 conjList conjList conjList conjList at h1
  rw [interpret_impl] at h1
  have h2 := h1 (by
    rw [interpret_conj, interpret_conj, interpret_conj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold sortGuard; rw [interp_member hD, interp_sortsDomain]; exact hσA
    · rw [interp_member hD, hinB]; exact hw
    · rw [interp_member hD, hinA]; exact ha
    · rw [interp_member hD, hinA]; exact hg)
  rw [interp_equal hD] at h2
  have h3 := (h2 a).mpr ((hinR a).mpr ha)
  have hfree : (vP 1).isFreeEvar topVar = false := by decide
  have hfreeA : sA.isFreeEvar topVar = false := by decide
  rw [interp_sImp] at h3
  have hprem := h3.2 (by
    rw [interp_sAnd, interp_sAnd, interp_sTop hD hfree, hinR]
    refine ⟨ha, ?_, ha⟩
    rw [interp_sIn hD hc (sB_at hB e) hR hσB hσA (fun z hz => by rw [hv, e2] at hz; rw [hz]; exact hw)]
    exact ⟨⟨w, (hv 2 w).mpr e2.symm, (interp_app2F _ (fun z => by rw [hv, e3]) (fun z => by rw [hv, e4]) w).mpr haw⟩, ha⟩)
  rw [interp_sEquals hD hc (sA_at hA e) hR hσA hσA] at hprem
  have happ : ∀ m, (firstP ⬝ vP 2).interpret I e m ↔ App1F I firstP w m :=
    interp_app1F _ (fun z => by rw [hv, e2])
  intro m
  constructor
  · intro hm
    have hmA : Inh I σA m := by
      have := hFr e m
      rw [interp_included hD] at this
      refine (hinA e m).mp (this m ?_)
      obtain ⟨s, hs, hsm⟩ := hm
      exact interp_app.mpr ⟨s, w, (sym_closed _ _ e s).mp hs, (hinB e w).mpr hw, hsm⟩
    have := (hprem.2 m hmA).mp ((happ m).mpr hm)
    rw [interp_sAnd, hv, e3] at this
    exact this.1
  · intro hm
    rw [hm]
    refine (happ a).mp ((hprem.2 a ha).mpr ?_)
    rw [interp_sAnd, hv, e3, interp_sTop hD hfreeA, hinA]
    exact ⟨rfl, ha⟩

end model

/-! ### The value -/

def xE : EVar := ⟨1⟩
def gE : EVar := ⟨2⟩

/-- **`first(and(x, g)) = x` from sentences 56 and 100**, for all elements x, g of A, for every H:
in every model of `PreFA H` (the two sentences as written, definedness and the signature). -/
theorem first_and_x (H : HookParams) :
    PreFA H ⊧ ((xE ∈∈ inhOf sA) ⇒ ((gE ∈∈ inhOf sA) ⇒
      (firstP ⬝ (andP ⬝ .evar xE ⬝ .evar gE) ≡ .evar xE))) := by
  intro M _ I hI e m0
  obtain ⟨hD, hc, ⟨σA, hA, hσA⟩, ⟨σB, hB, hσB⟩, h56, h100, hAr, hFr⟩ := facts H hI
  have hinA : ∀ z, (inhOf sA).interpret I e z ↔ Inh I σA z := fun z => interp_inhOf_of (sA_at hA e)
  rw [interpret_impl, interp_member hD, hinA]
  intro ha
  rw [interpret_impl, interp_member hD, hinA]
  intro hg
  obtain ⟨w, hw, hand⟩ := and_one hD hc hA hσA hB hσB h56 hAr ha hg
  have hfirst := first_at hD hc hA hσA hB hσB h100 hFr ha hg hw ((hand w).mpr rfl)
  rw [interp_equal hD]
  intro z
  rw [interp_evar, interp_app]
  constructor
  · rintro ⟨s, d, hs, hd, hz⟩
    have hdw : d = w := (hand d).mp ((interp_app2F _ (fun _ => interp_evar) (fun _ => interp_evar) d).mp hd)
    subst hdw
    exact (hfirst z).mp ⟨s, (sym_closed _ _ _ s).mp hs, hz⟩
  · intro hz
    obtain ⟨s, hs, hsz⟩ := (hfirst z).mpr hz
    exact ⟨s, w, (sym_closed _ _ e s).mp hs,
      (interp_app2F _ (fun _ => interp_evar) (fun _ => interp_evar) w).mpr ((hand w).mpr rfl), hsz⟩


/-! ### The premises have a model

`PreFA H` reads of H nothing (`preFA_hooks`). Every model of `Γ (cH H)` where H gives `and` a value
at every pair of values of A (`OpenTotal`) is a model of `PreFA H` (`gamma_pre`): `ΓSig` is part of
Γ; Γ entails sentence 100 (`s100_entailedFA`, Γ's item 0 read through the cut); and sentence 56
holds there because every element of A is the element of x or of y (A's no-junk sentence, a part
of Γ) and Γ holds the graph of `and` at values, whose value is one element of B. `Γc` with the
step's closure has a model at every H where `and` determines its first argument (`consistentFA`,
the clause of `first` coherent with itself), and `lawHooks c H` gives `and` its free applications,
which are total and determine their arguments. So `PreFA H` has a model for every H (`pre_model`),
a model of `Γc (cH (lawHooks c H))`; and at an H with `FirstDet H` and `OpenTotal (cH H)`, every
model of `Γc (cH H)` is one (`pre_model_firstDet`). -/

/-- **`PreFA H` reads nothing of H.** -/
theorem preFA_hooks (H H' : HookParams) : PreFA H = PreFA H' := rfl

namespace NonVacFA

/-! #### `Γc` has a model where `and` determines its first argument -/

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem params_raw : (c.params.filter (·.raw)).map (fun k => (k.sig.name, k.sig.args, k.sig.result, k.assoc, k.idem)) =
    [(andS, [aSrt, aSrt], bSrt, false, false)] := by decide +kernel

/-- `first(V) => X` with the predicate `V ∈ and(X, G)`; X and G of A, V of B. -/
def clFirst : Clause :=
  { vars := [aSrt, aSrt, bSrt], pats := [.var 2], req := none, rhs := .var 0, ens := none,
    pre := .mem bSrt (.var 2) (.app andS [.var 0, .var 1]) }
def fFirst : Fn := { label := firstS, args := [bSrt], result := aSrt, clauses := [clFirst] }

theorem first_text : c.fns = [fFirst] := by rfl
theorem first_lookupH (H : HookParams) : (cH H).lookupFn firstS = some fFirst := by rfl

/-- `and` as the definition's parameter: open, with no law. -/
def andK : ParamSig := { sig := ⟨andS, [aSrt, aSrt], bSrt⟩, raw := true }

theorem andK_mem : andK ∈ c.params := by decide +kernel
theorem and_syms : c.isCtor andS = false ∧ isHook andS = false ∧ c.isParam andS = true := by decide +kernel

theorem andK_shape (H : HookParams) : LawShape (cH H) andK :=
  Semantics.lawShape_core (coreOKH H) andK andK_mem rfl

/-- The value of `and` at H: what H gives, the application itself where H gives nothing, kept
where it is a value of B. -/
theorem and_paramVal (H : HookParams) {vs : List GroundTerm} {v : GroundTerm} :
    (cH H).paramVal andS vs = some v ↔ v = (H.app andS vs).getD (.ctor andS vs) ∧ (cH H).sortOf v = some bSrt :=
  paramVal_raw_sorted (c := cH H) (f := andS) (k := andK) (andK_shape H).1 rfl (andK_shape H).2.2.1

theorem first_srt1 {C : Semantics} {v : GroundTerm} {s : Srt} (h : C.sortOf v = some s) :
    C.sortsOf [v] = some [s] :=
  sortsOf_cons.mpr ⟨s, [], h, sortsOf_nil, rfl⟩

theorem first_srt2 {C : Semantics} {v w : GroundTerm} {s t : Srt} (h1 : C.sortOf v = some s)
    (h2 : C.sortOf w = some t) : C.sortsOf [v, w] = some [s, t] :=
  sortsOf_cons.mpr ⟨s, [t], h1, first_srt1 h2, rfl⟩

/-- The values H gives `and` at values of A determine the first argument. -/
def FirstDet (H : HookParams) : Prop :=
  ∀ a g a' g' v : GroundTerm, (cH H).sortOf a = some aSrt → (cH H).sortOf g = some aSrt →
    (cH H).sortOf a' = some aSrt → (cH H).sortOf g' = some aSrt →
    (cH H).paramVal andS [a, g] = some v → (cH H).paramVal andS [a', g'] = some v → a = a'

theorem first_owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel
theorem first_owed_clauses : c.owedClauses = ([] : List (Nat × Nat)) := by decide +kernel

theorem first_noWit (H : HookParams) :
    ∀ fn ∈ (cH H).fns, ∀ cl ∈ fn.clauses, cl.needsWitness (cH H) = true → cl.CondDecided (cH H) :=
  openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, first_owed_clauses]; intro p hp; cases hp)

theorem first_noExs : c.FnsNoExs := Semantics.fnsNoExs_of_all (by decide +kernel)
theorem first_noExsH (H : HookParams) : (cH H).FnsNoExs := (Semantics.fnsNoExs_withHooks _ _).mpr first_noExs

theorem holds_mem_inv {C : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {bb : Bool}
    (h : Holds C n σ (.mem s t u) bb) :
    ∃ r r', EvalTerm C σ t r ∧ EvalTerm C σ u r' ∧ bb = (r.isSome && sameResult r r') := by
  generalize hc : Cond.mem s t u = p at h
  cases h with
  | mem h h' => cases hc; exact ⟨_, _, h, h', rfl⟩
  | _ => cases hc

/-- Where the clause of `first` applies under σ at `vs`: `vs` is one value, the value of `and` at
σ's X and G, which are values of A. -/
theorem first_applies (H : HookParams) {σ : Subst} {vs : List GroundTerm} (h : clFirst.AppliesAt (cH H) σ vs) :
    ∃ a g v, σ.lookup 0 = some a ∧ (cH H).sortOf a = some aSrt ∧ (cH H).sortOf g = some aSrt ∧
      (cH H).paramVal andS [a, g] = some v ∧ vs = [v] := by
  obtain ⟨hws, hpat, -, hpre⟩ := h
  have hw : (cH H).WellSorted clFirst.vars σ := (wellSortedAt_univ (cl := clFirst) rfl).mp hws
  obtain ⟨a, ea, hsa⟩ := hw 0 aSrt (by simp [clFirst])
  obtain ⟨g, eg, hsg⟩ := hw 1 aSrt (by simp [clFirst])
  obtain ⟨w, vs', rfl, hpv, hnil⟩ := PatVals.cons_inv hpat
  cases hnil
  have ew := PatVal.var_inv hpv
  obtain ⟨r, r', hr, hr', hb⟩ := holds_mem_inv hpre
  have er := EvalTerm.var_inv hr
  obtain ⟨rs, hrs, err⟩ := EvalTerm.param_inv (c := cH H) and_syms.1 and_syms.2.1 and_syms.2.2 hr'
  obtain ⟨r0, rs0, rfl, h0, hrs0⟩ := EvalTerms.cons_inv hrs
  obtain ⟨r1, rs1, rfl, h1, hrs1⟩ := EvalTerms.cons_inv hrs0
  cases EvalTerms.nil_inv hrs1
  have e0 := EvalTerm.var_inv h0
  have e1 := EvalTerm.var_inv h1
  subst er; subst e0; subst e1; subst err
  rw [ew, ea, eg] at hb
  refine ⟨a, g, w, ea, hsa, hsg, ?_, rfl⟩
  have hb' : sameResult (some w) ((cH H).paramVal andS [a, g]) = true := by simpa [allSome] using hb.symm
  cases hq : (cH H).paramVal andS [a, g] with
  | none => rw [hq] at hb'; simp [sameResult] at hb'
  | some w' =>
    rw [hq] at hb'
    simp only [sameResult, beq_iff_eq] at hb'
    rw [cmp_eq_iff.mp hb']

/-- Under `FirstDet H` the clause of `first` is coherent with itself. -/
theorem first_coherent (H : HookParams) (hH : FirstDet H) : Coherent (cH H) clFirst clFirst := by
  intro vs σ σ' h1 h2 _ _ _ _ _
  refine .inl ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht => by cases ht⟩
  have hi0 : i = 0 := by simpa [clFirst, varOccs] using hi
  subst hi0
  obtain ⟨a, g, v, e0, hsa, hsg, hpv, hvs⟩ := first_applies H h1
  obtain ⟨a', g', v', e0', hsa', hsg', hpv', hvs'⟩ := first_applies H h2
  subst hvs
  have hv : v' = v := by simpa using hvs'.symm
  subst hv
  rw [e0, e0', hH a g a' g' _ hsa hsg hsa' hsg' hpv hpv']

def firstOrder : List Sym := [firstS]

theorem first_term_named : c.preRankObligationsFP firstOrder = [] := by decide +kernel
theorem first_agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem first_match_named : c.matchObligationsL = [(firstS, 0)] := by decide +kernel
theorem first_fnOvl : c.fnOvlSyms = [] := by decide +kernel
theorem first_rightHeld (H : HookParams) : (cH H).RightHeld :=
  Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H

theorem first_matchObl (H : HookParams) (hH : FirstDet H) : Det.MatchObligationsL (cH H) := by
  intro p hp fn hfn cl hcl
  rw [Det.Semantics.matchObligationsL_withHooks, first_match_named, List.mem_singleton] at hp
  subst hp
  rw [first_lookupH] at hfn
  cases hfn
  simp only [fFirst, List.getElem?_cons_zero, Option.some.injEq] at hcl
  subst hcl
  exact (matchIndependent_iff_noExs rfl).mpr (first_coherent H hH)

theorem first_openLaws (H : HookParams) : OpenLaws (cH H) := fun k hk hr => by
  have hk' : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩
  have hm := List.mem_map_of_mem (f := fun k : ParamSig => (k.sig.name, k.sig.args, k.sig.result, k.assoc, k.idem)) hk'
  rw [params_raw, List.mem_singleton] at hm
  simp only [Prod.mk.injEq] at hm
  exact ⟨fun h => (by rw [hm.2.2.2.1] at h; cases h), fun h => (by rw [hm.2.2.2.2] at h; cases h)⟩

theorem first_fnHyp (H : HookParams) (hH : FirstDet H) : FnHyp (cH H) :=
  fnHyp_of_decidedPre (coreOKH H) (first_rightHeld H) (show (cH H).fnOvlSyms = [] from first_fnOvl) firstOrder
    (fun g hg => by rw [Semantics.preRankObligationsFP_withHooks, first_term_named] at hg; cases hg)
    (fun fn hfn ht => by
      have hfn' : fn ∈ [fFirst] := first_text ▸ hfn
      rw [List.mem_singleton] at hfn'
      subst hfn'
      exact absurd ht (by decide))
    (fun f hf => by rw [Det.Semantics.agreeObligationsI_withHooks, first_agree_named] at hf; cases hf)
    (first_matchObl H hH)
    ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, first_owed_rules]; intro i hi; cases hi),
      first_noWit H⟩
    (first_openLaws H) (hnoEx := first_noExsH H)

/-- **`Γc` with the step's closure has a model at every H where `and` determines its first
argument.** -/
theorem consistentFA (H : HookParams) (hH : FirstDet H) : Consistent (cH H) :=
  consistent_of_fnHyp _ (coreOKH H) (first_fnHyp H hH)

theorem lawHooks_and (H : HookParams) (vs : List GroundTerm) :
    (lawHooks c H).app andS vs = some (.ctor andS vs) :=
  (lawHooks_app_self (c := c) (H := H) (k := andK) (Semantics.lawShape_core coreOK andK andK_mem rfl) vs).trans
    (congrArg some (lawApp_plain (k := andK) rfl rfl vs))

/-- `lawHooks c H` makes `and` determine its arguments, for every H. -/
theorem firstDet_lawHooks (H : HookParams) : FirstDet (lawHooks c H) := by
  intro a g a' g' v _ _ _ _ hp hp'
  have e1 := ((and_paramVal (lawHooks c H)).mp hp).1
  have e2 := ((and_paramVal (lawHooks c H)).mp hp').1
  rw [lawHooks_and, Option.getD_some] at e1 e2
  exact (List.cons.inj (GroundTerm.ctor.inj (e1.symm.trans e2)).2).1

/-! #### Γ entails sentence 100 -/

/-- A model of Γ satisfies each of Γ's equations. -/
theorem fnItem_sat {c : Semantics} {H : HookParams} {M : Type} {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (c.withHooks H)) {j : Nat} {a : Kore.Axiom} (ha : (TiePair.fnAxioms c)[j]? = some a) :
    I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat := by
  have hg := TiePair.gammaPats_at ha
  obtain ⟨it, hit, he⟩ : ∃ it ∈ fnItems c, it.pat = (trAxiom [] [] ⟨0, "kernel", a⟩).pat := by
    unfold TiePair.gammaPats at hg
    rw [List.getElem?_map] at hg
    cases h : (fnItems c)[j]? with
    | none => rw [h] at hg; cases hg
    | some it => rw [h] at hg; exact ⟨it, List.mem_of_getElem? h, Option.some.inj hg⟩
  rw [← he]
  exact hI _ (TiePair.mem_Γ_fns (Or.inl ⟨it, by rw [TiePair.fnItems_withHooks]; exact hit, rfl⟩))

/-- Γ's axiom of item 0, the equation `first(X0) = X` under `X0 ∈ V` and `V ∈ and(X, _Gen0)`. -/
noncomputable def ax0 : Kore.Axiom := ((TiePair.fnAxioms c)[0]?).getD ⟨[], .top KoreAML.R, []⟩
theorem ax0_at : (TiePair.fnAxioms c)[0]? = some ax0 := by decide +kernel

noncomputable def pt : TieEqArgCut.Parts := ((TieEqArgCut.partsOf [1, 0] [] ax0)).getD
  ⟨KoreAML.R, .top KoreAML.R, KoreAML.R, [], KoreAML.R, KoreAML.R, ⟨⟨⟨""⟩⟩, KoreAML.R⟩, .hole, KoreAML.R,
    ⟨⟨⟨""⟩⟩, KoreAML.R⟩, .top KoreAML.R⟩
kernel_rfl parts0 : TieEqArgCut.partsOf [1, 0] [] ax0 = some pt

noncomputable def text0 : P := TieEqArgCut.textItemOf ax0 pt
theorem sub0 : TieEqArgCut.subOK ax0 pt = true := by decide +kernel
theorem fresh0 : TieEqArgCut.freshOK ax0 pt = true := by decide +kernel
theorem top0 : TieEqArgCut.topOK pt = true := by decide +kernel
theorem same0 : TieAlpha.acEqB text0 (trS U.ax100).pat = true := by decide +kernel
theorem sortB_tr : trSort (tableOf ax0.sortVars ax0.pattern) pt.S = sym (.sort "SortB") := by decide +kernel

/-- **Γ entails sentence 100**, for every H. -/
theorem s100_entailedFA (H : HookParams) : Γ (cH H) ⊧ (trS U.ax100).pat := by
  intro M _ I hI
  have hD := defOK hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σB, hσB1, hσB2⟩ := TieRhs.sortSing_sig hD hSig (b_numbered H)
  rw [show (cH H).sortName bSrt = "B" from names.2.1] at hσB1
  have hB : ∀ (e : Valuation M) a, (trSort (tableOf ax0.sortVars ax0.pattern) pt.S).interpret I e a ↔ a = σB :=
    fun e a => by rw [sortB_tr]; exact hσB1 a
  exact ((TieAlpha.acEqB_sat same0).symm.trans
    (TieEqArgCut.argCut_iff_top hD hc parts0 sub0 fresh0 top0 hB hσB2)).mpr (fnItem_sat hI ax0_at)

/-! #### Sentence 56 in a model of Γ where `and` is total at values -/

section gam
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

theorem a_cons (H : HookParams) : aSrt ∈ consSorts (cH H) := (by decide +kernel : aSrt ∈ consSorts c)
theorem a_gens (H : HookParams) : ((cH H).gens aSrt).isEmpty = false ∧
    ((cH H).gens aSrt).all (·.argSorts.isEmpty) = true :=
  (by decide +kernel : (c.gens aSrt).isEmpty = false ∧ (c.gens aSrt).all (·.argSorts.isEmpty) = true)

/-- **Every element of A is a value's element**, in a model of Γ: A's no-junk sentence makes it x or
y, each a value. -/
theorem elemA (H : HookParams) (hI : I ⊧ᴵP Γ (cH H)) {a : M} (ha : InS I ((cH H).sortName aSrt) a) :
    ∃ v, (cH H).sortOf v = some aSrt ∧ elemOf (cH H) I v = a := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have hD := defOK hI
  obtain ⟨g', hg', xs, hxs, hm⟩ := noJunk_elim hD
    (sat_cons hI (Or.inl ⟨_, noJunkItem_mem (a_cons H) (a_gens H).1, rfl⟩)) ha
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
  have hnil : g.argSorts = [] := by
    have := List.all_eq_true.mp (a_gens H).2 g hg
    simpa using this
  rw [toK_argSorts, hnil] at hxs
  cases hxs
  exact gen_value hI (sortCtx_of_all hok hsr (OvlOK.ovlCase hno)).trans
    (Model.namesApartK_spec (faithCoreOK_parts (Semantics.coreOK_parts (coreOKH H)).2.1).2.2.2.2.2.1)
    (fun k hk hkr => Semantics.raw_noInst_core_irs (coreOKH H) hk hkr) hg (ws := []) (by rw [hnil]; rfl)
    (fun k _ => OvlLaws.fnCover_none_of_not_fnOvl
      (by rw [show (cH H).fnOvlSyms = [] from first_fnOvl]; exact List.not_mem_nil) []) hm

/-- **`and` at two values of A is one element of B**, in a model of Γ at an H that gives it a value
there: Γ's graph of `and` at values. -/
theorem and_single (H : HookParams) (hI : I ⊧ᴵP Γ (cH H)) (ht : OpenTotal (cH H)) {va vg : GroundTerm}
    (ha : (cH H).sortOf va = some aSrt) (hg : (cH H).sortOf vg = some aSrt) :
    ∃ v, (cH H).sortOf v = some bSrt ∧
      ∀ m, App2F I andP (elemOf (cH H) I va) (elemOf (cH H) I vg) m ↔ m = elemOf (cH H) I v := by
  have hD := defOK hI
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hws : (cH H).sortsOf [va, vg] = some [aSrt, aSrt] := first_srt2 ha hg
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (ht andK andK_mem rfl [va, vg] hws)
  have hvB := ((and_paramVal H).mp hv).2
  refine ⟨v, hvB, fun m => ?_⟩
  have hv' : (cH H).paramVal andS [va, vg] = some v := hv
  have hax : I ⊧ᴵ (KoreAML.den (symApp (cH H) andS (GroundTerm.koreList (cH H) [va, vg])) ≡
      (match (cH H).paramVal andS [va, vg] with
        | some v => den (cH H) v
        | none => ⊥)) := sat_dom hI (Or.inr (Or.inl ⟨andK, [va, vg], andK_mem, hws, rfl⟩))
  have hsa : KoreAML.den (symApp (cH H) andS (GroundTerm.koreList (cH H) [va, vg])) =
      den (cH H) (.ctor andS [va, vg]) := by
    rw [symApp_noInst (f := andS) (Semantics.raw_noInst_core_irs (coreOKH H) andK_mem rfl)]; rfl
  rw [hsa, hv'] at hax
  have hgr := (KoreAML.interp_equal hD).mp (hax KoreAML.val0 default) m
  rw [← (elemOf_spec hI hvB KoreAML.val0).1 m, ← hgr,
    den_sig_gs hI (f := andS) (k := andK.sig) rfl hws KoreAML.val0 m]
  unfold GS App2F App1F
  simp only [List.map, AppE, Gen.toK, toK, genHead]
  constructor
  · rintro ⟨s, ⟨s0, hs0, hs0a⟩, hsm⟩
    exact ⟨s0, (sym_closed _ _ _ s0).mp hs0, s, hs0a, m, hsm, rfl⟩
  · rintro ⟨s0, hs0, s, hs0a, m', hsm, rfl⟩
    exact ⟨s, ⟨s0, (sym_closed _ _ _ s0).mp hs0, hs0a⟩, hsm⟩

/-- **Sentence 56 holds in a model of Γ where `and` is total at values.** -/
theorem s56_model (H : HookParams) (hI : I ⊧ᴵP Γ (cH H)) (ht : OpenTotal (cH H)) : I ⊧ᴵ pat56 := by
  have hD := defOK hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  have hAB : (∃ σA, (∀ z, I.evalSymb (.sort "SortA") z ↔ z = σA) ∧ IsSort I σA) ∧
      (∃ σB, (∀ z, I.evalSymb (.sort "SortB") z ↔ z = σB) ∧ IsSort I σB) :=
    ⟨sortConst_of hD (hSig _ (Or.inl (Or.inl ⟨_, sig_sortConst (a_numbered H), rfl⟩))),
     sortConst_of hD (hSig _ (Or.inl (Or.inl ⟨_, sig_sortConst (b_numbered H), rfl⟩)))⟩
  obtain ⟨⟨σA, hA, hσA⟩, ⟨σB, hB, hσB⟩⟩ := hAB
  have hinA : ∀ (e : Valuation M) z, (inhOf sA).interpret I e z ↔ Inh I σA z :=
    fun e z => interp_inhOf_of (sA_at hA e)
  have hinB : ∀ (e : Valuation M) z, (inhOf sB).interpret I e z ↔ Inh I σB z :=
    fun e z => interp_inhOf_of (sB_at hB e)
  have inSA : ∀ z, InS I ((cH H).sortName aSrt) z ↔ Inh I σA z := fun z => by
    unfold InS; rw [show (cH H).sortName aSrt = "A" from names.1]; exact hinA _ z
  have inSB : ∀ z, InS I ((cH H).sortName bSrt) z ↔ Inh I σB z := fun z => by
    unfold InS; rw [show (cH H).sortName bSrt = "B" from names.2.1]; exact hinB _ z
  intro e m0
  unfold pat56 conjList conjList conjList
  rw [interpret_impl]
  intro hg
  rw [interpret_conj, interpret_conj] at hg
  obtain ⟨h1, h3, h4⟩ := hg
  unfold sortGuard at h1
  rw [interp_member hD, interp_sortsDomain] at h1
  rw [interp_member hD, hinA] at h3 h4
  obtain ⟨va, hva, ea⟩ := elemA H hI ((inSA _).mpr h3)
  obtain ⟨vg, hvg, eg⟩ := elemA H hI ((inSA _).mpr h4)
  obtain ⟨v, hvB, happ⟩ := and_single H hI ht hva hvg
  rw [ea, eg] at happ
  have hwB : Inh I σB (elemOf (cH H) I v) :=
    (inSB _).mp ((inS_iff KoreAML.val0).mp (elemOf_spec hI hvB KoreAML.val0).2)
  rw [interp_equal hD]
  intro z
  have hR : ∀ y, (vP 1).interpret I e y ↔ y = e.evalEvar ⟨1⟩ := fun y => interp_evar
  rw [interp_sExists, interp_inhOf_of hR]
  constructor
  · rintro ⟨w, -, heq⟩
    let e2 : Valuation M := ⟨Function.update e.evalEvar ⟨2⟩ w, e.evalSvar⟩
    have hR2 : ∀ y, (vP 1).interpret I e2 y ↔ y = e.evalEvar ⟨1⟩ := fun y => by
      show y = e2.evalEvar ⟨1⟩ ↔ _
      simp [e2, Function.update]
    change (sEquals sB (vP 1) (vP 2) (andP ⬝ vP 3 ⬝ vP 4)).interpret I e2 z at heq
    rw [interp_sEquals hD hc (sB_at hB e2) hR2 hσB h1] at heq
    exact heq.1
  · intro hz
    let w := elemOf (cH H) I v
    let e2 : Valuation M := ⟨Function.update e.evalEvar ⟨2⟩ w, e.evalSvar⟩
    have e21 : e2.evalEvar ⟨1⟩ = e.evalEvar ⟨1⟩ := by simp [e2, Function.update]
    have e22 : e2.evalEvar ⟨2⟩ = w := by simp [e2]
    have e23 : e2.evalEvar ⟨3⟩ = e.evalEvar ⟨3⟩ := by simp [e2, Function.update]
    have e24 : e2.evalEvar ⟨4⟩ = e.evalEvar ⟨4⟩ := by simp [e2, Function.update]
    have hv : ∀ (n : Nat) (y : M), (vP n).interpret I e2 y ↔ y = e2.evalEvar ⟨n⟩ := fun n y => interp_evar
    refine ⟨w, ?_, ?_⟩
    · show (((⟨2⟩ : EVar) ∈∈ inhOf sB : P)).interpret I e2 z
      rw [interp_member hD, hinB, e22]; exact hwB
    · show (sEquals sB (vP 1) (vP 2) (andP ⬝ vP 3 ⬝ vP 4)).interpret I e2 z
      rw [interp_sEquals hD hc (sB_at hB e2) (fun y => by rw [hv, e21]) hσB h1]
      refine ⟨hz, fun y _ => ?_⟩
      have happ2 : ∀ y, (andP ⬝ vP 3 ⬝ vP 4).interpret I e2 y ↔
          App2F I andP (e.evalEvar ⟨3⟩) (e.evalEvar ⟨4⟩) y :=
        interp_app2F _ (fun y => by rw [hv, e23]) (fun y => by rw [hv, e24])
      rw [hv, e22, happ2, happ]

end gam

end NonVacFA

open NonVacFA in
/-- **Every model of Γ at an H that gives `and` a value at every pair of values of A is a model of
`PreFA H`.** -/
theorem gamma_pre (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (ht : OpenTotal (cH H)) : I ⊧ᴵP PreFA H := by
  rintro φ ((hφ | ⟨x, rfl⟩) | hφ)
  · rcases List.mem_cons.mp hφ with rfl | hφ
    · rw [s56_pat]; exact s56_model H hI ht
    · rw [List.mem_singleton.mp hφ]; exact s100_entailedFA H hI
  · exact sat_sig hI (Or.inl (Or.inr ⟨x, rfl⟩))
  · exact sat_sig hI hφ

open NonVacFA in
/-- **`PreFA H` has a model, for every H**: a model of `Γc` with the step's closure at
`lawHooks c H`, which gives `and` its free applications. The table `first_and_x` is not vacuous. -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP PreFA H := by
  obtain ⟨M, hM, I, hI⟩ := consistentFA (lawHooks c H) (firstDet_lawHooks H)
  exact ⟨M, hM, I, preFA_hooks (lawHooks c H) H ▸
    gamma_pre (lawHooks c H) (fun φ hφ => hI φ (Or.inl (Or.inl hφ))) (openTotal_lawHooks c NonVacFA.coreOK H)⟩

open NonVacFA in
/-- **At an H where `and` determines its first argument and has a value at every pair of values of
A, every model of `Γc (cH H)` is a model of `PreFA H`, and there is one.** -/
theorem pre_model_firstDet (H : HookParams) (hH : NonVacFA.FirstDet H) (ht : OpenTotal (cH H)) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), (I ⊧ᴵP Γc (cH H)) ∧ (I ⊧ᴵP PreFA H) := by
  obtain ⟨M, hM, I, hI⟩ := consistentFA H hH
  exact ⟨M, hM, I, fun φ hφ => hI φ (Or.inl hφ), gamma_pre H (fun φ hφ => hI φ (Or.inl (Or.inl hφ))) ht⟩

end KCore.OpenFirstAndText

#check @KCore.OpenFirstAndText.s56_pat
#check @KCore.OpenFirstAndText.s100_pat
#check @KCore.OpenFirstAndText.and_one
#check @KCore.OpenFirstAndText.first_at
#check @KCore.OpenFirstAndText.first_and_x
/-- info: 'KCore.OpenFirstAndText.first_and_x' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenFirstAndText.first_and_x
#check @KCore.OpenFirstAndText.preFA_hooks
#check @KCore.OpenFirstAndText.NonVacFA.consistentFA
#check @KCore.OpenFirstAndText.NonVacFA.s100_entailedFA
#check @KCore.OpenFirstAndText.NonVacFA.elemA
#check @KCore.OpenFirstAndText.NonVacFA.and_single
#check @KCore.OpenFirstAndText.NonVacFA.s56_model
#check @KCore.OpenFirstAndText.gamma_pre
#check @KCore.OpenFirstAndText.pre_model
#check @KCore.OpenFirstAndText.pre_model_firstDet
/-- info: 'KCore.OpenFirstAndText.pre_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenFirstAndText.pre_model
/-- info: 'KCore.OpenFirstAndText.pre_model_firstDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenFirstAndText.pre_model_firstDet
