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

end KCore.OpenFirstAndText

#check @KCore.OpenFirstAndText.s56_pat
#check @KCore.OpenFirstAndText.s100_pat
#check @KCore.OpenFirstAndText.and_one
#check @KCore.OpenFirstAndText.first_at
#check @KCore.OpenFirstAndText.first_and_x
/-- info: 'KCore.OpenFirstAndText.first_and_x' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenFirstAndText.first_and_x
