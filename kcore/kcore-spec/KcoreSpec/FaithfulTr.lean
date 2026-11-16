/-
  The interpretation of the patterns the translation (`tr`, `trAxiom`) produces, in a model of
  definedness and of the definedness symbols `⌈_⌉{s,s'}`: what the sorted connectives, equality,
  membership and inclusion mean as sets, and how a translated axiom constrains a model at a
  valuation that satisfies its guards. Nothing here is about K.
-/
import KcoreSpec.Kore.Gamma

set_option autoImplicit false

namespace KoreAML

open ML

variable {M : Type} {I : Interpretation Sym M}

/-! ## Definedness -/

/-- The model interprets `⌈_⌉` as definedness: `⌈a⌉` holds everywhere, for every element `a`. -/
def DefOK (I : Interpretation Sym M) : Prop :=
  ∀ a m : M, ∃ d, I.evalSymb HasDefined.defined d ∧ I.evalApp d a m

@[simp] theorem sing_iff {x a : M} : ({x} : Set M) a ↔ a = x := Iff.rfl

theorem interp_evar {e : Valuation M} {x : EVar} {a : M} :
    (Pattern.evar x : P).interpret I e a ↔ a = e.evalEvar x := Iff.rfl

theorem defOK_of (h : ∀ x : EVar, I ⊧ᴵ @definedness Sym _ x) : DefOK I := by
  intro a m
  have h1 := h ⟨0⟩ ⟨fun _ => a, fun _ _ => False⟩ m
  unfold definedness Pattern.universal at h1
  rw [interpret_neg, interpret_exists] at h1
  refine Classical.byContradiction fun hc => h1 ⟨a, ?_⟩
  rw [interpret_neg]
  intro h2
  simp only [Pattern.interpret] at h2
  obtain ⟨d, b, hd, hb, happ⟩ := h2
  have hb' : b = a := by rw [sing_iff] at hb; simpa using hb
  subst hb'
  exact hc ⟨d, hd, happ⟩

section
variable (hD : DefOK I) {e : Valuation M} {φ ψ : P} {m : M}
include hD

theorem interp_defined : (⌈φ⌉ : P).interpret I e m ↔ ∃ a, φ.interpret I e a := by
  constructor
  · intro h
    simp only [Pattern.interpret] at h
    obtain ⟨_, b, _, hb, _⟩ := h
    exact ⟨b, hb⟩
  · rintro ⟨a, ha⟩
    obtain ⟨d, hd, happ⟩ := hD a m
    exact ⟨d, a, hd, ha, happ⟩

theorem interp_total : (⌊φ⌋ : P).interpret I e m ↔ ∀ a, φ.interpret I e a := by
  unfold total
  rw [interpret_neg, interp_defined hD]
  simp

theorem interp_equal : (φ ≡ ψ : P).interpret I e m ↔ ∀ a, (φ.interpret I e a ↔ ψ.interpret I e a) := by
  unfold equal
  rw [interp_total hD]
  simp only [interpret_equiv]

theorem interp_member {x : EVar} : (x ∈∈ φ : P).interpret I e m ↔ φ.interpret I e (e.evalEvar x) := by
  unfold member
  rw [interp_defined hD]
  simp only [interpret_conj, interp_evar]
  constructor
  · rintro ⟨a, ha, h⟩
    subst ha
    exact h
  · intro h
    exact ⟨_, rfl, h⟩

theorem interp_included : (φ ⊆⊆ ψ : P).interpret I e m ↔ ∀ a, φ.interpret I e a → ψ.interpret I e a := by
  unfold included
  rw [interp_total hD]
  simp

theorem interp_notEqual : (notEqual φ ψ).interpret I e m ↔ ¬ ∀ a, (φ.interpret I e a ↔ ψ.interpret I e a) := by
  unfold notEqual
  rw [interpret_neg, interp_equal hD]

end

/-! ## Sorted connectives -/

section
variable {e : Valuation M} {s φ ψ : P} {m : M}

theorem interp_sNot : (sNot s φ).interpret I e m ↔ ¬ φ.interpret I e m ∧ (inhOf s).interpret I e m := by
  unfold sNot; rw [interpret_conj, interpret_neg]

theorem interp_sAnd : (sAnd φ ψ).interpret I e m ↔ φ.interpret I e m ∧ ψ.interpret I e m := by
  unfold sAnd; rw [interpret_conj]

theorem interp_sOr : (sOr s φ ψ).interpret I e m ↔
    (inhOf s).interpret I e m ∧ (φ.interpret I e m ∨ ψ.interpret I e m) := by
  unfold sOr; simp only [interp_sNot, interp_sAnd]
  by_cases h1 : φ.interpret I e m <;> by_cases h2 : ψ.interpret I e m <;>
    by_cases h3 : (inhOf s).interpret I e m <;> simp [h1, h2, h3]

theorem interp_sImp : (sImp s φ ψ).interpret I e m ↔
    (inhOf s).interpret I e m ∧ (φ.interpret I e m → ψ.interpret I e m) := by
  unfold sImp; simp only [interp_sOr, interp_sNot]
  by_cases h1 : φ.interpret I e m <;> by_cases h2 : ψ.interpret I e m <;>
    by_cases h3 : (inhOf s).interpret I e m <;> simp [h1, h2, h3]

theorem interp_sIff : (sIff s φ ψ).interpret I e m ↔
    (inhOf s).interpret I e m ∧ (φ.interpret I e m ↔ ψ.interpret I e m) := by
  unfold sIff; simp only [interp_sAnd, interp_sImp]
  by_cases h1 : φ.interpret I e m <;> by_cases h2 : ψ.interpret I e m <;>
    by_cases h3 : (inhOf s).interpret I e m <;> simp [h1, h2, h3]

theorem interp_sExists {x : EVar} : (sExists x s φ).interpret I e m ↔
    ∃ a, (x ∈∈ inhOf s : P).interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ m ∧
      φ.interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ m := by
  unfold sExists; simp only [interpret_exists, interpret_conj]

theorem interp_app : (φ ⬝ ψ).interpret I e m ↔
    ∃ a b, φ.interpret I e a ∧ ψ.interpret I e b ∧ I.evalApp a b m := by
  simp only [Pattern.interpret]

theorem interp_sym {σ : Sym} : (sym σ).interpret I e m ↔ I.evalSymb σ m := Iff.rfl

end

/-! ## Sorts as elements -/

/-- `m` is an inhabitant of the sort element `σ`: `m ∈ ⊤_ σ`. -/
def Inh (I : Interpretation Sym M) (σ m : M) : Prop := ∃ i, I.evalSymb .inh i ∧ I.evalApp i σ m

/-- `σ` is a sort: an inhabitant of the sort of sorts. -/
def IsSort (I : Interpretation Sym M) (σ : M) : Prop := ∃ s0, I.evalSymb .sortSort s0 ∧ Inh I s0 σ

section
variable {e : Valuation M} {S φ ψ : P} {m : M}

theorem interp_inhOf : (inhOf S).interpret I e m ↔ ∃ σ, S.interpret I e σ ∧ Inh I σ m := by
  unfold inhOf Inh
  simp only [interp_app, interp_sym]
  constructor
  · rintro ⟨i, σ, hi, hσ, h⟩; exact ⟨σ, hσ, i, hi, h⟩
  · rintro ⟨σ, hσ, i, hi, h⟩; exact ⟨i, σ, hi, hσ, h⟩

/-- `⊤_ S` for a pattern `S` that denotes the one element `σ`. -/
theorem interp_inhOf_of {σ : M} (hS : ∀ a, S.interpret I e a ↔ a = σ) :
    (inhOf S).interpret I e m ↔ Inh I σ m := by
  rw [interp_inhOf]
  constructor
  · rintro ⟨τ, hτ, h⟩; rw [(hS τ).mp hτ] at h; exact h
  · intro h; exact ⟨σ, (hS σ).mpr rfl, h⟩

theorem interp_sortsDomain : sortsDomain.interpret I e m ↔ IsSort I m := by
  unfold sortsDomain IsSort
  rw [interp_inhOf]
  rfl

end

/-! ## Closed patterns -/

/-- A pattern with no free variable: its interpretation does not depend on the valuation. -/
def Closed (φ : P) : Prop := (∀ x, φ.isFreeEvar x = false) ∧ ∀ X, φ.isFreeSvar X = false

theorem Closed.interp {φ : P} (h : Closed φ) (e e' : Valuation M) (m : M) :
    φ.interpret I e m ↔ φ.interpret I e' m := by
  have := @only_free_var_relevant Sym M I φ e.evalEvar e'.evalEvar e.evalSvar e'.evalSvar
    (fun x hx => by rw [h.1 x] at hx; cases hx) (fun X hX => by rw [h.2 X] at hX; cases hX) m
  exact this

theorem Closed.sym (σ : Sym) : Closed (sym σ) := ⟨fun _ => rfl, fun _ => rfl⟩

theorem Closed.app {φ ψ : P} (h1 : Closed φ) (h2 : Closed ψ) : Closed (φ ⬝ ψ) :=
  ⟨fun x => by simp [Pattern.isFreeEvar, h1.1 x, h2.1 x],
   fun X => by simp [Pattern.isFreeSvar, h1.2 X, h2.2 X]⟩

theorem Closed.appList {φ : P} {ψs : List P} (h1 : Closed φ) (h2 : ∀ ψ ∈ ψs, Closed ψ) :
    Closed (appList φ ψs) := by
  induction ψs generalizing φ with
  | nil => exact h1
  | cons ψ ψs ih =>
    exact ih (h1.app (h2 ψ (List.mem_cons_self ..))) (fun χ hχ => h2 χ (List.mem_cons_of_mem _ hχ))

/-! ## The definedness symbols `⌈_⌉{s,s'}` -/

/-- The element `⌈x⌉{σ,σ'}` contains `m`. -/
def CeilE (I : Interpretation Sym M) (σ σ' x m : M) : Prop :=
  ∃ a, (∃ a', (∃ h, I.evalSymb .ceil h ∧ I.evalApp h σ a') ∧ I.evalApp a' σ' a) ∧ I.evalApp a x m

theorem interp_sCeil_raw {e : Valuation M} {S S' φ : P} {m : M} :
    (sCeil S S' φ).interpret I e m ↔
      ∃ σ σ' x, S.interpret I e σ ∧ S'.interpret I e σ' ∧ φ.interpret I e x ∧ CeilE I σ σ' x m := by
  unfold sCeil CeilE
  simp only [interp_app, interp_sym]
  constructor
  · rintro ⟨a, x, ⟨a', σ', ⟨h, σ, hh, hσ, h1⟩, hσ', h2⟩, hx, h3⟩
    exact ⟨σ, σ', x, hσ, hσ', hx, a, ⟨a', ⟨h, hh, h1⟩, h2⟩, h3⟩
  · rintro ⟨σ, σ', x, hσ, hσ', hx, a, ⟨a', ⟨h, hh, h1⟩, h2⟩, h3⟩
    exact ⟨a, x, ⟨a', σ', ⟨h, σ, hh, hσ, h1⟩, hσ', h2⟩, hx, h3⟩

theorem interp_conjList {e : Valuation M} {ws : List P} {m : M}
    (h : ∀ w ∈ ws, w.interpret I e m) : (conjList ws).interpret I e m := by
  induction ws with
  | nil => simp [conjList, Pattern.top]
  | cons w ws ih =>
    cases ws with
    | nil => exact h w (List.mem_cons_self ..)
    | cons w' ws' =>
      unfold conjList
      rw [interpret_conj]
      exact ⟨h w (List.mem_cons_self ..), ih fun w'' hw => h w'' (List.mem_cons_of_mem _ hw)⟩

theorem interp_guarded {e : Valuation M} {ws : List P} {φ : P} {m : M}
    (h : (guarded ws φ).interpret I e m) (hw : ∀ w ∈ ws, w.interpret I e m) : φ.interpret I e m := by
  cases ws with
  | nil => exact h
  | cons w ws => exact h (interp_conjList hw)

section
variable [Inhabited M] (hD : DefOK I)
include hD

/-- In a model of `ceilDefItem`: `⌈x⌉{σ,σ'}` is the sort `σ'`, for an element `x` of the sort `σ`. -/
theorem ceilE_of (hc : I ⊧ᴵ ceilDefItem.pat) {σ σ' x : M} (hσ : IsSort I σ) (hσ' : IsSort I σ')
    (hx : Inh I σ x) (m : M) : CeilE I σ σ' x m ↔ Inh I σ' m := by
  let e : Valuation M := ⟨fun i => if i = ⟨1⟩ then σ else if i = ⟨2⟩ then σ' else x, fun _ _ => False⟩
  have h := hc e default
  unfold ceilDefItem at h
  dsimp only at h
  have hb := interp_guarded h (by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · unfold sortGuard; rw [interp_member hD, interp_sortsDomain]; exact hσ
    rcases List.mem_cons.mp hw with rfl | hw
    · unfold sortGuard; rw [interp_member hD, interp_sortsDomain]; exact hσ'
    rcases List.mem_cons.mp hw with rfl | hw
    · rw [interp_member hD, interp_inhOf]
      exact ⟨σ, by simp [e], by simpa [e] using hx⟩
    · cases hw)
  rw [interp_equal hD] at hb
  have := hb m
  rw [interp_sCeil_raw, interp_inhOf] at this
  simp only [interp_evar, e] at this
  constructor
  · intro hm
    obtain ⟨_, rfl, h2⟩ := this.mp ⟨σ, σ', x, by simp, by simp, by simp, hm⟩
    exact h2
  · intro hm
    obtain ⟨_, _, _, h1, h2, h3, h4⟩ := this.mpr ⟨σ', by simp, hm⟩
    simp at h1 h2 h3
    subst h1; subst h2; subst h3
    exact h4

end

section
variable [Inhabited M] (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
include hD hc

/-- `⌈φ⌉{S,S'}` for sort patterns `S`, `S'` that denote the sorts `σ`, `σ'` and a pattern `φ`
inside `σ`: the sort `σ'` where `φ` is not empty, empty where it is. -/
theorem interp_sCeil {e : Valuation M} {S S' φ : P} {σ σ' : M}
    (hS : ∀ a, S.interpret I e a ↔ a = σ) (hS' : ∀ a, S'.interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ') (hφ : ∀ a, φ.interpret I e a → Inh I σ a) (m : M) :
    (sCeil S S' φ).interpret I e m ↔ (∃ a, φ.interpret I e a) ∧ Inh I σ' m := by
  rw [interp_sCeil_raw]
  constructor
  · rintro ⟨τ, τ', x, h1, h2, h3, h4⟩
    rw [(hS τ).mp h1, (hS' τ').mp h2] at h4
    exact ⟨⟨x, h3⟩, (ceilE_of hD hc hσ hσ' (hφ x h3) m).mp h4⟩
  · rintro ⟨⟨x, hx⟩, hm⟩
    exact ⟨σ, σ', x, (hS σ).mpr rfl, (hS' σ').mpr rfl, hx, (ceilE_of hD hc hσ hσ' (hφ x hx) m).mpr hm⟩

/-- `φ =^{S'}_S ψ` holds (as the whole sort `σ'`) exactly when `φ` and `ψ` agree on the sort `σ`;
otherwise it is empty. -/
theorem interp_sEquals {e : Valuation M} {S S' φ ψ : P} {σ σ' : M}
    (hS : ∀ a, S.interpret I e a ↔ a = σ) (hS' : ∀ a, S'.interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ') (m : M) :
    (sEquals S S' φ ψ).interpret I e m ↔
      Inh I σ' m ∧ ∀ a, Inh I σ a → (φ.interpret I e a ↔ ψ.interpret I e a) := by
  unfold sEquals sFloor
  rw [interp_sNot, interp_sCeil hD hc hS hS' hσ hσ' (fun a ha => (interp_inhOf_of hS).mp (interp_sNot.mp ha).2) m,
    interp_inhOf_of hS']
  simp only [interp_sNot, interp_sIff, interp_inhOf_of hS]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun a ha => Classical.byContradiction fun hn => h1 ⟨⟨a, fun h => hn h.2, ha⟩, h2⟩⟩
  · rintro ⟨h2, h⟩
    exact ⟨fun ⟨⟨a, hn, ha⟩, _⟩ => hn ⟨ha, h a ha⟩, h2⟩

/-- `φ ∈^{S'}_S ψ`, for `φ` inside the sort `σ`: the sort `σ'` where `φ` and `ψ` meet. -/
theorem interp_sIn {e : Valuation M} {S S' φ ψ : P} {σ σ' : M}
    (hS : ∀ a, S.interpret I e a ↔ a = σ) (hS' : ∀ a, S'.interpret I e a ↔ a = σ')
    (hσ : IsSort I σ) (hσ' : IsSort I σ') (hφ : ∀ a, φ.interpret I e a → Inh I σ a) (m : M) :
    (sIn S S' φ ψ).interpret I e m ↔
      (∃ a, φ.interpret I e a ∧ ψ.interpret I e a) ∧ Inh I σ' m := by
  unfold sIn
  rw [interp_sCeil hD hc hS hS' hσ hσ' (fun a ha => hφ a (interp_sAnd.mp ha).1) m]
  simp only [interp_sAnd]

end

section
variable (hD : DefOK I)
include hD

/-- `⊤_s` is the sort `s`, for a sort pattern in which the variable it binds is not free. -/
theorem interp_sTop {e : Valuation M} {s : P} (hs : s.isFreeEvar topVar = false) (m : M) :
    (sTop s).interpret I e m ↔ (inhOf s).interpret I e m := by
  unfold sTop
  rw [interp_sExists]
  simp only [interp_member hD, interp_evar]
  have key : ∀ a, (inhOf s).interpret I ⟨Function.update e.evalEvar topVar a, e.evalSvar⟩ m ↔
      (inhOf s).interpret I e m := fun a =>
    only_free_var_relevant _ _ _ _ (fun x hx => by
      have : x ≠ topVar := by
        rintro rfl
        unfold inhOf at hx
        simp only [Pattern.isFreeEvar, hs] at hx
        simp [sym] at hx
      simp [Function.update, this]) (fun _ _ => rfl) m
  constructor
  · rintro ⟨a, h1, h2⟩
    simp only [Function.update_same] at h1 h2
    subst h2
    exact (key _).mp h1
  · intro h
    exact ⟨m, by rw [Function.update_same]; exact (key m).mpr h, by rw [Function.update_same]⟩

/-- A sort constant of the encoding (`sortConstantItem` without parameters) denotes one sort. -/
theorem sortConst_of [Inhabited M] {n : String} {b : Bool}
    (h : I ⊧ᴵ (sortConstantItem ⟨n, [], b⟩).pat) :
    ∃ σ, (∀ a, I.evalSymb (.sort n) a ↔ a = σ) ∧ IsSort I σ := by
  have h1 := h ⟨fun _ => default, fun _ _ => False⟩ default
  unfold sortConstantItem at h1
  dsimp only [paramTable, List.map, List.length] at h1
  unfold guarded at h1
  rw [interp_sExists] at h1
  obtain ⟨a, h2, h3⟩ := h1
  rw [interp_member hD, interp_inhOf] at h2
  rw [interp_equal hD] at h3
  obtain ⟨s0, hs0, ha⟩ := h2
  refine ⟨a, fun x => ?_, s0, hs0, ha⟩
  have := h3 x
  simpa [appList, interp_sym, interp_evar] using this

/-- A sort constant without parameters is inhabited (`nonemptyItem`). -/
theorem nonempty_of [Inhabited M] {n : String} {b : Bool}
    (h : I ⊧ᴵ (nonemptyItem ⟨n, [], b⟩).pat) {e : Valuation M} : ∃ a, (inhOf (sym (.sort n))).interpret I e a := by
  have h1 := h e default
  unfold nonemptyItem at h1
  dsimp only [paramTable, List.map] at h1
  unfold guarded at h1
  rw [interp_notEqual hD] at h1
  refine Classical.byContradiction fun hn => h1 fun a => ?_
  simp only [appList] at hn ⊢
  exact ⟨fun ha => hn ⟨a, ha⟩, fun hb => by simp [Pattern.interpret] at hb⟩

/-- A guard of `trAxiom` on a free element variable: its value is in its sort. -/
theorem interp_guard_evar {t : VarTable} {n : String} {s : Kore.KSort} {e : Valuation M} {m : M} :
    (guardOf t (.evar n s)).interpret I e m ↔
      (inhOf (trSort t s)).interpret I e (e.evalEvar (t.ev (.evar n s))) := by
  unfold guardOf; rw [interp_member hD]

/-- A guard of `trAxiom` on a sort variable: its value is a sort. -/
theorem interp_guard_sortVar {t : VarTable} {n : String} {e : Valuation M} {m : M} :
    (guardOf t (.sortVar n)).interpret I e m ↔ IsSort I (e.evalEvar (t.ev (.sortVar n))) := by
  unfold guardOf sortGuard; rw [interp_member hD, interp_sortsDomain]

/-- A translated axiom, at a valuation that satisfies its guards: the translation of its pattern
is the whole of its sort. -/
theorem trAxiom_at [Inhabited M] {ds : List SymbolDecl} {al : List String} {ad : AxiomDecl}
    (h : I ⊧ᴵ (trAxiom ds al ad).pat) (e : Valuation M)
    (hg : ∀ k ∈ (ad.ax.sortVars.map sortVarKey ++ freeOf [] ad.ax.pattern).eraseDups, ∀ m,
      (guardOf (tableOf ad.ax.sortVars ad.ax.pattern) k).interpret I e m) (m : M) :
    (tr ⟨tableOf ad.ax.sortVars ad.ax.pattern, al⟩ ad.ax.pattern).interpret I e m ↔
      (match sortOf ds ad.ax.pattern with
        | some s => inhOf (trSort (tableOf ad.ax.sortVars ad.ax.pattern) s)
        | none => sym (.untranslated "sort of the axiom")).interpret I e m := by
  have h1 := h e default
  unfold trAxiom at h1
  dsimp only at h1
  have h2 := h1 (interp_conjList fun w hw => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
    exact hg k hk default)
  rw [interp_equal hD] at h2
  exact h2 m

end

/-! ## Ground KORE patterns -/

/-- A KORE pattern built from applications with constant sort arguments and domain values of a
constant sort: the form of a ground value's KORE. -/
inductive KGround : Kore.Pattern → Prop
  | app {h : Kore.SymbolIdent} {ss : List Kore.KSort} {ps : List Kore.Pattern}
      (hs : ∀ s ∈ ss, ∃ C, s = .ctor C []) (hp : ∀ p ∈ ps, KGround p) : KGround (.app h ss ps)
  | dv {C : Kore.SortIdent} {lit : String} : KGround (.dv (.ctor C []) lit)

theorem trSort_const (t : VarTable) (C : Kore.SortIdent) : trSort t (.ctor C []) = sym (.sort C.ident.name) := by
  simp [trSort, trSortApp]

theorem trSortApp_closed {t : VarTable} {acc : P} {ss : List Kore.KSort} (ha : Closed acc)
    (hs : ∀ s ∈ ss, ∃ C, s = .ctor C []) : Closed (trSortApp t acc ss) := by
  induction ss generalizing acc with
  | nil => simpa [trSortApp] using ha
  | cons s ss ih =>
    obtain ⟨C, rfl⟩ := hs s (List.mem_cons_self ..)
    rw [trSortApp]
    exact ih (ha.app (by rw [trSort_const]; exact Closed.sym _)) (fun s' h => hs s' (List.mem_cons_of_mem _ h))

theorem trArgs_closed {ctx : Ctx} {acc : P} {ps : List Kore.Pattern} (ha : Closed acc)
    (hp : ∀ p ∈ ps, Closed (tr ctx p)) : Closed (trArgs ctx acc ps) := by
  induction ps generalizing acc with
  | nil => simpa [trArgs] using ha
  | cons p ps ih =>
    rw [trArgs]
    exact ih (ha.app (hp p (List.mem_cons_self ..))) (fun q h => hp q (List.mem_cons_of_mem _ h))

/-- The translation of a ground KORE pattern has no free variable. -/
theorem KGround.closed {p : Kore.Pattern} (h : KGround p) (ctx : Ctx) : Closed (tr ctx p) := by
  induction h with
  | app hs _ ih =>
    rw [tr]
    split
    · exact Closed.sym _
    · exact trArgs_closed (trSortApp_closed (Closed.sym _) hs) ih
  | dv =>
    rw [tr, trSort_const]
    exact (Closed.sym _).app (Closed.sym _)

/-! ## Unfolding the translation -/

section
variable {t : VarTable}

theorem tr_app0 (f : String) (ps : List Kore.Pattern) :
    tr ⟨t, []⟩ (.app ⟨⟨f⟩⟩ [] ps) = trArgs ⟨t, []⟩ (sym (.symbol f)) ps := by
  rw [tr]; simp [trSortApp]

theorem tr_injP (a b : String) (p : Kore.Pattern) :
    tr ⟨t, []⟩ (injP a b p) = appList (sym (.symbol "inj")) [Cons.sortP a, Cons.sortP b, tr ⟨t, []⟩ p] := by
  unfold injP
  rw [tr]
  simp [trSortApp, trSort_const, srt, trArgs, appList, Cons.sortP]

theorem tr_dv (n lit : String) : tr ⟨t, []⟩ (.dv (srt n) lit) = sym (.dv lit) ⬝ Cons.sortP n := by
  unfold srt; rw [tr, trSort_const]; rfl

theorem trArgs_cons (ctx : Ctx) (acc : P) (p : Kore.Pattern) (ps : List Kore.Pattern) :
    trArgs ctx acc (p :: ps) = trArgs ctx (acc ⬝ tr ctx p) ps := by
  rw [trArgs]

theorem trArgs_nil (ctx : Ctx) (acc : P) : trArgs ctx acc [] = acc := by
  rw [trArgs]

end

/-- Application is pointwise: its interpretation depends only on the sets its sides denote. -/
theorem interp_app_congr {e e' : Valuation M} {φ φ' ψ ψ' : P}
    (h1 : ∀ m, φ.interpret I e m ↔ φ'.interpret I e' m) (h2 : ∀ m, ψ.interpret I e m ↔ ψ'.interpret I e' m)
    (m : M) : (φ ⬝ ψ).interpret I e m ↔ (φ' ⬝ ψ').interpret I e' m := by
  simp only [interp_app, h1, h2]

end KoreAML
