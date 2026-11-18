/-
  Transfer of a sentence whose connectives are all at a sort variable `R`, the shape of a function
  equation `axiom{R} \implies{R}(premise, \and{R}(\equals{S,R}(f(X̄), rhs), ens))`.

  Such a sentence is not of the class `OwnSorted` (ConsTransfer.lean): in the extension `R` also
  ranges over the detached sort names. `RPred` is the class of its patterns: the definedness
  symbols `⌈ψ⌉{S,R}` at a sort `S` outside `D` and a pattern `ψ` of the class that lies within `S`,
  `⊤_R`, negation and conjunction at `R`, and a quantifier at a sort outside `D`, whose variable
  may be one of the free variables (it then hides that variable in its body). Each denotes the
  sort `R` or nothing, and which of the two does not depend on `R` (`rpred_inv`): a definedness
  symbol reads only whether `ψ` has an element, in the model and, at a detached sort name, in the
  extension.

  `transfer_R`: the extension satisfies `π = ⊤_R` where the model does, for a model in which some
  sort has an element. At that sort the sentence gives that `π` holds, and then it holds at every
  detached sort name.
-/
import KcoreSpec.ConsTransfer

set_option autoImplicit false

namespace KCore.Cons

open ML Faithful
open KoreAML (DefOK Inh IsSort)

/-- `ψ` lies within the sort named `N`, at a valuation that gives each variable of `G` an element
of its sort. -/
inductive WithinS (G : List (EVar × String)) (N : String) : KoreAML.P → Prop
  | not {φ} : WithinS G N (KoreAML.sNot (KoreAML.sym (.sort N)) φ)
  | var {x φ} : (x, N) ∈ G → WithinS G N (KoreAML.sAnd (.evar x) φ)
  | and {φ ψ} : WithinS G N φ → WithinS G N (KoreAML.sAnd φ ψ)

/-- **The patterns at the sort variable `R`**, with free variables among those of `G`, each at the
sort named beside it; `O` names the sorts that may occur. -/
inductive RPred (D : KoreAML.Sym → Prop) (O : String → Prop) (R : EVar) : List (EVar × String) → KoreAML.P → Prop
  | ceil {G N ψ} : O N → OwnSorted D (G.map (·.1)) [] .ex ψ → WithinS G N ψ →
      RPred D O R G (KoreAML.sCeil (KoreAML.sym (.sort N)) (.evar R) ψ)
  | top {G} : RPred D O R G (KoreAML.sTop (.evar R))
  | not {G π} : RPred D O R G π → RPred D O R G (KoreAML.sNot (.evar R) π)
  | and {G π π'} : RPred D O R G π → RPred D O R G π' → RPred D O R G (KoreAML.sAnd π π')
  | ex {G x N π} : O N → x ≠ R → RPred D O R ((x, N) :: G.filter (·.1 ≠ x)) π →
      RPred D O R G (KoreAML.sExists x (KoreAML.sym (.sort N)) π)

namespace RPred
variable {D : KoreAML.Sym → Prop} {O : String → Prop} {R : EVar} {G : List (EVar × String)}
  {π π' φ ψ : KoreAML.P} {N : String}

theorem sBot : RPred D O R G (KoreAML.sBot (.evar R)) := .not .top

/-- A quantifier whose variable is none of the free variables. -/
theorem exFresh {x : EVar} (hN : O N) (hx : x ≠ R) (hG : x ∉ G.map (·.1)) (h : RPred D O R ((x, N) :: G) π) :
    RPred D O R G (KoreAML.sExists x (KoreAML.sym (.sort N)) π) := by
  refine .ex hN hx ?_
  have : G.filter (·.1 ≠ x) = G := List.filter_eq_self.mpr fun p hp =>
    decide_eq_true fun hh => hG (hh ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
  rw [this]
  exact h
theorem sOr (h1 : RPred D O R G π) (h2 : RPred D O R G π') : RPred D O R G (KoreAML.sOr (.evar R) π π') :=
  .not (.and (.not h1) (.not h2))
theorem sImp (h1 : RPred D O R G π) (h2 : RPred D O R G π') : RPred D O R G (KoreAML.sImp (.evar R) π π') :=
  sOr (.not h1) h2
theorem sIff (h1 : RPred D O R G π) (h2 : RPred D O R G π') : RPred D O R G (KoreAML.sIff (.evar R) π π') :=
  .and (sImp h1 h2) (sImp h2 h1)

variable (hO : ∀ N, O N → ¬ D (.sort N))
include hO

/-- `⌊φ⌋{S,R}`. -/
theorem sFloor (hN : O N) (h : OwnSorted D (G.map (·.1)) [] .old φ) :
    RPred D O R G (KoreAML.sFloor (KoreAML.sym (.sort N)) (.evar R) φ) :=
  .not (.ceil hN (.sNot (.sortC (hO N hN)) h) .not)

/-- `φ ={S,R} ψ`. -/
theorem sEquals (hN : O N) (h1 : OwnSorted D (G.map (·.1)) [] .old φ) (h2 : OwnSorted D (G.map (·.1)) [] .old ψ) :
    RPred D O R G (KoreAML.sEquals (KoreAML.sym (.sort N)) (.evar R) φ ψ) :=
  sFloor hO hN (OwnSorted.toOld (.sIff (.sortC (hO N hN)) h1 h2))

omit hO in
/-- `x ∈{S,R} φ`, for a variable `x` of the sort `S`. -/
theorem sIn {x : EVar} (hN : O N) (hx : (x, N) ∈ G) (h : OwnSorted D (G.map (·.1)) [] .old φ) :
    RPred D O R G (KoreAML.sIn (KoreAML.sym (.sort N)) (.evar R) (.evar x) φ) :=
  .ceil hN (.sAnd (.evar (List.mem_map.mpr ⟨_, hx, rfl⟩)) h) (.var hx)

/-- At an old sort `R` the pattern is of the class `OwnSorted`. -/
theorem ownSorted (hRt : R ≠ KoreAML.topVar) (h : RPred D O R G π) :
    OwnSorted D (R :: G.map (·.1)) [] .ex π := by
  induction h with
  | ceil hN hψ _ =>
    exact .sCeil (.sortC (hO _ hN)) (.evar (List.mem_cons_self ..))
      (hψ.mono (fun x hx => List.mem_cons_of_mem _ hx) (fun _ h => h)).toOld
  | @top G =>
    exact .sEx (V' := [R]) (.evar (List.mem_cons_self ..)) (fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨List.mem_cons_self .., hRt⟩
      · exact absurd hy List.not_mem_nil) (.inl rfl) (.evar (List.mem_cons_self ..))
  | not _ ih => exact .sNot (.evar (List.mem_cons_self ..)) ih.toOld
  | and _ _ ih1 ih2 => exact .sAnd ih1 ih2.toOld
  | ex hN _ _ ih =>
    refine .sEx (V' := []) (.sortC (hO _ hN)) nil_sub (.inl rfl) (ih.mono (fun y hy => ?_) (fun _ h => h))
    simp only [List.map_cons, List.mem_cons] at hy ⊢
    rcases hy with h | h | h
    · exact .inr (.inl h)
    · exact .inl h
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
      exact .inr (.inr (List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, rfl⟩))

end RPred

section
variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The inhabitants, in the extension, of a detached sort's name. -/
theorem inh_new {n : String} {x : Ext M} :
    Inh (extModel c D I) (.inr (.srt n)) x ↔ InhX c D I (.inr n) x := by
  constructor
  · rintro ⟨i, hi, happ⟩
    cases i with
    | inl i0 => exact absurd happ app_inl_inr
    | inr ni =>
      rcases sym_new (σ := .inh) (fun h => h) hi with ⟨h', _⟩ | ⟨_, rfl⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, h', _⟩ <;>
        first | cases h' | skip
      exact happ
  · intro h
    exact ⟨.inr .inh, rfl, h⟩

/-- An added element of `⟦Sort⟧` is a sort name. -/
theorem sorts_new {e' : Valuation (Ext M)} {n0 : Added M}
    (h : KoreAML.sortsDomain.interpret (extModel c D I) e' (.inr n0)) : ∃ n, n0 = .srt n := by
  have h' : ∃ a b, (extModel c D I).evalSymb .inh a ∧ (extModel c D I).evalSymb .sortSort b ∧
      (extModel c D I).evalApp a b (.inr n0) := h
  obtain ⟨a, b, ha, hb, happ⟩ := h'
  cases a with
  | inl a0 =>
    cases b with
    | inl b0 => exact absurd happ app_inl_inl_inr
    | inr nb => exact absurd happ app_inl_inr
  | inr na =>
    rcases sym_new (σ := .inh) (fun h => h) ha with ⟨h', _⟩ | ⟨_, rfl⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, h', _⟩ <;>
      first | cases h' | skip
    cases b with
    | inl b0 => exact happ.elim
    | inr nb =>
      rcases sym_new (σ := .sortSort) (fun h => h) hb with ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, rfl⟩ | ⟨h', _⟩ | ⟨_, h', _⟩ <;>
        first | cases h' | skip
      obtain ⟨nm, _, h⟩ := happ
      exact ⟨nm, Sum.inr.inj h⟩

/-- `⌈b⌉{σ,R}` in the extension, at an old sort `σ` and a detached sort name: the sort name's
inhabitants, for `b` in `σ`. -/
theorem ceilE_new {σ b : M} {n : String} {x : Ext M} :
    KoreAML.CeilE (extModel c D I) (.inl σ) (.inr (.srt n)) (.inl b) x ↔ Inh I σ b ∧ InhX c D I (.inr n) x := by
  constructor
  · rintro ⟨a, ⟨a', ⟨h, hh, h1⟩, h2⟩, h3⟩
    cases h with
    | inl h0 =>
      cases a' with
      | inl a0 => exact absurd h2 app_inl_inr
      | inr na => exact absurd h1 app_inl_inl_inr
    | inr nh =>
      rcases sym_new (σ := .ceil) (fun h => h) hh with ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨_, rfl⟩ | ⟨_, h', _⟩ <;>
        first | cases h' | skip
      have e1 : a' = .inr (.ceil1 (.inl σ)) := h1
      subst e1
      have e2 : a = .inr (.ceil2 (.inl σ) (.inr n)) := h2
      subst e2
      obtain ⟨⟨m, hm, hinh⟩, hx⟩ := h3
      cases hm
      exact ⟨hinh, hx⟩
  · rintro ⟨hb, hx⟩
    exact ⟨_, ⟨_, ⟨.inr .ceil, rfl, rfl⟩, rfl⟩, ⟨b, rfl, hb⟩, hx⟩

/-- The valuation gives each variable of `G` an element of its sort. -/
def SortedAt (I : Interpretation KoreAML.Sym M) (G : List (EVar × String)) (e : Valuation M) : Prop :=
  ∀ p ∈ G, (KoreAML.inhOf (KoreAML.sym (.sort p.2))).interpret I e (e.evalEvar p.1)

omit [Inhabited M] in
theorem within_inh {G : List (EVar × String)} {N : String} {ψ : KoreAML.P} (hw : WithinS G N ψ)
    {e : Valuation M} (hG : SortedAt I G e) {σ : M} (hσ : ∀ a, I.evalSymb (.sort N) a ↔ a = σ) :
    ∀ a, ψ.interpret I e a → Inh I σ a := by
  have hS : ∀ a, (KoreAML.sym (.sort N)).interpret I e a ↔ a = σ := hσ
  induction hw with
  | not => intro a h; rw [KoreAML.interp_sNot] at h; exact (KoreAML.interp_inhOf_of hS).mp h.2
  | var hx =>
    intro a h
    rw [KoreAML.interp_sAnd] at h
    have ha : a = e.evalEvar _ := h.1
    rw [ha]
    exact (KoreAML.interp_inhOf_of hS).mp (hG _ hx)
  | and _ ih => intro a h; exact ih a (KoreAML.interp_sAnd.mp h).1

variable (hD : ∀ σ, D σ → plainSym σ) (hI : DefOK I) (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat)
  {O : String → Prop}
  (hO : ∀ N, O N → ¬ D (.sort N) ∧ ∃ σ, IsSort I σ ∧ ∀ a, I.evalSymb (.sort N) a ↔ a = σ)
  {R : EVar} (hRt : R ≠ KoreAML.topVar)
include hD hI hc hO hRt

/-- **A pattern at the sort variable `R` denotes `R` or nothing, the same at an old sort in the
model and at a detached sort name in the extension.** -/
theorem rpred_inv {n : String} {G : List (EVar × String)} {π : KoreAML.P} (h : RPred D O R G π) :
    ∀ (e : Valuation M) (e' : Valuation (Ext M)), OwnRel (G.map (·.1)) [] e e' → SortedAt I G e →
      IsSort I (e.evalEvar R) → e'.evalEvar R = .inr (.srt n) →
      ∃ tv : Prop, (∀ a, π.interpret I e a ↔ tv ∧ Inh I (e.evalEvar R) a) ∧
        ∀ x, π.interpret (extModel c D I) e' x ↔ tv ∧ InhX c D I (.inr n) x := by
  have hRI : ∀ (e : Valuation M) (a : M), (Pattern.evar R : KoreAML.P).interpret I e a ↔ a = e.evalEvar R :=
    fun _ _ => KoreAML.interp_evar
  have hRX : ∀ (e' : Valuation (Ext M)), e'.evalEvar R = .inr (.srt n) → ∀ x,
      (KoreAML.inhOf (.evar R)).interpret (extModel c D I) e' x ↔ InhX c D I (.inr n) x := fun e' he x =>
    (KoreAML.interp_inhOf_of (σ := .inr (.srt n)) (fun a => by rw [KoreAML.interp_evar, he])).trans inh_new
  have hfree : (Pattern.evar R : KoreAML.P).isFreeEvar KoreAML.topVar = false := by
    simp [Pattern.isFreeEvar, Ne.symm hRt]
  induction h with
  | @ceil G N ψ hN hψ hw =>
    intro e e' hr hs hτ hR'
    obtain ⟨hnD, σ, hσ, hσN⟩ := hO _ hN
    have hin := within_inh hw hs hσN
    have hinv := transfer_rel (c := c) hD hI hψ e e' hr
    refine ⟨∃ b, ψ.interpret I e b, fun a => ?_, fun x => ?_⟩
    · exact KoreAML.interp_sCeil hI hc (S := KoreAML.sym (.sort N)) (fun a => hσN a) (hRI e) hσ hτ hin a
    · rw [KoreAML.interp_sCeil_raw]
      constructor
      · rintro ⟨σ', ρ', y, h1, h2, h3, h4⟩
        have hσ' : σ' = .inl σ := by
          cases σ' with
          | inl s => exact congrArg Sum.inl ((hσN s).mp ((sym_old hnD s).mp h1))
          | inr ns => exact absurd h1 ((inv_sym (σ := .sort N) trivial hnD).2 ns)
        have hρ' : ρ' = .inr (.srt n) := by rw [KoreAML.interp_evar, hR'] at h2; exact h2
        subst hσ' hρ'
        cases y with
        | inr ny => exact absurd h3 (hinv.2 ny)
        | inl b => exact ⟨⟨b, (hinv.1 b).mp h3⟩, (ceilE_new.mp h4).2⟩
      · rintro ⟨⟨b, hb⟩, hx⟩
        exact ⟨.inl σ, .inr (.srt n), .inl b, (sym_old hnD σ).mpr ((hσN σ).mpr rfl),
          by rw [KoreAML.interp_evar, hR'], (hinv.1 b).mpr hb, ceilE_new.mpr ⟨hin b hb, hx⟩⟩
  | top =>
    intro e e' hr hs hτ hR'
    refine ⟨True, fun a => ?_, fun x => ?_⟩
    · rw [KoreAML.interp_sTop hI hfree, KoreAML.interp_inhOf_of (hRI e)]
      exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
    · rw [KoreAML.interp_sTop (ext_defOK c D I) hfree, hRX e' hR']
      exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | not _ ih =>
    intro e e' hr hs hτ hR'
    obtain ⟨tv, h1, h2⟩ := ih e e' hr hs hτ hR'
    refine ⟨¬ tv, fun a => ?_, fun x => ?_⟩
    · rw [KoreAML.interp_sNot, h1, KoreAML.interp_inhOf_of (hRI e)]
      exact ⟨fun h => ⟨fun ht => h.1 ⟨ht, h.2⟩, h.2⟩, fun h => ⟨fun h' => h.1 h'.1, h.2⟩⟩
    · rw [KoreAML.interp_sNot, h2, hRX e' hR']
      exact ⟨fun h => ⟨fun ht => h.1 ⟨ht, h.2⟩, h.2⟩, fun h => ⟨fun h' => h.1 h'.1, h.2⟩⟩
  | and _ _ ih1 ih2 =>
    intro e e' hr hs hτ hR'
    obtain ⟨tv1, h1, h2⟩ := ih1 e e' hr hs hτ hR'
    obtain ⟨tv2, h3, h4⟩ := ih2 e e' hr hs hτ hR'
    refine ⟨tv1 ∧ tv2, fun a => ?_, fun x => ?_⟩
    · rw [KoreAML.interp_sAnd, h1, h3]
      exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩⟩
    · rw [KoreAML.interp_sAnd, h2, h4]
      exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩⟩
  | @ex G x N π hN hxR _ ih =>
    intro e e' hr hs hτ hR'
    obtain ⟨hnD, σ, hσ, hσN⟩ := hO _ hN
    have hS : ∀ (e : Valuation M) (a : M), (KoreAML.sym (.sort N)).interpret I e a ↔ a = σ := fun _ a => hσN a
    have hRx : R ≠ x := Ne.symm hxR
    have key : ∀ a : M, Inh I σ a → ∃ tv : Prop,
        (∀ m, π.interpret I ⟨Function.update e.evalEvar x a, e.evalSvar⟩ m ↔ tv ∧ Inh I (e.evalEvar R) m) ∧
        ∀ y, π.interpret (extModel c D I) ⟨Function.update e'.evalEvar x (.inl a), e'.evalSvar⟩ y ↔
          tv ∧ InhX c D I (.inr n) y := fun a ha => by
      have h := ih ⟨Function.update e.evalEvar x a, e.evalSvar⟩ ⟨Function.update e'.evalEvar x (.inl a), e'.evalSvar⟩
        ⟨fun y hy => by
          show Function.update e'.evalEvar x (.inl a) y = .inl (Function.update e.evalEvar x a y)
          by_cases hy' : y = x
          · subst hy'; rw [Function.update_same, Function.update_same]
          · rw [Function.update_noteq hy', Function.update_noteq hy']
            rcases List.mem_cons.mp hy with h | h
            · exact absurd h hy'
            · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
              exact hr.1 _ (List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, rfl⟩), nil_sub⟩
        (fun p hp => by
          show (KoreAML.inhOf (KoreAML.sym (.sort p.2))).interpret I _ (Function.update e.evalEvar x a p.1)
          rcases List.mem_cons.mp hp with rfl | hp
          · rw [Function.update_same]; exact (KoreAML.interp_inhOf_of (hS _)).mpr ha
          · have hp' := List.mem_filter.mp hp
            have hne : p.1 ≠ x := of_decide_eq_true hp'.2
            rw [Function.update_noteq hne]
            exact hs p hp'.1)
        (by show IsSort I (Function.update e.evalEvar x a R); rw [Function.update_noteq hRx]; exact hτ)
        (by show Function.update e'.evalEvar x (.inl a) R = _; rw [Function.update_noteq hRx]; exact hR')
      obtain ⟨tv, h1, h2⟩ := h
      refine ⟨tv, fun m => ?_, h2⟩
      have := h1 m
      have hu : Function.update e.evalEvar x a R = e.evalEvar R := Function.update_noteq hRx ..
      show _ ↔ tv ∧ Inh I (e.evalEvar R) m
      rw [← hu]
      exact this
    have hi : OwnInv c D I .ex ((KoreAML.inhOf (KoreAML.sym (.sort N))).interpret I e)
        ((KoreAML.inhOf (KoreAML.sym (.sort N))).interpret (extModel c D I) e') :=
      inv_app_hd (inv_inh fun hσ' => (hD _ hσ' : plainSym .inh)) (inv_sym (σ := .sort N) trivial hnD)
    refine ⟨∃ a, ∃ ha : Inh I σ a, Classical.choose (key a ha), fun m => ?_, fun y => ?_⟩
    · rw [interp_sExists' hI]
      constructor
      · rintro ⟨a, hs1, hp⟩
        have ha : Inh I σ a := (KoreAML.interp_inhOf_of (hS _)).mp hs1
        have := ((Classical.choose_spec (key a ha)).1 m).mp hp
        exact ⟨⟨a, ha, this.1⟩, this.2⟩
      · rintro ⟨⟨a, ha, ht⟩, hm⟩
        exact ⟨a, (KoreAML.interp_inhOf_of (hS _)).mpr ha, ((Classical.choose_spec (key a ha)).1 m).mpr ⟨ht, hm⟩⟩
    · rw [interp_sExists' (ext_defOK c D I)]
      constructor
      · rintro ⟨a', hs1, hp⟩
        cases a' with
        | inr na => exact absurd hs1 (hi.2 na)
        | inl a =>
          have ha : Inh I σ a := (KoreAML.interp_inhOf_of (hS e)).mp ((hi.1 a).mp hs1)
          have := ((Classical.choose_spec (key a ha)).2 y).mp hp
          exact ⟨⟨a, ha, this.1⟩, this.2⟩
      · rintro ⟨⟨a, ha, ht⟩, hy⟩
        exact ⟨.inl a, (hi.1 a).mpr ((KoreAML.interp_inhOf_of (hS e)).mpr ha),
          ((Classical.choose_spec (key a ha)).2 y).mpr ⟨ht, hy⟩⟩

/-- **Transfer of a sentence at its sort variable `R`**: the extension satisfies `π = ⊤_R`, under
the guards of `R` and of the variables of `G`, where the model does, for a model in which some
sort has an element. A variable of `G` has a sort outside `D`, which need not be a sort of `O`. -/
theorem transfer_R (hne : ∃ τ, IsSort I τ ∧ ∃ m, Inh I τ m) {G : List (EVar × String)}
    (hG : ∀ p ∈ G, ¬ D (.sort p.2)) (hR : R ∉ G.map (·.1)) {π : KoreAML.P} (hπ : RPred D O R G π)
    (h : I ⊧ᴵ KoreAML.guarded (KoreAML.sortGuard R :: memGs (G.map fun p => (p.1, KoreAML.sym (.sort p.2))))
      (π ≡ KoreAML.inhOf (.evar R))) :
    extModel c D I ⊧ᴵ KoreAML.guarded (KoreAML.sortGuard R :: memGs (G.map fun p => (p.1, KoreAML.sym (.sort p.2))))
      (π ≡ KoreAML.inhOf (.evar R)) := by
  generalize hgs : (G.map fun p => (p.1, KoreAML.sym (.sort p.2))) = gs at h ⊢
  have hfst : gs.map (·.1) = G.map (·.1) := by rw [← hgs, List.map_map]; rfl
  have hs : ∀ p ∈ gs, OwnSorted D [] [] .ex p.2 := fun p hp => by
    rw [← hgs] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact .sortC (hG q hq)
  intro e' pt
  rw [guarded_iff]
  intro hw
  have hwg : ∀ w ∈ memGs gs, w.interpret (extModel c D I) e' pt := fun w hw' => hw w (List.mem_cons_of_mem _ hw')
  cases hRv : e'.evalEvar R with
  | inl r =>
    have hold := guards_old hD hI hs hwg (pullVal e')
    have hval : ∀ x ∈ R :: gs.map (·.1), e'.evalEvar x = .inl ((pullVal e').evalEvar x) := fun x hx => by
      show _ = Sum.inl (match e'.evalEvar x with | .inl m => m | .inr _ => default)
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hRv]
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        obtain ⟨m, hm, _⟩ := hold p hp
        rw [hm]
    have hcls : OwnSorted D (R :: gs.map (·.1)) [] .pred (KoreAML.guarded (KoreAML.sortGuard R :: memGs gs)
        (π ≡ KoreAML.inhOf (.evar R))) := by
      refine .guarded (fun w hw' => ?_) (.inl rfl) (.equal_ex
        (hfst ▸ hπ.ownSorted (fun N hN => (hO N hN).1) hRt) (.inhOf (.evar (List.mem_cons_self ..))))
      rcases List.mem_cons.mp hw' with rfl | hw'
      · exact .member (List.mem_cons_self ..) .sorts
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw'
        exact .member (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
          (((hs p hp).mono nil_sub nil_sub).inhOf.toOld)
    have hinv := transfer_rel (c := c) hD hI hcls (pullVal e') e' ⟨hval, nil_sub⟩
    have hpt : (KoreAML.guarded (KoreAML.sortGuard R :: memGs gs)
        (π ≡ KoreAML.inhOf (.evar R))).interpret (extModel c D I) e' pt := by
      cases pt with
      | inl m => exact (hinv.1 m).mpr (h (pullVal e') m)
      | inr n => exact (hinv.2.2 n).mpr (h (pullVal e'))
    exact guarded_iff.mp hpt hw
  | inr n0 =>
    have hsg := hw _ (List.mem_cons_self ..)
    unfold KoreAML.sortGuard at hsg
    rw [KoreAML.interp_member (ext_defOK c D I), hRv] at hsg
    obtain ⟨n, rfl⟩ := sorts_new hsg
    obtain ⟨τ, hτ, m0, hm0⟩ := hne
    let e : Valuation M := ⟨fun x => if x = R then τ else (pullVal e').evalEvar x, (pullVal e').evalSvar⟩
    have heR : e.evalEvar R = τ := by show (if R = R then τ else _) = τ; simp
    have hold := guards_old hD hI hs hwg e
    have hval : ∀ p ∈ gs, e'.evalEvar p.1 = .inl (e.evalEvar p.1) := fun p hp => by
      have hne : p.1 ≠ R := fun hh => hR (hfst ▸ hh ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
      obtain ⟨m, hm, _⟩ := hold p hp
      show _ = Sum.inl (if p.1 = R then τ else match e'.evalEvar p.1 with | .inl m => m | .inr _ => default)
      simp only [hne, ↓reduceIte, hm]
    have hrel : OwnRel (G.map (·.1)) [] e e' :=
      ⟨fun x hx => by
        rw [← hfst] at hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        exact hval p hp, nil_sub⟩
    have hmem : ∀ p ∈ gs, (KoreAML.inhOf p.2).interpret I e (e.evalEvar p.1) := fun p hp => by
      obtain ⟨m1, hm1, hin⟩ := hold p hp
      have := hval p hp
      rw [hm1] at this
      rw [← Sum.inl.inj this]
      exact hin
    have hsorted : SortedAt I G e := fun q hq =>
      hmem (q.1, KoreAML.sym (.sort q.2)) (hgs ▸ List.mem_map.mpr ⟨q, hq, rfl⟩)
    obtain ⟨tv, h1, h2⟩ := rpred_inv hD hI hc hO hRt (n := n) hπ e e' hrel hsorted (heR ▸ hτ) hRv
    have hRσ : ∀ a, (Pattern.evar R : KoreAML.P).interpret I e a ↔ a = τ := fun a => by
      rw [KoreAML.interp_evar, heR]
    have hI1 := guarded_iff.mp (h e default) fun w hw' => by
      rcases List.mem_cons.mp hw' with rfl | hw'
      · unfold KoreAML.sortGuard
        rw [KoreAML.interp_member hI, KoreAML.interp_sortsDomain, heR]
        exact hτ
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw'
        rw [KoreAML.interp_member hI]
        exact hmem p hp
    rw [KoreAML.interp_equal hI] at hI1
    have htv : tv := ((h1 m0).mp ((hI1 m0).mpr ((KoreAML.interp_inhOf_of hRσ).mpr hm0))).1
    rw [KoreAML.interp_equal (ext_defOK c D I)]
    intro x
    rw [h2 x]
    exact ⟨fun hx => (KoreAML.interp_inhOf_of (σ := .inr (.srt n)) (fun a => by rw [KoreAML.interp_evar, hRv])).mpr
        (inh_new.mpr hx.2),
      fun hx => ⟨htv, inh_new.mp ((KoreAML.interp_inhOf_of (σ := .inr (.srt n))
        (fun a => by rw [KoreAML.interp_evar, hRv])).mp hx)⟩⟩

/-- The name of the sort of an element variable's key, for a sort without parameters. -/
def keySortName : KoreAML.VarKey → String
  | .evar _ (.ctor C _) => C.ident.name
  | _ => ""

omit hRt in
/-- **Transfer of the translation of a sentence `axiom{R} P`** whose pattern is at the sort `R`,
whose free variables have sort constants outside `D`, and whose translation is of the class `RPred`. -/
theorem transfer_trAxiom_R (hne : ∃ τ, IsSort I τ ∧ ∃ m, Inh I τ m) {P : Kore.Pattern}
    {attrs : List Kore.AppPattern} (i : Nat) (md : String)
    (hsort : KoreAML.sortOf [] P = some KoreAML.R)
    (hfree : ∀ key ∈ KoreAML.freeOf [] P, ∃ x C, key = .evar x (.ctor C []) ∧ ¬ D (.sort C.ident.name))
    (hπ : RPred D O ((KoreAML.tableOf [KoreAML.Rv] P).ev (.sortVar "R"))
      (((KoreAML.freeOf [] P).filter fun b => b != KoreAML.VarKey.sortVar "R").eraseDups.map fun key =>
        ((KoreAML.tableOf [KoreAML.Rv] P).ev key, keySortName key))
      (KoreAML.tr ⟨KoreAML.tableOf [KoreAML.Rv] P, []⟩ P))
    (h : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, md, { sortVars := [KoreAML.Rv], pattern := P, attributes := attrs }⟩).pat) :
    extModel c D I ⊧ᴵ
      (KoreAML.trAxiom [] [] ⟨i, md, { sortVars := [KoreAML.Rv], pattern := P, attributes := attrs }⟩).pat := by
  have ht0 : ∃ rest, KoreAML.tableOf [KoreAML.Rv] P = KoreAML.VarKey.sortVar "R" :: rest :=
    ⟨_, List.eraseDups_cons⟩
  generalize ht : KoreAML.tableOf [KoreAML.Rv] P = t at hπ ht0
  generalize hfr : KoreAML.freeOf [] P = fr at hfree hπ
  let Rk : KoreAML.VarKey := .sortVar "R"
  let fk : List KoreAML.VarKey := (fr.filter fun b => b != Rk).eraseDups
  let G : List (EVar × String) := fk.map fun key => (t.ev key, keySortName key)
  have hfk : ∀ key ∈ fk, key ∈ fr ∧ key ≠ Rk := fun key hk => by
    have := List.mem_filter.mp (List.mem_eraseDups.mp hk)
    exact ⟨this.1, by simpa using this.2⟩
  have hfreeEq : ([KoreAML.Rv].map KoreAML.sortVarKey ++ KoreAML.freeOf [] P).eraseDups = Rk :: fk := by
    rw [hfr]
    exact List.eraseDups_cons
  have hgs : fk.map (KoreAML.guardOf t) = memGs (G.map fun p => (p.1, KoreAML.sym (.sort p.2))) := by
    show fk.map (KoreAML.guardOf t) = ((fk.map fun key => (t.ev key, keySortName key)).map
      fun p => (p.1, KoreAML.sym (.sort p.2))).map fun p => p.1 ∈∈ KoreAML.inhOf p.2
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun key hk => ?_
    obtain ⟨x, C, rfl, _⟩ := hfree key (hfk key hk).1
    show (t.ev (.evar x (.ctor C [])) ∈∈ KoreAML.inhOf (KoreAML.trSort t (.ctor C []))) =
      (t.ev (.evar x (.ctor C [])) ∈∈ KoreAML.inhOf (KoreAML.sym (.sort C.ident.name)))
    rw [KoreAML.trSort_const]
  have hpat : (KoreAML.trAxiom [] [] ⟨i, md, { sortVars := [KoreAML.Rv], pattern := P, attributes := attrs }⟩).pat =
      KoreAML.guarded (KoreAML.sortGuard (t.ev Rk) :: memGs (G.map fun p => (p.1, KoreAML.sym (.sort p.2))))
        (KoreAML.tr ⟨t, []⟩ P ≡ KoreAML.inhOf (.evar (t.ev Rk))) := by
    unfold KoreAML.trAxiom
    simp only
    rw [ht, hfreeEq, List.map_cons, hgs, hsort]
    rfl
  have hR : t.ev Rk ∉ G.map (·.1) := by
    intro hmem
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hmem
    obtain ⟨key, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨rest, hrest⟩ := ht0
    have hne := (hfk key hk).2
    have h1 : t.idxOf key + 1 = t.idxOf Rk + 1 := congrArg EVar.val hpe
    rw [hrest] at h1
    have hne' : KoreAML.VarKey.sortVar "R" ≠ key := Ne.symm hne
    simp [List.idxOf_cons, hne', Rk] at h1
  have hG : ∀ p ∈ G, ¬ D (.sort p.2) := fun p hp => by
    obtain ⟨key, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨x, C, rfl, hC⟩ := hfree key (hfk key hk).1
    exact hC
  have hRt : t.ev Rk ≠ KoreAML.topVar := fun hh => by
    have := congrArg EVar.val hh
    simp [KoreAML.VarTable.ev, KoreAML.VarTable.index, KoreAML.topVar] at this
  rw [hpat] at h ⊢
  exact transfer_R hD hI hc hO hRt hne hG hR hπ h

end

end KCore.Cons
