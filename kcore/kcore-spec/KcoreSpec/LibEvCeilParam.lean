/-
  KCore, checked layer: a definedness lemma over set variables, of a parameter symbol and a
  function of Γ, is refuted at values under every interpretation.

  `ceilFnPat c s f g A B z₀` (KcoreSpec/LibEvCeilFn.lean) is the sentence
  `#Ceil(f(@A, @B)) => {g(@B, z₀) #Equals true} #And #Ceil(@A) #And #Ceil(@B)` at the sort `s`.
  Here `f` is a parameter symbol of the semantics, whose graph at values Γ states from the
  interpretation (`ΓDomains`, `Semantics.paramVal`: a value of `f`'s result sort, or ⊥), and `g` a
  function of Γ. Let `p` and `z` be values of `s` with `g(p, z₀) = true` and `g(z, z₀) = false`.
  - Where the interpretation gives `f` a value at `(p, p)`, the sentence fails at `@A = {p}`,
    `@B = {p, z}`: the left side holds, and `g(@B, z₀)` holds the element of `false`
    (`ceilPat_refuted_some`).
  - Where it gives none, the sentence fails at `@A = @B = {p}`: Γ states `f(p, p)` to be ⊥, so the
    left side does not hold, and the right side does (`ceilPat_refuted_none`); that valuation's
    set variables hold one element each (`SetVarsAtMostOne`).
  So in every model of `Γ c` the sentence fails at a valuation at values, whatever the
  interpretation gives `f` (`ceilParam_refuted_at`): no interpretation meets it. At sets of at most
  one value it fails under the interpretations that give `f` no value at `(p, p)`
  (`ceilParam_refuted_one`).

  The two cases are stated over what Γ entails of the two applications (`ceilPat_refuted_some`,
  `ceilPat_refuted_none`), whichever part of Γ states it.
-/
import KcoreSpec.LibEvCeilFn
import KcoreSpec.ParamSchema

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- An application of a symbol to two patterns, the first holding exactly the element of the value
`x` and the second what the value `y` denotes, holds what Γ's writing of the application at
`(x, y)` denotes. -/
theorem ceilApp_eq {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ c) (f : Sym) {x y : GroundTerm} {sx : Srt} (hx : c.sortOf x = some sx)
    (e : Valuation M) {P Q : KoreAML.P} (hP : ∀ b, P.interpret I e b ↔ b = elemOf c I x)
    (hQ : ∀ b, Q.interpret I e b ↔ (den c y).interpret I e b) (a : M) :
    ((symHead c f ⬝ P) ⬝ Q).interpret I e a ↔
      (KoreAML.den (symApp c f (GroundTerm.koreList c [x, y]))).interpret I e a := by
  rw [KoreAML.den, tr_symApp]
  simp only [GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil, KoreAML.interp_app,
    tr_ground_den, hP, hQ, (elemOf_spec hI hx e).1]

/-- **The sentence between its two sides, at a valuation at values.** In a model of `Γ c` there is
an element `τB`, Bool's sort, such that at every valuation sending the sort variables to `τB` and
each set variable to a set of elements of values of `s`: the valuation meets `AtValues` and
`SetVarsAtValues`, and where the sentence holds there its two sides hold the element of `true`
together. -/
theorem ceilPat_body {c : Semantics} (h : c.coreOK = true) (s : Srt) (f g : Sym)
    (A B : String) (z₀ : GroundTerm) (hs : s < nRegSorts + c.sortNames.length)
    (hfree : ceilFnFreeOK c s (KoreAML.freeOf [] (ceilFnPat c s f g A B z₀)) = true)
    (ad : KoreAML.AxiomDecl) (hpat : ad.ax.pattern = ceilFnPat c s f g A B z₀)
    (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v])
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) :
    ∃ τB : M, KoreAML.IsSort I τB ∧
      (∀ (tbl : KoreAML.VarTable) (e' : Valuation M) (b : M),
        (KoreAML.trSort tbl (srtOf c Srt.bool)).interpret I e' b ↔ b = τB) ∧
      ∀ (S : SVar → M → Prop),
      (∀ X m, S X m → ∃ v, c.sortOf v = some s ∧ m = elemOf c I v) →
      AtValues c I ⟨fun _ => τB, S⟩ ad.ax ∧ SetVarsAtValues c I ⟨fun _ => τB, S⟩ ad.ax ∧
      ((KoreAML.trAxiom [] [] ad).pat.interpret I ⟨fun _ => τB, S⟩ default →
        ((KoreAML.tr ⟨KoreAML.tableOf [KoreAML.Rv, Q0v] (ceilFnPat c s f g A B z₀), []⟩
            (.ceil (srtOf c s) Q0 (symApp c f [ceilFnVar c s A, ceilFnVar c s B]))).interpret I
              ⟨fun _ => τB, S⟩ (elemOf c I (KCore.bool true)) ↔
          (KoreAML.tr ⟨KoreAML.tableOf [KoreAML.Rv, Q0v] (ceilFnPat c s f g A B z₀), []⟩
            (.and Q0 [.and Q0 [.and Q0 [.equals (srtOf c Srt.bool) Q0
                (symApp c g [ceilFnVar c s B, z₀.kore c]) ((KCore.bool true).kore c),
              .ceil (srtOf c s) Q0 (ceilFnVar c s A)],
              .ceil (srtOf c s) Q0 (ceilFnVar c s B)], .top Q0])).interpret I
              ⟨fun _ => τB, S⟩ (elemOf c I (KCore.bool true)))) := by
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨τ, hτS, hτ⟩ := srt_den hI hs
  obtain ⟨τB, hτBS, hτB⟩ := srt_den hI (s := Srt.bool) (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _))
  have hfree' : ∀ k ∈ KoreAML.freeOf [] (ceilFnPat c s f g A B z₀),
      (∃ n, k = .svar n (srtOf c s)) ∨ ∃ n, k = .sortVar n := by
    intro k hk
    have := List.all_eq_true.mp hfree k hk
    cases k with
    | svar n s' =>
      simp only [decide_eq_true_eq] at this
      exact Or.inl ⟨n, by rw [this]⟩
    | evar n s' => simp at this
    | sortVar n => exact Or.inr ⟨n, rfl⟩
  obtain ⟨idx, md, ⟨svs, pat, attrs⟩⟩ := ad
  simp only at hpat hsv
  subst hpat hsv
  refine ⟨τB, hτBS, hτB, fun S hvals => ⟨?_, ?_, ?_⟩⟩
  · intro n s' hk
    rcases hfree' _ (List.mem_eraseDups.mp hk) with ⟨_, h'⟩ | ⟨_, h'⟩ <;> cases h'
  · intro n s' hk m hm
    rcases hfree' _ (List.mem_eraseDups.mp hk) with ⟨_, h'⟩ | ⟨_, h'⟩
    · injection h' with h1 h2
      subst h2
      obtain ⟨v, hv, rfl⟩ := hvals _ m hm
      exact ⟨v, s, rfl, hv, ((elemOf_spec hI hv _).1 _).mpr rfl⟩
    · cases h'
  · intro hax
    let e : Valuation M := ⟨fun _ => τB, S⟩
    have hinh : ∀ (v : GroundTerm) (S' : Srt), c.sortOf v = some S' → ∀ σ : M,
        (∀ (tbl : KoreAML.VarTable) (e' : Valuation M) (b : M),
          (KoreAML.trSort tbl (srtOf c S')).interpret I e' b ↔ b = σ) →
        KoreAML.Inh I σ (elemOf c I v) := fun v S' hv σ hσ => by
      refine (KoreAML.interp_inhOf_of (e := KoreAML.val0) (fun b => ?_)).mp (elemOf_spec hI hv KoreAML.val0).2
      have := hσ [] KoreAML.val0 b
      rwa [trSort_srtOf_twoT] at this
    unfold KoreAML.trAxiom at hax
    dsimp only at hax
    rw [interpret_impl] at hax
    have hgd := hax (KoreAML.interp_conjList fun w hw => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
      have hk' := List.mem_eraseDups.mp hk
      have hfk : k ∈ KoreAML.freeOf [] (ceilFnPat c s f g A B z₀) → (∃ n, k = .svar n (srtOf c s)) ∨
          ∃ n, k = .sortVar n := hfree' k
      cases k with
      | sortVar n => exact (KoreAML.interp_guard_sortVar hD).mpr hτBS
      | evar n s' =>
        exfalso
        rcases List.mem_append.mp hk' with hs' | hf'
        · obtain ⟨_, -, hx⟩ := List.mem_map.mp hs'; cases hx
        · rcases hfk hf' with ⟨_, h'⟩ | ⟨_, h'⟩ <;> cases h'
      | svar n s' =>
        have hf' : KoreAML.VarKey.svar n s' ∈ KoreAML.freeOf [] (ceilFnPat c s f g A B z₀) := by
          rcases List.mem_append.mp hk' with hs' | hf'
          · obtain ⟨_, -, hx⟩ := List.mem_map.mp hs'; cases hx
          · exact hf'
        have hs'' : s' = srtOf c s := by
          rcases hfk hf' with ⟨_, h'⟩ | ⟨_, h'⟩
          · injection h'
          · cases h'
        unfold KoreAML.guardOf
        refine (KoreAML.interp_included hD).mpr fun a ha => ?_
        obtain ⟨v, hv, rfl⟩ := hvals _ a ha
        rw [hs'', trSort_srtOf_twoT]
        exact (elemOf_spec hI hv e).2)
    rw [KoreAML.interp_equal hD] at hgd
    have hRv : ∀ (t : KoreAML.VarTable) b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = τB :=
      fun t b => by rw [trSort_R, KoreAML.interp_evar]
    have hQv : ∀ (t : KoreAML.VarTable) b, (KoreAML.trSort t Q0).interpret I e b ↔ b = τB :=
      fun t b => by rw [trSort_Q0, KoreAML.interp_evar]
    have hbool : c.sortOf (KCore.bool true) = some Srt.bool := rfl
    have ha : KoreAML.Inh I τB (elemOf c I (KCore.bool true)) := hinh _ _ hbool τB hτB
    have hpat := (hgd (elemOf c I (KCore.bool true))).mpr (by
      simp only [ceilFnPat, KoreAML.sortOf]
      exact (KoreAML.interp_inhOf_of (hRv _)).mpr ha)
    unfold ceilFnPat at hpat
    rw [KoreAML.tr, KoreAML.interp_sImp, KoreAML.interp_inhOf_of (hRv _), KoreAML.tr,
      KoreAML.interp_sTop hD (by rw [trSort_R]; simp [Pattern.isFreeEvar]; exact fun hh => ev_ne_top hh.symm),
      KoreAML.interp_inhOf_of (hRv _), KoreAML.tr, KoreAML.interp_sEquals hD hc (hQv _) (hRv _) hτBS hτBS] at hpat
    obtain ⟨-, himp⟩ := hpat
    obtain ⟨-, hall⟩ := himp ha
    exact hall _ ha

/-- The element of a value of the sort `S'` inhabits the element the sort denotes. -/
theorem ceilPat_inh {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ c) (v : GroundTerm) (S' : Srt) (hv : c.sortOf v = some S') (σ : M)
    (hσ : ∀ (tbl : KoreAML.VarTable) (e' : Valuation M) (b : M),
      (KoreAML.trSort tbl (srtOf c S')).interpret I e' b ↔ b = σ) :
    KoreAML.Inh I σ (elemOf c I v) := by
  refine (KoreAML.interp_inhOf_of (e := KoreAML.val0) (fun b => ?_)).mp (elemOf_spec hI hv KoreAML.val0).2
  have := hσ [] KoreAML.val0 b
  rwa [trSort_srtOf_twoT] at this

/-- **Refuted where the application has a value**: where Γ entails that `f(p, q)` is the value `r`
and that `g(z, z₀)` is `false`, in every model of `Γ c` the sentence fails at the valuation sending
`@A` to the element of `p` and `@B` to the elements of `q` and `z`. -/
theorem ceilPat_refuted_some {c : Semantics} (h : c.coreOK = true) (s : Srt) (f g : Sym)
    (A B : String) (z₀ : GroundTerm) (hs : s < nRegSorts + c.sortNames.length)
    (hfree : ceilFnFreeOK c s (KoreAML.freeOf [] (ceilFnPat c s f g A B z₀)) = true)
    (p q z r : GroundTerm) (hp : c.sortOf p = some s) (hq : c.sortOf q = some s)
    (hz : c.sortOf z = some s) (hr : c.sortOf r = some s)
    (sf : Γ c ⊧ (KoreAML.den (symApp c f (GroundTerm.koreList c [p, q])) ≡ den c r))
    (sg : Γ c ⊧ (KoreAML.den (symApp c g (GroundTerm.koreList c [z, z₀])) ≡ den c (KCore.bool false)))
    (ad : KoreAML.AxiomDecl) (hpat : ad.ax.pattern = ceilFnPat c s f g A B z₀)
    (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v])
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) :
    ∃ e : Valuation M, AtValues c I e ad.ax ∧ SetVarsAtValues c I e ad.ax ∧
      ¬ (KoreAML.trAxiom [] [] ad).pat.interpret I e default := by
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨hok', hfa, -, -, hids⟩ := Semantics.coreOK_parts h
  obtain ⟨-, hgw, -⟩ := faithCoreOK_parts hfa
  obtain ⟨τ, hτS, hτ⟩ := srt_den hI hs
  obtain ⟨τB, hτBS, hτB, hbody⟩ := ceilPat_body h s f g A B z₀ hs hfree ad hpat hsv hI
  let T := KoreAML.tableOf [KoreAML.Rv, Q0v] (ceilFnPat c s f g A B z₀)
  let kA : KoreAML.VarKey := .svar A (srtOf c s)
  let kB : KoreAML.VarKey := .svar B (srtOf c s)
  let S : SVar → M → Prop := fun X m => (X = T.sv kA ∧ m = elemOf c I p) ∨
    (X = T.sv kB ∧ (m = elemOf c I q ∨ m = elemOf c I z))
  obtain ⟨hat, hsvv, hbd⟩ := hbody S (by
    rintro X m (⟨-, rfl⟩ | ⟨-, rfl | rfl⟩)
    · exact ⟨p, hp, rfl⟩
    · exact ⟨q, hq, rfl⟩
    · exact ⟨z, hz, rfl⟩)
  refine ⟨⟨fun _ => τB, S⟩, hat, hsvv, fun hax => ?_⟩
  let e : Valuation M := ⟨fun _ => τB, S⟩
  have hiff := hbd hax
  have hQv : ∀ (t : KoreAML.VarTable) b, (KoreAML.trSort t Q0).interpret I e b ↔ b = τB :=
    fun t b => by rw [trSort_Q0, KoreAML.interp_evar]
  have hbool : c.sortOf (KCore.bool true) = some Srt.bool := rfl
  have hbf : c.sortOf (KCore.bool false) = some Srt.bool := rfl
  have ha : KoreAML.Inh I τB (elemOf c I (KCore.bool true)) := ceilPat_inh hI _ _ hbool τB hτB
  -- the left side holds: `f(@A, @B)` holds the element of `r`
  have hL : (KoreAML.tr ⟨T, []⟩ (.ceil (srtOf c s) Q0 (symApp c f [ceilFnVar c s A, ceilFnVar c s B]))).interpret
      I e (elemOf c I (KCore.bool true)) := by
    rw [KoreAML.tr, KoreAML.interp_sCeil_raw]
    refine ⟨τ, τB, elemOf c I r, (hτ _ e τ).mpr rfl, (hQv _ τB).mpr rfl, ?_,
      (KoreAML.ceilE_of hD hc hτS hτBS (ceilPat_inh hI r s hr τ hτ) _).mpr ha⟩
    rw [tr_symApp, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
    have ef := ((KoreAML.interp_equal hD).mp (sf hI e default) (elemOf c I r)).mpr
      (((elemOf_spec hI hr e).1 _).mpr rfl)
    rw [KoreAML.den, tr_symApp] at ef
    simp only [GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil, KoreAML.interp_app,
      tr_ground_den] at ef
    obtain ⟨a', b, ⟨h0, x', hh0, hx', hhx⟩, hb, hab⟩ := ef
    rw [((elemOf_spec hI hp e).1 x').mp hx'] at hhx
    rw [KoreAML.interp_app]
    exact ⟨a', b, KoreAML.interp_app.mpr ⟨h0, _, hh0, Or.inl ⟨rfl, rfl⟩, hhx⟩,
      Or.inr ⟨rfl, Or.inl (((elemOf_spec hI hq e).1 b).mp hb)⟩, hab⟩
  have hR := hiff.mp hL
  -- the right side does not: `g(@B, z₀)` holds the element of `false`
  simp only [KoreAML.tr, KoreAML.trAndList, KoreAML.interp_sAnd] at hR
  obtain ⟨⟨⟨hEq, -⟩, -⟩, -⟩ := hR
  rw [KoreAML.interp_sEquals hD hc (hτB _ e) (hQv _) hτBS hτBS] at hEq
  obtain ⟨-, hgall⟩ := hEq
  have hgf := (hgall (elemOf c I (KCore.bool false)) (ceilPat_inh hI _ _ hbf τB hτB)).mp (by
    rw [tr_symApp, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil, tr_ground_den]
    have eg := ((KoreAML.interp_equal hD).mp (sg hI e default) (elemOf c I (KCore.bool false))).mpr
      (((elemOf_spec hI hbf e).1 _).mpr rfl)
    rw [KoreAML.den, tr_symApp] at eg
    simp only [GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil, KoreAML.interp_app,
      tr_ground_den] at eg
    obtain ⟨a', b, ⟨h0, x', hh0, hx', hhx⟩, hb, hab⟩ := eg
    rw [((elemOf_spec hI hz e).1 x').mp hx'] at hhx
    rw [KoreAML.interp_app]
    exact ⟨a', b, KoreAML.interp_app.mpr ⟨h0, _, hh0, Or.inr ⟨rfl, Or.inr rfl⟩, hhx⟩, hb, hab⟩)
  rw [tr_ground_den] at hgf
  have hft := ((elemOf_spec hI hbool e).1 _).mp hgf
  exact Bool.false_ne_true (fq_bool_inj (values_apart hI hgw (NamesApart.subsorts_trans_of hids hok')
    (apart_of_distinct bool_distinct) hbf hbool hft))

/-- **Refuted where the application has no value**: where Γ entails that `f(p, p)` is ⊥ and that
`g(p, z₀)` is `true`, in every model of `Γ c` the sentence fails at the valuation sending `@A` and
`@B` to the element of `p`: the left side does not hold, and the right side does. Each set
variable holds one element there. -/
theorem ceilPat_refuted_none {c : Semantics} (h : c.coreOK = true) (s : Srt) (f g : Sym)
    (A B : String) (z₀ : GroundTerm) (hs : s < nRegSorts + c.sortNames.length)
    (hfree : ceilFnFreeOK c s (KoreAML.freeOf [] (ceilFnPat c s f g A B z₀)) = true)
    (p : GroundTerm) (hp : c.sortOf p = some s)
    (sf : Γ c ⊧ (KoreAML.den (symApp c f (GroundTerm.koreList c [p, p])) ≡ ⊥))
    (sg : Γ c ⊧ (KoreAML.den (symApp c g (GroundTerm.koreList c [p, z₀])) ≡ den c (KCore.bool true)))
    (ad : KoreAML.AxiomDecl) (hpat : ad.ax.pattern = ceilFnPat c s f g A B z₀)
    (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v])
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) :
    ∃ e : Valuation M, AtValues c I e ad.ax ∧ SetVarsAtValues c I e ad.ax ∧ SetVarsAtMostOne e ad.ax ∧
      ¬ (KoreAML.trAxiom [] [] ad).pat.interpret I e default := by
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨τ, hτS, hτ⟩ := srt_den hI hs
  obtain ⟨τB, hτBS, hτB, hbody⟩ := ceilPat_body h s f g A B z₀ hs hfree ad hpat hsv hI
  let T := KoreAML.tableOf [KoreAML.Rv, Q0v] (ceilFnPat c s f g A B z₀)
  let S : SVar → M → Prop := fun _ m => m = elemOf c I p
  obtain ⟨hat, hsvv, hbd⟩ := hbody S (fun X m hm => ⟨p, hp, hm⟩)
  refine ⟨⟨fun _ => τB, S⟩, hat, hsvv, fun _ _ _ m m' hm hm' => hm.trans hm'.symm, fun hax => ?_⟩
  let e : Valuation M := ⟨fun _ => τB, S⟩
  have hiff := hbd hax
  have hQv : ∀ (t : KoreAML.VarTable) b, (KoreAML.trSort t Q0).interpret I e b ↔ b = τB :=
    fun t b => by rw [trSort_Q0, KoreAML.interp_evar]
  have hbool : c.sortOf (KCore.bool true) = some Srt.bool := rfl
  have ha : KoreAML.Inh I τB (elemOf c I (KCore.bool true)) := ceilPat_inh hI _ _ hbool τB hτB
  have hvar : ∀ (n : String) b, (KoreAML.tr ⟨T, []⟩ (ceilFnVar c s n)).interpret I e b ↔ b = elemOf c I p :=
    fun n b => Iff.rfl
  have hceil : ∀ n : String, (KoreAML.tr ⟨T, []⟩ (.ceil (srtOf c s) Q0 (ceilFnVar c s n))).interpret I e
      (elemOf c I (KCore.bool true)) := fun n => by
    rw [KoreAML.tr, KoreAML.interp_sCeil_raw]
    exact ⟨τ, τB, elemOf c I p, (hτ _ e τ).mpr rfl, (hQv _ τB).mpr rfl, (hvar n _).mpr rfl,
      (KoreAML.ceilE_of hD hc hτS hτBS (ceilPat_inh hI p s hp τ hτ) _).mpr ha⟩
  -- the right side holds
  have hR : (KoreAML.tr ⟨T, []⟩
      (.and Q0 [.and Q0 [.and Q0 [.equals (srtOf c Srt.bool) Q0
          (symApp c g [ceilFnVar c s B, z₀.kore c]) ((KCore.bool true).kore c),
        .ceil (srtOf c s) Q0 (ceilFnVar c s A)],
        .ceil (srtOf c s) Q0 (ceilFnVar c s B)], .top Q0])).interpret I e (elemOf c I (KCore.bool true)) := by
    simp only [KoreAML.tr, KoreAML.trAndList, KoreAML.interp_sAnd]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [KoreAML.interp_sEquals hD hc (hτB _ e) (hQv _) hτBS hτBS]
      refine ⟨ha, fun a _ => ?_⟩
      rw [tr_symApp, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil, tr_ground_den, tr_ground_den,
        ceilApp_eq hI g hp e (hvar B) (fun _ => Iff.rfl) a]
      exact (KoreAML.interp_equal hD).mp (sg hI e default) a
    · have := hceil A
      rwa [KoreAML.tr] at this
    · have := hceil B
      rwa [KoreAML.tr] at this
    · rw [KoreAML.interp_sTop hD (by rw [trSort_Q0]; simp [Pattern.isFreeEvar]; exact fun hh => ev_ne_top hh.symm)]
      exact (KoreAML.interp_inhOf_of (hQv _)).mpr ha
  -- the left side does not: Γ states `f(p, p)` to be ⊥
  have hL := hiff.mpr hR
  rw [KoreAML.tr, KoreAML.interp_sCeil_raw] at hL
  obtain ⟨-, -, x, -, -, hx, -⟩ := hL
  rw [tr_symApp, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil,
    ceilApp_eq hI f hp e (hvar A) (fun b => by rw [hvar B b, (elemOf_spec hI hp e).1 b]) x] at hx
  exact ((KoreAML.interp_equal hD).mp (sf hI e default) x).mp hx

/-! ## At a parameter symbol -/

/-- Γ's statement of a parameter's graph at values (`ΓDomains`), by the parameter's number. -/
theorem ceilParam_graph {c : Semantics} {f : Sym} {k : ParamSig} (hk : c.lookupParam f = some k)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.sig.args) :
    Γ c ⊧ (KoreAML.den (symApp c f (GroundTerm.koreList c vs)) ≡ (match c.paramVal f vs with
      | some v => den c v
      | none => ⊥)) := by
  have hmem : k ∈ c.params := by
    rw [Semantics.lookupParam_eq] at hk; exact List.mem_of_find?_eq_some hk
  have hname : k.sig.name = f := by
    rw [Semantics.lookupParam_eq] at hk
    exact beq_iff_eq.mp (List.find?_some (p := fun (x : ParamSig) => x.sig.name == f) hk)
  intro M _ I hI
  have := hI _ (ParamSchema.gamma_param c hmem hvs)
  rwa [hname] at this

/-- **The sentence at a parameter symbol is refuted at values, whatever the interpretation gives
the parameter.** `f` is a parameter symbol of the sort `s` at two arguments of `s`, `g` a function
of Γ that `Eval` gives `true` at `(p, z₀)` and `false` at `(z, z₀)`. In every model of `Γ c` the
sentence fails at a valuation at values: at `@A = {p}`, `@B = {p, z}` where the interpretation
gives `f(p, p)` a value, at `@A = @B = {p}` where it gives none. -/
theorem ceilParam_refuted_at {c : Semantics} (h : c.coreOK = true) (hok : c.ok = true) (s : Srt) (f g : Sym)
    (A B : String) (z₀ : GroundTerm) (hs : s < nRegSorts + c.sortNames.length)
    (hfree : ceilFnFreeOK c s (KoreAML.freeOf [] (ceilFnPat c s f g A B z₀)) = true)
    {k : ParamSig} {gn : Fn} (hk : c.lookupParam f = some k) (hres : k.sig.result = s)
    (hgn : c.lookupFn g = some gn)
    (p z : GroundTerm) (hp : c.sortOf p = some s) (hz : c.sortOf z = some s)
    (hpp : c.sortsOf [p, p] = some k.sig.args)
    (hpz : c.sortsOf [p, z₀] = some gn.args) (hgt : Eval c g [p, z₀] (some (bool true)))
    (hzz : c.sortsOf [z, z₀] = some gn.args) (hgf : Eval c g [z, z₀] (some (bool false)))
    (ad : KoreAML.AxiomDecl) (hpat : ad.ax.pattern = ceilFnPat c s f g A B z₀)
    (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v])
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) :
    ∃ e : Valuation M, AtValues c I e ad.ax ∧ SetVarsAtValues c I e ad.ax ∧
      ¬ (KoreAML.trAxiom [] [] ad).pat.interpret I e default := by
  have hsound : ∀ {vs : List GroundTerm} {v : GroundTerm}, c.sortsOf vs = some gn.args →
      Eval c g vs (some v) → Γ c ⊧ (KoreAML.den (symApp c g (GroundTerm.koreList c vs)) ≡ den c v) :=
    fun hvs hE => TiePair.eval_some_sound c (Semantics.preTop_of_okAll (Semantics.okAll_of_ok hok))
      (hypSound_of_core h) (Semantics.ok_clauseBinds hok) hE hgn hvs
  have sf : Γ c ⊧ (KoreAML.den (symApp c f (GroundTerm.koreList c [p, p])) ≡ (match c.paramVal f [p, p] with
      | some v => den c v
      | none => ⊥)) := ceilParam_graph hk hpp
  cases hv : c.paramVal f [p, p] with
  | some r =>
    rw [hv] at sf
    obtain ⟨k', hk', hr⟩ := Semantics.paramVal_sorted c hv
    rw [hk, Option.some.injEq] at hk'
    subst hk'
    exact ceilPat_refuted_some h s f g A B z₀ hs hfree p p z r hp hp hz (hr.trans (congrArg some hres)) sf
      (hsound hzz hgf) ad hpat hsv hI
  | none =>
    rw [hv] at sf
    obtain ⟨e, h1, h2, -, h3⟩ := ceilPat_refuted_none h s f g A B z₀ hs hfree p hp sf (hsound hpz hgt) ad hpat hsv hI
    exact ⟨e, h1, h2, h3⟩

/-- **At sets of at most one value the sentence fails where the interpretation gives the parameter
no value at `(p, p)`**, for `p` with `g(p, z₀) = true`: there the sentence asks `f(p, p)` to have a
value. So at such sets the sentence is a condition on the interpretation. -/
theorem ceilParam_refuted_one {c : Semantics} (h : c.coreOK = true) (hok : c.ok = true) (s : Srt) (f g : Sym)
    (A B : String) (z₀ : GroundTerm) (hs : s < nRegSorts + c.sortNames.length)
    (hfree : ceilFnFreeOK c s (KoreAML.freeOf [] (ceilFnPat c s f g A B z₀)) = true)
    {k : ParamSig} {gn : Fn} (hk : c.lookupParam f = some k) (hgn : c.lookupFn g = some gn)
    (p : GroundTerm) (hp : c.sortOf p = some s) (hpp : c.sortsOf [p, p] = some k.sig.args)
    (hpz : c.sortsOf [p, z₀] = some gn.args) (hgt : Eval c g [p, z₀] (some (bool true)))
    (hnone : c.paramVal f [p, p] = none)
    (ad : KoreAML.AxiomDecl) (hpat : ad.ax.pattern = ceilFnPat c s f g A B z₀)
    (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v])
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) :
    ∃ e : Valuation M, AtValues c I e ad.ax ∧ SetVarsAtValues c I e ad.ax ∧ SetVarsAtMostOne e ad.ax ∧
      ¬ (KoreAML.trAxiom [] [] ad).pat.interpret I e default := by
  have sf : Γ c ⊧ (KoreAML.den (symApp c f (GroundTerm.koreList c [p, p])) ≡ (match c.paramVal f [p, p] with
      | some v => den c v
      | none => ⊥)) := ceilParam_graph hk hpp
  rw [hnone] at sf
  exact ceilPat_refuted_none h s f g A B z₀ hs hfree p hp sf
    (TiePair.eval_some_sound c (Semantics.preTop_of_okAll (Semantics.okAll_of_ok hok))
      (hypSound_of_core h) (Semantics.ok_clauseBinds hok) hgt hgn hpz) ad hpat hsv hI

end LibEv

end KCore
