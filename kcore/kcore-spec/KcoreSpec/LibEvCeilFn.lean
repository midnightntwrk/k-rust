/-
  KCore, checked layer: a definedness lemma over set variables, of two functions of Γ, is refuted
  at values.

  `ceilFnPat c s f g A B z₀` is the sentence
  `#Ceil(f(@A, @B)) => {g(@B, z₀) #Equals true} #And #Ceil(@A) #And #Ceil(@B)` at the sort `s`, as
  kompile writes it, where `f` and `g` are functions of Γ with equations (not registry hooks, which
  `ceilIntEqn` of KcoreSpec/LibEvCeil.lean covers) and `z₀` is a value. `ceilFn_refuted_at`: where
  `Eval` gives `f` a value at `(p, q)` and gives `g` the value `false` at `(z, z₀)`, in every model
  of `Γ c` the sentence fails at a valuation sending `@A` to the element of `p` and `@B` to the
  elements of `q` and `z` (`AtValues`, `SetVarsAtValues`): the left side holds, and `g(@B, z₀)`
  holds the element of `false`, which the right side's `true` does not. The values `Eval` gives are
  theorems of Γ (`TiePair.eval_some_sound`); no hypothesis reads what Γ leaves open.
-/
import KcoreSpec.LibEvCeil
import KcoreSpec.TiePairs

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- The set variable `@n` of the sort `s`. -/
def ceilFnVar (c : Semantics) (s : Srt) (n : String) : Kore.Pattern :=
  .var (.svar ⟨⟨⟨n⟩⟩, srtOf c s⟩)

/-- `#Ceil(f(@A, @B)) => {g(@B, z₀) #Equals true} #And #Ceil(@A) #And #Ceil(@B)` at the sort `s`,
as kompile writes the sentence over the sort variables `R`, `Q0`, with the names Γ gives `f`, `g`,
`s`, Bool, `z₀` and `true`. -/
def ceilFnPat (c : Semantics) (s : Srt) (f g : Sym) (A B : String) (z₀ : GroundTerm) : Kore.Pattern :=
  .implies KoreAML.R (.top KoreAML.R)
    (.equals Q0 KoreAML.R (.ceil (srtOf c s) Q0 (symApp c f [ceilFnVar c s A, ceilFnVar c s B]))
      (.and Q0 [.and Q0 [.and Q0 [.equals (srtOf c Srt.bool) Q0 (symApp c g [ceilFnVar c s B, z₀.kore c])
          ((KCore.bool true).kore c), .ceil (srtOf c s) Q0 (ceilFnVar c s A)],
        .ceil (srtOf c s) Q0 (ceilFnVar c s B)], .top Q0]))

/-- The free variables `ks` are set variables of the sort `s` and sort variables. -/
def ceilFnFreeOK (c : Semantics) (s : Srt) (ks : List KoreAML.VarKey) : Bool :=
  ks.all fun k => match k with
    | .svar _ s' => decide (s' = srtOf c s)
    | .evar _ _ => false
    | .sortVar _ => true

/-- An application of a function of Γ to two set variables holds, at a valuation whose
variables hold the elements of `x` and `y`, the element of what `Eval` gives the function there. -/
theorem ceilFn_app {c : Semantics} (h : c.coreOK = true) (hok : c.ok = true) {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn)
    {x y v : GroundTerm} {sx sv : Srt} (hx : c.sortOf x = some sx)
    (hv : c.sortOf v = some sv) (hxy : c.sortsOf [x, y] = some fn.args) (hE : Eval c f [x, y] (some v))
    (e : Valuation M) {P Q : KoreAML.P}
    (hP : P.interpret I e (elemOf c I x)) (hQ : ∀ b, (den c y).interpret I e b → Q.interpret I e b) :
    ((symHead c f ⬝ P) ⬝ Q).interpret I e (elemOf c I v) := by
  have hD := defOK hI
  have sf : Γ c ⊧ (KoreAML.den (symApp c f (GroundTerm.koreList c [x, y])) ≡ den c v) :=
    TiePair.eval_some_sound c (Semantics.preTop_of_okAll (Semantics.okAll_of_ok hok))
    (hypSound_of_core h) (Semantics.ok_clauseBinds hok) hE hfn hxy
  have ef := ((KoreAML.interp_equal hD).mp (sf hI e default) (elemOf c I v)).mpr
    (((elemOf_spec hI hv e).1 _).mpr rfl)
  rw [KoreAML.den, tr_symApp] at ef
  simp only [GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil, KoreAML.interp_app,
    tr_ground_den] at ef
  obtain ⟨a', b, ⟨h0, x', hh0, hx', hhx⟩, hb, hab⟩ := ef
  rw [((elemOf_spec hI hx e).1 x').mp hx'] at hhx
  rw [KoreAML.interp_app]
  exact ⟨a', b, KoreAML.interp_app.mpr ⟨h0, _, hh0, hP, hhx⟩, hQ b hb, hab⟩

/-- **The lemma is refuted at values, for functions of Γ**: where `Eval` gives `f` a value `r` at
`(p, q)` and gives `g` the value `false` at `(z, z₀)`, in every model of `Γ c` the sentence fails
at the valuation sending `@A` to the element of `p` and `@B` to the elements of `q` and `z` (and
the sort variables to Bool's sort): the left side holds, and `g(@B, z₀)` holds the element of
`false`, which `true` does not. -/
theorem ceilFn_refuted_at {c : Semantics} (h : c.coreOK = true) (hok : c.ok = true) (s : Srt) (f g : Sym)
    (A B : String) (z₀ : GroundTerm) (hs : s < nRegSorts + c.sortNames.length)
    (hfree : ceilFnFreeOK c s (KoreAML.freeOf [] (ceilFnPat c s f g A B z₀)) = true)
    {fn gn : Fn} (hfn : c.lookupFn f = some fn) (hgn : c.lookupFn g = some gn)
    (p q z r : GroundTerm) (hp : c.sortOf p = some s) (hq : c.sortOf q = some s)
    (hz : c.sortOf z = some s) (hr : c.sortOf r = some s)
    (hpq : c.sortsOf [p, q] = some fn.args) (hf : Eval c f [p, q] (some r))
    (hzz : c.sortsOf [z, z₀] = some gn.args) (hg : Eval c g [z, z₀] (some (bool false)))
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
  obtain ⟨τB, hτBS, hτB⟩ := srt_den hI (s := Srt.bool) (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _))
  have hinh : ∀ (v : GroundTerm) (S : Srt), c.sortOf v = some S → ∀ σ : M,
      (∀ (tbl : KoreAML.VarTable) (e' : Valuation M) (b : M),
        (KoreAML.trSort tbl (srtOf c S)).interpret I e' b ↔ b = σ) →
      KoreAML.Inh I σ (elemOf c I v) := fun v S hv σ hσ => by
    refine (KoreAML.interp_inhOf_of (e := KoreAML.val0) (fun b => ?_)).mp (elemOf_spec hI hv KoreAML.val0).2
    have := hσ [] KoreAML.val0 b
    rwa [trSort_srtOf_twoT] at this
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
  let T := KoreAML.tableOf [KoreAML.Rv, Q0v] (ceilFnPat c s f g A B z₀)
  let kA : KoreAML.VarKey := .svar A (srtOf c s)
  let kB : KoreAML.VarKey := .svar B (srtOf c s)
  let e : Valuation M := ⟨fun _ => τB, fun X m => (X = T.sv kA ∧ m = elemOf c I p) ∨
    (X = T.sv kB ∧ (m = elemOf c I q ∨ m = elemOf c I z))⟩
  have hvals : ∀ X m, e.evalSvar X m → ∃ v, c.sortOf v = some s ∧ m = elemOf c I v := by
    rintro X m (⟨-, rfl⟩ | ⟨-, rfl | rfl⟩)
    · exact ⟨p, hp, rfl⟩
    · exact ⟨q, hq, rfl⟩
    · exact ⟨z, hz, rfl⟩
  refine ⟨e, ?_, ?_, ?_⟩
  · intro n s' hk
    rcases hfree' _ (List.mem_eraseDups.mp hk) with ⟨_, h'⟩ | ⟨_, h'⟩ <;> cases h'
  · intro n s' hk m hm
    rcases hfree' _ (List.mem_eraseDups.mp hk) with ⟨_, h'⟩ | ⟨_, h'⟩
    · injection h' with h1 h2
      subst h2
      obtain ⟨v, hv, rfl⟩ := hvals _ m hm
      exact ⟨v, s, rfl, hv, ((elemOf_spec hI hv e).1 _).mpr rfl⟩
    · cases h'
  · intro hax
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
    have hiff := hall _ ha
    -- the left side holds: `f(@A, @B)` holds the element of `r`
    have hL : (KoreAML.tr ⟨T, []⟩ (.ceil (srtOf c s) Q0 (symApp c f [ceilFnVar c s A, ceilFnVar c s B]))).interpret
        I e (elemOf c I (KCore.bool true)) := by
      rw [KoreAML.tr, KoreAML.interp_sCeil_raw]
      refine ⟨τ, τB, elemOf c I r, (hτ _ e τ).mpr rfl, (hQv _ τB).mpr rfl, ?_,
        (KoreAML.ceilE_of hD hc hτS hτBS (hinh r s hr τ hτ) _).mpr ha⟩
      rw [tr_symApp, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
      exact ceilFn_app h hok hI hfn hp hr hpq hf e (Or.inl ⟨rfl, rfl⟩)
        (fun b hb => Or.inr ⟨rfl, Or.inl (((elemOf_spec hI hq e).1 b).mp hb)⟩)
    have hR := hiff.mp hL
    -- the right side does not: `g(@B, z₀)` holds the element of `false`
    simp only [KoreAML.tr, KoreAML.trAndList, KoreAML.interp_sAnd] at hR
    obtain ⟨⟨⟨hEq, -⟩, -⟩, -⟩ := hR
    rw [KoreAML.interp_sEquals hD hc (hτB _ e) (hQv _) hτBS hτBS] at hEq
    obtain ⟨-, hgall⟩ := hEq
    have hbf : c.sortOf (KCore.bool false) = some Srt.bool := rfl
    have hgf := (hgall (elemOf c I (KCore.bool false)) (hinh _ _ hbf τB hτB)).mp (by
      rw [tr_symApp, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil, tr_ground_den]
      exact ceilFn_app h hok hI hgn hz hbf hzz hg e (Or.inr ⟨rfl, Or.inr rfl⟩) (fun b hb => hb))
    rw [tr_ground_den] at hgf
    have hft := ((elemOf_spec hI hbool e).1 _).mp hgf
    exact Bool.false_ne_true (fq_bool_inj (values_apart hI hgw (NamesApart.subsorts_trans_of hids hok')
      (apart_of_distinct bool_distinct) hbf hbool hft))

end LibEv

end KCore

