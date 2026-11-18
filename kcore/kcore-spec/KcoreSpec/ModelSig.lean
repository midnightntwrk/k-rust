/-
  KCore. The value model satisfies the signature (`SatSigGoal`): each numbered sort's name
  denotes that sort; every symbol maps values of its argument sorts to values of its result sort
  (a constructor builds a value of its sort, a hook's, a parameter's and a function's results have
  their declared sorts: subject reduction); `⌈_⌉{s,s'}` gives the sort `s'`; a successor of a
  configuration is a configuration; a literal accepted at a sort is a value of it.
-/
import KcoreSpec.ModelDen
import KcoreSpec.OvlLawsFn

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-! ## Elements of sorts -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem defOK_std : KoreAML.DefOK (stdI_T c T) := KoreAML.defOK_of (model_sat_definedness c)

end AtT

theorem defOK_std : KoreAML.DefOK (stdI c) :=
  AtT.defOK_std (c := c) (T := StepM c)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem inh_srt (s : Srt) (m : Elem) : KoreAML.Inh (stdI_T c T) (.srt s) m ↔ InSort c s m := by
  constructor
  · rintro ⟨i, hi, h⟩
    have hi' : i = .app .inh [] := hi
    subst hi'
    exact h
  · intro h
    exact ⟨.app .inh [], rfl, h⟩

end AtT

theorem inh_srt (s : Srt) (m : Elem) : KoreAML.Inh (stdI c) (.srt s) m ↔ InSort c s m :=
  AtT.inh_srt (c := c) (T := StepM c) (s := s) (m := m)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem isSort_iff (σ : Elem) : KoreAML.IsSort (stdI_T c T) σ ↔ ∃ s ∈ kernelSorts c, σ = .srt s := by
  constructor
  · rintro ⟨s0, hs0, i, hi, h⟩
    have hs0' : s0 = .app .sortSort [] := hs0
    have hi' : i = .app .inh [] := hi
    subst hs0' hi'
    exact h
  · intro h
    exact ⟨.app .sortSort [], rfl, .app .inh [], rfl, h⟩

end AtT

theorem isSort_iff (σ : Elem) : KoreAML.IsSort (stdI c) σ ↔ ∃ s ∈ kernelSorts c, σ = .srt s :=
  AtT.isSort_iff (c := c) (T := StepM c) (σ := σ)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- The inhabitants of a numbered sort, by its name: its values. -/
theorem inhOf_sort (hn : NamesApartK c) {s : Srt} (hs : s < nRegSorts + c.sortNames.length)
    (e : Valuation Elem) (m : Elem) :
    (KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName s)))).interpret (stdI_T c T) e m ↔ InSort c s m := by
  rw [KoreAML.interp_inhOf_of (sort_den hn hs e), inh_srt]

end AtT

/-- The inhabitants of a numbered sort, by its name: its values. -/
theorem inhOf_sort (hn : NamesApartK c) {s : Srt} (hs : s < nRegSorts + c.sortNames.length)
    (e : Valuation Elem) (m : Elem) :
    (KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName s)))).interpret (stdI c) e m ↔ InSort c s m :=
  AtT.inhOf_sort (c := c) (T := StepM c) (hn := hn) (s := s) (hs := hs) (e := e) (m := m)

theorem inSort_val {s : Srt} {m : Elem} (h : InSort c s m) : ∃ v, m = .val v ∧ c.sortOf v = some s := by
  cases m with
  | val v => exact ⟨v, rfl, h⟩
  | srt _ => exact h.elim
  | app _ _ => exact h.elim

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- Arguments in the inhabitants of numbered sorts are values of those sorts. -/
theorem args_vals (hn : NamesApartK c) {e : Valuation Elem} :
    ∀ (ss : List Srt), (∀ s ∈ ss, s < nRegSorts + c.sortNames.length) → ∀ (bs : List Elem),
      All2 (fun φ b => φ.interpret (stdI_T c T) e b)
        (ss.map fun s => KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName s)))) bs →
      ∃ vs, bs = vs.map Elem.val ∧ c.sortsOf vs = some ss
  | [], _, _, h => by cases h; exact ⟨[], rfl, sortsOf_nil⟩
  | s :: ss, hs, _, h => by
    cases h with
    | cons hb hbs =>
      rename_i b bs
      obtain ⟨v, rfl, hv⟩ := inSort_val ((inhOf_sort hn (hs s (List.mem_cons_self ..)) e b).mp hb)
      obtain ⟨vs, rfl, hvs⟩ := args_vals hn ss (fun s' h' => hs s' (List.mem_cons_of_mem _ h')) bs hbs
      exact ⟨v :: vs, rfl, sortsOf_cons.mpr ⟨s, ss, hv, hvs, rfl⟩⟩

end AtT

/-- Arguments in the inhabitants of numbered sorts are values of those sorts. -/
theorem args_vals (hn : NamesApartK c) {e : Valuation Elem} :
    ∀ (ss : List Srt), (∀ s ∈ ss, s < nRegSorts + c.sortNames.length) → ∀ (bs : List Elem),
      All2 (fun φ b => φ.interpret (stdI c) e b)
        (ss.map fun s => KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName s)))) bs →
      ∃ vs, bs = vs.map Elem.val ∧ c.sortsOf vs = some ss :=
  AtT.args_vals (c := c) (T := StepM c) (hn := hn) (e := e)

/-! ## Subject reduction for the symbols -/

theorem same_sym (hn : NamesApartK c) {k k' : CtorSig} (hk : k ∈ kernelSyms c) (hk' : k' ∈ kernelSyms c)
    (h : k.name = k'.name) : k = k' :=
  hn.1 k hk k' hk' (by rw [h])

/-- **What a symbol gives on values of its argument sorts is a value of its result sort**: a
constructor term has its constructor's sort, an overloading symbol's normal form its result sort
(`sortOf_norm_ovlF`), and the hooks', the parameters' and the functions' results have their declared
sorts. -/
theorem result_sorted (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) {x : Elem} (hx : result c k vs x) : InSort c k.result x := by
  have hn := h.namesK
  unfold result at hx
  by_cases hc : c.isCtor k.name = true
  · rw [if_pos hc] at hx
    subst hx
    obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp hc
    obtain ⟨hkm, hkn⟩ := lookupSig_spec hk'
    have := same_sym hn hk (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hkm)))) hkn.symm
    subst this
    show c.sortOf (.ctor k.name vs) = some k.result
    rw [Semantics.sortOf, hk']
    simp [hvs]
  rw [if_neg hc] at hx
  by_cases hh : isHook k.name = true
  · rw [if_pos hh] at hx
    obtain ⟨v, rfl, hv⟩ := hx
    obtain ⟨k', hk'⟩ := lookupSig_hookSigs_of_isHook hh
    obtain ⟨hkm, hkn⟩ := lookupSig_spec hk'
    have := same_sym hn hk (kernel_hook hkm) hkn.symm
    subst this
    exact hookRes_sorted (fun _ => (sortCtx_of_allClEx h.sound.1 h.sound.2.1 h.ovlCase).range) hk' hvs hv
  rw [if_neg hh] at hx
  by_cases hp : c.isParam k.name = true
  · rw [if_pos hp] at hx
    obtain ⟨v, rfl, hv⟩ := hx
    obtain ⟨kp, hkp, hsv⟩ := c.paramVal_sorted hv
    rw [Semantics.lookupParam_eq] at hkp
    have hkpm := List.mem_of_find?_eq_some hkp
    have hkpn : kp.sig.name = k.name := by simpa using List.find?_some hkp
    have := same_sym hn hk (kernel_param hkpm) hkpn.symm
    rw [this]
    exact hsv
  rw [if_neg hp] at hx
  by_cases ho : c.isOvl k.name = true
  · rw [if_pos ho] at hx
    obtain ⟨-, -, -, -, hsome⟩ := c.isOvl_parts ho
    obtain ⟨o, hlo⟩ := Option.isSome_iff_exists.mp hsome
    have H := h.ovlHyp
    have F := H.fnFacts
    obtain ⟨hom, hon, -⟩ := OvlLaws.ovl_facts_ovlF F hlo
    have := same_sym hn hk (List.mem_append_right _ (List.mem_map_of_mem hom)) hon.symm
    subst this
    cases hfc : c.fnCover o.sig.name vs with
    | none =>
      rw [ovlRes_none hfc] at hx
      subst hx
      exact OvlLaws.sortOf_norm_ovlF H F hlo hvs hfc
    | some kg =>
      -- a function overload covers the arguments: the function's value at the stripped
      -- arguments has the function's result sort, and lifts to the symbol's
      obtain ⟨v, rfl, hv⟩ := (ovlRes_some hlo hfc _).mp hx
      obtain ⟨o', ho', hkg, hb, hcv⟩ := OvlLaws.fnCover_some_parts hfc
      rw [hlo] at ho'; cases ho'
      obtain ⟨hl, -, hres, -⟩ := OvlLaws.over_ovlF F hlo hkg
      obtain ⟨-, -, hlies⟩ := OvlLaws.covers_iff.mp hcv
      obtain ⟨fn, -, hfn, hsig⟩ := OvlLaws.byFn_fn hkg hb
      have hsv : c.sortOf v = some kg.result := by
        subst hsig
        exact Eval.sorted (sortCtx_of_allClEx h.hyp.1 h.hyp.2.1 h.ovlCase) hv hfn
          (OvlLaws.sortsOf_stripAll hl hvs hlies) rfl
      exact OvlLaws.sortOf_lift H hsv hres
  rw [if_neg ho] at hx
  obtain ⟨v, rfl, hv⟩ := hx
  have hfn : ∃ fn, c.lookupFn k.name = some fn := Option.ne_none_iff_exists'.mp (Eval.lookupFn_ne hv)
  obtain ⟨fn, hfn⟩ := hfn
  rw [Semantics.lookupFn_eq] at hfn
  have hfnm := List.mem_of_find?_eq_some hfn
  have hfnn : fn.label = k.name := by simpa using List.find?_some hfn
  have heq := same_sym hn hk (fn_sig_mem hfnm) hfnn.symm
  rw [← Semantics.lookupFn_eq] at hfn
  have hvs' : c.sortsOf vs = some fn.args := by rw [hvs, heq]; rfl
  show c.sortOf v = some k.result
  rw [heq]
  exact Eval.sorted (sortCtx_of_allClEx h.hyp.1 h.hyp.2.1 h.ovlCase) hv hfn hvs' rfl

/-! ## Guards -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem conjList_elim {e : Valuation Elem} {m : Elem} :
    ∀ {ws : List KoreAML.P}, (KoreAML.conjList ws).interpret (stdI_T c T) e m → ∀ w ∈ ws, w.interpret (stdI_T c T) e m
  | [], _, _, hw => nomatch hw
  | [w], h, w', hw => by rw [List.mem_singleton.mp hw]; exact h
  | w :: w' :: ws, h, w'', hw => by
    unfold KoreAML.conjList at h
    rw [interpret_conj] at h
    rcases List.mem_cons.mp hw with rfl | hw
    · exact h.1
    · exact conjList_elim h.2 w'' hw

end AtT

theorem conjList_elim {e : Valuation Elem} {m : Elem} :
    ∀ {ws : List KoreAML.P}, (KoreAML.conjList ws).interpret (stdI c) e m → ∀ w ∈ ws, w.interpret (stdI c) e m :=
  AtT.conjList_elim (c := c) (T := StepM c) (e := e) (m := m)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem guarded_intro {ws : List KoreAML.P} {φ : KoreAML.P} {e : Valuation Elem} {m : Elem}
    (h : (∀ w ∈ ws, w.interpret (stdI_T c T) e m) → φ.interpret (stdI_T c T) e m) :
    (KoreAML.guarded ws φ).interpret (stdI_T c T) e m := by
  cases ws with
  | nil => exact h (fun _ hw => nomatch hw)
  | cons w ws => intro hc; exact h (conjList_elim hc)

end AtT

theorem guarded_intro {ws : List KoreAML.P} {φ : KoreAML.P} {e : Valuation Elem} {m : Elem}
    (h : (∀ w ∈ ws, w.interpret (stdI c) e m) → φ.interpret (stdI c) e m) :
    (KoreAML.guarded ws φ).interpret (stdI c) e m :=
  AtT.guarded_intro (c := c) (T := StepM c) (ws := ws) (φ := φ) (e := e) (m := m) (h := h)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sortGuard_iff {x : EVar} {e : Valuation Elem} {m : Elem} :
    (KoreAML.sortGuard x).interpret (stdI_T c T) e m ↔ ∃ s ∈ kernelSorts c, e.evalEvar x = .srt s := by
  unfold KoreAML.sortGuard
  rw [KoreAML.interp_member defOK_std, KoreAML.interp_sortsDomain, isSort_iff]

end AtT

theorem sortGuard_iff {x : EVar} {e : Valuation Elem} {m : Elem} :
    (KoreAML.sortGuard x).interpret (stdI c) e m ↔ ∃ s ∈ kernelSorts c, e.evalEvar x = .srt s :=
  AtT.sortGuard_iff (c := c) (T := StepM c) (x := x) (e := e) (m := m)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem inhOf_evar {x : EVar} {e : Valuation Elem} {s : Srt} (hx : e.evalEvar x = .srt s) (m : Elem) :
    (KoreAML.inhOf (.evar x)).interpret (stdI_T c T) e m ↔ InSort c s m := by
  rw [KoreAML.interp_inhOf_of (σ := .srt s) (fun a => by rw [KoreAML.interp_evar, hx]), inh_srt]

end AtT

theorem inhOf_evar {x : EVar} {e : Valuation Elem} {s : Srt} (hx : e.evalEvar x = .srt s) (m : Elem) :
    (KoreAML.inhOf (.evar x)).interpret (stdI c) e m ↔ InSort c s m :=
  AtT.inhOf_evar (c := c) (T := StepM c) (x := x) (e := e) (s := s) (hx := hx) (m := m)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem ceilE_iff (s s' : Srt) (x m : Elem) : KoreAML.CeilE (stdI_T c T) (.srt s) (.srt s') x m ↔ InSort c s' m := by
  constructor
  · rintro ⟨a, ⟨a', ⟨h0, h0s, h1⟩, h2⟩, h3⟩
    have h0' : h0 = .app .ceil [] := h0s
    subst h0'
    have h1' : a' = .app .ceil [.srt s] := h1
    subst h1'
    have h2' : a = .app .ceil [.srt s, .srt s'] := h2
    subst h2'
    exact h3
  · intro hm
    exact ⟨.app .ceil [.srt s, .srt s'], ⟨.app .ceil [.srt s], ⟨.app .ceil [], rfl, rfl⟩, rfl⟩, hm⟩

end AtT

theorem ceilE_iff (s s' : Srt) (x m : Elem) : KoreAML.CeilE (stdI c) (.srt s) (.srt s') x m ↔ InSort c s' m :=
  AtT.ceilE_iff (c := c) (T := StepM c) (s := s) (s' := s') (x := x) (m := m)

/-! ## The items of the signature -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_sortConst (hn : NamesApartK c) {s : Srt} (hs : s ∈ kernelSorts c) :
    stdI_T c T ⊧ᴵ (KoreAML.sortConstantItem (sortDeclOf c s)).pat := by
  intro e m
  show (KoreAML.sExists ⟨1⟩ (KoreAML.sym .sortSort)
    (KoreAML.sym (.sort ("Sort" ++ c.sortName s)) ≡ .evar ⟨1⟩)).interpret (stdI_T c T) e m
  rw [KoreAML.interp_sExists]
  refine ⟨.srt s, ?_, ?_⟩
  · rw [KoreAML.interp_member defOK_std, KoreAML.interp_inhOf]
    simp only [Function.update_same]
    exact ⟨.app .sortSort [], rfl, .app .inh [], rfl, s, hs, rfl⟩
  · rw [KoreAML.interp_equal defOK_std]
    intro b
    rw [sort_den hn (List.mem_range.mp hs), KoreAML.interp_evar]
    simp only [Function.update_same]

end AtT

theorem sat_sortConst (hn : NamesApartK c) {s : Srt} (hs : s ∈ kernelSorts c) :
    stdI c ⊧ᴵ (KoreAML.sortConstantItem (sortDeclOf c s)).pat :=
  AtT.sat_sortConst (c := c) (T := StepM c) (hn := hn) (s := s) (hs := hs)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem appE_symP {n : String} {k : CtorSig} {P : List Elem}
    (hres : ∀ pre : List GroundTerm, pre ≠ [] → resolve c n (P ++ pre.map Elem.val) = some (k, P.length)) :
    ∀ (pre rest : List GroundTerm), pre.length < k.args.length → pre.length + rest.length = k.args.length →
      ∀ m, AppE (stdI_T c T) (.app (.sym n) (P ++ pre.map Elem.val)) (rest.map Elem.val) m ↔
        result c k (pre ++ rest) m
  | pre, [], hlt, hlen, _ => by simp at hlen; omega
  | pre, w :: rest, hlt, hlen, m => by
    have hv2 : P ++ pre.map Elem.val ++ [Elem.val w] = P ++ (pre ++ [w]).map Elem.val := by simp
    have hr := hres (pre ++ [w]) (by simp)
    have hl2 : (P ++ (pre ++ [w]).map Elem.val).length = P.length + (pre.length + 1) := by simp
    have hev : ∀ x, (stdI_T c T).evalApp (.app (.sym n) (P ++ pre.map Elem.val)) (.val w) x ↔
        symAt c n (P ++ (pre ++ [w]).map Elem.val) x := fun x => by rw [← hv2]; exact Iff.rfl
    simp only [List.map_cons, AppE, hev]
    by_cases hl : pre.length + 1 < k.args.length
    · have ih := appE_symP hres (pre ++ [w]) rest (by simpa using hl) (by simp at hlen ⊢; omega) m
      simp only [List.append_assoc, List.singleton_append] at ih
      simp only [symAt_partial hr (by rw [hl2]; omega)]
      constructor
      · rintro ⟨a', ha', h⟩; rw [ha'] at h; exact ih.mp h
      · intro h; exact ⟨_, rfl, ih.mpr h⟩
    · have hrest : rest = [] := by
        cases rest with
        | nil => rfl
        | cons _ _ => simp at hlen; omega
      subst hrest
      simp only [symAt_full hr (by rw [hl2]; omega) (by rw [List.drop_left, vals_map])]
      simp only [AppE, List.map_nil]
      constructor
      · rintro ⟨a', ha', rfl⟩; exact ha'
      · intro h; exact ⟨m, h, rfl⟩

end AtT

theorem appE_symP {n : String} {k : CtorSig} {P : List Elem}
    (hres : ∀ pre : List GroundTerm, pre ≠ [] → resolve c n (P ++ pre.map Elem.val) = some (k, P.length)) :
    ∀ (pre rest : List GroundTerm), pre.length < k.args.length → pre.length + rest.length = k.args.length →
      ∀ m, AppE (stdI c) (.app (.sym n) (P ++ pre.map Elem.val)) (rest.map Elem.val) m ↔
        result c k (pre ++ rest) m :=
  AtT.appE_symP (c := c) (T := StepM c) (n := n) (k := k) (P := P) (hres := hres)


/-! ## `ite` at a sort -/

theorem kIte_name : c.symName kIte = "Lblite" := by
  unfold Semantics.symName
  rw [if_pos (by decide)]
  decide

theorem evalSymb_lblite (hn : NamesApartK c) (x : Elem) :
    evalSymb c (.symbol "Lblite") x ↔ x = .app (.sym "Lblite") [] := by
  have hkI : (⟨kIte, [Srt.bool, Srt.kitem, Srt.kitem], Srt.kitem⟩ : CtorSig) ∈ kernelSyms c :=
    kernel_hook (by decide)
  have := evalSymb_sym hn hkI x
  simp only [kIte_name] at this
  rw [this]
  simp

theorem find_ite (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {X : String}
    (hi : iteSort? (c.symName k.name) = some X) :
    (kernelSyms c).find? (fun k' => iteSort? (c.symName k'.name) == some X) = some k := by
  cases hf : (kernelSyms c).find? (fun k' => iteSort? (c.symName k'.name) == some X) with
  | none =>
    have := List.find?_eq_none.mp hf k hk
    simp [hi] at this
  | some k' =>
    have h1 : iteSort? (c.symName k'.name) = some X := by simpa using List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    have h3 := List.all_eq_true.mp h.ites k' h2
    simp only [Bool.and_eq_true] at h3
    have := List.all_eq_true.mp h3.2 k hk
    simp only [h1, hi, Option.isNone_some, bne_self_eq_false, Bool.false_or, beq_iff_eq] at this
    rw [this]

theorem resolve_ite (s : Srt) (tail : List Elem) :
    resolve c "Lblite" (.srt s :: tail) =
      ((kernelSyms c).find? fun k => iteSort? (c.symName k.name) == some (c.sortName s)).map (·, 1) := rfl

/-- `inhOf (SortX)` of the sorts of a list, as the arity item writes them. -/
theorem map_inh (ss : List Srt) :
    (ss.map (srtOf c)).map (fun s => KoreAML.inhOf (KoreAML.trSort [] s)) =
      ss.map fun s => KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName s))) := by
  simp [srtOf, trSort_srt]

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **Arity**: every symbol maps the values of its argument sorts into its result sort. -/
theorem sat_symArity (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) :
    stdI_T c T ⊧ᴵ (symArityItem c k).pat := by
  have hn := h.namesK
  have hsorts := h.symSorts hk
  have hargs : ∀ s ∈ k.args, s < nRegSorts + c.sortNames.length := fun s hs => hsorts s (List.mem_cons_of_mem _ hs)
  have hres := hsorts k.result (List.mem_cons_self ..)
  intro e m
  unfold symArityItem
  cases hi : iteSort? (c.symName k.name) with
  | none =>
    show (KoreAML.appList (KoreAML.sym (.symbol (c.symName k.name)))
        ((k.args.map (srtOf c)).map fun s => KoreAML.inhOf (KoreAML.trSort [] s)) ⊆⊆
      KoreAML.inhOf (KoreAML.trSort [] (srtOf c k.result))).interpret (stdI_T c T) e m
    rw [map_inh, KoreAML.interp_included defOK_std]
    intro a ha
    rw [srtOf, trSort_srt, inhOf_sort hn hres]
    rw [interp_appList] at ha
    obtain ⟨a0, ha0, bs, hbs, happ⟩ := ha
    obtain ⟨vs, rfl, hvs⟩ := args_vals (T := T) hn k.args hargs bs hbs
    exact result_sorted h hk hvs ((symE_vals hn hk (sortsOf_length hvs) a).mp ⟨a0, ha0, happ⟩)
  | some X =>
    show (KoreAML.appList (KoreAML.sym (.symbol "Lblite") ⬝ KoreAML.sym (.sort ("Sort" ++ X)))
        (k.args.map fun s => KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName s)))) ⊆⊆
      KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName k.result)))).interpret (stdI_T c T) e m
    rw [KoreAML.interp_included defOK_std]
    intro a ha
    rw [inhOf_sort hn hres]
    rw [interp_appList] at ha
    obtain ⟨a0, ha0, bs, hbs, happ⟩ := ha
    obtain ⟨vs, rfl, hvs⟩ := args_vals (T := T) hn k.args hargs bs hbs
    rw [KoreAML.interp_app] at ha0
    obtain ⟨h0, b0, hh0, hb0, hab⟩ := ha0
    have hb0' : ∃ s', sortOfName c ("Sort" ++ X) = some s' ∧ b0 = .srt s' := hb0
    obtain ⟨s', hs', rfl⟩ := hb0'
    have hs'n : c.sortName s' = X := by
      unfold sortOfName at hs'
      exact append_cancel (a := "Sort") (by simpa using List.find?_some hs')
    have hh0' : h0 = .app (.sym "Lblite") [] := (evalSymb_lblite hn h0).mp hh0
    subst hh0'
    have hr : ∀ tail, resolve c "Lblite" (.srt s' :: tail) = some (k, 1) := fun tail => by
      rw [resolve_ite, hs'n, find_ite h hk hi]; rfl
    have hab' : symAt c "Lblite" [.srt s'] a0 := hab
    have hl := sortsOf_length hvs
    by_cases h0 : k.args = []
    · rw [h0] at hl
      obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hl
      rw [symAt_full (hr []) (by simp [h0]) (show vals ([Elem.srt s'].drop 1) = some [] from rfl)] at hab'
      have : a = a0 := happ
      subst this
      exact result_sorted h hk hvs hab'
    · rw [symAt_partial (hr []) (by simp; exact List.length_pos_iff.mpr h0)] at hab'
      subst hab'
      have := appE_symP (T := T) (P := [.srt s']) (n := "Lblite") (k := k) (fun pre _ => hr _) [] vs
        (by simp; exact List.length_pos_iff.mpr h0) (by simpa using hl) a
      simp only [List.map_nil, List.append_nil, List.nil_append] at this
      exact result_sorted h hk hvs (this.mp happ)

end AtT

/-- **Arity**: every symbol maps the values of its argument sorts into its result sort. -/
theorem sat_symArity (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) :
    stdI c ⊧ᴵ (symArityItem c k).pat :=
  AtT.sat_symArity (c := c) (T := StepM c) (h := h) (k := k) (hk := hk)

/-! ## The definedness symbols, next, domain values -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_ceilArity : stdI_T c T ⊧ᴵ KoreAML.ceilArityItem.pat := by
  intro e m
  unfold KoreAML.ceilArityItem
  dsimp only
  refine guarded_intro (fun hg => ?_)
  obtain ⟨s, -, hs⟩ := sortGuard_iff.mp (hg _ (List.mem_cons_self ..))
  obtain ⟨s', -, hs'⟩ := sortGuard_iff.mp (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  rw [KoreAML.interp_included defOK_std]
  intro a ha
  rw [inhOf_evar hs']
  rw [KoreAML.interp_sCeil_raw] at ha
  obtain ⟨σ, σ', x, h1, h2, -, h4⟩ := ha
  rw [KoreAML.interp_evar, hs] at h1
  rw [KoreAML.interp_evar, hs'] at h2
  subst h1 h2
  exact (ceilE_iff s s' x a).mp h4

end AtT

theorem sat_ceilArity : stdI c ⊧ᴵ KoreAML.ceilArityItem.pat :=
  AtT.sat_ceilArity (c := c) (T := StepM c)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_ceilDef : stdI_T c T ⊧ᴵ KoreAML.ceilDefItem.pat := by
  intro e m
  unfold KoreAML.ceilDefItem
  dsimp only
  refine guarded_intro (fun hg => ?_)
  obtain ⟨s, -, hs⟩ := sortGuard_iff.mp (hg _ (List.mem_cons_self ..))
  obtain ⟨s', -, hs'⟩ := sortGuard_iff.mp (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  rw [KoreAML.interp_equal defOK_std]
  intro a
  rw [inhOf_evar hs', KoreAML.interp_sCeil_raw]
  constructor
  · rintro ⟨σ, σ', x, h1, h2, -, h4⟩
    rw [KoreAML.interp_evar, hs] at h1
    rw [KoreAML.interp_evar, hs'] at h2
    subst h1 h2
    exact (ceilE_iff s s' x a).mp h4
  · intro ha
    exact ⟨.srt s, .srt s', e.evalEvar ⟨3⟩, by rw [KoreAML.interp_evar, hs], by rw [KoreAML.interp_evar, hs'],
      rfl, (ceilE_iff s s' _ a).mpr ha⟩

end AtT

theorem sat_ceilDef : stdI c ⊧ᴵ KoreAML.ceilDefItem.pat :=
  AtT.sat_ceilDef (c := c) (T := StepM c)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_nextArity (hn : NamesApartK c) :
    stdI_T c T ⊧ᴵ (KoreAML.nextArityItem [] (srtOf c topCellSort)).pat := by
  intro e m
  show (KoreAML.sNext (KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName topCellSort)))) ⊆⊆
    KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName topCellSort)))).interpret (stdI_T c T) e m
  rw [KoreAML.interp_included defOK_std]
  intro a ha
  rw [inhOf_sort hn top_numbered]
  unfold KoreAML.sNext at ha
  rw [KoreAML.interp_app] at ha
  obtain ⟨a0, b0, ha0, -, hab⟩ := ha
  have ha0' : a0 = .app .next [] := ha0
  subst ha0'
  have hst : StepE_T c T a b0 := hab
  cases a with
  | val x =>
    cases b0 with
    | val y => obtain ⟨hx, -, -⟩ := hst; exact hx
    | srt _ => exact hst.elim
    | app _ _ => exact hst.elim
  | srt _ => exact hst.elim
  | app _ _ => exact hst.elim

end AtT

theorem sat_nextArity (hn : NamesApartK c) :
    stdI c ⊧ᴵ (KoreAML.nextArityItem [] (srtOf c topCellSort)).pat :=
  AtT.sat_nextArity (c := c) (T := StepM c) (hn := hn)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_dvArity (lit : String) : stdI_T c T ⊧ᴵ (KoreAML.dvArityItem lit).pat := by
  intro e m
  unfold KoreAML.dvArityItem
  dsimp only
  refine guarded_intro (fun hg => ?_)
  obtain ⟨s, -, hs⟩ := sortGuard_iff.mp (hg _ (List.mem_cons_self ..))
  rw [KoreAML.interp_included defOK_std]
  intro a ha
  rw [inhOf_evar hs]
  rw [KoreAML.interp_app] at ha
  obtain ⟨a0, b0, ha0, hb0, hab⟩ := ha
  have ha0' : a0 = .app (.dv lit) [] := ha0
  rw [KoreAML.interp_evar, hs] at hb0
  subst ha0' hb0
  have hab' : ∃ l, a = .val (.dv s l) ∧ l.text = lit ∧ dvOK c.lib s l = true := hab
  obtain ⟨l, rfl, -, hl⟩ := hab'
  show c.sortOf (.dv s l) = some s
  rw [Semantics.sortOf, if_pos hl]

end AtT

theorem sat_dvArity (lit : String) : stdI c ⊧ᴵ (KoreAML.dvArityItem lit).pat :=
  AtT.sat_dvArity (c := c) (T := StepM c) (lit := lit)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **`SatSigGoal`**: the value model satisfies the signature. -/
theorem satSigGoal (h : HypModelCore c) : (stdI_T c T ⊧ᴵP ΓSig c) := by
  intro φ hφ
  rcases hφ with hφ | ⟨lit, rfl⟩
  · refine sat_itemsPremises c (fun it hit => ?_) φ hφ
    simp only [sigItems, List.mem_append, List.mem_singleton, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false] at hit
    rcases hit with ((rfl | ⟨s, hs, rfl⟩) | ⟨k, hk, rfl⟩) | rfl | rfl | rfl
    · exact model_sat_definedness c _
    · exact sat_sortConst h.namesK hs
    · exact sat_symArity h hk
    · exact sat_ceilArity
    · exact sat_ceilDef
    · exact sat_nextArity h.namesK
  · exact sat_dvArity lit

end AtT

/-- **`SatSigGoal`**: the value model satisfies the signature. -/
theorem satSigGoal (h : HypModelCore c) : SatSigGoal c :=
  AtT.satSigGoal (c := c) (T := StepM c) (h := h)

end Model

end Faithful

end KCore
