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

/-- Where no symbol of `kernelSyms` is an instance at the head `n`, `n` applied to a sort resolves
to none. -/
theorem resolve_head_noInst {n : String}
    (hi : ∀ k ∈ kernelSyms c, ∀ xs, instDecode? (c.symName k.name) ≠ some (n, xs))
    (s : Srt) (tail : List Elem) : resolve c n (.srt s :: tail) = none := by
  show (kernelSyms c).findSome? (fun k => (instAt c n (.srt s :: tail) k).map (k, ·)) = none
  rw [List.findSome?_eq_none_iff]
  intro k hk
  cases hp : instAt c n (.srt s :: tail) k with
  | none => rfl
  | some p =>
    obtain ⟨xs, hd, -⟩ := instAt_spec hp
    exact absurd hd (hi k hk xs)

/-- Where no symbol of `kernelSyms` is an instance at the head `Lblite`, `Lblite` applied to a sort
resolves to none. -/
theorem resolve_lblite_noInst
    (hi : ∀ k ∈ kernelSyms c, ∀ xs, instDecode? (c.symName k.name) ≠ some ("Lblite", xs))
    (s : Srt) (tail : List Elem) : resolve c "Lblite" (.srt s :: tail) = none :=
  resolve_head_noInst hi s tail

/-! ## An instance's head at its sorts -/

/-- The sort names of an instance-named symbol of `kernelSyms` are the names of numbered sorts. -/
theorem instSorts_numbered (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {hd : String}
    {xs : List String} (hi : instDecode? (c.symName k.name) = some (hd, xs)) :
    ∃ ss : List Srt, (∀ s ∈ ss, s ∈ kernelSorts c) ∧ ss.map c.sortName = xs := by
  have h1 := (itesApart_inst h.ites hk hi).1
  clear hi
  induction xs with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons x xs ih =>
    obtain ⟨s, hs, rfl⟩ := h1 x (List.mem_cons_self ..)
    obtain ⟨ss, hss, rfl⟩ := ih (fun y hy => h1 y (List.mem_cons_of_mem _ hy))
    exact ⟨s :: ss, fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hs
      · exact hss t ht, rfl⟩

/-- **The head of an instance denotes its partial application at no argument**: it is not `inj`,
and a symbol of `kernelSyms` plainly named by it has an argument (`itesApart`), so it is no
constant's name. -/
theorem evalSymb_instHead (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {hd : String}
    {xs : List String} (hi : instDecode? (c.symName k.name) = some (hd, xs)) (x : Elem) :
    evalSymb c (.symbol hd) x ↔ x = .app (.sym hd) [] := by
  obtain ⟨-, -, hinj, hconst⟩ := itesApart_inst h.ites hk hi
  rw [evalSymb_symbol hinj, resolve_nil]
  cases hf : (kernelSyms c).find? (fun k' => c.symName k'.name == hd) with
  | none => exact Iff.rfl
  | some k' =>
    have hne := hconst k' (List.mem_of_find?_eq_some hf) (by simpa using List.find?_some hf)
    show (if k'.args = [] then result c k' [] else fun x => x = Elem.app (.sym hd) []) x ↔ _
    refine (ite_mem _ _ x).trans ?_
    rw [if_neg hne]

/-- **The head of an instance applied to its sorts, then to arguments, resolves to the instance**,
after its sort arguments: a symbol found there is named at the head and at as many sorts
(`itesApart`), so at these sorts, and two symbols of one decoding are one (`instsApart`). -/
theorem resolve_inst (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {hd : String}
    {ss : List Srt} (hne : ss ≠ []) (hi : instDecode? (c.symName k.name) = some (hd, ss.map c.sortName))
    (tail : List Elem) : resolve c hd (ss.map Elem.srt ++ tail) = some (k, ss.length) := by
  obtain ⟨s, ss', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hk0 : instAt c hd ((s :: ss').map Elem.srt ++ tail) k = some (s :: ss').length := by
    unfold instAt
    rw [hi]
    simp only [List.length_map, beq_self_eq_true, Bool.true_and, leadSorts_srts, ↓reduceIte]
  show (kernelSyms c).findSome? (fun k' => (instAt c hd ((s :: ss').map Elem.srt ++ tail) k').map (k', ·)) = _
  cases hf : (kernelSyms c).findSome? (fun k' => (instAt c hd ((s :: ss').map Elem.srt ++ tail) k').map (k', ·)) with
  | none =>
    have := List.findSome?_eq_none_iff.mp hf k hk
    rw [hk0] at this
    cases this
  | some kp =>
    obtain ⟨k', hk', hkp⟩ := List.exists_of_findSome?_eq_some hf
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hkp
    obtain ⟨xs', hd', hlen, hls⟩ := instAt_spec hp
    have hl := (itesApart_inst h.ites hk hi).2.1 k' hk' xs' hd'
    rw [List.length_map] at hl
    have hxs : xs' = (s :: ss').map c.sortName := by
      rw [← hlen, hl, leadSorts_srts] at hls
      exact (Option.some.inj hls).symm
    subst hxs
    rw [instsApart h.names hk' hk hd' hi, ← hlen, List.length_map]

/-- **At a nonempty proper prefix of an instance's sorts no symbol resolves, and the prefix begins
the instance** (`instPrefix`): every instance of the head has as many sorts as this one. -/
theorem resolve_instPrefix (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {hd : String}
    {pre post : List Srt} (hpre : pre ≠ []) (hpost : post ≠ [])
    (hi : instDecode? (c.symName k.name) = some (hd, (pre ++ post).map c.sortName)) :
    resolve c hd (pre.map Elem.srt) = none ∧ instPrefix c hd (pre.map Elem.srt) = true := by
  have hpl : 0 < post.length := List.length_pos_iff.mpr hpost
  constructor
  · obtain ⟨s, pre', rfl⟩ := List.exists_cons_of_ne_nil hpre
    show (kernelSyms c).findSome? (fun k' => (instAt c hd ((s :: pre').map Elem.srt) k').map (k', ·)) = none
    rw [List.findSome?_eq_none_iff]
    intro k' hk'
    cases hp : instAt c hd ((s :: pre').map Elem.srt) k' with
    | none => rfl
    | some p =>
      obtain ⟨xs', hd', hlen, hls⟩ := instAt_spec hp
      have hl := (itesApart_inst h.ites hk hi).2.1 k' hk' xs' hd'
      have h2 := (leadSorts_length hls).2
      simp only [List.length_map, List.length_append, List.length_cons, List.cons_append] at hl h2
      omega
  · refine List.any_eq_true.mpr ⟨k, hk, ?_⟩
    rw [hi]
    have hls := leadSorts_srts (c := c) pre []
    rw [List.append_nil] at hls
    simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      List.length_map, List.length_append]
    refine ⟨by omega, ?_⟩
    rw [hls, List.map_append, List.take_left' (by simp)]

/-- A list that is not empty ends with an element. -/
theorem snoc_of_ne_nil {α : Type} : ∀ (l : List α), l ≠ [] → ∃ pre a, l = pre ++ [a]
  | [], h => absurd rfl h
  | [a], _ => ⟨[], a, rfl⟩
  | a :: b :: l, _ => by
    obtain ⟨pre, x, hx⟩ := snoc_of_ne_nil (b :: l) (List.cons_ne_nil _ _)
    exact ⟨a :: pre, x, by rw [hx]; rfl⟩

/-- Induction on a list from its end. -/
theorem snoc_induction {α : Type} {P : List α → Prop} (hnil : P []) (hsnoc : ∀ l a, P l → P (l ++ [a])) :
    ∀ l, P l := by
  suffices ∀ n (l : List α), l.length = n → P l from fun l => this _ l rfl
  intro n
  induction n with
  | zero => intro l hl; rw [List.eq_nil_of_length_eq_zero hl]; exact hnil
  | succ n ih =>
    intro l hl
    obtain ⟨pre, a, rfl⟩ := snoc_of_ne_nil l (by intro h; rw [h] at hl; cases hl)
    exact hsnoc pre a (ih pre (by simpa using hl))

/-- An instance's head at one more sort is the head applied to that sort. -/
theorem instHeadP_snoc (hd : String) (xs : List String) (x : String) :
    instHeadP hd (xs ++ [x]) = instHeadP hd xs ⬝ KoreAML.sym (.sort ("Sort" ++ x)) := by
  unfold instHeadP; rw [List.foldl_append]; rfl

/-- `inhOf (SortX)` of the sorts of a list, as the arity item writes them. -/
theorem map_inh (ss : List Srt) :
    (ss.map (srtOf c)).map (fun s => KoreAML.inhOf (KoreAML.trSort [] s)) =
      ss.map fun s => KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName s))) := by
  simp [srtOf, trSort_srt]

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **The head of an instance applied to a proper prefix of its sorts denotes that partial
application.** -/
theorem instHeadP_prefix (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {hd : String}
    (pre : List Srt) : ∀ (post : List Srt), post ≠ [] → (∀ s ∈ pre ++ post, s ∈ kernelSorts c) →
    instDecode? (c.symName k.name) = some (hd, (pre ++ post).map c.sortName) →
    ∀ (e : Valuation Elem) (a : Elem),
      ((instHeadP hd (pre.map c.sortName)).interpret (stdI_T c T) e a ↔
        a = .app (.sym hd) (pre.map Elem.srt)) := by
  refine snoc_induction (P := fun pre => ∀ (post : List Srt), post ≠ [] →
    (∀ s ∈ pre ++ post, s ∈ kernelSorts c) →
    instDecode? (c.symName k.name) = some (hd, (pre ++ post).map c.sortName) →
    ∀ (e : Valuation Elem) (a : Elem),
      ((instHeadP hd (pre.map c.sortName)).interpret (stdI_T c T) e a ↔
        a = .app (.sym hd) (pre.map Elem.srt))) ?_ ?_ pre
  · intro post _ _ hi e a
    simp only [List.map_nil, instHeadP_nil, KoreAML.interp_sym, stdI_symb]
    exact evalSymb_instHead h hk hi a
  · intro pre s ih post hpost hs hi e a
    have hi' : instDecode? (c.symName k.name) = some (hd, (pre ++ s :: post).map c.sortName) := by
      simpa only [List.append_assoc, List.singleton_append] using hi
    have ihp := ih (s :: post) (List.cons_ne_nil _ _)
      (by simpa only [List.append_assoc, List.singleton_append] using hs) hi' e
    have hsn : s < nRegSorts + c.sortNames.length := List.mem_range.mp (hs s (by simp))
    obtain ⟨hr, hp⟩ := resolve_instPrefix h hk (pre := pre ++ [s]) (post := post) (by simp) hpost hi
    simp only [List.map_append, List.map_cons, List.map_nil] at hr hp ⊢
    rw [instHeadP_snoc, KoreAML.interp_app]
    constructor
    · rintro ⟨a0, b0, ha0, hb0, hab⟩
      rw [(ihp a0).mp ha0, (sort_den (T := T) h.namesK hsn e b0).mp hb0] at hab
      exact (symAt_instPrefix hr (by simp) hp a).mp hab
    · intro ha
      exact ⟨_, _, (ihp _).mpr rfl, (sort_den (T := T) h.namesK hsn e _).mpr rfl,
        (symAt_instPrefix hr (by simp) hp a).mpr ha⟩

/-- The head `symApp` writes for an instance-named symbol of `kernelSyms`, at its sorts, applied to
values: what the symbol gives. The head before its last sort is a partial application
(`instHeadP_prefix`), and at all its sorts it resolves to the symbol (`resolve_inst`). -/
theorem instHead_app_inst (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {hd : String}
    {xs : List String} (_hw : ∀ ps, symApp c k.name ps = .app ⟨⟨hd⟩⟩ (xs.map KoreAML.srt) ps)
    (hx : xs ≠ []) (hi : instDecode? (c.symName k.name) = some (hd, xs)) {vs : List GroundTerm}
    (hl : vs.length = k.args.length) (e : Valuation Elem) (m : Elem) :
    (∃ a, (instHeadP hd xs).interpret (stdI_T c T) e a ∧ AppE (stdI_T c T) a (vs.map Elem.val) m) ↔
      result c k vs m := by
  obtain ⟨ss, hss, rfl⟩ := instSorts_numbered h hk hi
  have hne : ss ≠ [] := fun h0 => hx (by rw [h0]; rfl)
  obtain ⟨pre, s, rfl⟩ := snoc_of_ne_nil ss hne
  have hsn : s < nRegSorts + c.sortNames.length := List.mem_range.mp (hss s (by simp))
  have hlen : (pre.map Elem.srt ++ [Elem.srt s]).length = pre.length + 1 := by simp
  have hr : ∀ tail, resolve c hd ((pre.map Elem.srt ++ [Elem.srt s]) ++ tail) = some (k, pre.length + 1) :=
    fun tail => by
      have := resolve_inst h hk hne hi tail
      simpa only [List.map_append, List.map_cons, List.map_nil, List.length_append, List.length_cons,
        List.length_nil] using this
  have hr0 := hr []
  rw [List.append_nil] at hr0
  have hpre := instHeadP_prefix (T := T) h hk pre [s] (List.cons_ne_nil _ _) hss hi e
  have hhead : ∀ a, (instHeadP hd ((pre ++ [s]).map c.sortName)).interpret (stdI_T c T) e a ↔
      symAt c hd (pre.map Elem.srt ++ [Elem.srt s]) a := by
    intro a
    rw [List.map_append, List.map_cons, List.map_nil, instHeadP_snoc, KoreAML.interp_app]
    constructor
    · rintro ⟨a0, b0, ha0, hb0, hab⟩
      rw [(hpre a0).mp ha0, (sort_den (T := T) h.namesK hsn e b0).mp hb0] at hab
      exact hab
    · intro ha
      exact ⟨_, _, (hpre _).mpr rfl, (sort_den (T := T) h.namesK hsn e _).mpr rfl, ha⟩
  simp only [hhead]
  by_cases h0 : k.args = []
  · rw [h0] at hl
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hl
    simp only [symAt_full hr0 (by rw [hlen, h0]; rfl)
      (show vals ((pre.map Elem.srt ++ [Elem.srt s]).drop (pre.length + 1)) = some [] by
        rw [List.drop_of_length_le (by rw [hlen]; exact Nat.le_refl _)]; rfl), List.map_nil, AppE]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hm; exact ⟨m, hm, rfl⟩
  · have hpos : 0 < k.args.length := List.length_pos_iff.mpr h0
    simp only [symAt_partial hr0 (by rw [hlen]; omega)]
    have := appE_symP (T := T) (P := pre.map Elem.srt ++ [Elem.srt s]) (n := hd) (k := k)
      (fun pre' _ => by rw [hlen]; exact hr _) [] vs (by simpa using hpos) (by simpa using hl) m
    simp only [List.map_nil, List.append_nil, List.nil_append] at this
    constructor
    · rintro ⟨a, rfl, ha⟩; exact this.mp ha
    · intro hm; exact ⟨_, rfl, this.mpr hm⟩

/-- **The head `symApp` writes**, at its sorts, applied to the values of a symbol of `kernelSyms`:
what the symbol gives. -/
theorem instHead_app (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {hd : String}
    {xs : List String} (hw : ∀ ps, symApp c k.name ps = .app ⟨⟨hd⟩⟩ (xs.map KoreAML.srt) ps)
    {vs : List GroundTerm} (hl : vs.length = k.args.length) (e : Valuation Elem) (m : Elem) :
    (∃ a, (instHeadP hd xs).interpret (stdI_T c T) e a ∧ AppE (stdI_T c T) a (vs.map Elem.val) m) ↔
      result c k vs m := by
  obtain ⟨hd', xs', hof, hw'⟩ := symApp_head c k.name
  obtain ⟨rfl, rfl⟩ := symApp_writes_eq_iha hw hw'
  rcases hof with ⟨rfl, rfl⟩ | ⟨hx, hi⟩
  · exact symE_vals h.namesK hk hl m
  · exact instHead_app_inst h hk hw hx hi hl e m

/-- **Arity**: every symbol maps the values of its argument sorts into its result sort. -/
theorem sat_symArity (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) :
    stdI_T c T ⊧ᴵ (symArityItem c k).pat := by
  have hn := h.namesK
  have hsorts := h.symSorts hk
  have hargs : ∀ s ∈ k.args, s < nRegSorts + c.sortNames.length := fun s hs => hsorts s (List.mem_cons_of_mem _ hs)
  have hres := hsorts k.result (List.mem_cons_self ..)
  obtain ⟨hd, xs, -, hw⟩ := symApp_head c k.name
  intro e m
  rw [symArityItem_of_symApp hw]
  show (KoreAML.appList (instHeadP hd xs)
        (k.args.map fun s => KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName s)))) ⊆⊆
      KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName k.result)))).interpret (stdI_T c T) e m
  rw [KoreAML.interp_included defOK_std]
  intro a ha
  rw [inhOf_sort hn hres]
  rw [interp_appList] at ha
  obtain ⟨a0, ha0, bs, hbs, happ⟩ := ha
  obtain ⟨vs, rfl, hvs⟩ := args_vals (T := T) hn k.args hargs bs hbs
  exact result_sorted h hk hvs ((instHead_app h hk hw (sortsOf_length hvs) e a).mp ⟨a0, ha0, happ⟩)

end AtT

/-- The head `symApp` writes, at its sorts, applied to the values of a symbol of `kernelSyms`: what
the symbol gives. -/
theorem instHead_app (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {hd : String}
    {xs : List String} (hw : ∀ ps, symApp c k.name ps = .app ⟨⟨hd⟩⟩ (xs.map KoreAML.srt) ps)
    {vs : List GroundTerm} (hl : vs.length = k.args.length) (e : Valuation Elem) (m : Elem) :
    (∃ a, (instHeadP hd xs).interpret (stdI c) e a ∧ AppE (stdI c) a (vs.map Elem.val) m) ↔
      result c k vs m :=
  AtT.instHead_app (c := c) (T := StepM c) h hk hw hl e m

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
