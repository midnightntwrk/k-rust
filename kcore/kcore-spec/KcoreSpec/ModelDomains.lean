/-
  KCore. The value model satisfies the domains (`SatDomainsGoal`): an interpreted hook applied
  to values is what `hook` gives, a parameter what `paramVal` gives, by the definition of `result`;
  every value is one element of its sort and distinct values are distinct elements (`den_val`);
  every value of a collection sort is built from the unit by adding its entries one at a time, so
  it lies in every set closed under that construction, the least fixed point `collNoJunk` states.
-/
import KcoreSpec.ModelSig

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-! ## More of what `HypModelCore` gives -/

theorem HypModelCore.genWf (h : HypModelCore c) : genWf c = true := h.sound.2.2.2.1

theorem HypModelCore.collSortsOK (h : HypModelCore c) : collSortsOK c = true := h.sound.2.2.2.2.2.1

theorem HypModelCore.hookNotCtor (h : HypModelCore c) {k : CtorSig} (hk : k ∈ hookSigs) : c.isCtor k.name = false := by
  have := h.kinds
  simp only [kindsApart, Bool.and_eq_true, List.all_eq_true] at this
  simpa using this.1 k hk

theorem HypModelCore.paramKinds (h : HypModelCore c) {kp : ParamSig} (hkp : kp ∈ c.params) :
    c.isCtor kp.sig.name = false ∧ isHook kp.sig.name = false := by
  have := h.kinds
  simp only [kindsApart, Bool.and_eq_true, List.all_eq_true] at this
  simpa using this.2 kp hkp

theorem HypModelCore.iteSorted (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {X : String}
    (hi : iteSort? (c.symName k.name) = some X) : ∃ s ∈ kernelSorts c, c.sortName s = X :=
  itesApart_iteSorted h.ites hk hi

theorem HypModelCore.collOf_self (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) : c.collOf k.sort = some k := by
  rcases List.mem_append.mp hk with hb | hu
  · simp only [builtinColls, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> rfl
  · exact (collSymsOK_spec (collsOK_colls h.collsOK hu)).1

/-- The sort of a value is numbered. -/
theorem sortOf_numbered (h : HypModelCore c) {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) :
    s < nRegSorts + c.sortNames.length := by
  cases v with
  | ctor f ts =>
    haveI : OvlOK c := h.sound.2.2.2.2.2.2.2.2
    rcases sortOf_ctor_cases h.sound.2.2.2.1 hv with ⟨k, hk, -, rfl⟩ | ⟨o, hlo, -, -, -, rfl, -⟩ | ⟨kp, hko, -, -, -, -, rfl, -⟩
    rotate_right
    · exact h.symSorts (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (f := (·.sig)) (c.lookupOpen_spec hko).1)))) _ (List.mem_cons_self ..)
    · exact h.symSorts (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (lookupSig_spec hk).1)))) _ (List.mem_cons_self ..)
    · exact h.symSorts (List.mem_append_right _ (List.mem_map_of_mem (OvlLaws.ovl_parts h.ovlOK hlo).1)) _
        (List.mem_cons_self ..)
  | inj a b t =>
    obtain ⟨hab, -, -, rfl⟩ := sortOf_inj.mp hv
    exact (h.subSorts hab).2
  | dv s0 lit =>
    obtain ⟨hd, rfl⟩ := sortOf_dv.mp hv
    exact h.dvSort hd
  | map s0 es =>
    obtain ⟨k, -, hco, -, -, -, -, rfl⟩ := sortOf_mapS_fwd hv
    obtain ⟨hk, rfl⟩ := collOf_spec hco
    exact (h.collSorts hk).1
  | set s0 es =>
    obtain ⟨k, hco, -, -, -, rfl⟩ := sortOf_setS.mp hv
    obtain ⟨hk, rfl⟩ := collOf_spec hco
    exact (h.collSorts hk).1
  | list s0 es =>
    obtain ⟨k, hco, -, -, rfl⟩ := sortOf_listS.mp hv
    obtain ⟨hk, rfl⟩ := collOf_spec hco
    exact (h.collSorts hk).1

/-- The interpreted hooks have registry names, none named like `ite` at a sort. -/
theorem hookSigs_plain : ∀ k ∈ hookSigs, k.name < nRegSyms ∧ iteSort? (regSymNames.getD k.name "") = none := by
  decide +kernel

theorem hook_plain {k : CtorSig} (hk : k ∈ hookSigs) : iteSort? (c.symName k.name) = none := by
  obtain ⟨h1, h2⟩ := hookSigs_plain k hk
  unfold Semantics.symName
  rw [if_pos h1]
  exact h2

/-! ## Applications at values, as the graphs write them -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem den_koreList (h : HypModelCore c) {vs : List GroundTerm} {ss : List Srt} (hvs : c.sortsOf vs = some ss)
    (e : Valuation Elem) :
    All2 (fun φ x => ∀ m, φ.interpret (stdI_T c T) e m ↔ m = x)
      ((GroundTerm.koreList c vs).map (KoreAML.tr ⟨[], []⟩)) (vs.map Elem.val) :=
  den_list h vs hvs e

end AtT

theorem den_koreList (h : HypModelCore c) {vs : List GroundTerm} {ss : List Srt} (hvs : c.sortsOf vs = some ss)
    (e : Valuation Elem) :
    All2 (fun φ x => ∀ m, φ.interpret (stdI c) e m ↔ m = x)
      ((GroundTerm.koreList c vs).map (KoreAML.tr ⟨[], []⟩)) (vs.map Elem.val) :=
  AtT.den_koreList (c := c) (T := StepM c) (h := h) (vs := vs) (ss := ss) (hvs := hvs) (e := e)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- A symbol not named like `ite`, applied to values: what the symbol gives. -/
theorem symApp_plain (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c)
    (hi : iteSort? (c.symName k.name) = none) {vs : List GroundTerm} {ss : List Srt}
    (hvs : c.sortsOf vs = some ss) (hl : vs.length = k.args.length) (e : Valuation Elem) (m : Elem) :
    (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs))).interpret (stdI_T c T) e m ↔ result c k vs m := by
  unfold symApp
  rw [hi]
  dsimp only
  unfold KoreAML.den
  rw [show (Kore.Pattern.app ⟨⟨c.symName k.name⟩⟩ [] (GroundTerm.koreList c vs)) =
    KoreAML.ap (c.symName k.name) (GroundTerm.koreList c vs) from rfl, tr_ap,
    interp_symList _ _ _ (den_koreList h hvs e) m]
  exact symE_vals h.namesK hk hl m

end AtT

/-- A symbol not named like `ite`, applied to values: what the symbol gives. -/
theorem symApp_plain (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c)
    (hi : iteSort? (c.symName k.name) = none) {vs : List GroundTerm} {ss : List Srt}
    (hvs : c.sortsOf vs = some ss) (hl : vs.length = k.args.length) (e : Valuation Elem) (m : Elem) :
    (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs))).interpret (stdI c) e m ↔ result c k vs m :=
  AtT.symApp_plain (c := c) (T := StepM c) (h := h) (k := k) (hk := hk) (hi := hi) (vs := vs) (ss := ss) (hvs := hvs) (hl := hl) (e := e) (m := m)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- `Lblite` applied to the sort `X` of a symbol named like `ite` at `X`, then to values: what the
symbol gives. -/
theorem lblite_app (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {X : String}
    (hi : iteSort? (c.symName k.name) = some X) {vs : List GroundTerm} (hl : vs.length = k.args.length)
    (e : Valuation Elem) (m : Elem) :
    (∃ a, (KoreAML.sym (.symbol "Lblite") ⬝ KoreAML.sym (.sort ("Sort" ++ X))).interpret (stdI_T c T) e a ∧
      AppE (stdI_T c T) a (vs.map Elem.val) m) ↔ result c k vs m := by
  have hn := h.namesK
  obtain ⟨s', hs'm, rfl⟩ := h.iteSorted hk hi
  have hr : ∀ tail, resolve c "Lblite" (.srt s' :: tail) = some (k, 1) := fun tail => by
    rw [resolve_ite, find_ite h hk hi]; rfl
  have hhead : ∀ a, (KoreAML.sym (.symbol "Lblite") ⬝ KoreAML.sym (.sort ("Sort" ++ c.sortName s'))).interpret
      (stdI_T c T) e a ↔ symAt c "Lblite" [.srt s'] a := by
    intro a
    rw [KoreAML.interp_app]
    simp only [KoreAML.interp_sym, stdI_symb]
    constructor
    · rintro ⟨h0, b0, hh0, hb0, hab⟩
      rw [(evalSymb_lblite hn h0).mp hh0] at hab
      have hb0' : b0 = .srt s' := (sort_den (T := T) hn (List.mem_range.mp hs'm) e b0).mp hb0
      subst hb0'
      exact hab
    · intro ha
      exact ⟨_, _, (evalSymb_lblite hn _).mpr rfl,
        (sort_den (T := T) hn (List.mem_range.mp hs'm) e _).mpr rfl, ha⟩
  simp only [hhead]
  by_cases h0 : k.args = []
  · rw [h0] at hl
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hl
    simp only [symAt_full (hr []) (by simp [h0]) (show vals ([Elem.srt s'].drop 1) = some [] from rfl),
      List.map_nil, AppE]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hm; exact ⟨m, hm, rfl⟩
  · simp only [symAt_partial (hr []) (by simp; exact List.length_pos_iff.mpr h0)]
    have := appE_symP (T := T) (P := [.srt s']) (n := "Lblite") (k := k) (fun pre _ => hr _) [] vs
      (by simp; exact List.length_pos_iff.mpr h0) (by simpa using hl) m
    simp only [List.map_nil, List.append_nil, List.nil_append] at this
    constructor
    · rintro ⟨a, rfl, ha⟩; exact this.mp ha
    · intro hm; exact ⟨_, rfl, this.mpr hm⟩

end AtT

/-- `Lblite` applied to the sort `X` of a symbol named like `ite` at `X`, then to values: what the
symbol gives. -/
theorem lblite_app (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {X : String}
    (hi : iteSort? (c.symName k.name) = some X) {vs : List GroundTerm} (hl : vs.length = k.args.length)
    (e : Valuation Elem) (m : Elem) :
    (∃ a, (KoreAML.sym (.symbol "Lblite") ⬝ KoreAML.sym (.sort ("Sort" ++ X))).interpret (stdI c) e a ∧
      AppE (stdI c) a (vs.map Elem.val) m) ↔ result c k vs m :=
  AtT.lblite_app (c := c) (T := StepM c) (h := h) (k := k) (hk := hk) (X := X) (hi := hi) (vs := vs) (hl := hl) (e := e) (m := m)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- Any symbol of the semantics applied to values, as `symApp` writes it: what the symbol gives. -/
theorem symApp_val (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {vs : List GroundTerm}
    {ss : List Srt} (hvs : c.sortsOf vs = some ss) (hl : vs.length = k.args.length) (e : Valuation Elem) (m : Elem) :
    (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs))).interpret (stdI_T c T) e m ↔ result c k vs m := by
  cases hi : iteSort? (c.symName k.name) with
  | none => exact symApp_plain h hk hi hvs hl e m
  | some X =>
    unfold symApp
    rw [hi]
    dsimp only
    unfold KoreAML.den
    rw [KoreAML.tr]
    simp only [List.contains_nil, Bool.false_eq_true, if_false]
    rw [trArgs_appList]
    show (KoreAML.appList (KoreAML.sym (.symbol "Lblite") ⬝ KoreAML.trSort [] (KoreAML.srt X)) _).interpret _ _ _ ↔ _
    rw [trSort_srt, interp_appList_sing _ _ _ (den_koreList h hvs e) m]
    exact lblite_app h hk hi hl e m

end AtT

/-- Any symbol of the semantics applied to values, as `symApp` writes it: what the symbol gives. -/
theorem symApp_val (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {vs : List GroundTerm}
    {ss : List Srt} (hvs : c.sortsOf vs = some ss) (hl : vs.length = k.args.length) (e : Valuation Elem) (m : Elem) :
    (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs))).interpret (stdI c) e m ↔ result c k vs m :=
  AtT.symApp_val (c := c) (T := StepM c) (h := h) (k := k) (hk := hk) (vs := vs) (ss := ss) (hvs := hvs) (hl := hl) (e := e) (m := m)

/-! ## The graphs -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_hookGraph (h : HypModelCore c) {k : CtorSig} {vs : List GroundTerm} {r : Option GroundTerm}
    (hk : k ∈ hookSigs) (hvs : c.sortsOf vs = some k.args) (hr : c.hookRes k.name vs = some r) :
    stdI_T c T ⊧ᴵ (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) ≡ (match (generalizing := false) r with
      | some v => den c v
      | none => ⊥)) := by
  intro e m
  rw [KoreAML.interp_equal defOK_std]
  intro a
  rw [symApp_val h (kernel_hook hk) hvs (sortsOf_length hvs),
    result_hook (h.hookNotCtor hk) (hookSigs_hooked k hk)]
  cases r with
  | none =>
    simp only [Pattern.interpret]
    constructor
    · rintro ⟨v, -, hv⟩; rw [hr] at hv; cases hv
    · intro hf; exact hf.elim
  | some v =>
    obtain ⟨k', hk'⟩ := lookupSig_hookSigs_of_isHook (hookSigs_hooked k hk)
    obtain ⟨hk'm, hk'n⟩ := lookupSig_spec hk'
    have := same_sym h.namesK (kernel_hook hk'm) (kernel_hook hk) hk'n
    subst this
    have hsv := hookRes_sorted (fun _ => (sortCtx_of_allClEx h.sound.1 h.sound.2.1 h.ovlCase).range) hk' hvs hr
    dsimp only
    rw [den_val h v hsv e a]
    constructor
    · rintro ⟨v', rfl, hv'⟩; rw [hr] at hv'; cases hv'; rfl
    · rintro rfl; exact ⟨v, rfl, hr⟩

end AtT

theorem sat_hookGraph (h : HypModelCore c) {k : CtorSig} {vs : List GroundTerm} {r : Option GroundTerm}
    (hk : k ∈ hookSigs) (hvs : c.sortsOf vs = some k.args) (hr : c.hookRes k.name vs = some r) :
    stdI c ⊧ᴵ (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) ≡ (match (generalizing := false) r with
      | some v => den c v
      | none => ⊥)) :=
  AtT.sat_hookGraph (c := c) (T := StepM c) (h := h) (k := k) (vs := vs) (r := r) (hk := hk) (hvs := hvs) (hr := hr)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_paramGraph (h : HypModelCore c) {kp : ParamSig} {vs : List GroundTerm}
    (hkp : kp ∈ c.params) (hvs : c.sortsOf vs = some kp.sig.args) :
    stdI_T c T ⊧ᴵ (KoreAML.den (symApp c kp.sig.name (GroundTerm.koreList c vs)) ≡
      (match c.paramVal kp.sig.name vs with
        | some v => den c v
        | none => ⊥)) := by
  intro e m
  rw [KoreAML.interp_equal defOK_std]
  intro a
  obtain ⟨hc, hh⟩ := h.paramKinds hkp
  have hp : c.isParam kp.sig.name = true := by
    unfold Semantics.isParam
    rw [Semantics.lookupParam_eq]
    cases hf : c.params.find? (·.sig.name == kp.sig.name) with
    | none => have := List.find?_eq_none.mp hf kp hkp; simp at this
    | some _ => rfl
  rw [symApp_val h (kernel_param hkp) hvs (sortsOf_length hvs), result_param hc hh hp]
  cases hpv : c.paramVal kp.sig.name vs with
  | none =>
    simp only [Pattern.interpret]
    constructor
    · rintro ⟨v, -, hv⟩; cases hv
    · intro hf; exact hf.elim
  | some v =>
    obtain ⟨kp', -, hsv⟩ := c.paramVal_sorted hpv
    dsimp only
    rw [den_val h v hsv e a]
    constructor
    · rintro ⟨v', rfl, hv'⟩; cases hv'; rfl
    · rintro rfl; exact ⟨v, rfl, rfl⟩

/-- **A parameter symbol applied to values, in the value model**: exactly `paramVal`'s value, and
no element where `paramVal` has none. For every parameter, an open generator among them. -/
theorem paramGraph_val (h : HypModelCore c) {kp : ParamSig} {vs : List GroundTerm}
    (hkp : kp ∈ c.params) (hvs : c.sortsOf vs = some kp.sig.args) (e : Valuation Elem) (m : Elem) :
    (KoreAML.den (symApp c kp.sig.name (GroundTerm.koreList c vs))).interpret (stdI_T c T) e m ↔
      ∃ v, c.paramVal kp.sig.name vs = some v ∧ m = .val v := by
  obtain ⟨hc, hh⟩ := h.paramKinds hkp
  have hp : c.isParam kp.sig.name = true := by
    unfold Semantics.isParam
    rw [Semantics.lookupParam_eq]
    cases hf : c.params.find? (·.sig.name == kp.sig.name) with
    | none => have := List.find?_eq_none.mp hf kp hkp; simp at this
    | some _ => rfl
  rw [symApp_val h (kernel_param hkp) hvs (sortsOf_length hvs), result_param hc hh hp]
  exact ⟨fun ⟨v, h1, h2⟩ => ⟨v, h2, h1⟩, fun ⟨v, h1, h2⟩ => ⟨v, h2, h1⟩⟩

/-- **An open generator applied to values, in the value model**: the interpretation's answer, or
the raw application where it gives none, where that has the generator's result sort; no element
otherwise. From the parameter its symbol names (`hlp`), with no registry hook (`hi`). -/
theorem openGraph_val (h : HypModelCore c) {kp : ParamSig} {vs : List GroundTerm}
    (hkp : kp ∈ c.params) (hraw : kp.raw = true) (hlp : c.lookupParam kp.sig.name = some kp)
    (hi : kp.impl = none) (hvs : c.sortsOf vs = some kp.sig.args) (e : Valuation Elem) (m : Elem) :
    (KoreAML.den (symApp c kp.sig.name (GroundTerm.koreList c vs))).interpret (stdI_T c T) e m ↔
      ∃ v, v = (c.hooks.app kp.sig.name vs).getD (.ctor kp.sig.name vs) ∧
        c.sortOf v = some kp.sig.result ∧ m = .val v := by
  rw [paramGraph_val h hkp hvs e m]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨h1, h2⟩ := (paramVal_raw_sorted hlp hraw hi).mp hv
    exact ⟨v, h1, h2, rfl⟩
  · rintro ⟨v, h1, h2, rfl⟩
    exact ⟨v, (paramVal_raw_sorted hlp hraw hi).mpr ⟨h1, h2⟩, rfl⟩

end AtT

theorem sat_paramGraph (h : HypModelCore c) {kp : ParamSig} {vs : List GroundTerm}
    (hkp : kp ∈ c.params) (hvs : c.sortsOf vs = some kp.sig.args) :
    stdI c ⊧ᴵ (KoreAML.den (symApp c kp.sig.name (GroundTerm.koreList c vs)) ≡
      (match c.paramVal kp.sig.name vs with
        | some v => den c v
        | none => ⊥)) :=
  AtT.sat_paramGraph (c := c) (T := StepM c) (h := h) (kp := kp) (vs := vs) (hkp := hkp) (hvs := hvs)

/-- **A parameter symbol applied to values, in the value model** (`AtT.paramGraph_val` at the value
model). -/
theorem paramGraph_val (h : HypModelCore c) {kp : ParamSig} {vs : List GroundTerm}
    (hkp : kp ∈ c.params) (hvs : c.sortsOf vs = some kp.sig.args) (e : Valuation Elem) (m : Elem) :
    (KoreAML.den (symApp c kp.sig.name (GroundTerm.koreList c vs))).interpret (stdI c) e m ↔
      ∃ v, c.paramVal kp.sig.name vs = some v ∧ m = .val v :=
  AtT.paramGraph_val (c := c) (T := StepM c) h hkp hvs e m

/-- **An open generator applied to values, in the value model** (`AtT.openGraph_val` at the value
model). -/
theorem openGraph_val (h : HypModelCore c) {kp : ParamSig} {vs : List GroundTerm}
    (hkp : kp ∈ c.params) (hraw : kp.raw = true) (hlp : c.lookupParam kp.sig.name = some kp)
    (hi : kp.impl = none) (hvs : c.sortsOf vs = some kp.sig.args) (e : Valuation Elem) (m : Elem) :
    (KoreAML.den (symApp c kp.sig.name (GroundTerm.koreList c vs))).interpret (stdI c) e m ↔
      ∃ v, v = (c.hooks.app kp.sig.name vs).getD (.ctor kp.sig.name vs) ∧
        c.sortOf v = some kp.sig.result ∧ m = .val v :=
  AtT.openGraph_val (c := c) (T := StepM c) h hkp hraw hlp hi hvs e m

/-! ## Values are elements, distinct values distinct -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_valElem (h : HypModelCore c) {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) :
    stdI_T c T ⊧ᴵ KoreAML.sExists ⟨1⟩ (sortP (c.sortName s)) (den c v ≡ .evar ⟨1⟩) := by
  intro e m
  rw [KoreAML.interp_sExists]
  refine ⟨.val v, ?_, ?_⟩
  · rw [KoreAML.interp_member defOK_std]
    simp only [Function.update_same]
    exact (inhOf_sort h.namesK (sortOf_numbered h hv) _ _).mpr hv
  · rw [KoreAML.interp_equal defOK_std]
    intro b
    rw [den_val h v hv, KoreAML.interp_evar]
    simp only [Function.update_same]

end AtT

theorem sat_valElem (h : HypModelCore c) {v : GroundTerm} {s : Srt} (hv : c.sortOf v = some s) :
    stdI c ⊧ᴵ KoreAML.sExists ⟨1⟩ (sortP (c.sortName s)) (den c v ≡ .evar ⟨1⟩) :=
  AtT.sat_valElem (c := c) (T := StepM c) (h := h) (v := v) (s := s) (hv := hv)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_distinct (h : HypModelCore c) {v w : GroundTerm} {s : Srt} (hv : c.sortOf v = some s)
    (hw : c.sortOf w = some s) (hne : GroundTerm.cmp v w ≠ .eq) : stdI_T c T ⊧ᴵ ∼(den c v ⋀ den c w) := by
  intro e m
  rw [interpret_neg, interpret_conj, den_val h v hv, den_val h w hw]
  rintro ⟨rfl, hvw⟩
  cases hvw
  exact hne (GroundTerm.cmp_refl v)

end AtT

theorem sat_distinct (h : HypModelCore c) {v w : GroundTerm} {s : Srt} (hv : c.sortOf v = some s)
    (hw : c.sortOf w = some s) (hne : GroundTerm.cmp v w ≠ .eq) : stdI c ⊧ᴵ ∼(den c v ⋀ den c w) :=
  AtT.sat_distinct (c := c) (T := StepM c) (h := h) (v := v) (w := w) (s := s) (hv := hv) (hw := hw) (hne := hne)

/-! ## No junk in the collection sorts -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- A collection's symbol applied to values, read as `SymE`: the library hook's value at the
collection's sort. -/
theorem coll_symE (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) {f g : Sym} {args : List Srt}
    (hf : (f = k.unit ∧ g = (builtinColl k.kind).unit ∧ args = []) ∨
      (f = k.elem ∧ g = (builtinColl k.kind).elem ∧ args = elemArgs k) ∨
      (f = k.concat ∧ g = (builtinColl k.kind).concat ∧ args = [k.sort, k.sort]))
    {vs : List GroundTerm} (hlen : vs.length = args.length) {r : GroundTerm} (hv : hook g vs = some (some r))
    (hws : r.withSort (builtinColl k.kind).sort = r) (hsr : c.sortOf (r.withSort k.sort) = some k.sort)
    (m : Elem) : SymE (stdI_T c T) (c.symName f) (vs.map Elem.val) m ↔ m = .val (r.withSort k.sort) := by
  obtain ⟨kf, hkf, hkfn, hkfa, hres⟩ := coll_sym h hk hf
  rw [← hkfn, symE_vals h.namesK hkf (by rw [hkfa]; exact hlen)]
  exact hres hv hws hsr m

end AtT

/-- A collection's symbol applied to values, read as `SymE`: the library hook's value at the
collection's sort. -/
theorem coll_symE (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) {f g : Sym} {args : List Srt}
    (hf : (f = k.unit ∧ g = (builtinColl k.kind).unit ∧ args = []) ∨
      (f = k.elem ∧ g = (builtinColl k.kind).elem ∧ args = elemArgs k) ∨
      (f = k.concat ∧ g = (builtinColl k.kind).concat ∧ args = [k.sort, k.sort]))
    {vs : List GroundTerm} (hlen : vs.length = args.length) {r : GroundTerm} (hv : hook g vs = some (some r))
    (hws : r.withSort (builtinColl k.kind).sort = r) (hsr : c.sortOf (r.withSort k.sort) = some k.sort)
    (m : Elem) : SymE (stdI c) (c.symName f) (vs.map Elem.val) m ↔ m = .val (r.withSort k.sort) :=
  AtT.coll_symE (c := c) (T := StepM c) (h := h) (k := k) (hk := hk) (f := f) (g := g) (args := args) (hf := hf) (vs := vs) (hlen := hlen) (r := r) (hv := hv) (hws := hws) (hsr := hsr) (m := m)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem symP_unit_of {k : CollSig} {e : Valuation Elem} {x : Elem}
    (hs : SymE (stdI_T c T) (c.symName k.unit) [] x) :
    (symP (c.symName k.unit)).interpret (stdI_T c T) e x := by
  obtain ⟨a, ha, hx⟩ := hs
  have : x = a := hx
  subst this
  exact ha

end AtT

theorem symP_unit_of {k : CollSig} {e : Valuation Elem} {x : Elem}
    (hs : SymE (stdI c) (c.symName k.unit) [] x) :
    (symP (c.symName k.unit)).interpret (stdI c) e x :=
  AtT.symP_unit_of (c := c) (T := StepM c) (k := k) (e := e) (x := x) (hs := hs)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- An application `f(φ₁, …, φₙ)` holds of `x` when `f` applied to elements of the `φᵢ` gives `x`. -/
theorem appList_of {f : String} {φs : List KoreAML.P} {bs : List Elem} {e : Valuation Elem} {x : Elem}
    (hb : All2 (fun φ b => φ.interpret (stdI_T c T) e b) φs bs) (hs : SymE (stdI_T c T) f bs x) :
    (KoreAML.appList (symP f) φs).interpret (stdI_T c T) e x := by
  obtain ⟨a, ha, hx⟩ := hs
  rw [interp_appList]
  exact ⟨a, ha, bs, hb, hx⟩

end AtT

/-- An application `f(φ₁, …, φₙ)` holds of `x` when `f` applied to elements of the `φᵢ` gives `x`. -/
theorem appList_of {f : String} {φs : List KoreAML.P} {bs : List Elem} {e : Valuation Elem} {x : Elem}
    (hb : All2 (fun φ b => φ.interpret (stdI c) e b) φs bs) (hs : SymE (stdI c) f bs x) :
    (KoreAML.appList (symP f) φs).interpret (stdI c) e x :=
  AtT.appList_of (c := c) (T := StepM c) (f := f) (φs := φs) (bs := bs) (e := e) (x := x) (hb := hb) (hs := hs)

/-- A value of a collection sort is a collection of that sort, of the collection's kind (`coll_shape`,
read with the overloading symbols: a raw overloading application has a constructor sort,
`ovl_result_cons`). -/
theorem HypModelCore.coll_shape' (h : HypModelCore c) {k : CollSig} (hco : c.collOf k.sort = some k)
    (hso : collSortOK c k.sort = true) {w : GroundTerm} (hw : c.sortOf w = some k.sort) :
    ((k.kind = .map ∨ k.kind = .rangeMap) ∧ ∃ es, w = .map k.sort es) ∨ (k.kind = .set ∧ ∃ es, w = .set k.sort es) ∨
      (k.kind = .list ∧ ∃ es, w = .list k.sort es) := by
  have hg := h.genWf
  have hnc : k.sort ∉ consSorts c := fun hm => by
    have := (genWf_cons hg hm).2.2.2.2.2.2
    rw [hco] at this; cases this
  have hcar : c.lib.carriers.all (·.1 != k.sort) = true := by
    unfold collSortOK at hso; simp only [Bool.and_eq_true] at hso; exact hso.2
  unfold collSortOK at hso
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hso
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hi, hb⟩, hkv⟩, ht⟩, hy⟩, hfl⟩, hstr⟩, hbys⟩, -⟩ := hso
  cases w with
  | ctor f ts =>
    rcases c.sortOf_ctor_iff.mp hw with ⟨k', hk, -, hr⟩ | ⟨-, o, ho, -, -, hr⟩ | ⟨-, -, kp, hko, -, -, hr⟩
    rotate_right
    · exact absurd (hr ▸ genWf_raw_cons hg (c.lookupOpen_spec hko).1 (c.lookupOpen_spec hko).2.1) hnc
    · exact absurd (hr ▸ genWf_ctor hg (lookupSig_spec hk).1) hnc
    · exact absurd (hr ▸ OvlLaws.ovl_result_cons h.ovlHyp ho) hnc
  | inj a b t =>
    obtain ⟨hab, -, -, hr⟩ := sortOf_inj.mp hw
    exact absurd (hr ▸ (genWf_sub hg hab).1) hnc
  | dv s lit =>
    obtain ⟨hok, hs⟩ := sortOf_dv.mp hw
    rw [← hs] at hok
    rw [dvOK_self (Lib.carrier_of_not _ hcar)] at hok
    exfalso
    cases lit with
    | int i => exact hi (beq_iff_eq.mp hok)
    | bool b => exact hb (beq_iff_eq.mp hok)
    | tok t =>
      simp only [dvOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
      rcases hok with ((h | h) | h) | ⟨h | h, -⟩
      · exact hkv h
      · exact hstr h
      · rw [ht] at h; cases h
      · exact hbys h
      · rw [hy] at h; cases h
    | float _ _ _ =>
      simp only [dvOK, Bool.and_eq_true, beq_iff_eq] at hok; exact hfl hok.1
  | map s es =>
    obtain ⟨k', -, hk', hkind, -, -, -, rfl⟩ := sortOf_mapS_fwd hw
    rw [hco] at hk'; cases hk'
    exact Or.inl ⟨hkind, es, rfl⟩
  | set s es =>
    obtain ⟨k', hk', hkind, -, -, rfl⟩ := sortOf_setS.mp hw
    rw [hco] at hk'; cases hk'
    exact Or.inr (Or.inl ⟨hkind, es, rfl⟩)
  | list s es =>
    obtain ⟨k', hk', hkind, -, rfl⟩ := sortOf_listS.mp hw
    rw [hco] at hk'; cases hk'
    exact Or.inr (Or.inr ⟨hkind, es, rfl⟩)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_collNoJunk (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) : stdI_T c T ⊧ᴵ collNoJunk c k := by
  have hn := h.namesK
  have hco := h.collOf_self hk
  obtain ⟨hsS, hsK, hsV⟩ := h.collSorts hk
  intro e m
  unfold collNoJunk
  dsimp only
  rw [KoreAML.interp_included defOK_std]
  intro a ha
  unfold sortP at ha
  rw [inhOf_sort hn hsS] at ha
  obtain ⟨w, rfl, hw⟩ := inSort_val ha
  intro B hB
  -- the valuation inside the fixed point
  let e' : Valuation Elem := ⟨e.evalEvar, Function.update e.evalSvar ⟨1⟩ B⟩
  have hX : ∀ x, (Pattern.svar ⟨1⟩ : KoreAML.P).interpret (stdI_T c T) e' x ↔ B x := fun x => by
    show Function.update e.evalSvar ⟨1⟩ B ⟨1⟩ x ↔ B x
    rw [Function.update_same]
  have hinh : ∀ (s : Srt), s < nRegSorts + c.sortNames.length → ∀ x, c.sortOf x = some s →
      (KoreAML.inhOf (sortP (c.sortName s))).interpret (stdI_T c T) e' (.val x) := fun s hs x hx =>
    (inhOf_sort hn hs e' _).mpr hx
  rcases h.coll_shape' hco (collSortsOK_mem h.collSortsOK hk) hw with
    ⟨hkind, es, rfl⟩ | ⟨hkind, es, rfl⟩ | ⟨hkind, es, rfl⟩
  · -- maps: by the entries, from the last
    rcases hkind with hkind | hkind
    rotate_left
    · -- a range map, the library's or the definition's own
      obtain ⟨k', vs, hk', hval, -, -, -⟩ := sortOf_mapS_iff.mp hw
      rw [hco] at hk'; cases hk'
      have hvs : vs = valSort k := by simp [valSort, hval]
      subst hvs
      obtain ⟨hr, hent⟩ := (sortOf_rmK_iff hco hkind hval).mp hw
      clear hw ha
      rw [hkind] at hB
      induction es with
      | nil =>
        have hU : SymE (stdI_T c T) (c.symName k.unit) [] (.val (.map k.sort [])) :=
          (coll_symE h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) rfl (r := rmV []) (by rw [hkind]; exact rmM_unit)
            (by rw [hkind]; rfl) ((sortOf_rmK_iff hco hkind hval).mpr ⟨rfl, rfl⟩) _).mpr rfl
        exact hB _ (interpret_disj.mpr (Or.inl (symP_unit_of hU)))
      | cons x es ih =>
        obtain ⟨hx, hent'⟩ := entriesOK_cons'.mp hent
        have hr' := rmM_tail hr
        have hB' := ih hr' hent'
        obtain ⟨xa, xb⟩ := x
        obtain ⟨ha', hb'⟩ := entryOK_iff.mp hx
        have hxr := rangesOK_head hr
        have hE : SymE (stdI_T c T) (c.symName k.elem) [.val xa, .val xb] (.val (.map k.sort [(xa, xb)])) :=
          (coll_symE h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (vs := [xa, xb]) (by unfold elemArgs; rw [hkind]; rfl)
            (r := rmV [(xa, xb)]) (by rw [hkind]; exact rmM_elem hxr) (by rw [hkind]; rfl)
            ((sortOf_rmK_iff hco hkind hval).mpr
              ⟨by simpa [rangesOK] using hxr, by simp [Semantics.entriesOK, hx]⟩) _).mpr rfl
        have hC : SymE (stdI_T c T) (c.symName k.concat) [.val (.map k.sort [(xa, xb)]), .val (.map k.sort es)]
            (.val (.map k.sort ((xa, xb) :: es))) :=
          (coll_symE h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (vs := [.map k.sort [(xa, xb)], .map k.sort es]) rfl
            (r := rmV ((xa, xb) :: es)) (by rw [hkind]; exact rmM_concat_sortK hr) (by rw [hkind]; rfl)
            ((sortOf_rmK_iff hco hkind hval).mpr ⟨hr, hent⟩) _).mpr rfl
        have hEl := appList_of (T := T) (e := e') (.cons (hinh _ hsK _ ha') (.cons (hinh _ hsV _ hb') .nil)) hE
        exact hB _ (interpret_disj.mpr (Or.inr (appList_of (.cons hEl (.cons ((hX _).mpr hB') .nil)) hC)))
    obtain ⟨-, hks, hent⟩ := (sortOf_map_iff hco (h.mapVal hk hkind) hkind).mp hw
    clear hw ha
    rw [hkind] at hB
    induction es with
    | nil =>
      have hU : SymE (stdI_T c T) (c.symName k.unit) [] (.val (.map k.sort [])) :=
        (coll_symE h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) rfl (r := .map Srt.map [])
          (by rw [hkind, builtinColl_map, Exec.hook_unit_eq]) (by rw [hkind, builtinColl_map]; rfl)
          ((sortOf_map_iff hco (h.mapVal hk hkind) hkind).mpr ⟨hkind, rfl, rfl⟩) _).mpr rfl
      exact hB _ (interpret_disj.mpr (Or.inl (symP_unit_of hU)))
    | cons x es ih =>
      obtain ⟨hx, hent'⟩ := entriesOK_cons'.mp hent
      have hks' := keysSorted_tail hks
      have hB' := ih hks' hent'
      obtain ⟨xa, xb⟩ := x
      obtain ⟨ha', hb'⟩ := entryOK_iff.mp hx
      have hE : SymE (stdI_T c T) (c.symName k.elem) [.val xa, .val xb] (.val (.map k.sort [(xa, xb)])) :=
        (coll_symE h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (vs := [xa, xb]) (elemArgs_length hkind).symm
          (r := .map Srt.map [(xa, xb)]) (by rw [hkind, builtinColl_map, Exec.hook_elem_eq])
          (by rw [hkind, builtinColl_map]; rfl)
          ((sortOf_map_iff hco (h.mapVal hk hkind) hkind).mpr ⟨hkind, rfl, by simp [Semantics.entriesOK, hx]⟩) _).mpr rfl
      have hC : SymE (stdI_T c T) (c.symName k.concat) [.val (.map k.sort [(xa, xb)]), .val (.map k.sort es)]
          (.val (.map k.sort ((xa, xb) :: es))) :=
        (coll_symE h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (vs := [.map k.sort [(xa, xb)], .map k.sort es]) rfl
          (r := .map Srt.map ((xa, xb) :: es))
          (by rw [hkind, builtinColl_map, Exec.hook_concat_eq]
              show some ((union [(xa, xb)] es).map (GroundTerm.map Srt.map)) = _; rw [union_first hks]; rfl)
          (by rw [hkind, builtinColl_map]; rfl) ((sortOf_map_iff hco (h.mapVal hk hkind) hkind).mpr ⟨hkind, hks, hent⟩) _).mpr rfl
      have hEl := appList_of (T := T) (e := e') (.cons (hinh _ hsK _ ha') (.cons (hinh _ hsV _ hb') .nil)) hE
      exact hB _ (interpret_disj.mpr (Or.inr (appList_of (.cons hEl (.cons ((hX _).mpr hB') .nil)) hC)))
  · -- sets
    have hkind' : k.kind = .set ∨ k.kind = .list := .inl hkind
    have hev : ∀ l, elemsVal k l = .set k.sort l := fun l => by unfold elemsVal; rw [hkind]
    have hw' : c.sortOf (elemsVal k es) = some k.sort := by rw [hev]; exact hw
    obtain ⟨hso, hall⟩ := (sortOf_elems_iff hco hkind').mp hw'
    clear hw ha hw'
    rw [hkind] at hB
    have hsv : ∀ l, (k.kind = .set → elemsSorted l = true) → (∀ z ∈ l, c.sortOf z = some k.key) →
        c.sortOf (.set k.sort l) = some k.sort := fun l h1 h2 => by
      rw [← hev]; exact (sortOf_elems_iff hco hkind').mpr ⟨h1, h2⟩
    induction es with
    | nil =>
      have hU : SymE (stdI_T c T) (c.symName k.unit) [] (.val (.set k.sort [])) :=
        (coll_symE h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) rfl (r := .set Srt.set [])
          (by rw [hkind, builtinColl_set, hook_setUnit_eq]) (by rw [hkind, builtinColl_set]; rfl)
          (hsv [] (fun _ => rfl) (fun _ h => nomatch h)) _).mpr rfl
      exact hB _ (interpret_disj.mpr (Or.inl (symP_unit_of hU)))
    | cons x es ih =>
      have hso' : elemsSorted es = true := by
        have := hso hkind
        cases es with
        | nil => rfl
        | cons y es => simp only [elemsSorted, Bool.and_eq_true] at this; exact this.2
      have hB' := ih (fun _ => hso') (fun z hz => hall z (List.mem_cons_of_mem _ hz))
      have hx := hall x (List.mem_cons_self ..)
      have hE : SymE (stdI_T c T) (c.symName k.elem) [.val x] (.val (.set k.sort [x])) :=
        (coll_symE h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (vs := [x]) (elemArgs_length' hkind').symm
          (r := .set Srt.set [x]) (by rw [hkind, builtinColl_set, hook_setElem_eq])
          (by rw [hkind, builtinColl_set]; rfl)
          (hsv [x] (fun _ => rfl) (fun z hz => by rw [List.mem_singleton.mp hz]; exact hx)) _).mpr rfl
      have hC : SymE (stdI_T c T) (c.symName k.concat) [.val (.set k.sort [x]), .val (.set k.sort es)]
          (.val (.set k.sort (x :: es))) :=
        (coll_symE h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (vs := [.set k.sort [x], .set k.sort es]) rfl
          (r := .set Srt.set (x :: es))
          (by rw [hkind, builtinColl_set, hook_setConcat_eq]
              show some ((concatS [x] es).map (GroundTerm.set Srt.set)) = _
              rw [concatS_first (elemsSorted_iff.mp (hso hkind))]; rfl)
          (by rw [hkind, builtinColl_set]; rfl) (hsv _ hso hall) _).mpr rfl
      have hEl := appList_of (T := T) (e := e') (.cons (hinh _ hsK _ hx) .nil) hE
      exact hB _ (interpret_disj.mpr (Or.inr (appList_of (.cons hEl (.cons ((hX _).mpr hB') .nil)) hC)))
  · -- lists
    have hkind' : k.kind = .set ∨ k.kind = .list := .inr hkind
    have hev : ∀ l, elemsVal k l = .list k.sort l := fun l => by unfold elemsVal; rw [hkind]
    have hw' : c.sortOf (elemsVal k es) = some k.sort := by rw [hev]; exact hw
    obtain ⟨-, hall⟩ := (sortOf_elems_iff hco hkind').mp hw'
    clear hw ha hw'
    rw [hkind] at hB
    have hnset : k.kind ≠ .set := by rw [hkind]; exact (by intro h; cases h)
    have hsv : ∀ l, (∀ z ∈ l, c.sortOf z = some k.key) → c.sortOf (.list k.sort l) = some k.sort := fun l h2 => by
      rw [← hev]; exact (sortOf_elems_iff hco hkind').mpr ⟨fun h => absurd h hnset, h2⟩
    induction es with
    | nil =>
      have hU : SymE (stdI_T c T) (c.symName k.unit) [] (.val (.list k.sort [])) :=
        (coll_symE h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) rfl (r := .list Srt.list [])
          (by rw [hkind, builtinColl_list, hook_listUnit_eq]) (by rw [hkind, builtinColl_list]; rfl)
          (hsv [] (fun _ h => nomatch h)) _).mpr rfl
      exact hB _ (interpret_disj.mpr (Or.inl (symP_unit_of hU)))
    | cons x es ih =>
      have hB' := ih (fun z hz => hall z (List.mem_cons_of_mem _ hz))
      have hx := hall x (List.mem_cons_self ..)
      have hE : SymE (stdI_T c T) (c.symName k.elem) [.val x] (.val (.list k.sort [x])) :=
        (coll_symE h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (vs := [x]) (elemArgs_length' hkind').symm
          (r := .list Srt.list [x]) (by rw [hkind, builtinColl_list, hook_listElem_eq])
          (by rw [hkind, builtinColl_list]; rfl)
          (hsv [x] (fun z hz => by rw [List.mem_singleton.mp hz]; exact hx)) _).mpr rfl
      have hC : SymE (stdI_T c T) (c.symName k.concat) [.val (.list k.sort [x]), .val (.list k.sort es)]
          (.val (.list k.sort (x :: es))) :=
        (coll_symE h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (vs := [.list k.sort [x], .list k.sort es]) rfl
          (r := .list Srt.list (x :: es))
          (by rw [hkind, builtinColl_list, hook_listConcat_eq]; rfl)
          (by rw [hkind, builtinColl_list]; rfl) (hsv _ hall) _).mpr rfl
      have hEl := appList_of (T := T) (e := e') (.cons (hinh _ hsK _ hx) .nil) hE
      exact hB _ (interpret_disj.mpr (Or.inr (appList_of (.cons hEl (.cons ((hX _).mpr hB') .nil)) hC)))

end AtT

theorem sat_collNoJunk (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) : stdI c ⊧ᴵ collNoJunk c k :=
  AtT.sat_collNoJunk (c := c) (T := StepM c) (h := h) (k := k) (hk := hk)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **`SatDomainsGoal`**: the value model satisfies the domains. -/
theorem satDomainsGoal (h : HypModelCore c) : (stdI_T c T ⊧ᴵP ΓDomains c) := by
  intro φ hφ
  rcases hφ with ⟨k, vs, r, hk, hvs, hr, hs, rfl⟩ | ⟨kp, vs, hkp, hvs, rfl⟩ | ⟨v, s, hv, rfl⟩ |
    ⟨v, w, s, -, hv, hw, hne, rfl⟩ | ⟨k, hk, rfl⟩
  · exact sat_hookGraph h hk hvs (Semantics.hookRes_of_hook hr hs)
  · exact sat_paramGraph h hkp hvs
  · exact sat_valElem h hv
  · exact sat_distinct h hv hw hne
  · exact sat_collNoJunk h hk

end AtT

/-- **`SatDomainsGoal`**: the value model satisfies the domains. -/
theorem satDomainsGoal (h : HypModelCore c) : SatDomainsGoal c :=
  AtT.satDomainsGoal (c := c) (T := StepM c) (h := h)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- The value model satisfies the interpretation's values at silent points: there an interpreted
symbol's result (`result`, through `hookRes`) is the fallback. -/
theorem sat_silentGraph (h : HypModelCore c) {k : CtorSig} {vs : List GroundTerm} (hk : k ∈ hookSigs)
    (hvs : c.sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = true) :
    stdI_T c T ⊧ᴵ (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) ≡ (match c.fallback k.name vs with
      | some v => den c v
      | none => ⊥)) :=
  sat_hookGraph h hk hvs (Semantics.hookRes_of_silent hh hs)

end AtT

/-- The value model satisfies the interpretation's values at silent points: there an interpreted
symbol's result (`result`, through `hookRes`) is the fallback. -/
theorem sat_silentGraph (h : HypModelCore c) {k : CtorSig} {vs : List GroundTerm} (hk : k ∈ hookSigs)
    (hvs : c.sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = true) :
    stdI c ⊧ᴵ (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) ≡ (match c.fallback k.name vs with
      | some v => den c v
      | none => ⊥)) :=
  AtT.sat_silentGraph (c := c) (T := StepM c) (h := h) (k := k) (vs := vs) (hk := hk) (hvs := hvs) (hh := hh) (hs := hs)

end Model

end Faithful

end KCore
