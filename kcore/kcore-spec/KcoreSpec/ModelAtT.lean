/-
  KCore. The value model at any transition T satisfies every part of `Γ` and `Γcl` that does not
  read the step: the signature, the constructors, the domains, the collections, the functions, the
  interpretation's values at silent points and Bool's closure (`model_parts_T`); each value denotes
  its own element (`den_val_T`); `•φ` is the elements with a T successor in φ (`sNext_iff_T`).

  The lemmas of namespace `AtT` are those of ModelCarrier.lean, ModelDen.lean, ModelSig.lean,
  ModelDomains.lean, ModelRead.lean, ModelColls.lean, ModelCons.lean, ModelPat.lean, ModelRules.lean,
  ModelStep.lean, ModelFns.lean, ModelFnsCl.lean and Confined.lean whose statements read the interpretation and that
  these proofs use, stated at `stdI_T c T` in place of `stdI c` (`evalApp_T c T` for `evalApp c`,
  `StepE_T c T` for `StepE c`), with the proofs of those files; the other lemmas of those files are
  used as they stand. The landed lemmas are the instances `T := StepM c` (`stdI c` is
  `stdI_T c (StepM c)` by definition).
-/
import KcoreSpec.ModelFns
import KcoreSpec.ModelFnsCl
import KcoreSpec.Confined

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

namespace AtT

/-- `φ` denotes exactly `x` in the value model at the transition `T`. -/
abbrev Sing (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (e : ML.Valuation Elem) (φ : KoreAML.P)
    (x : Elem) : Prop :=
  ∀ m, φ.interpret (stdI_T c T) e m ↔ m = x

/-- Every value of a sort denotes exactly its own element in the value model at `T`. -/
def DenGoalT (c : Semantics) (T : GroundTerm → GroundTerm → Prop) : Prop :=
  ∀ (v : GroundTerm) (s : Srt), c.sortOf v = some s → ∀ (e : ML.Valuation Elem) (m : Elem),
    (den c v).interpret (stdI_T c T) e m ↔ m = .val v

/-- `EqnAt` (ModelFns.lean) in the value model at `T`. -/
structure EqnAt (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (fn : Fn) (vars : List Srt)
    (tbl : KoreAML.VarTable) (e : ML.Valuation Elem) (ws : List GroundTerm) : Prop where
  R : KoreAML.VarKey.sortVar "R" ∈ tbl
  Xk : ∀ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s →
    KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl
  Vk : ∀ i < vars.length, canonKey c vars i ∈ tbl
  Rs : KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R")))
  args : ArgsAt c tbl e fn.args ws
  vin : ∀ i < vars.length, InSort c (vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c vars i)))

-- ModelCarrier.lean
section
set_option autoImplicit false
open ML
variable (c : Semantics)
variable {T : GroundTerm → GroundTerm → Prop}

/-- `⌈φ⌉` is everything wherever `φ` is not empty. -/
theorem defined_app (φ : KoreAML.P) (e : Valuation Elem) (m : Elem) :
    (⌈φ⌉ : KoreAML.P).interpret (stdI_T c T) e m ↔ ∃ a, φ.interpret (stdI_T c T) e a := by
  simp only [Pattern.interpret]
  constructor
  · rintro ⟨d, a, -, ha, -⟩; exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨.app .defined [], a, rfl, ha, True.intro⟩

end

-- ModelCarrier.lean
section
set_option autoImplicit false
open ML
variable (c : Semantics)
variable {T : GroundTerm → GroundTerm → Prop}

/-- **Definedness holds**: `∀x. ⌈x⌉`. -/
theorem model_sat_definedness (x : EVar) : stdI_T c T ⊧ᴵ @definedness KoreAML.Sym _ x := by
  intro e m
  simp only [definedness, Pattern.interpret]
  rintro ⟨a, ha⟩
  exact ha ⟨.app .defined [], _, rfl, rfl, True.intro⟩

end

-- ModelCarrier.lean
section
set_option autoImplicit false
open ML
variable (c : Semantics)
variable {T : GroundTerm → GroundTerm → Prop}

/-- A list of items holds in the model when each item's pattern does: `itemsPremises` adds only
the definedness axiom. -/
theorem sat_itemsPremises {its : List KoreAML.Item} (h : ∀ it ∈ its, stdI_T c T ⊧ᴵ it.pat) :
    stdI_T c T ⊧ᴵP KoreAML.itemsPremises its := by
  rintro φ (⟨it, hit, rfl⟩ | ⟨x, rfl⟩)
  · exact h it hit
  · exact model_sat_definedness c x

end

-- ModelDen.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- A symbol applied to the elements of values, one at a time, from a partial application. -/
theorem appE_sym {n : String} {k : CtorSig}
    (hres : ∀ args : List Elem, (∀ s, args.head? ≠ some (.srt s)) → resolve c n args = some (k, 0)) :
    ∀ (pre rest : List GroundTerm), pre.length < k.args.length → pre.length + rest.length = k.args.length →
      ∀ m, AppE (stdI_T c T) (.app (.sym n) (pre.map Elem.val)) (rest.map Elem.val) m ↔ result c k (pre ++ rest) m
  | pre, [], hlt, hlen, _ => by simp at hlen; omega
  | pre, w :: rest, hlt, hlen, m => by
    have hv2 : pre.map Elem.val ++ [Elem.val w] = (pre ++ [w]).map Elem.val := by simp
    have hr := hres ((pre ++ [w]).map Elem.val) (by intro s; cases pre <;> simp)
    have hl2 : ((pre ++ [w]).map Elem.val).length = pre.length + 1 := by simp
    have hev : ∀ x, (stdI_T c T).evalApp (.app (.sym n) (pre.map Elem.val)) (.val w) x ↔
        symAt c n ((pre ++ [w]).map Elem.val) x := fun x => by rw [← hv2]; exact Iff.rfl
    simp only [List.map_cons, AppE, hev]
    by_cases hl : pre.length + 1 < k.args.length
    · have ih := appE_sym hres (pre ++ [w]) rest (by simpa using hl) (by simp at hlen ⊢; omega) m
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
      simp only [symAt_full hr (by rw [hl2]; omega) (by rw [List.drop_zero, vals_map])]
      simp only [AppE, List.map_nil]
      constructor
      · rintro ⟨a', ha', rfl⟩; exact ha'
      · intro h; exact ⟨m, h, rfl⟩

end

-- ModelDen.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **A symbol of the semantics, at values**: the symbol of a name, applied to the elements of
values, gives what the symbol gives on the values (`result`). -/
theorem symE_vals (hn : NamesApartK c) {k : CtorSig} (hk : k ∈ kernelSyms c) {vs : List GroundTerm}
    (hl : vs.length = k.args.length) (m : Elem) :
    SymE (stdI_T c T) (c.symName k.name) (vs.map Elem.val) m ↔ result c k vs m := by
  have hinj : c.symName k.name ≠ "inj" := hn.2.1 k hk
  have hres := resolve_sym hn hk
  unfold SymE
  show (∃ a, evalSymb c (.symbol _) a ∧ _) ↔ _
  simp only [evalSymb_sym hn hk]
  by_cases h0 : k.args = []
  · simp only [if_pos h0]
    rw [h0] at hl
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hl
    simp only [List.map_nil, AppE]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro h; exact ⟨m, h, rfl⟩
  · simp only [if_neg h0]
    have := appE_sym (T := T) hres [] vs (by simp; exact List.length_pos_iff.mpr h0) (by simpa using hl) m
    simp only [List.map_nil, List.nil_append] at this
    constructor
    · rintro ⟨a, ha, h⟩; rw [ha] at h; exact this.mp h
    · intro h; exact ⟨_, rfl, this.mpr h⟩

end

-- ModelDen.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem sort_den (hn : NamesApartK c) {s : Srt} (hs : s < nRegSorts + c.sortNames.length)
    (e : Valuation Elem) (m : Elem) :
    (KoreAML.sym (.sort ("Sort" ++ c.sortName s))).interpret (stdI_T c T) e m ↔ m = .srt s := by
  show (∃ s', sortOfName c _ = some s' ∧ m = .srt s') ↔ _
  rw [sortOfName_eq hn hs]
  simp

end

-- ModelDen.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem stdI_symb (σ : KoreAML.Sym) : (stdI_T c T).evalSymb σ = evalSymb c σ := rfl

end

-- ModelDen.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem stdI_app : (stdI_T c T).evalApp = evalApp_T c T := rfl

end

-- ModelDen.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem evalApp_inj0 (b : Elem) : evalApp_T c T (.app .inj []) b = fun x => x = .app .inj [b] := rfl

end

-- ModelDen.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem evalApp_inj1 (a b : Elem) : evalApp_T c T (.app .inj [a]) b = fun x => x = .app .inj [a, b] := rfl

end

-- ModelDen.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem evalApp_inj2 (a b : Srt) (v : GroundTerm) :
    evalApp_T c T (.app .inj [.srt a, .srt b]) (.val v) = fun x => x = .val (injNormal a b v) := rfl

end

-- ModelDen.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- A collection's symbol applied to patterns that denote values: the value its library hook gives,
at the collection's sort. -/
theorem coll_app (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) {f g : Sym} {args : List Srt}
    (hf : (f = k.unit ∧ g = (builtinColl k.kind).unit ∧ args = []) ∨
      (f = k.elem ∧ g = (builtinColl k.kind).elem ∧ args = elemArgs k) ∨
      (f = k.concat ∧ g = (builtinColl k.kind).concat ∧ args = [k.sort, k.sort]))
    {vs : List GroundTerm} {φs : List KoreAML.P} {e : Valuation Elem}
    (H : All2 (fun φ x => ∀ m, φ.interpret (stdI_T c T) e m ↔ m = x) φs (vs.map Elem.val))
    (hlen : vs.length = args.length) {r : GroundTerm} (hv : hook g vs = some (some r))
    (hws : r.withSort (builtinColl k.kind).sort = r) (hsr : c.sortOf (r.withSort k.sort) = some k.sort)
    (m : Elem) :
    (KoreAML.appList (KoreAML.sym (.symbol (c.symName f))) φs).interpret (stdI_T c T) e m ↔
      m = .val (r.withSort k.sort) := by
  obtain ⟨kf, hkf, hkfn, hkfa, hres⟩ := coll_sym h hk hf
  rw [interp_symList _ φs _ H m, ← hkfn, symE_vals h.namesK hkf (by rw [hkfa]; exact hlen)]
  exact hres hv hws hsr m

end

-- ModelDen.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- A one-element set or list, from the reading of its element. -/
theorem den_elem1 (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .set ∨ k.kind = .list) (x : GroundTerm) (hs : c.sortOf (elemsVal k [x]) = some k.sort)
    {e : Valuation Elem} (hx : ∀ m, (den c x).interpret (stdI_T c T) e m ↔ m = .val x) :
    ∀ m, (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreElems c k [x])).interpret (stdI_T c T) e m ↔ m = .val (elemsVal k [x]) := by
  rw [GroundTerm.koreElems.eq_2, tr_ap]
  have H : All2 (fun φ x => ∀ m, φ.interpret (stdI_T c T) e m ↔ m = x)
      ([GroundTerm.kore c x].map (KoreAML.tr ⟨[], []⟩)) ([x].map Elem.val) := .cons hx .nil
  have hl := (elemArgs_length' hkind).symm
  rcases hkind with hkind | hkind
  · have hev : elemsVal k [x] = .set k.sort [x] := by unfold elemsVal; rw [hkind]
    rw [hev] at hs ⊢
    exact coll_app h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) H hl (r := .set Srt.set [x])
      (by rw [hkind, builtinColl_set, hook_setElem_eq]) (by rw [hkind, builtinColl_set]; rfl) hs
  · have hev : elemsVal k [x] = .list k.sort [x] := by unfold elemsVal; rw [hkind]
    rw [hev] at hs ⊢
    exact coll_app h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) H hl (r := .list Srt.list [x])
      (by rw [hkind, builtinColl_list, hook_listElem_eq]) (by rw [hkind, builtinColl_list]; rfl) hs

end

-- ModelDen.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

mutual

/-- **Every value denotes itself.** -/
theorem den_val (h : HypModelCore c) : ∀ (v : GroundTerm) {s : Srt}, c.sortOf v = some s →
    ∀ (e : Valuation Elem), Sing c T e (den c v) (.val v)
  | .ctor f ts, s, hv, e => by
    have hd : den c (.ctor f ts) = KoreAML.appList (KoreAML.sym (.symbol (c.symName f)))
        ((GroundTerm.koreList c ts).map (KoreAML.tr ⟨[], []⟩)) := by
      unfold den KoreAML.den; rw [GroundTerm.kore]; exact tr_ap _ _
    rcases c.sortOf_ctor_iff.mp hv with ⟨k, hk, hts', -⟩ | ⟨hk, o, ho, hts', -, -⟩
    · obtain ⟨hkm, hkn⟩ := lookupSig_spec hk
      have hks : k ∈ kernelSyms c :=
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hkm)))
      have hc : c.isCtor k.name = true := by unfold Semantics.isCtor; rw [hkn, hk]; rfl
      intro m
      rw [hd, interp_symList _ _ _ (den_list h ts hts' e) m, ← hkn,
        symE_vals h.namesK hks (sortsOf_length hts'), result_ctor hc]
    · -- a raw overloading application: the symbol's normal form, which is itself (`norm_fixed`)
      have H := h.ovlHyp
      obtain ⟨hon, hio, -⟩ := OvlLaws.ovl_facts H ho
      have hom : o ∈ c.ovls := List.mem_of_find?_eq_some ho
      have hks : o.sig ∈ kernelSyms c := List.mem_append_right _ (List.mem_map_of_mem hom)
      have hfix := OvlLaws.norm_fixed H ho hv
      intro m
      rw [hd, interp_symList _ _ _ (den_list h ts hts' e) m, ← hon,
        symE_vals h.namesK hks (sortsOf_length hts'), result_ovl (by rw [hon]; exact hio), hon, hfix]
  | .inj a b t, s, hv, e => by
    rw [Semantics.sortOf] at hv
    split at hv
    · rename_i hc
      cases hv
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
      obtain ⟨⟨hab, hni⟩, hta⟩ := hc
      obtain ⟨ha, hb⟩ := h.subSorts (List.contains_iff_mem.mp hab)
      have hd : den c (.inj a b t) = KoreAML.appList (KoreAML.sym (.symbol "inj"))
          [KoreAML.sym (.sort ("Sort" ++ c.sortName a)), KoreAML.sym (.sort ("Sort" ++ c.sortName b)), den c t] := by
        unfold den KoreAML.den; rw [GroundTerm.kore, KoreAML.tr_injP]; rfl
      intro m
      rw [hd, interp_appList_sing _ _ [.srt a, .srt b, .val t]
        (.cons (sort_den h.namesK ha e) (.cons (sort_den h.namesK hb e) (.cons (den_val h t hta e) .nil))) m]
      simp only [KoreAML.interp_sym, stdI_symb, evalSymb_inj, AppE, stdI_app, exists_eq_left,
        evalApp_inj0, evalApp_inj1, evalApp_inj2, injNormal_plain hni]
    · cases hv
  | .dv s0 lit, s, hv, e => by
    rw [Semantics.sortOf] at hv
    split at hv
    · rename_i hd0
      cases hv
      have hd : den c (.dv s0 lit) =
          KoreAML.sym (.dv lit.text) ⬝ KoreAML.sym (.sort ("Sort" ++ c.sortName s0)) := by
        unfold den KoreAML.den; rw [GroundTerm.kore, KoreAML.tr_dv]; rfl
      intro m
      rw [hd, KoreAML.interp_app]
      simp only [KoreAML.interp_sym, stdI_symb, sort_den h.namesK (h.dvSort hd0) e, stdI_app]
      constructor
      · rintro ⟨a, b, ha, rfl, hab⟩
        have ha' : a = .app (.dv lit.text) [] := ha
        subst ha'
        have hab' : ∃ l, m = .val (.dv s0 l) ∧ l.text = lit.text ∧ dvOK c.lib s0 l = true := hab
        obtain ⟨l, rfl, ht, hl⟩ := hab'
        rw [lit_unique h.lits hl hd0 ht]
      · rintro rfl
        exact ⟨_, _, rfl, rfl, lit, rfl, rfl, hd0⟩
    · cases hv
  | .map s0 es, s, hv, e => by
    obtain ⟨k, vs, hco, hkind, hval, hks, hent, rfl⟩ := sortOf_mapS_fwd hv
    obtain ⟨hk, hks0⟩ := collOf_spec hco
    rcases hkind with hkind | hkind
    rotate_left
    · subst hks0
      have hvs : vs = valSort k := by simp [valSort, hval]
      subst hvs
      obtain ⟨hr, -⟩ := (sortOf_rmK_iff hco hkind hval).mp hv
      have hd : den c (.map k.sort es) = KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries c k es) := by
        unfold den KoreAML.den; rw [GroundTerm.kore]; unfold Semantics.collSig; rw [hco]; rfl
      rw [hd]
      exact den_rmEntriesK h k hk hco hkind hval es hr hent e
    subst hks0
    have hvs : vs = valSort k := by simp [valSort, hval]
    subst hvs
    have hd : den c (.map k.sort es) = KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries c k es) := by
      unfold den KoreAML.den; rw [GroundTerm.kore]; unfold Semantics.collSig; rw [hco]; rfl
    rw [hd]
    exact den_entries h k hk hco hkind es hks hent e
  | .set s0 es, s, hv, e => by
    obtain ⟨rfl, k, hco, hkind⟩ := sortOf_set_some hv
    obtain ⟨hk, hks0⟩ := collOf_spec hco
    subst hks0
    have hev : elemsVal k es = .set k.sort es := by unfold elemsVal; rw [hkind]
    have hd : den c (.set k.sort es) = KoreAML.tr ⟨[], []⟩ (GroundTerm.koreElems c k es) := by
      unfold den KoreAML.den; rw [GroundTerm.kore]; unfold Semantics.collSig; rw [hco]; rfl
    rw [hd, ← hev]
    exact den_elems h k hk hco (.inl hkind) es (by rw [hev]; exact hv) e
  | .list s0 es, s, hv, e => by
    obtain ⟨rfl, k, hco, hkind⟩ := sortOf_list_some hv
    obtain ⟨hk, hks0⟩ := collOf_spec hco
    subst hks0
    have hev : elemsVal k es = .list k.sort es := by unfold elemsVal; rw [hkind]
    have hd : den c (.list k.sort es) = KoreAML.tr ⟨[], []⟩ (GroundTerm.koreElems c k es) := by
      unfold den KoreAML.den; rw [GroundTerm.kore]; unfold Semantics.collSig; rw [hco]; rfl
    rw [hd, ← hev]
    exact den_elems h k hk hco (.inr hkind) es (by rw [hev]; exact hv) e
  termination_by structural v => v

theorem den_list (h : HypModelCore c) : ∀ (ts : List GroundTerm) {ss : List Srt}, c.sortsOf ts = some ss →
    ∀ (e : Valuation Elem), All2 (fun φ x => Sing c T e φ x)
      ((GroundTerm.koreList c ts).map (KoreAML.tr ⟨[], []⟩)) (ts.map Elem.val)
  | [], _, _, _ => .nil
  | t :: ts, _, hts, e => by
    obtain ⟨s, ss', h1, h2, -⟩ := sortsOf_cons.mp hts
    exact .cons (den_val h t h1 e) (den_list h ts h2 e)
  termination_by structural ts => ts

theorem den_entries (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .map) : ∀ (es : List (GroundTerm × GroundTerm)), keysSorted es = true →
      c.entriesOK k.key (valSort k) es = true → ∀ (e : Valuation Elem),
      Sing c T e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries c k es)) (.val (.map k.sort es))
  | [], _, _, e => by
    rw [GroundTerm.koreEntries, tr_ap]
    exact coll_app h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) .nil rfl (r := .map Srt.map [])
      (by rw [hkind, builtinColl_map, Exec.hook_unit_eq]) (by rw [hkind, builtinColl_map]; rfl) ((sortOf_map_iff hco (h.mapVal hk hkind) hkind).mpr ⟨hkind, rfl, rfl⟩)
  | [x], _, hent, e => by
    rw [GroundTerm.koreEntries.eq_2]
    exact den_entry h k hk hco hkind x (entriesOK_cons'.mp hent).1 e
  | x :: y :: es, hs, hent, e => by
    obtain ⟨hx, hent'⟩ := entriesOK_cons'.mp hent
    have hs' := keysSorted_tail hs
    rw [GroundTerm.koreEntries.eq_3 c k x (y :: es) (List.cons_ne_nil _ _), tr_ap]
    exact coll_app h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (vs := [.map k.sort [x], .map k.sort (y :: es)])
      (.cons (den_entry h k hk hco hkind x hx e) (.cons (den_entries h k hk hco hkind (y :: es) hs' hent' e) .nil))
      rfl (r := .map Srt.map (x :: y :: es))
      (by rw [hkind, builtinColl_map, Exec.hook_concat_eq]; show some ((union [x] (y :: es)).map (GroundTerm.map Srt.map)) = _; rw [union_first hs]; rfl)
      (by rw [hkind, builtinColl_map]; rfl) ((sortOf_map_iff hco (h.mapVal hk hkind) hkind).mpr ⟨hkind, hs, hent⟩)
  termination_by structural es => es

theorem den_entry (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .map) : ∀ (x : GroundTerm × GroundTerm), c.entryOK k.key (valSort k) x = true →
      ∀ (e : Valuation Elem), Sing c T e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntry c k x)) (.val (.map k.sort [x]))
  | (a, b), hx, e => by
    obtain ⟨ha, hb⟩ := entryOK_iff.mp hx
    rw [GroundTerm.koreEntry, tr_ap]
    exact coll_app h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (vs := [a, b])
      (.cons (den_val h a ha e) (.cons (den_val h b hb e) .nil)) (elemArgs_length hkind).symm
      (r := .map Srt.map [(a, b)]) (by rw [hkind, builtinColl_map, Exec.hook_elem_eq]) (by rw [hkind, builtinColl_map]; rfl)
      ((sortOf_map_iff hco (h.mapVal hk hkind) hkind).mpr ⟨hkind, rfl, by simp [Semantics.entriesOK, hx]⟩)
  termination_by structural x => x

/-- A range map value of a collection of kind `.rangeMap`, the library's or the definition's own,
denotes itself: the unit, or its first entry's element concatenated with the rest. -/
theorem den_rmEntriesK (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .rangeMap) (hval : k.val = some (valSort k)) :
    ∀ (es : List (GroundTerm × GroundTerm)), rangesOK es = true →
      c.entriesOK k.key (valSort k) es = true → ∀ (e : Valuation Elem),
      Sing c T e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntries c k es)) (.val (.map k.sort es))
  | [], _, _, e => by
    rw [GroundTerm.koreEntries, tr_ap]
    exact coll_app h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) .nil rfl (r := rmV [])
      (by rw [hkind]; exact rmM_unit) (by rw [hkind]; rfl) ((sortOf_rmK_iff hco hkind hval).mpr ⟨rfl, rfl⟩)
  | [x], hr, hent, e => by
    rw [GroundTerm.koreEntries.eq_2]
    exact den_rmEntryK h k hk hco hkind hval x (by obtain ⟨_, _⟩ := x; exact rangesOK_head hr)
      (entriesOK_cons'.mp hent).1 e
  | x :: y :: es, hr, hent, e => by
    obtain ⟨hx, hent'⟩ := entriesOK_cons'.mp hent
    have hr' := rmM_tail hr
    rw [GroundTerm.koreEntries.eq_3 c _ x (y :: es) (List.cons_ne_nil _ _), tr_ap]
    exact coll_app h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (vs := [.map k.sort [x], .map k.sort (y :: es)])
      (.cons (den_rmEntryK h k hk hco hkind hval x (by obtain ⟨_, _⟩ := x; exact rangesOK_head hr) hx e)
        (.cons (den_rmEntriesK h k hk hco hkind hval (y :: es) hr' hent' e) .nil))
      rfl (r := rmV (x :: y :: es)) (by rw [hkind]; exact rmM_concat_sortK hr) (by rw [hkind]; rfl)
      ((sortOf_rmK_iff hco hkind hval).mpr ⟨hr, hent⟩)
  termination_by structural es => es

/-- One entry of a range map of a collection of kind `.rangeMap`: the element symbol at its proper
range and its value. -/
theorem den_rmEntryK (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .rangeMap) (hval : k.val = some (valSort k)) :
    ∀ (x : GroundTerm × GroundTerm), (asRange x.1).isSome = true →
      c.entryOK k.key (valSort k) x = true → ∀ (e : Valuation Elem),
      Sing c T e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreEntry c k x)) (.val (.map k.sort [x]))
  | (a, b), hr, hx, e => by
    obtain ⟨ha, hb⟩ := entryOK_iff.mp hx
    rw [GroundTerm.koreEntry, tr_ap]
    exact coll_app h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (vs := [a, b])
      (.cons (den_val h a ha e) (.cons (den_val h b hb e) .nil)) (by unfold elemArgs; rw [hkind]; rfl)
      (r := rmV [(a, b)]) (by rw [hkind]; exact rmM_elem hr) (by rw [hkind]; rfl)
      ((sortOf_rmK_iff hco hkind hval).mpr ⟨by simpa [rangesOK] using hr, by simp [Semantics.entriesOK, hx]⟩)
  termination_by structural x => x

theorem den_elems (h : HypModelCore c) (k : CollSig) (hk : k ∈ c.allColls) (hco : c.collOf k.sort = some k)
    (hkind : k.kind = .set ∨ k.kind = .list) : ∀ (es : List GroundTerm),
      c.sortOf (elemsVal k es) = some k.sort → ∀ (e : Valuation Elem),
      Sing c T e (KoreAML.tr ⟨[], []⟩ (GroundTerm.koreElems c k es)) (.val (elemsVal k es))
  | [], hs, e => by
    rw [GroundTerm.koreElems, tr_ap]
    rcases hkind with hkind | hkind
    · have hev : elemsVal k [] = .set k.sort [] := by unfold elemsVal; rw [hkind]
      rw [hev] at hs ⊢
      exact coll_app h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) .nil rfl (r := .set Srt.set [])
        (by rw [hkind, builtinColl_set, hook_setUnit_eq]) (by rw [hkind, builtinColl_set]; rfl) hs
    · have hev : elemsVal k [] = .list k.sort [] := by unfold elemsVal; rw [hkind]
      rw [hev] at hs ⊢
      exact coll_app h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) .nil rfl (r := .list Srt.list [])
        (by rw [hkind, builtinColl_list, hook_listUnit_eq]) (by rw [hkind, builtinColl_list]; rfl) hs
  | [x], hs, e => by
    have hx : c.sortOf x = some k.key := ((sortOf_elems_iff hco hkind).mp hs).2 x (List.mem_singleton_self _)
    rw [GroundTerm.koreElems.eq_2, tr_ap]
    have H : All2 (fun φ x => Sing c T e φ x) ([GroundTerm.kore c x].map (KoreAML.tr ⟨[], []⟩)) ([x].map Elem.val) :=
      .cons (den_val h x hx e) .nil
    have hl := (elemArgs_length' hkind).symm
    rcases hkind with hkind | hkind
    · have hev : elemsVal k [x] = .set k.sort [x] := by unfold elemsVal; rw [hkind]
      rw [hev] at hs ⊢
      exact coll_app h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) H hl (r := .set Srt.set [x])
        (by rw [hkind, builtinColl_set, hook_setElem_eq]) (by rw [hkind, builtinColl_set]; rfl) hs
    · have hev : elemsVal k [x] = .list k.sort [x] := by unfold elemsVal; rw [hkind]
      rw [hev] at hs ⊢
      exact coll_app h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) H hl (r := .list Srt.list [x])
        (by rw [hkind, builtinColl_list, hook_listElem_eq]) (by rw [hkind, builtinColl_list]; rfl) hs
  | x :: y :: es, hs, e => by
    obtain ⟨hso, hall⟩ := (sortOf_elems_iff hco hkind).mp hs
    have hx : c.sortOf x = some k.key := hall x (List.mem_cons_self ..)
    have hs1 : c.sortOf (elemsVal k [x]) = some k.sort :=
      (sortOf_elems_iff hco hkind).mpr ⟨fun _ => rfl, fun z hz => by rw [List.mem_singleton.mp hz]; exact hx⟩
    have hs2 : c.sortOf (elemsVal k (y :: es)) = some k.sort :=
      (sortOf_elems_iff hco hkind).mpr ⟨fun hk' => by
        have := hso hk'; simp only [elemsSorted, Bool.and_eq_true] at this; exact this.2,
        fun z hz => hall z (List.mem_cons_of_mem _ hz)⟩
    rw [GroundTerm.koreElems.eq_3 c k x (y :: es) (List.cons_ne_nil _ _), tr_ap]
    have H1 : Sing c T e (KoreAML.tr ⟨[], []⟩ (KoreAML.ap (c.symName k.elem) [GroundTerm.kore c x]))
        (.val (elemsVal k [x])) := by
      rw [← GroundTerm.koreElems.eq_2]
      exact den_elem1 h k hk hco hkind x hs1 (den_val h x hx e)
    have H2 := den_elems h k hk hco hkind (y :: es) hs2 e
    rcases hkind with hkind | hkind
    · have hev : ∀ l, elemsVal k l = .set k.sort l := fun l => by unfold elemsVal; rw [hkind]
      rw [hev] at hs H1 H2 ⊢
      exact coll_app h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (vs := [.set k.sort [x], .set k.sort (y :: es)])
        (.cons H1 (.cons H2 .nil)) rfl (r := .set Srt.set (x :: y :: es))
        (by rw [hkind, builtinColl_set, hook_setConcat_eq]; show some ((concatS [x] (y :: es)).map (GroundTerm.set Srt.set)) = _
            rw [concatS_first (elemsSorted_iff.mp (hso hkind))]; rfl)
        (by rw [hkind, builtinColl_set]; rfl) hs
    · have hev : ∀ l, elemsVal k l = .list k.sort l := fun l => by unfold elemsVal; rw [hkind]
      rw [hev] at hs H1 H2 ⊢
      exact coll_app h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (vs := [.list k.sort [x], .list k.sort (y :: es)])
        (.cons H1 (.cons H2 .nil)) rfl (r := .list Srt.list (x :: y :: es))
        (by rw [hkind, builtinColl_list, hook_listConcat_eq]; rfl) (by rw [hkind, builtinColl_list]; rfl) hs
  termination_by structural es => es

end

end

-- ModelDen.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **`DenGoal`**: under `HypModelCore`, every value of a sort denotes exactly its own element. -/
theorem denGoal (h : HypModelCore c) : DenGoalT c T :=
  fun v _ hv e m => den_val h v hv e m

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem defOK_std : KoreAML.DefOK (stdI_T c T) := KoreAML.defOK_of (model_sat_definedness c)

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem inh_srt (s : Srt) (m : Elem) : KoreAML.Inh (stdI_T c T) (.srt s) m ↔ InSort c s m := by
  constructor
  · rintro ⟨i, hi, h⟩
    have hi' : i = .app .inh [] := hi
    subst hi'
    exact h
  · intro h
    exact ⟨.app .inh [], rfl, h⟩

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- The inhabitants of a numbered sort, by its name: its values. -/
theorem inhOf_sort (hn : NamesApartK c) {s : Srt} (hs : s < nRegSorts + c.sortNames.length)
    (e : Valuation Elem) (m : Elem) :
    (KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName s)))).interpret (stdI_T c T) e m ↔ InSort c s m := by
  rw [KoreAML.interp_inhOf_of (sort_den hn hs e), inh_srt]

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem guarded_intro {ws : List KoreAML.P} {φ : KoreAML.P} {e : Valuation Elem} {m : Elem}
    (h : (∀ w ∈ ws, w.interpret (stdI_T c T) e m) → φ.interpret (stdI_T c T) e m) :
    (KoreAML.guarded ws φ).interpret (stdI_T c T) e m := by
  cases ws with
  | nil => exact h (fun _ hw => nomatch hw)
  | cons w ws => intro hc; exact h (conjList_elim hc)

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem sortGuard_iff {x : EVar} {e : Valuation Elem} {m : Elem} :
    (KoreAML.sortGuard x).interpret (stdI_T c T) e m ↔ ∃ s ∈ kernelSorts c, e.evalEvar x = .srt s := by
  unfold KoreAML.sortGuard
  rw [KoreAML.interp_member defOK_std, KoreAML.interp_sortsDomain, isSort_iff]

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem inhOf_evar {x : EVar} {e : Valuation Elem} {s : Srt} (hx : e.evalEvar x = .srt s) (m : Elem) :
    (KoreAML.inhOf (.evar x)).interpret (stdI_T c T) e m ↔ InSort c s m := by
  rw [KoreAML.interp_inhOf_of (σ := .srt s) (fun a => by rw [KoreAML.interp_evar, hx]), inh_srt]

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelSig.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelDomains.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem den_koreList (h : HypModelCore c) {vs : List GroundTerm} {ss : List Srt} (hvs : c.sortsOf vs = some ss)
    (e : Valuation Elem) :
    All2 (fun φ x => ∀ m, φ.interpret (stdI_T c T) e m ↔ m = x)
      ((GroundTerm.koreList c vs).map (KoreAML.tr ⟨[], []⟩)) (vs.map Elem.val) :=
  den_list h vs hvs e

end

-- ModelDomains.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelDomains.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelDomains.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelDomains.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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
    have hsv := hookRes_sorted (fun _ => (sortCtx_of_allCl h.sound.1 h.sound.2.1 h.ovlCase).range) hk' hvs hr
    dsimp only
    rw [den_val h v hsv e a]
    constructor
    · rintro ⟨v', rfl, hv'⟩; rw [hr] at hv'; cases hv'; rfl
    · rintro rfl; exact ⟨v, rfl, hr⟩

end

-- ModelDomains.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelDomains.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelDomains.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_distinct (h : HypModelCore c) {v w : GroundTerm} {s : Srt} (hv : c.sortOf v = some s)
    (hw : c.sortOf w = some s) (hne : GroundTerm.cmp v w ≠ .eq) : stdI_T c T ⊧ᴵ ∼(den c v ⋀ den c w) := by
  intro e m
  rw [interpret_neg, interpret_conj, den_val h v hv, den_val h w hw]
  rintro ⟨rfl, hvw⟩
  cases hvw
  exact hne (GroundTerm.cmp_refl v)

end

-- ModelDomains.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelDomains.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem symP_unit_of {k : CollSig} {e : Valuation Elem} {x : Elem}
    (hs : SymE (stdI_T c T) (c.symName k.unit) [] x) :
    (symP (c.symName k.unit)).interpret (stdI_T c T) e x := by
  obtain ⟨a, ha, hx⟩ := hs
  have : x = a := hx
  subst this
  exact ha

end

-- ModelDomains.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- An application `f(φ₁, …, φₙ)` holds of `x` when `f` applied to elements of the `φᵢ` gives `x`. -/
theorem appList_of {f : String} {φs : List KoreAML.P} {bs : List Elem} {e : Valuation Elem} {x : Elem}
    (hb : All2 (fun φ b => φ.interpret (stdI_T c T) e b) φs bs) (hs : SymE (stdI_T c T) f bs x) :
    (KoreAML.appList (symP f) φs).interpret (stdI_T c T) e x := by
  obtain ⟨a, ha, hx⟩ := hs
  rw [interp_appList]
  exact ⟨a, ha, bs, hb, hx⟩

end

-- ModelDomains.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelDomains.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
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

end

-- ModelDomains.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- The value model satisfies the interpretation's values at silent points: there an interpreted
symbol's result (`result`, through `hookRes`) is the fallback. -/
theorem sat_silentGraph (h : HypModelCore c) {k : CtorSig} {vs : List GroundTerm} (hk : k ∈ hookSigs)
    (hvs : c.sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = true) :
    stdI_T c T ⊧ᴵ (KoreAML.den (symApp c k.name (GroundTerm.koreList c vs)) ≡ (match c.fallback k.name vs with
      | some v => den c v
      | none => ⊥)) :=
  sat_hookGraph h hk hvs (Semantics.hookRes_of_silent hh hs)

end

-- ModelRead.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {vs : List KoreAML.Var} {tbl : KoreAML.VarTable} {e : Valuation Elem} {σ : Subst}
variable {T : GroundTerm → GroundTerm → Prop}

/-- Elements of the arguments' readings are the values of a list of evaluations. -/
theorem args_read {ts : List Term}
    (ih : ∀ t ∈ ts, ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret (stdI_T c T) e m ↔
      ∃ v, EvalTerm c σ t (some v) ∧ m = .val v) :
    ∀ {bs : List Elem}, All2 (fun φ b => φ.interpret (stdI_T c T) e b)
      ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) bs →
      ∃ ws : List GroundTerm, bs = ws.map Elem.val ∧ EvalTerms c σ ts (ws.map some) := by
  induction ts with
  | nil => intro bs h; cases h; exact ⟨[], rfl, .nil⟩
  | cons t ts iht =>
    intro bs h
    cases h with
    | cons hb hbs =>
      obtain ⟨v, hv, rfl⟩ := (ih t (List.mem_cons_self ..) _).mp hb
      obtain ⟨ws, rfl, hws⟩ := iht (fun t' ht' => ih t' (List.mem_cons_of_mem _ ht')) hbs
      exact ⟨v :: ws, rfl, .cons hv hws⟩

end

-- ModelRead.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {vs : List KoreAML.Var} {tbl : KoreAML.VarTable} {e : Valuation Elem} {σ : Subst}
variable {T : GroundTerm → GroundTerm → Prop}

/-- The values of defined evaluations of the arguments are elements of their readings. -/
theorem args_read' {ts : List Term}
    (ih : ∀ t ∈ ts, ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret (stdI_T c T) e m ↔
      ∃ v, EvalTerm c σ t (some v) ∧ m = .val v) :
    ∀ {rs : List (Option GroundTerm)} {ws : List GroundTerm}, EvalTerms c σ ts rs → allSome rs = some ws →
      All2 (fun φ b => φ.interpret (stdI_T c T) e b) ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩))
        (ws.map Elem.val) := by
  induction ts with
  | nil => intro rs ws h hs; cases h; cases hs; exact .nil
  | cons t ts iht =>
    intro rs ws h hs
    cases h with
    | cons ht hts =>
      rename_i r rs'
      cases r with
      | none => simp [allSome] at hs
      | some v =>
        cases hr : allSome rs' with
        | none => simp [allSome, hr] at hs
        | some ws' =>
          simp only [allSome, hr, Option.bind_some, Option.map_some, Option.some.injEq] at hs
          subst hs
          exact .cons ((ih t (List.mem_cons_self ..) _).mpr ⟨v, ht, rfl⟩)
            (iht (fun t' ht' => ih t' (List.mem_cons_of_mem _ ht')) hts hr)

end

-- ModelRead.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- The head of an application as `Term.kore` writes it, applied to argument elements: what the
symbol gives on their values. -/
theorem head_app (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {tbl : KoreAML.VarTable}
    {vs : List KoreAML.Var} {ts : List Term} {e : Valuation Elem} {ws : List GroundTerm}
    (hl : ws.length = k.args.length) (m : Elem) :
    (∃ a, (match iteSort? (c.symName k.name) with
        | some X => KoreAML.sym (.symbol "Lblite") ⬝ KoreAML.sym (.sort ("Sort" ++ X))
        | none => KoreAML.sym (.symbol (c.symName k.name))).interpret (stdI_T c T) e a ∧
      AppE (stdI_T c T) a (ws.map Elem.val) m) ↔ result c k ws m := by
  cases hi : iteSort? (c.symName k.name) with
  | none => exact symE_vals h.namesK hk hl m
  | some X => exact lblite_app h hk hi hl e m

end

-- ModelRead.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **The reading of a term**: under a valuation that reads each variable as its value in σ, a
term denotes exactly the values `EvalTerm` gives it under σ. -/
theorem tr_term (h : HypModelCore c) {P : Nat → Prop} {vs : List KoreAML.Var} {tbl : KoreAML.VarTable}
    {e : Valuation Elem} {σ : Subst}
    (hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v) {t : Term} (ht : TermOK c P t) :
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret (stdI_T c T) e m ↔
      ∃ v, EvalTerm c σ t (some v) ∧ m = .val v := by
  have hn := h.namesK
  induction ht with
  | @var i hi =>
    intro m
    rw [Term.kore, hvar i hi m]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, by rw [← hv]; exact .var, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, (evalTerm_var_inv hv).symm, rfl⟩
  | @dv s lit hd =>
    intro m
    rw [Term.kore, KoreAML.tr]
    show (KoreAML.sym (.dv lit.text) ⬝ KoreAML.trSort tbl (KoreAML.srt (c.sortName s))).interpret (stdI_T c T) e m ↔ _
    rw [trSort_srt, KoreAML.interp_app]
    simp only [KoreAML.interp_sym, stdI_symb, sort_den hn (h.dvSort hd) e, stdI_app]
    constructor
    · rintro ⟨a, b, ha, rfl, hab⟩
      have ha' : a = .app (.dv lit.text) [] := ha
      subst ha'
      have hab' : ∃ l, m = .val (.dv s l) ∧ l.text = lit.text ∧ dvOK c.lib s l = true := hab
      obtain ⟨l, rfl, hlt, hl⟩ := hab'
      rw [lit_unique h.lits hl hd hlt]
      exact ⟨_, .dv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      cases evalTerm_dv_inv hv
      exact ⟨_, _, rfl, rfl, lit, rfl, rfl, hd⟩
  | @inj a b t ha hb _ ih =>
    intro m
    rw [Term.kore, KoreAML.tr_injP]
    rw [interp_appList]
    simp only [KoreAML.interp_sym, stdI_symb, evalSymb_inj]
    constructor
    · rintro ⟨a0, rfl, bs, hbs, happ⟩
      cases hbs with
      | cons h1 hbs =>
        cases hbs with
        | cons h2 hbs =>
          cases hbs with
          | cons h3 hbs =>
            cases hbs
            rename_i x1 x2 x3
            have e1 : x1 = .srt a := (sort_den hn ha e x1).mp h1
            have e2 : x2 = .srt b := (sort_den hn hb e x2).mp h2
            subst e1 e2
            obtain ⟨w, hw, rfl⟩ := (ih x3).mp h3
            simp only [AppE, stdI_app, evalApp_inj0, evalApp_inj1, evalApp_inj2, exists_eq_left] at happ
            subst happ
            exact ⟨injNormal a b w, EvalTerm.inj hw, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨r', hr', hr⟩ := evalTerm_inj_inv hv
      cases r' with
      | none => cases hr
      | some w =>
        simp only [Option.map_some, Option.some.injEq] at hr
        subst hr
        refine ⟨_, rfl, [.srt a, .srt b, .val w], .cons ((sort_den hn ha e _).mpr rfl)
          (.cons ((sort_den hn hb e _).mpr rfl) (.cons ((ih _).mpr ⟨w, hr', rfl⟩) .nil)), ?_⟩
        simp only [AppE, stdI_app, evalApp_inj0, evalApp_inj1, evalApp_inj2, exists_eq_left]
  | @app f ts k hk hkn hl _ ih =>
    intro m
    subst hkn
    rw [kore_app_tr, interp_appList]
    constructor
    · rintro ⟨a, ha, bs, hbs, happ⟩
      obtain ⟨ws, rfl, hws⟩ := args_read (T := T) ih hbs
      have hlw : ws.length = k.args.length := by
        rw [← hl, evalTerms_length hws]; simp
      have hr := (head_app h hk (tbl := tbl) (vs := vs) (ts := ts) hlw m).mp ⟨a, ha, happ⟩
      unfold result at hr
      by_cases hc : c.isCtor k.name = true
      · rw [if_pos hc] at hr
        subst hr
        refine ⟨_, ?_, rfl⟩
        have := EvalTerm.ctor (σ := σ) hc hws
        rw [allSome_map] at this
        exact this
      rw [if_neg hc] at hr
      have hc' : c.isCtor k.name = false := by simpa using hc
      by_cases hh : isHook k.name = true
      · rw [if_pos hh] at hr
        obtain ⟨v, rfl, hv⟩ := hr
        exact ⟨v, .hook hc' hh hws (fun ws' h' => by rw [allSome_map] at h'; cases h'; exact hv)
          (fun h' => by rw [allSome_map] at h'; cases h'), rfl⟩
      rw [if_neg hh] at hr
      have hh' : isHook k.name = false := by simpa using hh
      by_cases hp : c.isParam k.name = true
      · rw [if_pos hp] at hr
        obtain ⟨v, rfl, hv⟩ := hr
        exact ⟨v, .param hc' hh' hp hws (by rw [allSome_map]; exact hv.symm), rfl⟩
      rw [if_neg hp] at hr
      have hp' : c.isParam k.name = false := by simpa using hp
      by_cases ho : c.isOvl k.name = true
      · rw [if_pos ho] at hr
        subst hr
        refine ⟨_, ?_, rfl⟩
        have := EvalTerm.ovl (σ := σ) hc' ho hws
        rw [allSome_map] at this
        exact this
      rw [if_neg ho] at hr
      obtain ⟨v, rfl, hv⟩ := hr
      exact ⟨v, .call hc' hh' hws (allSome_map ws) hv hp', rfl⟩
    · rintro ⟨v, hv, rfl⟩
      have key : ∀ (rs : List (Option GroundTerm)) (ws : List GroundTerm), EvalTerms c σ ts rs →
          allSome rs = some ws → result c k ws (.val v) →
          ∃ a, (match iteSort? (c.symName k.name) with
            | some X => KoreAML.sym (.symbol "Lblite") ⬝ KoreAML.sym (.sort ("Sort" ++ X))
            | none => KoreAML.sym (.symbol (c.symName k.name))).interpret (stdI_T c T) e a ∧
            ∃ bs, All2 (fun φ b => φ.interpret (stdI_T c T) e b)
              ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) bs ∧ AppE (stdI_T c T) a bs (.val v) := by
        intro rs ws hts hws hres
        have hlw : ws.length = k.args.length := by
          rw [← hl, evalTerms_length hts, allSome_length hws]
        obtain ⟨a, ha, happ⟩ := (head_app h hk (tbl := tbl) (vs := vs) (ts := ts) hlw _).mpr hres
        exact ⟨a, ha, _, args_read' ih hts hws, happ⟩
      generalize hr : some v = r at hv
      cases hv with
      | ctor hc hts =>
        rename_i rs
        cases hws : allSome rs with
        | none => rw [hws] at hr; cases hr
        | some ws =>
          rw [hws] at hr
          simp only [Option.map_some, Option.some.injEq] at hr
          subst hr
          exact key rs ws hts hws ((result_ctor hc _).mpr rfl)
      | hook hc hhk hts hh hund =>
        rename_i rs
        subst hr
        cases hws : allSome rs with
        | none => exact absurd (hund hws) (by simp)
        | some ws => exact key rs ws hts hws ((result_hook hc hhk _).mpr
          ⟨v, rfl, hh ws hws⟩)
      | param hc hhk hp hts hr' =>
        rename_i rs
        subst hr
        cases hws : allSome rs with
        | none => rw [hws] at hr'; cases hr'
        | some ws =>
          rw [hws] at hr'
          exact key rs ws hts hws ((result_param hc hhk hp _).mpr ⟨v, rfl, hr'.symm⟩)
      | call hc hh hts hvs hf hp =>
        rename_i rs ws
        subst hr
        exact key rs ws hts hvs ((result_fn hc hh hp (Eval.isOvl_false hf) _).mpr ⟨v, rfl, hf⟩)
      | callUndef => cases hr
      | ovl hc ho hts =>
        rename_i rs
        cases hws : allSome rs with
        | none => rw [hws] at hr; cases hr
        | some ws =>
          rw [hws] at hr
          simp only [Option.map_some, Option.some.injEq] at hr
          subst hr
          exact key rs ws hts hws ((result_ovl ho _).mpr rfl)

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .map)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem U_map (e : Valuation Elem) (x : Elem) :
    (collU c k).interpret (stdI_T c T) e x ↔ x = .val (.map k.sort []) := by
  have hco := h.collOf_self hk
  have := coll_symE (T := T) h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) rfl (r := .map Srt.map [])
    (by rw [hkind, builtinColl_map, Exec.hook_unit_eq]) (by rw [hkind, builtinColl_map]; rfl)
    ((sortOf_map_iff hco (h.mapVal hk hkind) hkind).mpr ⟨hkind, rfl, rfl⟩) x
  refine Iff.trans ?_ this
  unfold collU symP SymE
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨a, ha, hx⟩; have : x = a := hx; subst this; exact ha

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .map)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem E_map {e : Valuation Elem} {A B : EVar} {a b : GroundTerm} (ha : c.sortOf a = some k.key)
    (hb : c.sortOf b = some (valSort k)) (hA : e.evalEvar A = .val a) (hB : e.evalEvar B = .val b) (x : Elem) :
    (collE c k (.evar A) (.evar B)).interpret (stdI_T c T) e x ↔ x = .val (.map k.sort [(a, b)]) := by
  have hco := h.collOf_self hk
  unfold collE symP
  rw [interp_symList _ _ [.val a, .val b]
    (.cons (fun m => by rw [KoreAML.interp_evar, hA]) (.cons (fun m => by rw [KoreAML.interp_evar, hB]) .nil)) x]
  exact coll_symE h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (vs := [a, b]) (elemArgs_length hkind).symm
    (r := .map Srt.map [(a, b)]) (by rw [hkind, builtinColl_map, Exec.hook_elem_eq])
    (by rw [hkind, builtinColl_map]; rfl)
    ((sortOf_map_iff hco (h.mapVal hk hkind) hkind).mpr ⟨hkind, rfl, by simp [Semantics.entriesOK, Semantics.entryOK, ha, hb]⟩) x

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .map)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem C_map {e : Valuation Elem} {φ ψ : KoreAML.P} {es1 es2 : Entries}
    (h1 : keysSorted es1 = true ∧ c.entriesOK k.key (valSort k) es1 = true)
    (h2 : keysSorted es2 = true ∧ c.entriesOK k.key (valSort k) es2 = true)
    (hφ : ∀ m, φ.interpret (stdI_T c T) e m ↔ m = .val (.map k.sort es1))
    (hψ : ∀ m, ψ.interpret (stdI_T c T) e m ↔ m = .val (.map k.sort es2)) (x : Elem) :
    (collC c k φ ψ).interpret (stdI_T c T) e x ↔ ∃ u, union es1 es2 = some u ∧ x = .val (.map k.sort u) := by
  have hco := h.collOf_self hk
  have hcc : (c.symName k.concat = c.symName k.concat ∧ (builtinColl k.kind).concat = (builtinColl k.kind).concat ∧
      [k.sort, k.sort] = [k.sort, k.sort]) := ⟨rfl, rfl, rfl⟩
  obtain ⟨kf, hkf, hkfn, hkfa, hres⟩ := coll_sym h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  unfold collC symP
  rw [interp_symList _ _ [.val (.map k.sort es1), .val (.map k.sort es2)] (.cons hφ (.cons hψ .nil)) x,
    show [Elem.val (.map k.sort es1), Elem.val (.map k.sort es2)] = [GroundTerm.map k.sort es1, .map k.sort es2].map Elem.val
      from rfl, ← hkfn, symE_vals h.namesK hkf (by rw [hkfa]; rfl)]
  have hhook : hook (builtinColl k.kind).concat [.map k.sort es1, .map k.sort es2] =
      some ((union es1 es2).map (GroundTerm.map Srt.map)) := by
    rw [hkind, builtinColl_map, Exec.hook_concat_eq]
  have hsr : ∀ u, union es1 es2 = some u → c.sortOf ((GroundTerm.map Srt.map u).withSort k.sort) = some k.sort :=
    fun u hu => by
      refine (sortOf_map_iff hco (h.mapVal hk hkind) hkind).mpr ⟨hkind, union_sorted h2.1 hu, entriesOK_iff.mpr fun e he => ?_⟩
      rcases (union_spec hu).1 e |>.mp he with he | he
      · exact entriesOK_iff.mp h1.2 e he
      · exact entriesOK_iff.mp h2.2 e he
  constructor
  · intro hr
    obtain ⟨v, hv⟩ := coll_sym_inv h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
      (by rw [hkind]; exact silentKey_of_mem rfl) hkfn hr
    have hv0 := hv
    rw [hhook] at hv0
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hv0)
    exact ⟨u, hu, (hres hv (by rw [hkind, builtinColl_map]; rfl) (hsr u hu) x).mp hr⟩
  · rintro ⟨u, hu, rfl⟩
    have hv : hook (builtinColl k.kind).concat [.map k.sort es1, .map k.sort es2] = some (some (.map Srt.map u)) := by
      rw [hhook, hu]; rfl
    exact (hres hv (by rw [hkind, builtinColl_map]; rfl) (hsr u hu) _).mpr rfl

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem evar_eq_iff {e : Valuation Elem} {x : EVar} {φ : KoreAML.P} {w : Elem} (hx : e.evalEvar x = w)
    (hφ : ∀ m, φ.interpret (stdI_T c T) e m ↔ m = w) (m : Elem) :
    (Pattern.evar x ≡ φ : KoreAML.P).interpret (stdI_T c T) e m := by
  rw [KoreAML.interp_equal defOK_std]
  intro a
  rw [KoreAML.interp_evar, hx, hφ]

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem guard_val (hn : NamesApartK c) {s : Srt} (hs : s < nRegSorts + c.sortNames.length) {x : EVar}
    {e : Valuation Elem} {m : Elem} (hg : (x ∈∈ inSort c s : KoreAML.P).interpret (stdI_T c T) e m) :
    ∃ v, e.evalEvar x = .val v ∧ c.sortOf v = some s := by
  rw [KoreAML.interp_member defOK_std] at hg
  unfold inSort sortP at hg
  exact inSort_val ((inhOf_sort hn hs e _).mp hg)

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .map)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_mapUnitSplit : stdI_T c T ⊧ᴵ mapUnitSplitAx c k := by
  obtain ⟨hsS, -, -⟩ := h.collSorts hk
  intro e m
  unfold mapUnitSplitAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨w1, h1, hw1⟩ := guard_val (T := T) h.namesK hsS (hg _ (List.mem_cons_self ..))
  obtain ⟨w2, h2, hw2⟩ := guard_val (T := T) h.namesK hsS (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain ⟨es1, rfl, hs1, he1⟩ := map_val h hk hkind hw1
  obtain ⟨es2, rfl, hs2, he2⟩ := map_val h hk hkind hw2
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, U_map h hk hkind, C_map h hk hkind ⟨hs1, he1⟩ ⟨hs2, he2⟩
    (fun m => by rw [KoreAML.interp_evar, h1]) (fun m => by rw [KoreAML.interp_evar, h2])] at hx
  obtain ⟨rfl, u, hu, hx⟩ := hx
  cases hx
  obtain ⟨rfl, rfl⟩ := union_nil hu
  rw [interpret_conj]
  exact ⟨evar_eq_iff h1 (U_map h hk hkind e) m, evar_eq_iff h2 (U_map h hk hkind e) m⟩

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .map)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_mapElemNotUnit : stdI_T c T ⊧ᴵ mapElemNotUnitAx c k := by
  obtain ⟨-, hsK, hsV⟩ := h.collSorts hk
  intro e m
  unfold mapElemNotUnitAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_self ..))
  obtain ⟨b, hb, hwb⟩ := guard_val (T := T) h.namesK hsV (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  rw [interpret_neg, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, U_map h hk hkind, E_map h hk hkind hwa hwb ha hb] at hx
  obtain ⟨rfl, hx⟩ := hx
  cases hx

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .map)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_mapElemAtom : stdI_T c T ⊧ᴵ mapElemAtomAx c k := by
  obtain ⟨hsS, hsK, hsV⟩ := h.collSorts hk
  intro e m
  unfold mapElemAtomAx
  dsimp only
  refine guarded_intro fun hg => ?_
  have g := fun i (hi : i < 5) => hg _ (List.getElem_mem (l := [(⟨1⟩ : EVar) ∈∈ inSort c k.key, (⟨2⟩ : EVar) ∈∈ inSort c (valSort k),
    (⟨3⟩ : EVar) ∈∈ inSort c k.key, (⟨4⟩ : EVar) ∈∈ inSort c (valSort k), (⟨5⟩ : EVar) ∈∈ inSort c k.sort]) hi)
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (g 0 (by decide))
  obtain ⟨b, hb, hwb⟩ := guard_val (T := T) h.namesK hsV (g 1 (by decide))
  obtain ⟨a', ha', hwa'⟩ := guard_val (T := T) h.namesK hsK (g 2 (by decide))
  obtain ⟨b', hb', hwb'⟩ := guard_val (T := T) h.namesK hsV (g 3 (by decide))
  obtain ⟨w, hr, hw⟩ := guard_val (T := T) h.namesK hsS (g 4 (by decide))
  obtain ⟨rs, rfl, hrs, hre⟩ := map_val h hk hkind hw
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, E_map h hk hkind hwa' hwb' ha' hb',
    C_map h hk hkind ⟨rfl, by simp [Semantics.entriesOK, Semantics.entryOK, hwa, hwb]⟩ ⟨hrs, hre⟩
      (E_map h hk hkind hwa hwb ha hb) (fun m => by rw [KoreAML.interp_evar, hr])] at hx
  obtain ⟨rfl, u, hu, hx⟩ := hx
  cases hx
  obtain ⟨rfl, hp⟩ := union_single hu
  cases hp
  simp only [interpret_conj]
  exact ⟨⟨evar_eq_iff ha (fun m => by rw [KoreAML.interp_evar, ha']) m,
    evar_eq_iff hb (fun m => by rw [KoreAML.interp_evar, hb']) m⟩, evar_eq_iff hr (U_map h hk hkind e) m⟩

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .map)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_mapDecomp : stdI_T c T ⊧ᴵ mapDecompAx c k := by
  obtain ⟨hsS, hsK, hsV⟩ := h.collSorts hk
  intro e m
  unfold mapDecompAx
  dsimp only
  refine guarded_intro fun hg => ?_
  have g := fun i (hi : i < 5) => hg _ (List.getElem_mem (l := [(⟨1⟩ : EVar) ∈∈ inSort c k.key, (⟨2⟩ : EVar) ∈∈ inSort c (valSort k),
    (⟨3⟩ : EVar) ∈∈ inSort c k.sort, (⟨4⟩ : EVar) ∈∈ inSort c k.sort, (⟨5⟩ : EVar) ∈∈ inSort c k.sort]) hi)
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (g 0 (by decide))
  obtain ⟨b, hb, hwb⟩ := guard_val (T := T) h.namesK hsV (g 1 (by decide))
  obtain ⟨wr, hr, hwr⟩ := guard_val (T := T) h.namesK hsS (g 2 (by decide))
  obtain ⟨w1, h1, hw1⟩ := guard_val (T := T) h.namesK hsS (g 3 (by decide))
  obtain ⟨w2, h2, hw2⟩ := guard_val (T := T) h.namesK hsS (g 4 (by decide))
  obtain ⟨rs, rfl, hrs, hre⟩ := map_val h hk hkind hwr
  obtain ⟨es1, rfl, hs1, he1⟩ := map_val h hk hkind hw1
  obtain ⟨es2, rfl, hs2, he2⟩ := map_val h hk hkind hw2
  have hab : keysSorted [(a, b)] = true ∧ c.entriesOK k.key (valSort k) [(a, b)] = true :=
    ⟨rfl, by simp [Semantics.entriesOK, Semantics.entryOK, hwa, hwb]⟩
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, C_map h hk hkind hab ⟨hrs, hre⟩ (E_map h hk hkind hwa hwb ha hb)
      (fun m => by rw [KoreAML.interp_evar, hr]),
    C_map h hk hkind ⟨hs1, he1⟩ ⟨hs2, he2⟩ (fun m => by rw [KoreAML.interp_evar, h1])
      (fun m => by rw [KoreAML.interp_evar, h2])] at hx
  obtain ⟨⟨u, hu, rfl⟩, u', hu', hx⟩ := hx
  cases hx
  have hdrop : ∀ es : Entries, keysSorted es = true → c.entriesOK k.key (valSort k) es = true →
      keysSorted (dropKey a es) = true ∧ c.entriesOK k.key (valSort k) (dropKey a es) = true := fun es hs he =>
    ⟨sorted_sublist (dropKey_sublist _ _) hs,
      entriesOK_iff.mpr fun e' he' => entriesOK_iff.mp he e' (mem_dropKey.mp he').1⟩
  have hsy : ∀ ys : Entries, keysSorted ys = true → c.entriesOK k.key (valSort k) ys = true →
      c.sortOf (.map k.sort ys) = some k.sort := fun ys h1 h2 =>
    (sortOf_map_iff (h.collOf_self hk) (h.mapVal hk hkind) hkind).mpr ⟨hkind, h1, h2⟩
  -- the valuation with `y` (index 6) set to the element of `ys`
  have hval : ∀ ys : Entries, ∀ i, i ≠ 6 →
      (⟨Function.update e.evalEvar ⟨6⟩ (.val (.map k.sort ys)), e.evalSvar⟩ : Valuation Elem).evalEvar ⟨i⟩ =
        e.evalEvar ⟨i⟩ := fun ys i hi => upd_ne hi _
  rw [interpret_disj]
  rcases map_decomp hrs hs1 hs2 hu hu' with ⟨hl, hrr⟩ | ⟨hl, hrr⟩
  · left
    obtain ⟨hys, hye⟩ := hdrop es1 hs1 he1
    rw [KoreAML.interp_sExists]
    refine ⟨.val (.map k.sort (dropKey a es1)), ?_, ?_⟩
    · rw [KoreAML.interp_member defOK_std]
      simp only [Function.update_same]
      exact (inhOf_sort h.namesK hsS _ _).mpr (hsy _ hys hye)
    · have hy : ∀ m, (Pattern.evar (⟨6⟩ : EVar) : KoreAML.P).interpret (stdI_T c T)
          ⟨Function.update e.evalEvar ⟨6⟩ (.val (.map k.sort (dropKey a es1))), e.evalSvar⟩ m ↔
            m = .val (.map k.sort (dropKey a es1)) := fun m => by
        rw [KoreAML.interp_evar]; simp only [Function.update_same]
      rw [interpret_conj]
      constructor
      · refine evar_eq_iff ((hval _ 4 (by decide)).trans h1) (fun m => ?_) m
        rw [C_map h hk hkind hab ⟨hys, hye⟩ (E_map h hk hkind hwa hwb ((hval _ 1 (by decide)).trans ha)
          ((hval _ 2 (by decide)).trans hb)) hy]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hl] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hl, rfl⟩
      · refine evar_eq_iff ((hval _ 3 (by decide)).trans hr) (fun m => ?_) m
        rw [C_map h hk hkind ⟨hys, hye⟩ ⟨hs2, he2⟩ hy
          (fun m => by rw [KoreAML.interp_evar, (hval _ 5 (by decide)).trans h2])]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hrr] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hrr, rfl⟩
  · right
    obtain ⟨hys, hye⟩ := hdrop es2 hs2 he2
    rw [KoreAML.interp_sExists]
    refine ⟨.val (.map k.sort (dropKey a es2)), ?_, ?_⟩
    · rw [KoreAML.interp_member defOK_std]
      simp only [Function.update_same]
      exact (inhOf_sort h.namesK hsS _ _).mpr (hsy _ hys hye)
    · have hy : ∀ m, (Pattern.evar (⟨6⟩ : EVar) : KoreAML.P).interpret (stdI_T c T)
          ⟨Function.update e.evalEvar ⟨6⟩ (.val (.map k.sort (dropKey a es2))), e.evalSvar⟩ m ↔
            m = .val (.map k.sort (dropKey a es2)) := fun m => by
        rw [KoreAML.interp_evar]; simp only [Function.update_same]
      rw [interpret_conj]
      constructor
      · refine evar_eq_iff ((hval _ 5 (by decide)).trans h2) (fun m => ?_) m
        rw [C_map h hk hkind hab ⟨hys, hye⟩ (E_map h hk hkind hwa hwb ((hval _ 1 (by decide)).trans ha)
          ((hval _ 2 (by decide)).trans hb)) hy]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hl] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hl, rfl⟩
      · refine evar_eq_iff ((hval _ 3 (by decide)).trans hr) (fun m => ?_) m
        rw [C_map h hk hkind ⟨hs1, he1⟩ ⟨hys, hye⟩
          (fun m => by rw [KoreAML.interp_evar, (hval _ 4 (by decide)).trans h1]) hy]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hrr] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hrr, rfl⟩

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .list)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem U_list (e : Valuation Elem) (x : Elem) :
    (collU c k).interpret (stdI_T c T) e x ↔ x = .val (.list k.sort []) := by
  have := coll_symE (T := T) h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) rfl (r := .list Srt.list [])
    (by rw [hkind, builtinColl_list, hook_listUnit_eq]) (by rw [hkind, builtinColl_list]; rfl)
    ((sortOf_list_iff h hk hkind).mpr fun _ h => nomatch h) x
  refine Iff.trans ?_ this
  unfold collU symP SymE
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨a, ha, hx⟩; have : x = a := hx; subst this; exact ha

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .list)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem I_list {e : Valuation Elem} {A : EVar} {a : GroundTerm} (ha : c.sortOf a = some k.key)
    (hA : e.evalEvar A = .val a) (x : Elem) :
    (collI c k (.evar A)).interpret (stdI_T c T) e x ↔ x = .val (.list k.sort [a]) := by
  unfold collI symP
  rw [interp_symList _ _ [.val a] (.cons (fun m => by rw [KoreAML.interp_evar, hA]) .nil) x]
  exact coll_symE h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (vs := [a]) (elemArgs_length' (.inr hkind)).symm
    (r := .list Srt.list [a]) (by rw [hkind, builtinColl_list, hook_listElem_eq])
    (by rw [hkind, builtinColl_list]; rfl)
    ((sortOf_list_iff h hk hkind).mpr fun z hz => (List.mem_singleton.mp hz) ▸ ha) x

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .list)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem C_list {e : Valuation Elem} {φ ψ : KoreAML.P} {l1 l2 : List GroundTerm}
    (h1 : ∀ z ∈ l1, c.sortOf z = some k.key) (h2 : ∀ z ∈ l2, c.sortOf z = some k.key)
    (hφ : ∀ m, φ.interpret (stdI_T c T) e m ↔ m = .val (.list k.sort l1))
    (hψ : ∀ m, ψ.interpret (stdI_T c T) e m ↔ m = .val (.list k.sort l2)) (x : Elem) :
    (collC c k φ ψ).interpret (stdI_T c T) e x ↔ x = .val (.list k.sort (l1 ++ l2)) := by
  unfold collC symP
  rw [interp_symList _ _ [.val (.list k.sort l1), .val (.list k.sort l2)] (.cons hφ (.cons hψ .nil)) x]
  exact coll_symE h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (vs := [.list k.sort l1, .list k.sort l2]) rfl
    (r := .list Srt.list (l1 ++ l2)) (by rw [hkind, builtinColl_list, hook_listConcat_eq])
    (by rw [hkind, builtinColl_list]; rfl)
    ((sortOf_list_iff h hk hkind).mpr fun z hz => by
      rcases List.mem_append.mp hz with hz | hz
      · exact h1 z hz
      · exact h2 z hz) x

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .list)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_listUnitSplit : stdI_T c T ⊧ᴵ listUnitSplitAx c k := by
  obtain ⟨hsS, -, -⟩ := h.collSorts hk
  intro e m
  unfold listUnitSplitAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨w1, h1, hw1⟩ := guard_val (T := T) h.namesK hsS (hg _ (List.mem_cons_self ..))
  obtain ⟨w2, h2, hw2⟩ := guard_val (T := T) h.namesK hsS (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain ⟨l1, rfl, hl1⟩ := list_val h hk hkind hw1
  obtain ⟨l2, rfl, hl2⟩ := list_val h hk hkind hw2
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, U_list h hk hkind, C_list h hk hkind hl1 hl2
    (fun m => by rw [KoreAML.interp_evar, h1]) (fun m => by rw [KoreAML.interp_evar, h2])] at hx
  obtain ⟨rfl, hx⟩ := hx
  simp only [Elem.val.injEq, GroundTerm.list.injEq, true_and, List.singleton_append] at hx
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hx.symm
  rw [interpret_conj]
  exact ⟨evar_eq_iff h1 (U_list h hk hkind e) m, evar_eq_iff h2 (U_list h hk hkind e) m⟩

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .list)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_listElemNotUnit : stdI_T c T ⊧ᴵ listElemNotUnitAx c k := by
  obtain ⟨-, hsK, -⟩ := h.collSorts hk
  intro e m
  unfold listElemNotUnitAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_self ..))
  rw [interpret_neg, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, U_list h hk hkind, I_list h hk hkind hwa ha] at hx
  obtain ⟨rfl, hx⟩ := hx
  cases hx

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .list)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_listElemAtom : stdI_T c T ⊧ᴵ listElemAtomAx c k := by
  obtain ⟨hsS, hsK, -⟩ := h.collSorts hk
  intro e m
  unfold listElemAtomAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_self ..))
  obtain ⟨a', ha', hwa'⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain ⟨w, hr, hw⟩ := guard_val (T := T) h.namesK hsS
    (hg _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  obtain ⟨rs, rfl, hrs⟩ := list_val h hk hkind hw
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, I_list h hk hkind hwa' ha',
    C_list h hk hkind (fun z hz => by rw [List.mem_singleton.mp hz]; exact hwa) hrs
      (I_list h hk hkind hwa ha) (fun m => by rw [KoreAML.interp_evar, hr])] at hx
  obtain ⟨rfl, hx⟩ := hx
  simp only [Elem.val.injEq, GroundTerm.list.injEq, true_and, List.singleton_append] at hx
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  rw [interpret_conj]
  exact ⟨evar_eq_iff ha (fun m => by rw [KoreAML.interp_evar, ha']) m, evar_eq_iff hr (U_list h hk hkind e) m⟩

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .list)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_listElemAtomBack : stdI_T c T ⊧ᴵ listElemAtomBackAx c k := by
  obtain ⟨hsS, hsK, -⟩ := h.collSorts hk
  intro e m
  unfold listElemAtomBackAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_self ..))
  obtain ⟨a', ha', hwa'⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain ⟨w, hr, hw⟩ := guard_val (T := T) h.namesK hsS
    (hg _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  obtain ⟨rs, rfl, hrs⟩ := list_val h hk hkind hw
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, I_list h hk hkind hwa' ha',
    C_list h hk hkind hrs (fun z hz => by rw [List.mem_singleton.mp hz]; exact hwa)
      (fun m => by rw [KoreAML.interp_evar, hr]) (I_list h hk hkind hwa ha)] at hx
  obtain ⟨rfl, hx⟩ := hx
  simp only [Elem.val.injEq, GroundTerm.list.injEq, true_and, List.singleton_append] at hx
  have heq := hx
  have hrs0 : rs = [] ∧ a' = a := by
    cases rs with
    | nil => exact ⟨rfl, (List.cons.inj heq).1⟩
    | cons z rs' =>
      have := (List.cons.inj heq).2
      exact absurd this.symm (by simp)
  obtain ⟨rfl, rfl⟩ := hrs0
  rw [interpret_conj]
  exact ⟨evar_eq_iff ha (fun m => by rw [KoreAML.interp_evar, ha']) m, evar_eq_iff hr (U_list h hk hkind e) m⟩

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .list)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_listDecomp : stdI_T c T ⊧ᴵ listDecompAx c k := by
  obtain ⟨hsS, hsK, -⟩ := h.collSorts hk
  intro e m
  unfold listDecompAx
  dsimp only
  refine guarded_intro fun hg => ?_
  have g := fun i (hi : i < 4) => hg _ (List.getElem_mem (l := [(⟨1⟩ : EVar) ∈∈ inSort c k.key,
    (⟨2⟩ : EVar) ∈∈ inSort c k.sort, (⟨3⟩ : EVar) ∈∈ inSort c k.sort, (⟨4⟩ : EVar) ∈∈ inSort c k.sort]) hi)
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (g 0 (by decide))
  obtain ⟨wr, hr, hwr⟩ := guard_val (T := T) h.namesK hsS (g 1 (by decide))
  obtain ⟨w1, h1, hw1⟩ := guard_val (T := T) h.namesK hsS (g 2 (by decide))
  obtain ⟨w2, h2, hw2⟩ := guard_val (T := T) h.namesK hsS (g 3 (by decide))
  obtain ⟨rs, rfl, hrs⟩ := list_val h hk hkind hwr
  obtain ⟨l1, rfl, hl1⟩ := list_val h hk hkind hw1
  obtain ⟨l2, rfl, hl2⟩ := list_val h hk hkind hw2
  have ha1 : ∀ z ∈ [a], c.sortOf z = some k.key := fun z hz => by rw [List.mem_singleton.mp hz]; exact hwa
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, C_list h hk hkind ha1 hrs (I_list h hk hkind hwa ha) (fun m => by rw [KoreAML.interp_evar, hr]),
    C_list h hk hkind hl1 hl2 (fun m => by rw [KoreAML.interp_evar, h1])
      (fun m => by rw [KoreAML.interp_evar, h2])] at hx
  obtain ⟨rfl, hx⟩ := hx
  simp only [Elem.val.injEq, GroundTerm.list.injEq, true_and, List.singleton_append] at hx
  have heq := hx
  rw [interpret_disj]
  cases l1 with
  | nil =>
    left
    simp only [List.nil_append] at heq
    subst heq
    rw [interpret_conj]
    exact ⟨evar_eq_iff h1 (U_list h hk hkind e) m,
      evar_eq_iff h2 (C_list h hk hkind ha1 hrs (I_list h hk hkind hwa ha) (fun m => by rw [KoreAML.interp_evar, hr])) m⟩
  | cons z l1' =>
    right
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    have hl1' : ∀ z ∈ l1', c.sortOf z = some k.key := fun z hz => hl1 z (List.mem_cons_of_mem _ hz)
    rw [KoreAML.interp_sExists]
    refine ⟨.val (.list k.sort l1'), ?_, ?_⟩
    · rw [KoreAML.interp_member defOK_std]
      simp only [Function.update_same]
      exact (inhOf_sort h.namesK hsS _ _).mpr ((sortOf_list_iff h hk hkind).mpr hl1')
    · have hy : ∀ m, (Pattern.evar (⟨5⟩ : EVar) : KoreAML.P).interpret (stdI_T c T)
          ⟨Function.update e.evalEvar ⟨5⟩ (.val (.list k.sort l1')), e.evalSvar⟩ m ↔
            m = .val (.list k.sort l1') := fun m => by
        rw [KoreAML.interp_evar]; simp only [Function.update_same]
      have hval : ∀ i, i ≠ 5 →
          (⟨Function.update e.evalEvar ⟨5⟩ (.val (.list k.sort l1')), e.evalSvar⟩ : Valuation Elem).evalEvar ⟨i⟩ =
            e.evalEvar ⟨i⟩ := fun i hi => upd_ne hi _
      rw [interpret_conj]
      constructor
      · exact evar_eq_iff ((hval 3 (by decide)).trans h1)
          (C_list h hk hkind ha1 hl1' (I_list h hk hkind hwa ((hval 1 (by decide)).trans ha)) hy) m
      · exact evar_eq_iff ((hval 2 (by decide)).trans hr)
          (C_list h hk hkind hl1' hl2 hy (fun m => by rw [KoreAML.interp_evar, (hval 4 (by decide)).trans h2])) m

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .set)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem U_set (e : Valuation Elem) (x : Elem) :
    (collU c k).interpret (stdI_T c T) e x ↔ x = .val (.set k.sort []) := by
  have := coll_symE (T := T) h hk (Or.inl ⟨rfl, rfl, rfl⟩) (vs := []) rfl (r := .set Srt.set [])
    (by rw [hkind, builtinColl_set, hook_setUnit_eq]) (by rw [hkind, builtinColl_set]; rfl)
    ((sortOf_set_iff h hk hkind).mpr ⟨rfl, fun _ h => nomatch h⟩) x
  refine Iff.trans ?_ this
  unfold collU symP SymE
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨a, ha, hx⟩; have : x = a := hx; subst this; exact ha

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .set)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem I_set {e : Valuation Elem} {A : EVar} {a : GroundTerm} (ha : c.sortOf a = some k.key)
    (hA : e.evalEvar A = .val a) (x : Elem) :
    (collI c k (.evar A)).interpret (stdI_T c T) e x ↔ x = .val (.set k.sort [a]) := by
  unfold collI symP
  rw [interp_symList _ _ [.val a] (.cons (fun m => by rw [KoreAML.interp_evar, hA]) .nil) x]
  exact coll_symE h hk (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (vs := [a]) (elemArgs_length' (.inl hkind)).symm
    (r := .set Srt.set [a]) (by rw [hkind, builtinColl_set, hook_setElem_eq])
    (by rw [hkind, builtinColl_set]; rfl)
    ((sortOf_set_iff h hk hkind).mpr ⟨rfl, fun z hz => (List.mem_singleton.mp hz) ▸ ha⟩) x

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .set)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem C_set {e : Valuation Elem} {φ ψ : KoreAML.P} {l1 l2 : List GroundTerm}
    (h1 : ∀ z ∈ l1, c.sortOf z = some k.key) (hs2 : elemsSorted l2 = true) (h2 : ∀ z ∈ l2, c.sortOf z = some k.key)
    (hφ : ∀ m, φ.interpret (stdI_T c T) e m ↔ m = .val (.set k.sort l1))
    (hψ : ∀ m, ψ.interpret (stdI_T c T) e m ↔ m = .val (.set k.sort l2)) (x : Elem) :
    (collC c k φ ψ).interpret (stdI_T c T) e x ↔ ∃ u, concatS l1 l2 = some u ∧ x = .val (.set k.sort u) := by
  obtain ⟨kf, hkf, hkfn, hkfa, hres⟩ := coll_sym h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  unfold collC symP
  rw [interp_symList _ _ [.val (.set k.sort l1), .val (.set k.sort l2)] (.cons hφ (.cons hψ .nil)) x,
    show [Elem.val (.set k.sort l1), Elem.val (.set k.sort l2)] = [GroundTerm.set k.sort l1, .set k.sort l2].map Elem.val
      from rfl, ← hkfn, symE_vals h.namesK hkf (by rw [hkfa]; rfl)]
  have hhook : hook (builtinColl k.kind).concat [.set k.sort l1, .set k.sort l2] =
      some ((concatS l1 l2).map (GroundTerm.set Srt.set)) := by
    rw [hkind, builtinColl_set, hook_setConcat_eq]
  have hsr : ∀ u, concatS l1 l2 = some u → c.sortOf ((GroundTerm.set Srt.set u).withSort k.sort) = some k.sort :=
    fun u hu => by
      rw [← (concatS_iff.mp hu).2]
      exact (sortOf_set_iff h hk hkind).mpr ⟨elemsSorted_iff.mpr (unionS_sorted (elemsSorted_iff.mp hs2)),
        fun z hz => by
          rcases unionS_mem hz with hz | hz
          · exact h1 z hz
          · exact h2 z hz⟩
  constructor
  · intro hr
    obtain ⟨v, hv⟩ := coll_sym_inv h hk (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
      (by rw [hkind]; exact silentKey_of_mem rfl) hkfn hr
    have hv0 := hv
    rw [hhook] at hv0
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hv0)
    exact ⟨u, hu, (hres hv (by rw [hkind, builtinColl_set]; rfl) (hsr u hu) x).mp hr⟩
  · rintro ⟨u, hu, rfl⟩
    have hv : hook (builtinColl k.kind).concat [.set k.sort l1, .set k.sort l2] = some (some (.set Srt.set u)) := by
      rw [hhook, hu]; rfl
    exact (hres hv (by rw [hkind, builtinColl_set]; rfl) (hsr u hu) _).mpr rfl

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .set)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_setUnitSplit : stdI_T c T ⊧ᴵ setUnitSplitAx c k := by
  obtain ⟨hsS, -, -⟩ := h.collSorts hk
  intro e m
  unfold setUnitSplitAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨w1, h1, hw1⟩ := guard_val (T := T) h.namesK hsS (hg _ (List.mem_cons_self ..))
  obtain ⟨w2, h2, hw2⟩ := guard_val (T := T) h.namesK hsS (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain ⟨l1, rfl, -, he1⟩ := set_val h hk hkind hw1
  obtain ⟨l2, rfl, hs2, he2⟩ := set_val h hk hkind hw2
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, U_set h hk hkind, C_set h hk hkind he1 hs2 he2
    (fun m => by rw [KoreAML.interp_evar, h1]) (fun m => by rw [KoreAML.interp_evar, h2])] at hx
  obtain ⟨rfl, u, hu, hx⟩ := hx
  cases hx
  obtain ⟨rfl, rfl⟩ := concatS_nil hu
  rw [interpret_conj]
  exact ⟨evar_eq_iff h1 (U_set h hk hkind e) m, evar_eq_iff h2 (U_set h hk hkind e) m⟩

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .set)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_setElemNotUnit : stdI_T c T ⊧ᴵ setElemNotUnitAx c k := by
  obtain ⟨-, hsK, -⟩ := h.collSorts hk
  intro e m
  unfold setElemNotUnitAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_self ..))
  rw [interpret_neg, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, U_set h hk hkind, I_set h hk hkind hwa ha] at hx
  obtain ⟨rfl, hx⟩ := hx
  cases hx

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .set)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_setElemAtom : stdI_T c T ⊧ᴵ setElemAtomAx c k := by
  obtain ⟨hsS, hsK, -⟩ := h.collSorts hk
  intro e m
  unfold setElemAtomAx
  dsimp only
  refine guarded_intro fun hg => ?_
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_self ..))
  obtain ⟨a', ha', hwa'⟩ := guard_val (T := T) h.namesK hsK (hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain ⟨w, hr, hw⟩ := guard_val (T := T) h.namesK hsS
    (hg _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  obtain ⟨rs, rfl, hrso, hrs⟩ := set_val h hk hkind hw
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, I_set h hk hkind hwa' ha',
    C_set h hk hkind (fun z hz => by rw [List.mem_singleton.mp hz]; exact hwa) hrso hrs
      (I_set h hk hkind hwa ha) (fun m => by rw [KoreAML.interp_evar, hr])] at hx
  obtain ⟨rfl, u, hu, hx⟩ := hx
  simp only [Elem.val.injEq, GroundTerm.set.injEq, true_and] at hx
  subst hx
  obtain ⟨rfl, rfl⟩ := concatS_single hu
  rw [interpret_conj]
  exact ⟨evar_eq_iff ha (fun m => by rw [KoreAML.interp_evar, ha']) m, evar_eq_iff hr (U_set h hk hkind e) m⟩

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {k : CollSig} (hk : k ∈ c.allColls) (hkind : k.kind = .set)
include h hk hkind
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_setDecomp : stdI_T c T ⊧ᴵ setDecompAx c k := by
  obtain ⟨hsS, hsK, -⟩ := h.collSorts hk
  intro e m
  unfold setDecompAx
  dsimp only
  refine guarded_intro fun hg => ?_
  have g := fun i (hi : i < 4) => hg _ (List.getElem_mem (l := [(⟨1⟩ : EVar) ∈∈ inSort c k.key,
    (⟨2⟩ : EVar) ∈∈ inSort c k.sort, (⟨3⟩ : EVar) ∈∈ inSort c k.sort, (⟨4⟩ : EVar) ∈∈ inSort c k.sort]) hi)
  obtain ⟨a, ha, hwa⟩ := guard_val (T := T) h.namesK hsK (g 0 (by decide))
  obtain ⟨wr, hr, hwr⟩ := guard_val (T := T) h.namesK hsS (g 1 (by decide))
  obtain ⟨w1, h1, hw1⟩ := guard_val (T := T) h.namesK hsS (g 2 (by decide))
  obtain ⟨w2, h2, hw2⟩ := guard_val (T := T) h.namesK hsS (g 3 (by decide))
  obtain ⟨rs, rfl, hrs, hre⟩ := set_val h hk hkind hwr
  obtain ⟨s1, rfl, hs1, he1⟩ := set_val h hk hkind hw1
  obtain ⟨s2, rfl, hs2, he2⟩ := set_val h hk hkind hw2
  have ha1 : ∀ z ∈ [a], c.sortOf z = some k.key := fun z hz => by rw [List.mem_singleton.mp hz]; exact hwa
  rw [interpret_impl, defined_app]
  rintro ⟨x, hx⟩
  rw [interpret_conj, C_set h hk hkind ha1 hrs hre (I_set h hk hkind hwa ha)
      (fun m => by rw [KoreAML.interp_evar, hr]),
    C_set h hk hkind he1 hs2 he2 (fun m => by rw [KoreAML.interp_evar, h1])
      (fun m => by rw [KoreAML.interp_evar, h2])] at hx
  obtain ⟨⟨u, hu, rfl⟩, u', hu', hx⟩ := hx
  cases hx
  have hdrop : ∀ s : List GroundTerm, elemsSorted s = true → (∀ z ∈ s, c.sortOf z = some k.key) →
      elemsSorted (dropS a s) = true ∧ ∀ z ∈ dropS a s, c.sortOf z = some k.key := fun s hs he =>
    ⟨Set.filter_canon hs _, fun z hz => he z (mem_dropS.mp hz).1⟩
  have hsy : ∀ ys : List GroundTerm, elemsSorted ys = true → (∀ z ∈ ys, c.sortOf z = some k.key) →
      c.sortOf (.set k.sort ys) = some k.sort := fun ys h1 h2 => (sortOf_set_iff h hk hkind).mpr ⟨h1, h2⟩
  -- the valuation with `y` (index 5) set to the element of `ys`
  have hval : ∀ ys : List GroundTerm, ∀ i, i ≠ 5 →
      (⟨Function.update e.evalEvar ⟨5⟩ (.val (.set k.sort ys)), e.evalSvar⟩ : Valuation Elem).evalEvar ⟨i⟩ =
        e.evalEvar ⟨i⟩ := fun ys i hi => upd_ne hi _
  rw [interpret_disj]
  rcases set_decomp hrs hs1 hs2 hu hu' with ⟨hl, hrr⟩ | ⟨hl, hrr⟩
  · left
    obtain ⟨hys, hye⟩ := hdrop s1 hs1 he1
    rw [KoreAML.interp_sExists]
    refine ⟨.val (.set k.sort (dropS a s1)), ?_, ?_⟩
    · rw [KoreAML.interp_member defOK_std]
      simp only [Function.update_same]
      exact (inhOf_sort h.namesK hsS _ _).mpr (hsy _ hys hye)
    · have hy : ∀ m, (Pattern.evar (⟨5⟩ : EVar) : KoreAML.P).interpret (stdI_T c T)
          ⟨Function.update e.evalEvar ⟨5⟩ (.val (.set k.sort (dropS a s1))), e.evalSvar⟩ m ↔
            m = .val (.set k.sort (dropS a s1)) := fun m => by
        rw [KoreAML.interp_evar]; simp only [Function.update_same]
      rw [interpret_conj]
      constructor
      · refine evar_eq_iff ((hval _ 3 (by decide)).trans h1) (fun m => ?_) m
        rw [C_set h hk hkind ha1 hys hye (I_set h hk hkind hwa ((hval _ 1 (by decide)).trans ha)) hy]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hl] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hl, rfl⟩
      · refine evar_eq_iff ((hval _ 2 (by decide)).trans hr) (fun m => ?_) m
        rw [C_set h hk hkind hye hs2 he2 hy
          (fun m => by rw [KoreAML.interp_evar, (hval _ 4 (by decide)).trans h2])]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hrr] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hrr, rfl⟩
  · right
    obtain ⟨hys, hye⟩ := hdrop s2 hs2 he2
    rw [KoreAML.interp_sExists]
    refine ⟨.val (.set k.sort (dropS a s2)), ?_, ?_⟩
    · rw [KoreAML.interp_member defOK_std]
      simp only [Function.update_same]
      exact (inhOf_sort h.namesK hsS _ _).mpr (hsy _ hys hye)
    · have hy : ∀ m, (Pattern.evar (⟨5⟩ : EVar) : KoreAML.P).interpret (stdI_T c T)
          ⟨Function.update e.evalEvar ⟨5⟩ (.val (.set k.sort (dropS a s2))), e.evalSvar⟩ m ↔
            m = .val (.set k.sort (dropS a s2)) := fun m => by
        rw [KoreAML.interp_evar]; simp only [Function.update_same]
      rw [interpret_conj]
      constructor
      · refine evar_eq_iff ((hval _ 4 (by decide)).trans h2) (fun m => ?_) m
        rw [C_set h hk hkind ha1 hys hye (I_set h hk hkind hwa ((hval _ 1 (by decide)).trans ha)) hy]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hl] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hl, rfl⟩
      · refine evar_eq_iff ((hval _ 2 (by decide)).trans hr) (fun m => ?_) m
        rw [C_set h hk hkind he1 hys hye
          (fun m => by rw [KoreAML.interp_evar, (hval _ 3 (by decide)).trans h1]) hy]
        constructor
        · rintro ⟨u0, hu0, rfl⟩; rw [hrr] at hu0; cases hu0; rfl
        · rintro rfl; exact ⟨_, hrr, rfl⟩

end

-- ModelColls.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **`SatCollsGoal`**: the value model satisfies the collections' axioms. -/
theorem satCollsGoal (h : HypModelCore c) : (stdI_T c T ⊧ᴵP ΓColls c) := by
  rintro φ ⟨k, hk, hφ⟩
  unfold collAxioms at hφ
  cases hkind : k.kind with
  | map =>
    rw [hkind] at hφ
    simp only [mapCollAxioms, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl
    · exact sat_mapUnitSplit h hk hkind
    · exact sat_mapElemNotUnit h hk hkind
    · exact sat_mapElemAtom h hk hkind
    · exact sat_mapDecomp h hk hkind
  | set =>
    rw [hkind] at hφ
    simp only [setCollAxioms, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl
    · exact sat_setUnitSplit h hk hkind
    · exact sat_setElemNotUnit h hk hkind
    · exact sat_setElemAtom h hk hkind
    · exact sat_setDecomp h hk hkind
  | list =>
    rw [hkind] at hφ
    simp only [listCollAxioms, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl
    · exact sat_listUnitSplit h hk hkind
    · exact sat_listElemNotUnit h hk hkind
    · exact sat_listElemAtom h hk hkind
    · exact sat_listElemAtomBack h hk hkind
    · exact sat_listDecomp h hk hkind
  | rangeMap =>
    rw [hkind] at hφ
    exact absurd hφ List.not_mem_nil

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem gs_ovl (hn : NamesApartK c) {o : OvlSig} (ho : o ∈ c.ovls) (hio : c.isOvl o.sig.name = true) (N : String)
    {vs : List GroundTerm} (hl : vs.length = o.sig.args.length) (m : Elem) :
    GS (stdI_T c T) N (Gen.toK c (.ctor o.sig)) (vs.map Elem.val) m ↔ m = .val (c.norm o.sig.name vs) := by
  rw [← result_ovl (vs := vs) hio]
  exact symE_vals hn (ovl_kernel ho) hl m

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem gs_ctor (hn : NamesApartK c) {k : CtorSig} (hk : k ∈ c.ctorSigs) (N : String) {vs : List GroundTerm}
    (hl : vs.length = k.args.length) (m : Elem) :
    GS (stdI_T c T) N (Gen.toK c (.ctor k)) (vs.map Elem.val) m ↔ m = .val (.ctor k.name vs) := by
  rw [← result_ctor (vs := vs) (isCtor_of_mem hk)]
  exact symE_vals hn (ctor_kernel hk) hl m

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem appE_inj2 (a N : Srt) (x m : Elem) :
    AppE (stdI_T c T) (.app .inj [.srt a, .srt N]) [x] m ↔ ∃ v, x = .val v ∧ m = .val (injNormal a N v) := by
  simp only [AppE]
  constructor
  · rintro ⟨a', ha', rfl⟩
    cases x with
    | val v => exact ⟨v, rfl, ha'⟩
    | srt _ => exact ha'.elim
    | app _ _ => exact ha'.elim
  · rintro ⟨v, rfl, rfl⟩
    exact ⟨_, rfl, rfl⟩

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem gs_inj (hn : NamesApartK c) {a N : Srt} (ha : a < nRegSorts + c.sortNames.length)
    (hN : N < nRegSorts + c.sortNames.length) (x m : Elem) :
    GS (stdI_T c T) (c.sortName N) (.inj (c.sortName a)) [x] m ↔ ∃ v, x = .val v ∧ m = .val (injNormal a N v) := by
  unfold GS genHead
  have hh : ∀ y, (KoreAML.appList (KoreAML.sym (.symbol "inj"))
      [KoreAML.Cons.sortP (c.sortName a), KoreAML.Cons.sortP (c.sortName N)]).interpret (stdI_T c T) KoreAML.val0 y ↔
      y = .app .inj [.srt a, .srt N] := by
    intro y
    rw [interp_appList_sing _ _ [.srt a, .srt N]
      (.cons (sort_den hn ha _) (.cons (sort_den hn hN _) .nil))]
    simp only [KoreAML.interp_sym, stdI_symb, evalSymb_inj, exists_eq_left, AppE, stdI_app, evalApp_inj0,
      evalApp_inj1]
  simp only [hh, exists_eq_left]
  exact appE_inj2 a N x m

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **A generator builds one value of its sort** from values of its argument sorts. -/
theorem gs_gen (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c) {g : Gen} (hg : g ∈ c.gens N)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some g.argSorts) :
    (∀ m, GS (stdI_T c T) (c.sortName N) (Gen.toK c g) (vs.map Elem.val) m ↔ m = .val (genVal c N g vs)) ∧
      c.sortOf (genVal c N g vs) = some N := by
  have hn := h.namesK
  rcases mem_gens hg with ⟨k, hk, rfl, rfl⟩ | ⟨o, ho, rfl, rfl⟩ | ⟨a, ha, rfl⟩
  · simp only [genVal, norm_ctor h hk]
    refine ⟨fun m => gs_ctor hn hk _ (sortsOf_len hvs) m, ?_⟩
    exact result_sorted h (ctor_kernel hk) hvs ((result_ctor (isCtor_of_mem hk) _).mpr rfl)
  · have hlo := OvlLaws.lookupOvl_of_mem h.ovlHyp ho
    obtain ⟨-, hio, -⟩ := OvlLaws.ovl_facts h.ovlHyp hlo
    exact ⟨fun m => gs_ovl hn ho hio _ (sortsOf_len hvs) m, OvlLaws.sortOf_norm h.ovlHyp hlo hvs⟩
  · obtain ⟨v, rfl, hv⟩ := sortsOf_single hvs
    obtain ⟨hsa, hsN⟩ := h.subSorts ha
    refine ⟨fun m => ?_, sortOf_injNormal h.trans ha hv⟩
    show GS (stdI_T c T) (c.sortName N) (.inj (c.sortName a)) [Elem.val v] m ↔ _
    rw [gs_inj hn hsa hsN]
    constructor
    · rintro ⟨v', hv', rfl⟩; cases hv'; rfl
    · rintro rfl; exact ⟨v, rfl, rfl⟩

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem disjList_intro {e : Valuation Elem} {m : Elem} : ∀ {ws : List KoreAML.P} {w : KoreAML.P}, w ∈ ws →
    w.interpret (stdI_T c T) e m → (KoreAML.disjList ws).interpret (stdI_T c T) e m
  | [], _, hw, _ => absurd hw List.not_mem_nil
  | [_], _, hw, h => by rw [List.mem_singleton.mp hw] at h; exact h
  | w' :: w'' :: ws, w, hw, h => by
    unfold KoreAML.disjList
    rw [interpret_disj]
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inl h
    · exact Or.inr (disjList_intro hw h)

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- Membership guards of numbered sorts hold of values of those sorts. -/
theorem memGuards_vals (hn : NamesApartK c) {e : Valuation Elem} {m : Elem} :
    ∀ (xs : List EVar) (ss : List Srt), (∀ s ∈ ss, s < nRegSorts + c.sortNames.length) → xs.length = ss.length →
    (∀ w ∈ KoreAML.Cons.memGuards xs (ss.map c.sortName), w.interpret (stdI_T c T) e m) →
    ∃ vs, xs.map e.evalEvar = vs.map Elem.val ∧ c.sortsOf vs = some ss
  | [], [], _, _, _ => ⟨[], rfl, sortsOf_nil⟩
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | x :: xs, s :: ss, hs, hl, hg => by
    rw [List.map_cons, memGuards_cons] at hg
    have h1 := hg _ (List.mem_cons_self ..)
    rw [KoreAML.interp_member defOK_std] at h1
    obtain ⟨v, hv, hvs⟩ := inSort_val ((inhOf_sort hn (hs s (List.mem_cons_self ..)) e _).mp h1)
    obtain ⟨vs, h3, h4⟩ := memGuards_vals hn xs ss (fun s' h' => hs s' (List.mem_cons_of_mem _ h'))
      (by simpa using hl) (fun w hw => hg w (List.mem_cons_of_mem _ hw))
    exact ⟨v :: vs, by simp [hv, h3], sortsOf_cons.mpr ⟨_, _, hvs, h4, rfl⟩⟩

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- `inj{s,t}(φ)` at a pattern that denotes one value. -/
theorem inj_sing (hn : NamesApartK c) {s t : Srt} (hs : s < nRegSorts + c.sortNames.length)
    (ht : t < nRegSorts + c.sortNames.length) {e : Valuation Elem} {φ : KoreAML.P} {u : GroundTerm}
    (hφ : ∀ m, φ.interpret (stdI_T c T) e m ↔ m = .val u) (m : Elem) :
    (KoreAML.appList (KoreAML.sym (.symbol "inj"))
      [KoreAML.Cons.sortP (c.sortName s), KoreAML.Cons.sortP (c.sortName t), φ]).interpret (stdI_T c T) e m ↔
      m = .val (injNormal s t u) := by
  rw [interp_injApp]
  simp only [hφ, exists_eq_left]
  rw [gs_inj hn hs ht]
  simp

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c)
include h hN
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_funItem {g : Gen} (hg : g ∈ c.gens N) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.funItem (c.sortName N) (Gen.toK c g)).pat := by
  have hn := h.namesK
  intro e m
  unfold KoreAML.Cons.funItem
  dsimp only
  simp only [toK_argSorts]
  refine guarded_intro fun hgd => ?_
  obtain ⟨vs, hxs, hvs⟩ := memGuards_vals (T := T) hn _ g.argSorts (gen_args_numbered h hg) (by simp [xs_length]) hgd
  obtain ⟨hgs, hsort⟩ := gs_gen (T := T) h hN hg hvs
  rw [KoreAML.interp_sExists]
  refine ⟨.val (genVal c N g vs), ?_, ?_⟩
  · rw [KoreAML.interp_member defOK_std]
    simp only [Function.update_same]
    exact (inhOf_sort hn (consSorts_numbered h hN) _ _).mpr hsort
  · rw [KoreAML.interp_equal defOK_std]
    intro a
    rw [interp_genPat_vars, KoreAML.interp_evar]
    simp only [Function.update_same]
    rw [map_update_xs 0 _ _ _ _ (fun i hi he => by simp only [EVar.mk.injEq, List.length_map] at he hi; omega), hxs]
    exact hgs a

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c)
include h hN
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_injItem {g : Gen} (hg : g ∈ c.gens N) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.injItem (c.sortName N) (Gen.toK c g)).pat := by
  have hn := h.namesK
  intro e m
  unfold KoreAML.Cons.injItem
  dsimp only
  simp only [toK_argSorts]
  refine guarded_intro fun hgd => ?_
  have hnum := gen_args_numbered h hg
  obtain ⟨vs, hxs, hvs⟩ := memGuards_vals (T := T) hn _ g.argSorts hnum (by simp [xs_length])
    (fun w hw => hgd w (List.mem_append_left _ hw))
  obtain ⟨ws, hys, hws⟩ := memGuards_vals (T := T) hn _ g.argSorts hnum (by simp [xs_length])
    (fun w hw => hgd w (List.mem_append_right _ hw))
  rw [interpret_impl]
  intro heq
  rw [KoreAML.interp_equal defOK_std] at heq
  have hv : genVal c N g vs = genVal c N g ws := by
    have := heq (.val (genVal c N g vs))
    rw [interp_genPat_vars, interp_genPat_vars, hxs, hys, (gs_gen h hN hg hvs).1, (gs_gen h hN hg hws).1] at this
    exact Elem.val.inj (this.mp rfl)
  have hvw : vs = ws := genVal_inj h hg hvs hws hv
  subst hvw
  rw [← hys] at hxs
  apply KoreAML.interp_conjList
  intro w hw
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hw
  rw [KoreAML.interp_equal defOK_std]
  intro z
  rw [KoreAML.interp_evar, KoreAML.interp_evar, zip_map_eq e.evalEvar _ _ hxs _ hab]

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c)
include h hN
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_dist_of {g g' : Gen} (hg : g ∈ c.gens N) (hg' : g' ∈ c.gens N)
    (hne : ∀ vs ws, c.sortsOf vs = some g.argSorts → c.sortsOf ws = some g'.argSorts →
      genVal c N g vs ≠ genVal c N g' ws) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.distItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')).pat := by
  have hn := h.namesK
  intro e m
  unfold KoreAML.Cons.distItem
  dsimp only
  simp only [toK_argSorts]
  refine guarded_intro fun hgd => ?_
  obtain ⟨vs, hxs, hvs⟩ := memGuards_vals (T := T) hn _ g.argSorts (gen_args_numbered h hg) (by simp [xs_length])
    (fun w hw => hgd w (List.mem_append_left _ hw))
  obtain ⟨ws, hys, hws⟩ := memGuards_vals (T := T) hn _ g'.argSorts (gen_args_numbered h hg') (by simp [xs_length])
    (fun w hw => hgd w (List.mem_append_right _ hw))
  rw [KoreAML.interp_notEqual defOK_std]
  intro heq
  have := heq (.val (genVal c N g vs))
  rw [interp_genPat_vars, interp_genPat_vars, hxs, hys, (gs_gen h hN hg hvs).1, (gs_gen h hN hg' hws).1] at this
  exact hne vs ws hvs hws (Elem.val.inj (this.mp rfl))

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem inj_sing' (hn : NamesApartK c) {s t : Srt} (hs : s < nRegSorts + c.sortNames.length)
    (ht : t < nRegSorts + c.sortNames.length) {e : Valuation Elem} {φ : KoreAML.P} {u : GroundTerm}
    (hφ : ∀ m, φ.interpret (stdI_T c T) e m ↔ m = .val u) (m : Elem) :
    (KoreAML.appList (KoreAML.sym (.symbol "inj"))
      [sortP (c.sortName s), sortP (c.sortName t), φ]).interpret (stdI_T c T) e m ↔
      m = .val (injNormal s t u) :=
  inj_sing hn hs ht hφ m

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c)
include h hN
variable {T : GroundTerm → GroundTerm → Prop}

omit hN in
theorem sat_distLb {a b : Srt} (ha : (a, N) ∈ c.subsorts) (hb : (b, N) ∈ c.subsorts)
    (hab : (c.le a b || c.le b a) = false) :
    stdI_T c T ⊧ᴵ (distLbItem (c.sortName N) (c.sortName a) (c.sortName b) ((c.lowerBounds a b).map c.sortName)).pat := by
  have hn := h.namesK
  obtain ⟨hsa, hsN⟩ := h.subSorts ha
  obtain ⟨hsb, -⟩ := h.subSorts hb
  intro e m
  unfold distLbItem
  dsimp only
  refine guarded_intro fun hgd => ?_
  obtain ⟨v, hv1, hv⟩ := guard_val (T := T) hn hsa (hgd _ (List.mem_cons_self ..))
  obtain ⟨w, hw1, hw⟩ := guard_val (T := T) hn hsb (hgd _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  rw [interpret_impl]
  intro heq
  rw [KoreAML.interp_equal defOK_std] at heq
  have hx : ∀ m, (Pattern.evar ⟨1⟩ : KoreAML.P).interpret (stdI_T c T) e m ↔ m = .val v := fun m => by
    rw [KoreAML.interp_evar, hv1]
  have hy : ∀ m, (Pattern.evar ⟨2⟩ : KoreAML.P).interpret (stdI_T c T) e m ↔ m = .val w := fun m => by
    rw [KoreAML.interp_evar, hw1]
  have he := heq (.val (injNormal a N v))
  rw [inj_sing' hn hsa hsN hx, inj_sing' hn hsb hsN hy] at he
  obtain ⟨x, u, hxl, hu, hui, rfl, rfl⟩ := inj_inj_eq hab hv hw (Elem.val.inj (he.mp rfl))
  obtain ⟨hsx, -⟩ := h.subSorts (mem_lowerBounds hxl).1
  refine disjList_intro (List.mem_map.mpr ⟨c.sortName x, List.mem_map.mpr ⟨x, hxl, rfl⟩, rfl⟩) ?_
  rw [KoreAML.interp_sExists]
  refine ⟨.val u, ?_, ?_⟩
  · rw [KoreAML.interp_member defOK_std]
    simp only [Function.update_same]
    exact (inhOf_sort hn hsx _ _).mpr hu
  · have hz : ∀ m, (Pattern.evar ⟨3⟩ : KoreAML.P).interpret (stdI_T c T)
        ⟨Function.update e.evalEvar ⟨3⟩ (.val u), e.evalSvar⟩ m ↔ m = .val u := fun m => by
      rw [KoreAML.interp_evar]; simp only [Function.update_same]
    rw [interpret_conj, KoreAML.interp_equal defOK_std, KoreAML.interp_equal defOK_std]
    refine ⟨fun z => ?_, fun z => ?_⟩
    · rw [inj_sing' hn hsx hsa hz, KoreAML.interp_evar, injNormal_of_not hui]
      simp only [upd_ne (show 1 ≠ 3 by decide), hv1]
    · rw [inj_sing' hn hsx hsb hz, KoreAML.interp_evar, injNormal_of_not hui]
      simp only [upd_ne (show 2 ≠ 3 by decide), hw1]

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c)
include h hN
variable {T : GroundTerm → GroundTerm → Prop}

omit hN in
/-- The uncovered guard of an overloading generator, in the model: its arguments are covered by
none of its overloads. -/
theorem unc_guard {o : OvlSig} (ho : o ∈ c.ovls) {x : List EVar} {z : EVar} (hz : z ∉ x) {e : Valuation Elem}
    {m : Elem} {vs : List GroundTerm} (hxs : x.map e.evalEvar = vs.map Elem.val)
    (hvs : c.sortsOf vs = some o.sig.args)
    (hg : (KoreAML.Cons.uncoveredP (o.sig.args.map c.sortName) ((c.ovlOver o).map fun kg => kg.args.map c.sortName)
      x z).interpret (stdI_T c T) e m) :
    c.uncovered o.sig.name vs = true := by
  have H := h.ovlHyp
  have hn := h.namesK
  have hlo := OvlLaws.lookupOvl_of_mem H ho
  obtain ⟨-, -, -, -, -, hover, -⟩ := OvlLaws.ovl_facts H hlo
  simp only [Semantics.uncovered, hlo, List.all_eq_true, Bool.not_eq_true']
  intro kg hkg
  cases hcv : c.ovlCovers o.sig kg vs with
  | false => rfl
  | true =>
  exfalso
  obtain ⟨hl, hvl, hli⟩ := OvlLaws.covers_iff.mp hcv
  have hli := OvlLaws.zip3_all_iff.mp hli
  have hxl : x.length = vs.length := by simpa using congrArg List.length hxs
  unfold KoreAML.Cons.uncoveredP at hg
  have hd := conjList_elim (T := T) hg _ (List.mem_map.mpr ⟨kg.args.map c.sortName, List.mem_map_of_mem hkg, rfl⟩)
  obtain ⟨w, hw, hwi⟩ := disjList_mem hd
  obtain ⟨⟨⟨A, B⟩, xi⟩, hmem, hF⟩ := List.mem_filterMap.mp hw
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hmem
  simp only [List.length_zip, List.length_map] at hi
  simp only [List.getElem_zip, List.getElem_map, Prod.mk.injEq] at hie
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hie
  dsimp only at hF
  have hkk := (hover kg hkg).1
  have hkern : kg ∈ kernelSyms c := by
    rcases OvlLaws.knownSig_mem hkk with hm | hm
    · exact ctor_kernel hm
    · exact List.mem_append_right _ hm
  have hA := h.symSorts hkern _ (List.mem_cons_of_mem _ (List.getElem_mem (show i < kg.args.length by omega)))
  have hB := h.symSorts (ovl_kernel ho) _ (List.mem_cons_of_mem _ (List.getElem_mem (show i < o.sig.args.length by omega)))
  have hAB : kg.args[i]'(by omega) ≠ o.sig.args[i]'(by omega) := by
    intro he
    rw [he] at hF
    simp at hF
  have hneq : (c.sortName (kg.args[i]'(by omega)) == c.sortName (o.sig.args[i]'(by omega))) = false := by
    rw [beq_eq_false_iff_ne]
    intro he
    exact hAB (hn.2.2 _ (List.mem_range.mpr hA) _ (List.mem_range.mpr hB) he)
  simp only [hneq, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hF
  subst hF
  rw [interpret_neg] at hwi
  apply hwi
  have hvi : (vs[i]'(by omega)) = vs[i]'(by omega) := rfl
  obtain ⟨-, hvi'⟩ := OvlLaws.sortsOf_iff.mp hvs
  have hv := hvi' i (by omega) (by omega)
  have hlies := hli i (by omega) (by omega) (by omega)
  have hex : e.evalEvar (x[i]'(by omega)) = .val (vs[i]'(by omega)) := by
    have := congrArg (·[i]?) hxs
    simp only [List.getElem?_map, List.getElem?_eq_getElem (show i < x.length by omega),
      List.getElem?_eq_getElem (show i < vs.length by omega), Option.map_some, Option.some.injEq] at this
    exact this
  have hu := OvlLaws.sortOf_strip hv hlies
  have hback := OvlLaws.lift_strip hv hlies
  rw [OvlLaws.lift_ne hAB] at hback
  have hxz : x[i]'(by omega) ≠ z := fun he => hz (he ▸ List.getElem_mem _)
  unfold KoreAML.Cons.liesP
  rw [KoreAML.interp_sExists]
  refine ⟨.val (strip (kg.args[i]'(by omega)) (o.sig.args[i]'(by omega)) (vs[i]'(by omega))), ?_, ?_⟩
  · rw [KoreAML.interp_member defOK_std]
    simp only [Function.update_same]
    exact (inhOf_sort hn hA _ _).mpr hu
  · rw [KoreAML.interp_equal defOK_std]
    intro b
    rw [KoreAML.interp_evar, inj_sing hn hA hB (fun m => by
      rw [KoreAML.interp_evar]; simp only [Function.update_same]; exact Iff.rfl) b, hback]
    simp only [Function.update_noteq hxz, hex]

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c)
include h hN
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_distUnc_of {g g' : Gen} (hg : g ∈ c.gens N) (hg' : g' ∈ c.gens N)
    (hne : ∀ vs ws, c.sortsOf vs = some g.argSorts → c.sortsOf ws = some g'.argSorts →
      UncG c g vs → UncG c g' ws → genVal c N g vs ≠ genVal c N g' ws) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g) (Gen.toK c g') (ovlArgsOf c g)
      (ovlArgsOf c g')).pat := by
  have hn := h.namesK
  intro e m
  unfold KoreAML.Cons.distUncItem
  dsimp only
  simp only [toK_argSorts]
  refine guarded_intro fun hgd => ?_
  obtain ⟨vs, hxs, hvs⟩ := memGuards_vals (T := T) hn _ g.argSorts (gen_args_numbered h hg) (by simp [xs_length])
    (fun w hw => hgd w (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hw))))
  obtain ⟨ws, hys, hws⟩ := memGuards_vals (T := T) hn _ g'.argSorts (gen_args_numbered h hg') (by simp [xs_length])
    (fun w hw => hgd w (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw))))
  have unc : ∀ (g0 : Gen), g0 ∈ c.gens N → ∀ (x : List EVar) (us : List GroundTerm) (z : EVar), z ∉ x →
      x.map e.evalEvar = us.map Elem.val → c.sortsOf us = some g0.argSorts →
      (∀ w ∈ (match ovlArgsOf c g0 with
        | some covs => [KoreAML.Cons.uncoveredP (g0.argSorts.map c.sortName) covs x z]
        | none => []), w.interpret (stdI_T c T) e m) → UncG c g0 us := by
    intro g0 hg0 x us z hz hx hus hw
    cases g0 with
    | inj a => trivial
    | ctor k =>
      intro hio
      rcases mem_gens hg0 with ⟨k', hk', -, he⟩ | ⟨o, ho, -, he⟩ | ⟨a, -, he⟩
      · cases he; rw [isOvl_of_ctorSigs hk'] at hio; cases hio
      · cases he
        have hlo := OvlLaws.lookupOvl_of_mem h.ovlHyp ho
        have hov : ovlArgsOf c (.ctor o.sig) = some ((c.ovlOver o).map fun kg => kg.args.map c.sortName) := by
          simp [ovlArgsOf, hio, hlo]
        rw [hov] at hw
        exact unc_guard h ho hz hx hus (hw _ (List.mem_singleton_self _))
      · cases he
  have hu := unc g hg (KoreAML.Cons.xs 0 (g.argSorts.map c.sortName).length) vs
    ⟨(g.argSorts.map c.sortName).length + (g'.argSorts.map c.sortName).length + 1⟩
    (notMem_xs_z (by omega)) hxs hvs
    (fun w hw => hgd w (List.mem_append_left _ (List.mem_append_right _ hw)))
  have hu' := unc g' hg' (KoreAML.Cons.xs (g.argSorts.map c.sortName).length (g'.argSorts.map c.sortName).length) ws
    ⟨(g.argSorts.map c.sortName).length + (g'.argSorts.map c.sortName).length + 1⟩
    (notMem_xs_z (by omega)) hys hws
    (fun w hw => hgd w (List.mem_append_right _ hw))
  rw [KoreAML.interp_notEqual defOK_std]
  intro heq
  have := heq (.val (genVal c N g vs))
  rw [interp_genPat_vars, interp_genPat_vars, hxs, hys, (gs_gen h hN hg hvs).1, (gs_gen h hN hg' hws).1] at this
  exact hne vs ws hvs hws hu hu' (Elem.val.inj (this.mp rfl))

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c)
include h hN
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_pairItem {g g' : Gen} (hp : (g, g') ∈ pairs (c.gens N)) {it : KoreAML.Item}
    (hit : it ∈ (match g, g' with
      | .inj a, .inj b =>
        if c.le a b || c.le b a then []
        else match c.lowerBounds a b with
          | [] => [KoreAML.Cons.distItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')]
          | lbs => [distLbItem (c.sortName N) (c.sortName a) (c.sortName b) (lbs.map c.sortName)]
      | _, _ =>
        if c.distGuarded g g' then
          [KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')
            (ovlArgsOf c g) (ovlArgsOf c g')]
        else [KoreAML.Cons.distItem (c.sortName N) (Gen.toK c g) (Gen.toK c g')])) :
    stdI_T c T ⊧ᴵ it.pat := by
  obtain ⟨hg, hg'⟩ := pairs_mem hp
  have hci : ∀ (f : Sym) (b : Srt) (vs ws : List GroundTerm), GroundTerm.ctor f vs ≠ injNormal b N (ws.headD (.ctor 0 [])) :=
    fun f b vs ws he => by have := injNormal_isInj b N (ws.headD (.ctor 0 [])); rw [← he] at this; cases this
  have hctor : ∀ {k : CtorSig}, Gen.ctor k ∈ c.gens N → c.isOvl k.name = false → k ∈ c.ctorSigs := by
    intro k hk hio
    rcases mem_gens hk with ⟨k', hk', -, he⟩ | ⟨o, ho, -, he⟩ | ⟨a, -, he⟩
    · cases he; exact hk'
    · cases he
      rw [(OvlLaws.ovl_facts h.ovlHyp (OvlLaws.lookupOvl_of_mem h.ovlHyp ho)).2.1] at hio
      cases hio
    · cases he
  cases g with
  | ctor k =>
    cases g' with
    | ctor k' =>
      have hkk := gen_known h hg
      have hkk' := gen_known h hg'
      by_cases hdg : c.distGuarded (.ctor k) (.ctor k') = true
      · simp only [hdg, ↓reduceIte, List.mem_singleton] at hit
        rw [hit]
        refine sat_distUnc_of h hN hg hg' fun vs ws hvs hws hu hu' he => ?_
        rw [genVal_unc h hg hvs hu, genVal_unc h hg' hws hu', GroundTerm.ctor.injEq] at he
        exact pairs_ctor_names h hp he.1
      · simp only [hdg, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hit
        rw [hit]
        refine sat_dist_of h hN hg hg' fun vs ws hvs hws he => ?_
        obtain ⟨A, f, us, hf, hfk⟩ := OvlLaws.norm_head h.ovlHyp hkk.1 hvs
        obtain ⟨A', f', us', hf', hfk'⟩ := OvlLaws.norm_head h.ovlHyp hkk'.1 hws
        simp only [genVal] at he
        rw [hf, hf', hkk.2, hkk'.2] at he
        obtain ⟨rfl, -⟩ := OvlLaws.lift_ctor_inj he
        simp only [Semantics.distGuarded, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true,
          List.contains_iff_mem, not_and] at hdg
        cases ho : c.isOvl k.name || c.isOvl k'.name with
        | true =>
          simp only [Bool.or_eq_true] at ho
          exact hdg ho ⟨f, hfk, hfk'⟩
        | false =>
          simp only [Bool.or_eq_false_iff] at ho
          have hv := norm_ctor h (hctor hg ho.1) vs
          have hw := norm_ctor h (hctor hg' ho.2) ws
          have e1 : k.name = f := (OvlLaws.lift_ctor_inj (A := k.result) (B := k.result)
            (by rw [OvlLaws.lift_self, ← hv]; exact hf)).1
          have e2 : k'.name = f := (OvlLaws.lift_ctor_inj (A := k'.result) (B := k'.result)
            (by rw [OvlLaws.lift_self, ← hw]; exact hf')).1
          exact pairs_ctor_names h hp (e1.trans e2.symm)
    | inj b =>
      have hkk := gen_known h hg
      by_cases hdg : c.isOvl k.name = true
      · have hdg' : c.distGuarded (.ctor k) (.inj b) = true := by simp [Semantics.distGuarded, hdg]
        simp only [hdg', ↓reduceIte, List.mem_singleton] at hit
        rw [hit]
        refine sat_distUnc_of h hN hg hg' fun vs ws hvs _ hu _ he => ?_
        rw [genVal_unc h hg hvs hu] at he
        exact hci k.name b vs ws he
      · have hdg' : c.distGuarded (.ctor k) (.inj b) = false := by simpa [Semantics.distGuarded] using hdg
        simp only [hdg', Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hit
        rw [hit]
        refine sat_dist_of h hN hg hg' fun vs ws _ _ he => ?_
        simp only [genVal] at he
        rw [norm_ctor h (hctor hg (by simpa using hdg))] at he
        exact hci k.name b vs ws he
  | inj a =>
    cases g' with
    | ctor k' =>
      by_cases hdg : c.isOvl k'.name = true
      · have hdg' : c.distGuarded (.inj a) (.ctor k') = true := by simp [Semantics.distGuarded, hdg]
        simp only [hdg', ↓reduceIte, List.mem_singleton] at hit
        rw [hit]
        refine sat_distUnc_of h hN hg hg' fun vs ws _ hws _ hu' he => ?_
        rw [genVal_unc h hg' hws hu'] at he
        exact hci k'.name a ws vs he.symm
      · have hdg' : c.distGuarded (.inj a) (.ctor k') = false := by simpa [Semantics.distGuarded] using hdg
        simp only [hdg', Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hit
        rw [hit]
        refine sat_dist_of h hN hg hg' fun vs ws _ _ he => ?_
        simp only [genVal] at he
        rw [norm_ctor h (hctor hg' (by simpa using hdg))] at he
        exact hci k'.name a ws vs he.symm
    | inj b =>
      have ha : (a, N) ∈ c.subsorts := by
        rcases mem_gens hg with ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩ | ⟨a', ha', he⟩
        · cases he
        · cases he
        · cases he; exact ha'
      have hb : (b, N) ∈ c.subsorts := by
        rcases mem_gens hg' with ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩ | ⟨b', hb', he⟩
        · cases he
        · cases he
        · cases he; exact hb'
      dsimp only at hit
      cases hle : (c.le a b || c.le b a) with
      | true => rw [hle] at hit; simp at hit
      | false =>
        rw [hle] at hit
        simp only [Bool.false_eq_true, ↓reduceIte] at hit
        cases hl : c.lowerBounds a b with
        | nil =>
          rw [hl] at hit
          rw [List.mem_singleton.mp hit]
          refine sat_dist_of h hN hg hg' fun vs ws hvs hws he => ?_
          obtain ⟨v, rfl, hv⟩ := sortsOf_single hvs
          obtain ⟨w, rfl, hw⟩ := sortsOf_single hws
          obtain ⟨x, -, hxl, -⟩ := inj_inj_eq hle hv hw he
          rw [hl] at hxl
          exact absurd hxl List.not_mem_nil
        | cons l ls =>
          rw [hl] at hit
          rw [List.mem_singleton.mp hit, ← hl]
          exact sat_distLb h ha hb hle

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c)
include h hN
variable {T : GroundTerm → GroundTerm → Prop}

omit h hN in
theorem genPat_interp (N' : String) (g : KoreAML.Gen) (args : List KoreAML.P) (e : Valuation Elem) (x : Elem) :
    (KoreAML.Cons.genPat N' g args).interpret (stdI_T c T) e x ↔
      ∃ bs, All2 (fun φ b => φ.interpret (stdI_T c T) e b) args bs ∧ GS (stdI_T c T) N' g bs x := by
  rw [genPat_eq, interp_appList]
  constructor
  · rintro ⟨a, ha, bs, hbs, hx⟩
    exact ⟨bs, hbs, a, ((genHead_closed N' g).interp e KoreAML.val0 a).mp ha, hx⟩
  · rintro ⟨bs, hbs, a, ha, hx⟩
    exact ⟨a, ((genHead_closed N' g).interp e KoreAML.val0 a).mpr ha, bs, hbs, hx⟩

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem updAll_at : ∀ (xs : List EVar) (as : List Elem) (e : Valuation Elem), xs.Nodup → xs.length = as.length →
    All2 (fun x a => (Pattern.evar x : KoreAML.P).interpret (stdI_T c T) (updAll e xs as) a) xs as
  | [], [], _, _, _ => .nil
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, a :: as, e, hn, hl => by
    rw [List.nodup_cons] at hn
    refine .cons ?_ (updAll_at xs as _ hn.2 (by simpa using hl))
    show a = (updAll _ xs as).evalEvar x
    rw [updAll_off xs as _ x hn.1]; simp

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- `∃b̄. body` holds where body holds at the valuation updated at the binders with elements of their sorts. -/
theorem existsAll_upd (hn : NamesApartK c) (t : KoreAML.VarTable) (S : Kore.KSort) (body : Kore.Pattern) :
    ∀ {bs : List Kore.EVar} {as : List Elem} (e : Valuation Elem) (m : Elem),
    All2 (fun (b : Kore.EVar) a => ∃ s, s < nRegSorts + c.sortNames.length ∧ b.sort = KoreAML.srt (c.sortName s) ∧ InSort c s a) bs as →
    (KoreAML.tr ⟨t, []⟩ body).interpret (stdI_T c T) (updAll e (bs.map fun b => t.ev (KoreAML.evarKey b)) as) m →
    (KoreAML.tr ⟨t, []⟩ (KoreAML.existsAll S bs body)).interpret (stdI_T c T) e m
  | _, _, _, _, .nil, hb => hb
  | b :: bs, a :: as, e, m, .cons ⟨s, hs, hbs, ha⟩ hrest, hb => by
    show (KoreAML.tr ⟨t, []⟩ (.exist S b (KoreAML.existsAll S bs body))).interpret (stdI_T c T) e m
    rw [KoreAML.tr, KoreAML.interp_sExists]
    refine ⟨a, ?_, existsAll_upd hn t S body _ m hrest hb⟩
    rw [KoreAML.interp_member defOK_std]
    simp only [Function.update_same]
    rw [hbs, trSort_srt]
    exact (inhOf_sort hn hs _ _).mpr ha

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem trOrList_intro {ctx : KoreAML.Ctx} {s : KoreAML.P} {e : Valuation Elem} {m : Elem}
    (hs : (KoreAML.inhOf s).interpret (stdI_T c T) e m) :
    ∀ {ps : List Kore.Pattern} {p : Kore.Pattern}, p ∈ ps → (KoreAML.tr ctx p).interpret (stdI_T c T) e m →
      (KoreAML.trOrList ctx s ps).interpret (stdI_T c T) e m
  | [_], _, hp, h => by rw [List.mem_singleton.mp hp] at h; rw [KoreAML.trOrList]; exact h
  | q :: q' :: ps, p, hp, h => by
    rw [KoreAML.trOrList, KoreAML.interp_sOr]
    refine ⟨hs, ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inl h
    · exact Or.inr (trOrList_intro hs hp h)

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem trOr_noJunk_inh {ctx : KoreAML.Ctx} {N : String} {seen : List (String × List String)}
    {gs : List KoreAML.Gen} {e : Valuation Elem} {m : Elem}
    (h : (KoreAML.trOrList ctx (KoreAML.trSort ctx.vars (KoreAML.srt N)) (KoreAML.noJunkDisjuncts N seen gs)).interpret (stdI_T c T) e m) :
    (KoreAML.inhOf (KoreAML.trSort ctx.vars (KoreAML.srt N))).interpret (stdI_T c T) e m := by
  cases gs with
  | nil =>
    simp only [KoreAML.noJunkDisjuncts, KoreAML.trOrList, KoreAML.tr] at h
    unfold KoreAML.sBot at h
    exact (KoreAML.interp_sNot.mp h).2
  | cons g gs =>
    have hne := noJunkDisjuncts_ne_nil N seen (g :: gs)
    obtain ⟨d, rest, hdr⟩ : ∃ d rest, KoreAML.noJunkDisjuncts N seen (g :: gs) = d :: rest :=
      match KoreAML.noJunkDisjuncts N seen (g :: gs), hne with
      | d :: rest, _ => ⟨d, rest, rfl⟩
    have hrest : rest ≠ [] := by
      cases g with
      | ctor k =>
        simp only [KoreAML.noJunkDisjuncts, List.cons.injEq] at hdr
        rw [← hdr.2]; exact noJunkDisjuncts_ne_nil _ _ _
      | inj a =>
        simp only [KoreAML.noJunkDisjuncts, List.cons.injEq] at hdr
        rw [← hdr.2]; exact noJunkDisjuncts_ne_nil _ _ _
    obtain ⟨d', rest', rfl⟩ : ∃ d' rest', rest = d' :: rest' :=
      match rest, hrest with
      | d' :: rest', _ => ⟨d', rest', rfl⟩
    rw [hdr, KoreAML.trOrList] at h
    exact (KoreAML.interp_sOr.mp h).1

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c)
include h hN
variable {T : GroundTerm → GroundTerm → Prop}

/-- The text's no-junk sentence of N, read in the value model, holds of N's values and nothing else. -/
theorem noJunk_sentence (e : Valuation Elem) (a : Elem) :
    (KoreAML.tr ⟨KoreAML.tableOf [] (KoreAML.Cons.noJunkAx (c.sortName N) ((c.gens N).map (Gen.toK c))).pattern, []⟩
        (KoreAML.Cons.noJunkAx (c.sortName N) ((c.gens N).map (Gen.toK c))).pattern).interpret (stdI_T c T) e a ↔
      InSort c N a := by
  have hn := h.namesK
  have hNn := consSorts_numbered h hN
  let X := (KoreAML.Cons.noJunkAx (c.sortName N) ((c.gens N).map (Gen.toK c))).pattern
  let t := KoreAML.tableOf [] X
  have hinh : ∀ e' a', (KoreAML.inhOf (KoreAML.trSort t (KoreAML.srt (c.sortName N)))).interpret (stdI_T c T) e' a' ↔ InSort c N a' :=
    fun e' a' => by rw [trSort_srt]; exact inhOf_sort hn hNn e' a'
  show (KoreAML.tr ⟨t, []⟩ (.or (KoreAML.srt (c.sortName N)) _)).interpret (stdI_T c T) e a ↔ _
  rw [KoreAML.tr]
  constructor
  · intro ha
    exact (hinh e a).mp (trOr_noJunk_inh (ctx := ⟨t, []⟩) ha)
  · intro ha
    obtain ⟨w, rfl, hw⟩ := inSort_val ha
    have hgen : ∃ g ∈ c.gens N, ∃ vs, c.sortsOf vs = some g.argSorts ∧ genVal c N g vs = w := by
      rcases consSort_shape h.genWf hN hw with ⟨f, ws, rfl⟩ | ⟨a, b, w0, rfl⟩
      · rcases c.sortOf_ctor_iff.mp hw with ⟨k, hk, hws, rfl⟩ | ⟨-, o, hlo, hws, hu, rfl⟩
        · obtain ⟨hkm, rfl⟩ := lookupSig_spec hk
          exact ⟨.ctor k, gens_ctor hkm, ws, hws, norm_ctor h hkm ws⟩
        · have hom : o ∈ c.ovls := List.mem_of_find?_eq_some hlo
          obtain ⟨hon, -⟩ := OvlLaws.ovl_facts h.ovlHyp hlo
          refine ⟨.ctor o.sig, gens_ovl hom, ws, hws, ?_⟩
          show c.norm o.sig.name ws = _
          rw [hon]
          exact OvlLaws.norm_fixed h.ovlHyp hlo hw
      · obtain ⟨hab, hni, hw0, rfl⟩ := sortOf_inj.mp hw
        exact ⟨.inj a, gens_inj hab, [w0], sortsOf_cons.mpr ⟨a, [], hw0, sortsOf_nil, rfl⟩,
          by simp [genVal, injNormal_of_not hni]⟩
    obtain ⟨g, hg, vs, hvs, rfl⟩ := hgen
    obtain ⟨bs, body, hm, hsorts, hnd, htr⟩ := noJunkDisjuncts_gen (c.sortName N) [] ((c.gens N).map (Gen.toK c))
      (Gen.toK c g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
    refine trOrList_intro ((hinh e _).mpr ha) hm ?_
    rw [toK_argSorts] at hsorts
    have hgd := guards_of hn hsorts hvs (gen_args_numbered h hg)
    refine existsAll_upd hn t _ body e _ hgd ?_
    rw [htr, genPat_interp]
    refine ⟨vs.map Elem.val, ?_, ((gs_gen h hN hg hvs).1 _).mpr rfl⟩
    -- the binders' indices are distinct: their keys are, and all lie in the table
    have hkt : ∀ b ∈ bs, KoreAML.evarKey b ∈ t := fun b hb =>
      List.mem_eraseDups.mpr (List.mem_append_right _ (by
        show KoreAML.evarKey b ∈ KoreAML.varsOf (.or _ _)
        rw [KoreAML.varsOf]
        exact List.mem_append_right _ (mem_varsOfList hm (varsOf_existsAll' hb))))
    have hidx : (bs.map fun b => t.ev (KoreAML.evarKey b)).Nodup := by
      rw [show (bs.map fun b => t.ev (KoreAML.evarKey b)) = (bs.map KoreAML.evarKey).map t.ev by rw [List.map_map]; rfl]
      refine nodup_map_of_injOn t.ev (fun k hk k' hk' he => ?_) hnd
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hk'
      exact ev_inj (hkt b hb) (hkt b' hb') he
    have := updAll_at (T := T) (c := c) _ (vs.map Elem.val) e hidx (by rw [List.length_map, hgd.length])
    have h2 := all2_map_left_inv (R := fun x a => (Pattern.evar x : KoreAML.P).interpret (stdI_T c T) _ a)
      (f := fun b => t.ev (KoreAML.evarKey b)) this
    refine all2_map_left ?_
    exact h2
where
  all2_map_left_inv {α β γ : Type} {R : α → β → Prop} {f : γ → α} : ∀ {l : List γ} {bs : List β},
      All2 R (l.map f) bs → All2 (fun x b => R (f x) b) l bs
    | [], [], _ => .nil
    | [], _ :: _, hb => by cases hb
    | _ :: _, [], hb => by cases hb
    | _ :: _, _ :: _, .cons h hs => .cons h (all2_map_left_inv hs)

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable (h : HypModelCore c) {N : Srt} (hN : N ∈ consSorts c)
include h hN
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_noJunk : stdI_T c T ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName N) ((c.gens N).map (Gen.toK c))).pat := by
  have hn := h.namesK
  have hNn := consSorts_numbered h hN
  intro e m
  rw [noJunk_pat]
  dsimp only
  rw [interpret_impl]
  intro _
  rw [KoreAML.interp_equal defOK_std]
  intro a
  refine (noJunk_sentence h hN e a).trans ?_
  unfold KoreAML.Cons.sortP
  exact (inhOf_sort hn hNn e a).symm

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_coh (h : HypModelCore c) {a b d : Srt} (hab : (a, b) ∈ c.subsorts) (hbd : (b, d) ∈ c.subsorts) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.cohItem (c.sortName a) (c.sortName b) (c.sortName d)).pat := by
  have hn := h.namesK
  obtain ⟨hsa, hsb⟩ := h.subSorts hab
  obtain ⟨-, hsd⟩ := h.subSorts hbd
  intro e m
  unfold KoreAML.Cons.cohItem
  dsimp only
  refine guarded_intro fun hgd => ?_
  obtain ⟨v, hv1, -⟩ := guard_val (T := T) hn hsa (hgd _ (List.mem_cons_self ..))
  have hx : ∀ m, (Pattern.evar ⟨1⟩ : KoreAML.P).interpret (stdI_T c T) e m ↔ m = .val v := fun m => by
    rw [KoreAML.interp_evar, hv1]
  rw [KoreAML.interp_equal defOK_std]
  intro z
  rw [inj_sing hn hsb hsd (inj_sing hn hsa hsb hx), inj_sing hn hsa hsd hx, injNormal_comp]

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem evars_den {e : Valuation Elem} :
    ∀ (xs : List EVar) (us : List GroundTerm), xs.map e.evalEvar = us.map Elem.val →
      All2 (fun φ x => ∀ m, φ.interpret (stdI_T c T) e m ↔ m = x) (xs.map Pattern.evar) (us.map Elem.val)
  | [], [], _ => .nil
  | [], _ :: _, he => by simp at he
  | _ :: _, [], he => by simp at he
  | x :: xs, u :: us, he => by
    simp only [List.map_cons, List.cons.injEq] at he
    exact .cons (fun m => by rw [KoreAML.interp_evar, he.1]) (evars_den xs us he.2)

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- The overload equation's argument patterns: each variable, injected where the two sorts differ,
denotes its value lifted. -/
theorem liftArgs_den (hn : NamesApartK c) {e : Valuation Elem} (F : (String × String) × EVar → KoreAML.P)
    (hF : ∀ A B xi, F ((A, B), xi) = if A == B then Pattern.evar xi else
      KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP A, KoreAML.Cons.sortP B, .evar xi]) :
    ∀ (as bs : List Srt) (xs : List EVar) (us : List GroundTerm),
      (∀ s ∈ as, s < nRegSorts + c.sortNames.length) → (∀ s ∈ bs, s < nRegSorts + c.sortNames.length) →
      xs.map e.evalEvar = us.map Elem.val → as.length = bs.length → us.length = as.length →
      All2 (fun φ x => ∀ m, φ.interpret (stdI_T c T) e m ↔ m = x)
        ((((as.map c.sortName).zip (bs.map c.sortName)).zip xs).map F) ((liftAll as bs us).map Elem.val)
  | [], _, _, _, _, _, _, _, _ => by simp [liftAll]; exact .nil
  | _ :: _, [], _, _, _, _, _, hl, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, _, he, _, hu => by
    simp at he; subst he; simp at hu
  | _ :: _, _ :: _, _ :: _, [], _, _, he, _, hu => by simp at hu
  | a :: as, b :: bs, x :: xs, u :: us, ha, hb, he, hl, hu => by
    simp only [List.map_cons, List.cons.injEq] at he
    have hla : liftAll (a :: as) (b :: bs) (u :: us) = lift a b u :: liftAll as bs us := rfl
    rw [hla, List.map_cons, List.map_cons, List.zip_cons_cons, List.zip_cons_cons, List.map_cons]
    have han := ha a (List.mem_cons_self ..)
    have hbn := hb b (List.mem_cons_self ..)
    refine .cons (fun m => ?_) (liftArgs_den hn F hF as bs xs us (fun s hs => ha s (List.mem_cons_of_mem _ hs))
      (fun s hs => hb s (List.mem_cons_of_mem _ hs)) he.2 (by simpa using hl) (by simpa using hu))
    rw [hF]
    by_cases hab : a = b
    · subst hab
      simp only [beq_self_eq_true, ↓reduceIte, KoreAML.interp_evar, he.1, OvlLaws.lift_self]
    · have hne : (c.sortName a == c.sortName b) = false := by
        rw [beq_eq_false_iff_ne]
        intro hs
        exact hab (hn.2.2 _ (List.mem_range.mpr han) _ (List.mem_range.mpr hbn) hs)
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      rw [inj_sing hn han hbn (fun m => by rw [KoreAML.interp_evar, he.1]) m, OvlLaws.lift_ne hab]

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **Each overload equation holds**: `f(lift x̄) = lift (g(x̄))` (`OvlLaws.norm_ovlEq`). -/
theorem sat_ovlEq (h : HypModelCore c) {o : OvlSig} (ho : o ∈ c.ovls) {kg : CtorSig} (hkg : kg ∈ c.ovlOver o) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.ovlEqItem (toK c o.sig) (toK c kg)).pat := by
  have hn := h.namesK
  have H := h.ovlHyp
  have hlo := OvlLaws.lookupOvl_of_mem H ho
  obtain ⟨-, hio, -, -, -, hover, -⟩ := OvlLaws.ovl_facts H hlo
  obtain ⟨hkk, hpair, -⟩ := hover kg hkg
  obtain ⟨hl, -, -⟩ := OvlLaws.pairOK_parts hpair
  have hkn := fun s hs => h.symSorts (known_kernel hkk) s (List.mem_cons_of_mem _ hs)
  have hon := fun s hs => h.symSorts (ovl_kernel ho) s (List.mem_cons_of_mem _ hs)
  have hkr := h.symSorts (known_kernel hkk) _ (List.mem_cons_self ..)
  have hor := h.symSorts (ovl_kernel ho) _ (List.mem_cons_self ..)
  intro e m
  unfold KoreAML.Cons.ovlEqItem
  dsimp only
  simp only [toK, List.length_map]
  refine guarded_intro fun hgd => ?_
  obtain ⟨as, hxs, has⟩ := memGuards_vals (T := T) hn _ kg.args hkn (by simp [xs_length]) hgd
  have hal := (OvlLaws.sortsOf_iff.mp has).1
  rw [KoreAML.interp_equal defOK_std]
  intro b
  rw [interp_symList _ _ ((liftAll kg.args o.sig.args as).map Elem.val)
    (liftArgs_den hn _ (fun A B xi => rfl) kg.args o.sig.args _ as hkn hon hxs hl hal) b,
    symE_vals hn (ovl_kernel ho) (by simp [OvlLaws.length_liftAll]; omega) b, result_ovl hio,
    OvlLaws.norm_ovlEq H hlo hkg has]
  have hin : ∀ m, (KoreAML.appList (KoreAML.sym (.symbol (c.symName kg.name)))
      ((KoreAML.Cons.xs 0 kg.args.length).map Pattern.evar)).interpret (stdI_T c T) e m ↔
      m = .val (c.norm kg.name as) := fun m => by
    rw [interp_symList _ _ (as.map Elem.val) (evars_den _ _ hxs) m,
      symE_vals hn (known_kernel hkk) (by omega) m, result_known h hkk]
  by_cases hres : kg.result = o.sig.result
  · simp only [hres, beq_self_eq_true, ↓reduceIte, OvlLaws.lift_self]
    exact (hin b).symm
  · have hne : (c.sortName kg.result == c.sortName o.sig.result) = false := by
      rw [beq_eq_false_iff_ne]
      intro hs
      exact hres (hn.2.2 _ (List.mem_range.mpr hkr) _ (List.mem_range.mpr hor) hs)
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [inj_sing hn hkr hor hin b, OvlLaws.lift_ne hres]

end

-- ModelCons.lean
section
set_option autoImplicit false
open ML
open KCore.NamesApart (lib_sorts_lt lib_ok)
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **`SatConsGoal`**: the value model satisfies the constructors' axioms. -/
theorem satConsGoal (h : HypModelCore c) : (stdI_T c T ⊧ᴵP ΓCons c) := by
  refine sat_itemsPremises c fun it hit => ?_
  unfold consItemsK at hit
  dsimp only at hit
  rcases List.mem_append.mp hit with hit | hit
  rotate_left
  · obtain ⟨o, ho, hit⟩ := List.mem_flatMap.mp hit
    obtain ⟨kg, hkg, rfl⟩ := List.mem_map.mp hit
    exact sat_ovlEq h ho hkg
  rcases List.mem_append.mp hit with hit | hit
  · obtain ⟨N, hN, hit⟩ := List.mem_flatMap.mp hit
    rcases List.mem_append.mp hit with hit | hit
    · rcases List.mem_append.mp hit with hit | hit
      · rcases List.mem_append.mp hit with hit | hit
        · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hit
          obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
          exact sat_funItem h hN hg
        · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hit
          obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hg').1
          exact sat_injItem h hN hg
      · obtain ⟨⟨g, g'⟩, hp, hit⟩ := List.mem_flatMap.mp hit
        exact sat_pairItem h hN hp hit
    · split at hit
      · exact absurd hit List.not_mem_nil
      · rw [List.mem_singleton.mp hit]
        exact sat_noJunk h hN
  · obtain ⟨⟨a, b⟩, hab, hit⟩ := List.mem_flatMap.mp hit
    obtain ⟨⟨b0, d⟩, hbd0, rfl⟩ := List.mem_map.mp hit
    obtain ⟨hbd, hb0⟩ := List.mem_filter.mp hbd0
    have hb : b0 = b := by simpa using hb0
    rw [hb] at hbd
    exact sat_coh h hab hbd

end

-- ModelPat.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {vs : List KoreAML.Var} {tbl : KoreAML.VarTable} {e : Valuation Elem} {σ : Subst}
variable {T : GroundTerm → GroundTerm → Prop}

theorem pargs_read {ts : List Term}
    (ih : ∀ t ∈ ts, ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret (stdI_T c T) e m ↔
      ∃ v, PatVal c σ t v ∧ m = .val v) :
    ∀ {bs : List Elem}, All2 (fun φ b => φ.interpret (stdI_T c T) e b)
      ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) bs →
      ∃ ws : List GroundTerm, bs = ws.map Elem.val ∧ PatVals c σ ts ws := by
  induction ts with
  | nil => intro bs h; cases h; exact ⟨[], rfl, .nil⟩
  | cons t ts iht =>
    intro bs h
    cases h with
    | cons hb hbs =>
      obtain ⟨v, hv, rfl⟩ := (ih t (List.mem_cons_self ..) _).mp hb
      obtain ⟨ws, rfl, hws⟩ := iht (fun t' ht' => ih t' (List.mem_cons_of_mem _ ht')) hbs
      exact ⟨v :: ws, rfl, .cons hv hws⟩

end

-- ModelPat.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {vs : List KoreAML.Var} {tbl : KoreAML.VarTable} {e : Valuation Elem} {σ : Subst}
variable {T : GroundTerm → GroundTerm → Prop}

theorem pargs_read' {ts : List Term}
    (ih : ∀ t ∈ ts, ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret (stdI_T c T) e m ↔
      ∃ v, PatVal c σ t v ∧ m = .val v) :
    ∀ {ws : List GroundTerm}, PatVals c σ ts ws →
      All2 (fun φ b => φ.interpret (stdI_T c T) e b) ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩))
        (ws.map Elem.val) := by
  induction ts with
  | nil => intro ws h; cases h; exact .nil
  | cons t ts iht =>
    intro ws h
    cases h with
    | cons ht hts =>
      exact .cons ((ih t (List.mem_cons_self ..) _).mpr ⟨_, ht, rfl⟩)
        (iht (fun t' ht' => ih t' (List.mem_cons_of_mem _ ht')) hts)

end

-- ModelPat.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **The reading of a pattern**: under a valuation that reads each variable as its value in σ, a
pattern denotes exactly the values it denotes under σ. -/
theorem tr_pat (h : HypModelCore c) {P : Nat → Prop} {vs : List KoreAML.Var} {tbl : KoreAML.VarTable}
    {e : Valuation Elem} {σ : Subst}
    (hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v) {p : Term} (hp : PatOK c P p) :
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs p)).interpret (stdI_T c T) e m ↔
      ∃ v, PatVal c σ p v ∧ m = .val v := by
  have hn := h.namesK
  induction hp with
  | @var i hi =>
    intro m
    rw [Term.kore, hvar i hi m]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, .var hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, patVal_var_inv hv, rfl⟩
  | @dv s lit hd =>
    intro m
    have := tr_term (T := T) h (P := fun _ => False) (vs := vs) (tbl := tbl) (e := e) (σ := σ) (fun _ hf => hf.elim)
      (TermOK.dv hd) m
    rw [this]
    constructor
    · rintro ⟨v, hv, rfl⟩; cases evalTerm_dv_inv hv; exact ⟨_, .dv, rfl⟩
    · rintro ⟨v, hv, rfl⟩; cases patVal_dv_inv hv; exact ⟨_, .dv, rfl⟩
  | @inj a b t ha hb _ ih =>
    intro m
    rw [Term.kore, KoreAML.tr_injP]
    rw [interp_appList]
    simp only [KoreAML.interp_sym, stdI_symb, evalSymb_inj]
    constructor
    · rintro ⟨a0, rfl, bs, hbs, happ⟩
      cases hbs with
      | cons h1 hbs =>
        cases hbs with
        | cons h2 hbs =>
          cases hbs with
          | cons h3 hbs =>
            cases hbs
            rename_i x1 x2 x3
            have e1 : x1 = .srt a := (sort_den hn ha e x1).mp h1
            have e2 : x2 = .srt b := (sort_den hn hb e x2).mp h2
            subst e1 e2
            obtain ⟨w, hw, rfl⟩ := (ih x3).mp h3
            simp only [AppE, stdI_app, evalApp_inj0, evalApp_inj1, evalApp_inj2, exists_eq_left] at happ
            subst happ
            exact ⟨injNormal a b w, .inj hw, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨w, hw, rfl⟩ := patVal_inj_inv hv
      refine ⟨_, rfl, [.srt a, .srt b, .val w], .cons ((sort_den hn ha e _).mpr rfl)
        (.cons ((sort_den hn hb e _).mpr rfl) (.cons ((ih _).mpr ⟨w, hw, rfl⟩) .nil)), ?_⟩
      simp only [AppE, stdI_app, evalApp_inj0, evalApp_inj1, evalApp_inj2, exists_eq_left]
  | @as t i _ hi ih =>
    intro m
    rw [Term.kore, tr_and2, KoreAML.interp_sAnd, ih m, hvar i hi m]
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, ⟨v', hv', he⟩⟩
      cases he
      exact ⟨v, .as hv hv', rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨h1, h2⟩ := patVal_as_inv hv
      exact ⟨⟨v, h1, rfl⟩, ⟨v, h2, rfl⟩⟩
  | @app f ts k hk hkn hl hkind _ ih =>
    intro m
    subst hkn
    rw [kore_app_tr, interp_appList]
    constructor
    · rintro ⟨a, ha, bs, hbs, happ⟩
      obtain ⟨ws, rfl, hws⟩ := pargs_read (T := T) ih hbs
      have hlw : ws.length = k.args.length := by
        rw [← hl, patVals_length hws]
      have hr := (head_app h hk (tbl := tbl) (vs := vs) (ts := ts) hlw m).mp ⟨a, ha, happ⟩
      unfold result at hr
      by_cases hc : c.isCtor k.name = true
      · rw [if_pos hc] at hr
        subst hr
        exact ⟨_, .ctor hc hws, rfl⟩
      rw [if_neg hc] at hr
      have hc' : c.isCtor k.name = false := by simpa using hc
      by_cases hh : isHook k.name = true
      · rw [if_pos hh] at hr
        obtain ⟨v, rfl, hv⟩ := hr
        by_cases hph : patternHooks.contains k.name = true
        · rw [Semantics.hookRes_of_notKey (silentKey_of_patternHook hph)] at hv
          exact ⟨v, .hook hph hws hv, rfl⟩
        · have hcp : c.isCollPat k.name = true := by
            rcases hkind with h1 | h1 | h1 | h1
            · exact absurd h1 hc
            · exact absurd h1 hph
            · exact h1
            · rw [(c.isOvl_parts h1).2.1] at hh; cases hh
          have hcs : silentKey k.name = false := by
            unfold Semantics.isCollPat at hcp
            simp only [hh, if_true, Bool.and_eq_true] at hcp
            exact silentKey_of_collPatternHook hcp.2
          rw [Semantics.hookRes_of_notKey hcs] at hv
          exact ⟨v, .coll hc' hcp hws (by rw [collVal_hook hh, hv]; rfl), rfl⟩
      rw [if_neg hh] at hr
      have hh' : isHook k.name = false := by simpa using hh
      by_cases ho : c.isOvl k.name = true
      · have hp' := (c.isOvl_parts ho).2.2.1
        simp only [hp', ho, Bool.false_eq_true, ↓reduceIte] at hr
        subst hr
        exact ⟨_, .ovl hc' ho hws rfl, rfl⟩
      have hcp : c.isCollPat k.name = true := by
        rcases hkind with h1 | h1 | h1 | h1
        · exact absurd h1 hc
        · exact absurd (patternHooks_hook h1) hh
        · exact h1
        · exact absurd h1 ho
      have hp := collPat_param hcp hh'
      rw [if_pos hp] at hr
      obtain ⟨v, rfl, hv⟩ := hr
      exact ⟨v, .coll hc' hcp hws (by rw [collVal_param hh', hv]), rfl⟩
    · rintro ⟨v, hv, rfl⟩
      have key : ∀ (ws : List GroundTerm), PatVals c σ ts ws → result c k ws (.val v) →
          ∃ a, (match iteSort? (c.symName k.name) with
            | some X => KoreAML.sym (.symbol "Lblite") ⬝ KoreAML.sym (.sort ("Sort" ++ X))
            | none => KoreAML.sym (.symbol (c.symName k.name))).interpret (stdI_T c T) e a ∧
            ∃ bs, All2 (fun φ b => φ.interpret (stdI_T c T) e b)
              ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) bs ∧ AppE (stdI_T c T) a bs (.val v) := by
        intro ws hts hres
        have hlw : ws.length = k.args.length := by rw [← hl, patVals_length hts]
        obtain ⟨a, ha, happ⟩ := (head_app h hk (tbl := tbl) (vs := vs) (ts := ts) hlw _).mpr hres
        exact ⟨a, ha, _, pargs_read' ih hts, happ⟩
      generalize hf : k.name = f at hv
      cases hv with
      | ctor hc hts =>
        subst hf
        exact key _ hts ((result_ctor hc _).mpr rfl)
      | hook hph hts hv' =>
        subst hf
        have hh := patternHooks_hook hph
        have hc : c.isCtor k.name = false := by
          cases hcb : c.isCtor k.name with
          | false => rfl
          | true =>
            exfalso
            obtain ⟨k', hk'⟩ := lookupSig_hookSigs_of_isHook hh
            have hk'm := (lookupSig_spec hk').1
            have := h.hookNotCtor hk'm
            rw [(lookupSig_spec hk').2, hcb] at this
            cases this
        exact key _ hts ((result_hook hc hh _).mpr ⟨v, rfl, Semantics.hookRes_of_value hv'⟩)
      | coll hc hcp hts hv' =>
        subst hf
        by_cases hh : isHook k.name = true
        · rw [collVal_hook hh, join_eq_some] at hv'
          exact key _ hts ((result_hook hc hh _).mpr ⟨v, rfl, Semantics.hookRes_of_value hv'⟩)
        · have hh' : isHook k.name = false := by simpa using hh
          rw [collVal_param hh'] at hv'
          exact key _ hts ((result_param hc hh' (collPat_param hcp hh') _).mpr ⟨v, rfl, hv'⟩)
      | ovl _ ho hts hnv =>
        subst hf
        exact key _ hts ((result_ovl ho _).mpr (by rw [hnv]))

end

-- ModelPat.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem tr_true {tbl : KoreAML.VarTable} (h : HypModelCore c) (e : Valuation Elem) (a : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (.dv (KoreAML.srt "Bool") "true")).interpret (stdI_T c T) e a ↔ a = .val (bool true) := by
  rw [KoreAML.tr_dv, ← KoreAML.tr_dv (t := [])]
  have := denGoal (T := T) h (bool true) Srt.bool (sortOf_bool true) e a
  unfold den KoreAML.den bool at this
  rw [GroundTerm.kore, sortName_bool] at this
  exact this

end

-- ModelPat.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **`⌈req = true⌉` holds exactly where `req` evaluates to `true`**, at the sort `σ'` of the
premise. -/
theorem reqPat_iff (h : HypModelCore c) {P : Nat → Prop} {vs : List KoreAML.Var} {tbl : KoreAML.VarTable}
    {e : Valuation Elem} {σ : Subst}
    (hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v) {t : Term} (ht : TermOK c P t)
    {S : Kore.KSort} {σ' : Elem} (hS : ∀ a, (KoreAML.trSort tbl S).interpret (stdI_T c T) e a ↔ a = σ')
    (hσ' : KoreAML.IsSort (stdI_T c T) σ') (m : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (reqPat S (some (Term.kore c vs t)))).interpret (stdI_T c T) e m ↔
      KoreAML.Inh (stdI_T c T) σ' m ∧ EvalTerm c σ t (some (bool true)) := by
  have hn := h.namesK
  have hmi := h.det
  have hB : ∀ a, (KoreAML.trSort tbl (KoreAML.srt "Bool")).interpret (stdI_T c T) e a ↔ a = .srt Srt.bool := by
    intro a; rw [trSort_srt, ← sortName_bool (c := c)]; exact sort_den hn bool_numbered e a
  have hBs : KoreAML.IsSort (stdI_T c T) (.srt Srt.bool) :=
    (isSort_iff _).mpr ⟨Srt.bool, List.mem_range.mpr bool_numbered, rfl⟩
  simp only [reqPat]
  rw [KoreAML.tr, KoreAML.interp_sEquals defOK_std sat_ceilDef hB hS hBs hσ']
  simp only [inh_srt, tr_term h hvar ht, tr_true h]
  constructor
  · rintro ⟨hm, hall⟩
    obtain ⟨v, hv, he⟩ := (hall (.val (bool true)) (sortOf_bool true)).mpr rfl
    cases he
    exact ⟨hm, hv⟩
  · rintro ⟨hm, hv⟩
    refine ⟨hm, fun a _ => ⟨?_, ?_⟩⟩
    · rintro ⟨v', hv', rfl⟩
      cases EvalTerm.functional_of_fnDet hmi hv' hv
      rfl
    · rintro rfl; exact ⟨_, hv, rfl⟩

end

-- ModelPat.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- A variable of a translated term, through the table `tbl`: its element. -/
theorem var_read {tbl : KoreAML.VarTable} {vs : List KoreAML.Var} {e : Valuation Elem} (i : Nat) (m : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e m ↔ m = e.evalEvar (tbl.ev (keyAt vs i)) := by
  unfold KoreAML.varAt; rw [KoreAML.tr]; exact Iff.rfl

end

-- ModelPat.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- Where a valuation gives each variable a value of its sort, its substitution is well sorted and
each variable reads as its value. -/
theorem substE_ok {tbl : KoreAML.VarTable} {vars : List Srt} {e : Valuation Elem}
    (hin : ∀ i < vars.length, InSort c (vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c vars i)))) :
    c.WellSorted vars (substE c tbl vars e) ∧
      ∀ i, i < vars.length → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c vars) i)).interpret (stdI_T c T) e m ↔
        ∃ v, (substE c tbl vars e).lookup i = some v ∧ m = .val v := by
  have hv : ∀ i < vars.length, ∃ v, e.evalEvar (tbl.ev (canonKey c vars i)) = .val v ∧
      c.sortOf v = some (vars.getD i 0) := fun i hi => inSort_val (hin i hi)
  constructor
  · intro i s hs
    have hi : i < vars.length := (List.getElem?_eq_some_iff.mp hs).1
    obtain ⟨v, he, hsv⟩ := hv i hi
    refine ⟨v, by rw [substE_lookup hi, he]; rfl, ?_⟩
    rwa [List.getD_eq_getElem?_getD, hs, Option.getD_some] at hsv
  · intro i hi m
    obtain ⟨v, he, -⟩ := hv i hi
    rw [var_read, substE_lookup hi]
    show m = e.evalEvar (tbl.ev (canonKey c vars i)) ↔ _
    rw [he]
    simp [toVal]

end

-- ModelPat.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- `∃b̄. body` holds at `e` where `body` holds at a valuation that differs from `e` at the binders
only, and gives each binder an element of its sort. -/
theorem existsAll_intro {tbl : KoreAML.VarTable} {S : Kore.KSort} {body : Kore.Pattern} :
    ∀ (bs : List Kore.EVar) (e e' : Valuation Elem) (m : Elem),
    (bs.map fun b => tbl.ev (KoreAML.evarKey b)).Nodup →
    (∀ b ∈ bs, ∃ n, b.sort = KoreAML.srt n) →
    (∀ x, (∀ b ∈ bs, x ≠ tbl.ev (KoreAML.evarKey b)) → e'.evalEvar x = e.evalEvar x) →
    e'.evalSvar = e.evalSvar →
    (∀ b ∈ bs, ∀ n, b.sort = KoreAML.srt n → InS (stdI_T c T) n (e'.evalEvar (tbl.ev (KoreAML.evarKey b)))) →
    (KoreAML.tr ⟨tbl, []⟩ body).interpret (stdI_T c T) e' m →
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll S bs body)).interpret (stdI_T c T) e m
  | [], e, e', m, _, _, hoff, hsv, _, hb => by
    have : e' = e := by
      cases e; cases e'
      simp only at hsv
      subst hsv
      congr 1
      funext x
      exact hoff x (fun _ h => absurd h List.not_mem_nil)
    subst this
    exact hb
  | b :: bs, e, e', m, hnd, hs, hoff, hsv, hg, hb => by
    show (KoreAML.tr ⟨tbl, []⟩ (.exist S b (KoreAML.existsAll S bs body))).interpret (stdI_T c T) e m
    rw [KoreAML.tr, KoreAML.interp_sExists]
    rw [List.map_cons, List.nodup_cons] at hnd
    refine ⟨e'.evalEvar (tbl.ev (KoreAML.evarKey b)), ?_, ?_⟩
    · rw [KoreAML.interp_member defOK_std]
      simp only [Function.update_same]
      obtain ⟨n, hn⟩ := hs b (List.mem_cons_self ..)
      rw [hn, trSort_srt]
      exact (inS_iff _).mpr (hg b (List.mem_cons_self ..) n hn)
    · refine existsAll_intro bs _ e' m hnd.2 (fun b' hb' => hs b' (List.mem_cons_of_mem _ hb'))
        (fun x hx => ?_) hsv (fun b' hb' => hg b' (List.mem_cons_of_mem _ hb')) hb
      show e'.evalEvar x = Function.update e.evalEvar (tbl.ev (KoreAML.evarKey b)) (e'.evalEvar (tbl.ev (KoreAML.evarKey b))) x
      by_cases hxb : x = tbl.ev (KoreAML.evarKey b)
      · subst hxb; simp only [Function.update_same]
      · rw [Function.update_noteq hxb]
        exact hoff x (fun b' hb' => by
          rcases List.mem_cons.mp hb' with rfl | hb'
          · exact hxb
          · exact hx b' hb')

end

-- ModelRules.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem sNext_iff (φ : KoreAML.P) (e : Valuation Elem) (x : GroundTerm) :
    (KoreAML.sNext φ).interpret (stdI_T c T) e (.val x) ↔ ∃ y, φ.interpret (stdI_T c T) e (.val y) ∧ StepE_T c T (.val x) (.val y) := by
  unfold KoreAML.sNext
  rw [KoreAML.interp_app]
  constructor
  · rintro ⟨a0, b0, ha0, hb, hab⟩
    have ha0' : a0 = .app .next [] := ha0
    subst ha0'
    have hst : StepE_T c T (.val x) b0 := hab
    cases b0 with
    | val y => exact ⟨y, hb, hst⟩
    | srt _ => exact hst.elim
    | app _ _ => exact hst.elim
  · rintro ⟨y, hy, hst⟩
    exact ⟨.app .next [], .val y, rfl, hy, hst⟩

end

-- ModelFns.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem R_read {tbl : KoreAML.VarTable} (e : Valuation Elem) (a : Elem) :
    (KoreAML.trSort tbl KoreAML.R).interpret (stdI_T c T) e a ↔ a = e.evalEvar (tbl.ev (.sortVar "R")) := by
  rw [trSort_R, KoreAML.interp_evar]

end

-- ModelFns.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem vars_numbered_read {tbl : KoreAML.VarTable} {e : Valuation Elem} :
    ∀ (ss : List String) (ws : List GroundTerm) (j : Nat), ss.length = ws.length →
    (∀ (n : Nat) (w : GroundTerm) (s : String), ws[n]? = some w → ss[n]? = some s →
      e.evalEvar (tbl.ev (.evar ("X" ++ toString (j + n)) (KoreAML.srt s))) = .val w) →
    All2 (fun φ x => ∀ m, φ.interpret (stdI_T c T) e m ↔ m = x)
      ((KoreAML.vars (KoreAML.numbered "X" j ss)).map (KoreAML.tr ⟨tbl, []⟩)) (ws.map Elem.val)
  | [], [], _, _, _ => .nil
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | s :: ss, w :: ws, j, hl, hX => by
    simp only [KoreAML.numbered, KoreAML.vars, List.map_cons, Function.comp]
    refine .cons (fun m => ?_) ?_
    · rw [KoreAML.tr, KoreAML.interp_evar]
      have := hX 0 w s rfl rfl
      rw [Nat.add_zero] at this
      exact Iff.of_eq (congrArg (m = ·) this)
    · have := vars_numbered_read ss ws (j + 1) (by simpa using hl)
        (fun n w' s' h1 h2 => by
          have := hX (n + 1) w' s' (by simpa using h1) (by simpa using h2)
          rwa [show j + (n + 1) = j + 1 + n by omega] at this)
      simpa [KoreAML.vars] using this

end

-- ModelFns.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **The call `f(X̄)`**, at a valuation giving `X̄` the arguments' values: the values `Eval`
gives. -/
theorem call_read (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {tbl : KoreAML.VarTable} {e : Valuation Elem}
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    (hX : ∀ (j : Nat) (w : GroundTerm) (s : String), ws[j]? = some w → (fn.args.map c.sortName)[j]? = some s →
      e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) = .val w) (b : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.ap (c.symName fn.label)
      (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret (stdI_T c T) e b ↔
      ∃ v, b = .val v ∧ Eval c fn.label ws (some v) := by
  obtain ⟨hc, hh, hp⟩ := h.fnApart hfn
  have hl : ws.length = fn.args.length := sortsOf_len hws
  rw [tr_ap_tbl, interp_symList _ _ (ws.map Elem.val)
    (vars_numbered_read _ ws 0 (by simp [hl]) (fun n w s h1 h2 => by rw [Nat.zero_add]; exact hX n w s h1 h2)) b]
  rw [show c.symName fn.label = c.symName fn.sig.name from rfl,
    symE_vals h.namesK (fn_sig_mem hfn) (by rw [hl]; rfl) b]
  exact result_fn (k := fn.sig) hc hh hp (c.isOvl_of_lookupFn (h.lookupFn hfn)) b

end

-- ModelFns.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem anyOfC_iff {tbl : KoreAML.VarTable} {S : Kore.KSort} {e : Valuation Elem} {σS : Elem}
    (hS : ∀ a, (KoreAML.trSort tbl S).interpret (stdI_T c T) e a ↔ a = σS)
    (hfree : (KoreAML.trSort tbl S).isFreeEvar KoreAML.topVar = false) :
    ∀ (cs : List Kore.Pattern) (a : Elem), (KoreAML.tr ⟨tbl, []⟩ (anyOfC S cs)).interpret (stdI_T c T) e a ↔
      KoreAML.Inh (stdI_T c T) σS a ∧ ∃ φ ∈ cs, (KoreAML.tr ⟨tbl, []⟩ φ).interpret (stdI_T c T) e a
  | [], a => by
    rw [anyOfC, KoreAML.tr]
    unfold KoreAML.sBot
    rw [KoreAML.interp_sNot, KoreAML.interp_sTop defOK_std hfree]
    simp
  | φ :: cs, a => by
    rw [anyOfC, KoreAML.tr]
    simp only [KoreAML.trOrList]
    rw [KoreAML.interp_sOr, anyOfC_iff hS hfree cs a, KoreAML.interp_inhOf_of hS]
    constructor
    · rintro ⟨hi, hφ | ⟨-, ψ, hψ, hψa⟩⟩
      · exact ⟨hi, φ, List.mem_cons_self .., hφ⟩
      · exact ⟨hi, ψ, List.mem_cons_of_mem _ hψ, hψa⟩
    · rintro ⟨hi, ψ, hψ, hψa⟩
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact ⟨hi, Or.inl hψa⟩
      · exact ⟨hi, Or.inr ⟨hi, ψ, hψ, hψa⟩⟩

end

-- ModelFns.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem argsConj_iff {tbl : KoreAML.VarTable} {e : Valuation Elem} {σR : Elem}
    (hR : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret (stdI_T c T) e a ↔ a = σR) (hRs : KoreAML.IsSort (stdI_T c T) σR) :
    ∀ (j : Nat) (l : List (String × Kore.Pattern)),
    (∀ (n : Nat) (s : String) (p : Kore.Pattern), l[n]? = some (s, p) → ∃ σs, (∀ a, (KoreAML.trSort tbl (KoreAML.srt s)).interpret (stdI_T c T) e a ↔ a = σs) ∧
      KoreAML.IsSort (stdI_T c T) σs ∧
      KoreAML.Inh (stdI_T c T) σs (e.evalEvar (tbl.ev (.evar ("X" ++ toString (j + n)) (KoreAML.srt s))))) →
    ∀ a, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.argsConj j l)).interpret (stdI_T c T) e a ↔
      KoreAML.Inh (stdI_T c T) σR a ∧ ∀ (n : Nat) (s : String) (p : Kore.Pattern), l[n]? = some (s, p) →
        (KoreAML.tr ⟨tbl, []⟩ p).interpret (stdI_T c T) e (e.evalEvar (tbl.ev (.evar ("X" ++ toString (j + n)) (KoreAML.srt s))))
  | j, [], _, a => by
    simp only [KoreAML.argsConj]
    rw [KoreAML.tr, KoreAML.interp_sTop defOK_std isFree_R, KoreAML.interp_inhOf_of hR]
    simp
  | j, (s, p) :: l, hs, a => by
    simp only [KoreAML.argsConj]
    rw [tr_and2, KoreAML.interp_sAnd, argsConj_iff hR hRs (j + 1) l (fun n s' p' hn => by
      obtain ⟨σs, h1, h2, h3⟩ := hs (n + 1) s' p' (by simpa using hn)
      exact ⟨σs, h1, h2, by rwa [show j + (n + 1) = j + 1 + n by omega] at h3⟩) a]
    obtain ⟨σs, hσs, hσss, hXs⟩ := hs 0 s p rfl
    rw [Nat.add_zero] at hXs
    have hXr : ∀ b, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.ev s!"X{j}" (KoreAML.srt s))).interpret (stdI_T c T) e b ↔
        b = e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) := fun b => by
      unfold KoreAML.ev; rw [KoreAML.tr, KoreAML.interp_evar]; rfl
    rw [KoreAML.tr, KoreAML.interp_sIn defOK_std sat_ceilDef hσs hR hσss hRs (fun b hb => by
      rw [(hXr b).mp hb]; exact hXs)]
    have hex : (∃ b, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.ev s!"X{j}" (KoreAML.srt s))).interpret (stdI_T c T) e b ∧
        (KoreAML.tr ⟨tbl, []⟩ p).interpret (stdI_T c T) e b) ↔
        (KoreAML.tr ⟨tbl, []⟩ p).interpret (stdI_T c T) e (e.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s)))) :=
      ⟨fun ⟨b, hb, hp⟩ => (hXr b).mp hb ▸ hp, fun hp => ⟨_, (hXr _).mpr rfl, hp⟩⟩
    rw [hex]
    constructor
    · rintro ⟨⟨hp, hi⟩, -, hrest⟩
      refine ⟨hi, fun n s' p' hn => ?_⟩
      cases n with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        rw [Nat.add_zero]; exact hp
      | succ n =>
        have := hrest n s' p' (by simpa using hn)
        rwa [show j + 1 + n = j + (n + 1) by omega] at this
    · rintro ⟨hi, hall⟩
      refine ⟨⟨?_, hi⟩, hi, fun n s' p' hn => ?_⟩
      · have := hall 0 s p rfl; rwa [Nat.add_zero] at this
      · have := hall (n + 1) s' p' (by simpa using hn)
        rwa [show j + (n + 1) = j + 1 + n by omega] at this

end

-- ModelFns.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **A premise** `⌈req = true⌉ ∧ X̄ ∈ p̄` holds exactly where the `requires` evaluates to `true`
under σ and the patterns denote the arguments under σ. -/
theorem premise_iff (h : HypModelCore c) {vars args : List Srt} {req : Option Term} {pats : List Term}
    {tbl : KoreAML.VarTable} {e : Valuation Elem} {σR : Elem}
    (hR : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret (stdI_T c T) e a ↔ a = σR) (hRs : KoreAML.IsSort (stdI_T c T) σR)
    {σ : Subst}
    (hvar : ∀ i, i < vars.length → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c vars) i)).interpret (stdI_T c T) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v)
    (hreqOK : ∀ t, req = some t → TermOK c (· < vars.length) t)
    (hpatOK : ∀ p ∈ pats, PatOK c (· < vars.length) p) (hlen : pats.length = args.length)
    {ws : List GroundTerm} (hX : ArgsAt c tbl e args ws) (a : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (premise (args.map c.sortName) (req.map (Term.kore c (canonVars c vars)))
      (Term.koreList c (canonVars c vars) pats))).interpret (stdI_T c T) e a ↔
      KoreAML.Inh (stdI_T c T) σR a ∧ (∀ t, req = some t → EvalTerm c σ t (some (bool true))) ∧ PatVals c σ pats ws := by
  have hn := h.namesK
  have hwl : ws.length = args.length := sortsOf_len hX.sorts
  unfold premise
  rw [tr_and2, KoreAML.interp_sAnd]
  have hreq : (KoreAML.tr ⟨tbl, []⟩ (reqPat KoreAML.R (req.map (Term.kore c (canonVars c vars))))).interpret (stdI_T c T) e a ↔
      KoreAML.Inh (stdI_T c T) σR a ∧ ∀ t, req = some t → EvalTerm c σ t (some (bool true)) := by
    cases hq : req with
    | none =>
      simp only [Option.map_none, reqPat]
      rw [KoreAML.tr, KoreAML.interp_sTop defOK_std isFree_R, KoreAML.interp_inhOf_of hR]
      simp
    | some t =>
      simp only [Option.map_some]
      rw [reqPat_iff h hvar (hreqOK t hq) hR hRs]
      simp
  rw [hreq, argsConj_iff hR hRs 0 _ (fun n s p hn' => ?_)]
  · constructor
    · rintro ⟨⟨hi, hq⟩, -, hall⟩
      refine ⟨hi, hq, patVals_of_get (by rw [hlen, hwl]) fun n p w hp hw => ?_⟩
      have hlt : n < args.length := by rw [← hwl]; exact (List.getElem?_eq_some_iff.mp hw).1
      have hs : (args.map c.sortName)[n]? = some (c.sortName (args[n]'hlt)) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
      have hl : ((args.map c.sortName).zip (Term.koreList c (canonVars c vars) pats))[n]? =
          some (c.sortName (args[n]'hlt), Term.kore c (canonVars c vars) p) := by
        rw [List.getElem?_zip_eq_some]
        refine ⟨hs, ?_⟩
        rw [koreList_get hp]
      have := hall n _ _ hl
      rw [Nat.zero_add, hX.X n w _ hw hs] at this
      obtain ⟨v, hv, he⟩ := (tr_pat h hvar (hpatOK p (List.mem_of_getElem? hp)) _).mp this
      cases he
      exact hv
    · rintro ⟨hi, hq, hpv⟩
      refine ⟨⟨hi, hq⟩, hi, fun n s p hl => ?_⟩
      obtain ⟨hs, hp⟩ := List.getElem?_zip_eq_some.mp hl
      obtain ⟨p0, hp0, rfl⟩ := koreList_get_inv (c := c) hp
      rw [List.getElem?_map] at hs
      obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp hs
      obtain ⟨w, hw, -⟩ := sortsOf_get hX.sorts ha0
      rw [Nat.zero_add, hX.X n w _ hw (by rw [List.getElem?_map, ha0]; rfl)]
      exact (tr_pat h hvar (hpatOK p0 (List.mem_of_getElem? hp0)) _).mpr ⟨w, patVals_get hpv n p0 w hp0 hw, rfl⟩
  · obtain ⟨hs, -⟩ := List.getElem?_zip_eq_some.mp hn'
    rw [List.getElem?_map] at hs
    obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp hs
    have hnum := hX.num a0 (List.mem_of_getElem? ha0)
    obtain ⟨w, hw, hsw⟩ := sortsOf_get hX.sorts ha0
    refine ⟨.srt a0, fun b => by rw [trSort_srt]; exact sort_den hn hnum e b,
      (isSort_iff _).mpr ⟨a0, List.mem_range.mpr hnum, rfl⟩, ?_⟩
    rw [Nat.zero_add, hX.X n w _ hw (by rw [List.getElem?_map, ha0]; rfl), inh_srt]
    exact hsw

end

-- ModelFns.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **An equation holds in the value model** where, at every valuation of its guards, its premise
gives `Eval` what the right-hand side gives. Each variable is free in the axiom, in its premise or
in its conclusion, so the guards give it an element of its sort. -/
theorem sat_eqnCl (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {vars : List Srt}
    (hnum : ∀ i < vars.length, vars.getD i 0 < nRegSorts + c.sortNames.length)
    {prem : Kore.Pattern} {rhs : Term} (hrhsOK : TermOK c (· < vars.length) rhs)
    {ens : Option Term} (hensOK : ∀ t, ens = some t → TermOK c (· < vars.length) t)
    (hV : ∀ i < vars.length, canonKey c vars i ∈ KoreAML.freeOf [] (.implies KoreAML.R prem
      (fnConcl c fn (Term.kore c (canonVars c vars) rhs) (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars)))))))
    (hVv : ∀ i < vars.length, canonKey c vars i ∈ KoreAML.varsOf (.implies KoreAML.R prem
      (fnConcl c fn (Term.kore c (canonVars c vars) rhs) (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars)))))))
    (hread : ∀ (tbl : KoreAML.VarTable) (e : Valuation Elem) (ws : List GroundTerm) (a : Elem), EqnAt c T fn vars tbl e ws →
      (∀ k ∈ KoreAML.varsOf prem, k ∈ tbl) →
      KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a → (KoreAML.tr ⟨tbl, []⟩ prem).interpret (stdI_T c T) e a →
      ∀ v, Eval c fn.label ws (some v) ↔ EvalTerm c (substE c tbl vars e) rhs (some v) ∧
        ∀ t, ens = some t → EvalTerm c (substE c tbl vars e) t (some (bool true))) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv],
      .implies KoreAML.R prem (fnConcl c fn (Term.kore c (canonVars c vars) rhs)
        (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars))))), []⟩ : Kore.Axiom)⟩).pat := by
  have hn := h.namesK
  have hfs := h.fnSorts hfn
  intro e m
  unfold KoreAML.trAxiom
  dsimp only
  have hsortP : KoreAML.sortOf [] (.implies KoreAML.R prem (fnConcl c fn (Term.kore c (canonVars c vars) rhs)
        (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars)))))) =
      some KoreAML.R := rfl
  simp only [hsortP]
  rw [interpret_impl]
  intro hgs
  generalize hP : (Kore.Pattern.implies KoreAML.R prem (fnConcl c fn (Term.kore c (canonVars c vars) rhs)
        (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars)))))) = P at hgs ⊢
  have hPv : ∀ k ∈ KoreAML.varsOf prem, k ∈ KoreAML.varsOf P := fun k hk => by
    rw [← hP, KoreAML.varsOf]; exact List.mem_append_left _ (List.mem_append_right _ hk)
  generalize htb : KoreAML.tableOf [KoreAML.Rv] P = tbl at hgs ⊢
  have hvarsP : ∀ k ∈ KoreAML.varsOf P, k ∈ tbl := fun k hk => by
    rw [← htb]; exact List.mem_eraseDups.mpr (List.mem_append_right _ hk)
  have hguard : ∀ k ∈ (([KoreAML.Rv].map KoreAML.sortVarKey) ++ KoreAML.freeOf [] P).eraseDups,
      (KoreAML.guardOf tbl k).interpret (stdI_T c T) e m := fun k hk =>
    conjList_elim hgs _ (List.mem_map.mpr ⟨k, hk, rfl⟩)
  have hfreeP : ∀ k ∈ KoreAML.freeOf [] P, k ∈ (([KoreAML.Rv].map KoreAML.sortVarKey) ++ KoreAML.freeOf [] P).eraseDups :=
    fun k hk => List.mem_eraseDups.mpr (List.mem_append_right _ hk)
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by
    rw [← htb]; exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩))
  have hRs : KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) := by
    have := hguard (.sortVar "R") (List.mem_eraseDups.mpr (List.mem_append_left _
      (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩)))
    obtain ⟨s, hs, he⟩ := sortGuard_iff.mp this
    rw [he]; exact (isSort_iff _).mpr ⟨s, hs, rfl⟩
  have hcallF : ∀ j s, (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ KoreAML.freeOf [] P := fun j s hj => by
    rw [← hP, KoreAML.freeOf]
    refine List.mem_append_right _ ?_
    unfold fnConcl
    rw [KoreAML.freeOf]
    refine List.mem_append_left _ ?_
    unfold KoreAML.ap
    rw [KoreAML.freeOf]
    have := X_mem_call _ 0 j s hj
    rwa [Nat.zero_add] at this
  have hXk : ∀ j s, (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl := fun j s hj => by
    refine hvarsP _ ?_
    rw [← hP, KoreAML.varsOf]
    refine List.mem_append_right _ ?_
    unfold fnConcl
    rw [KoreAML.varsOf]
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    unfold KoreAML.ap
    rw [KoreAML.varsOf]
    refine List.mem_append_right _ ?_
    have := X_mem_varsOf_call _ 0 j s hj
    rwa [Nat.zero_add] at this
  obtain ⟨ws, hws⟩ := argsAt_of (tbl := tbl) (e := e) (fun s hs => hfs s (List.mem_cons_of_mem _ hs)) (fun j hj => by
    have hs : (fn.args.map c.sortName)[j]? = some (c.sortName (fn.args[j]'hj)) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
    have hg := hguard _ (hfreeP _ (hcallF j _ hs))
    rw [KoreAML.interp_guard_evar defOK_std, trSort_srt] at hg
    exact (inhOf_sort hn (hfs _ (List.mem_cons_of_mem _ (List.getElem_mem hj))) e _).mp hg)
  have hvin : ∀ i < vars.length, InSort c (vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c vars i))) := by
    intro i hi
    have hk : canonKey c vars i ∈ KoreAML.freeOf [] P := hP ▸ hV i hi
    have hg := hguard _ (hfreeP _ hk)
    have hkk := canonKey_eq c hi
    rw [hkk, KoreAML.interp_guard_evar defOK_std, trSort_srt, ← hkk] at hg
    exact (inhOf_sort hn (hnum i hi) e _).mp hg
  have hEq : EqnAt c T fn vars tbl e ws :=
    ⟨hRmem, hXk, fun i hi => hvarsP _ (hP ▸ hVv i hi), hRs, hws, hvin⟩
  obtain ⟨hσ, hvar⟩ := substE_ok (T := T) hvin
  have hres := hfs fn.result (List.mem_cons_self ..)
  rw [KoreAML.interp_equal defOK_std]
  intro a
  have hPtr : KoreAML.tr ⟨tbl, []⟩ P = KoreAML.sImp (KoreAML.trSort tbl KoreAML.R) (KoreAML.tr ⟨tbl, []⟩ prem)
      (KoreAML.tr ⟨tbl, []⟩ (fnConcl c fn (Term.kore c (canonVars c vars) rhs)
        (reqPat (srtOf c fn.result) (ens.map (Term.kore c (canonVars c vars)))))) := by
    rw [← hP, KoreAML.tr]
  rw [hPtr, KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun hprem => ?_⟩
    rw [KoreAML.interp_inhOf_of (R_read e)] at ha
    have hrd := hread tbl e ws a hEq (fun k hk => hvarsP _ (hPv _ hk)) ha hprem
    have hSres : ∀ b, (KoreAML.trSort tbl (KoreAML.srt (c.sortName fn.result))).interpret (stdI_T c T) e b ↔
        b = .srt fn.result := fun b => by rw [trSort_srt]; exact sort_den hn hres e b
    unfold fnConcl
    rw [KoreAML.tr, KoreAML.interp_sEquals defOK_std sat_ceilDef hSres (R_read e)
      ((isSort_iff _).mpr ⟨fn.result, List.mem_range.mpr hres, rfl⟩) hRs]
    refine ⟨ha, fun b hb => ?_⟩
    have hSres' : ∀ b, (KoreAML.trSort tbl (srtOf c fn.result)).interpret (stdI_T c T) e b ↔
        b = .srt fn.result := fun b => by unfold srtOf; exact hSres b
    have hens : ((KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c fn.result)
        (ens.map (Term.kore c (canonVars c vars))))).interpret (stdI_T c T) e b ↔
          ∀ t, ens = some t → EvalTerm c (substE c tbl vars e) t (some (bool true))) := by
      cases hq : ens with
      | none =>
        simp only [Option.map_none, reqPat]
        rw [KoreAML.tr, KoreAML.interp_sTop defOK_std (by unfold srtOf; rw [trSort_srt]; rfl),
          KoreAML.interp_inhOf_of hSres']
        exact ⟨fun _ t ht => (nomatch ht), fun _ => hb⟩
      | some t =>
        rw [Option.map_some, reqPat_iff h hvar (hensOK t hq) hSres'
          ((isSort_iff _).mpr ⟨fn.result, List.mem_range.mpr hres, rfl⟩) b]
        exact ⟨fun h' t' ht' => by cases ht'; exact h'.2, fun h' => ⟨hb, h' t rfl⟩⟩
    rw [inh_srt] at hb
    rw [call_read h hfn hws.sorts hws.X, tr_and2, KoreAML.interp_sAnd, hens, tr_term h hvar hrhsOK]
    constructor
    · rintro ⟨v, rfl, hv⟩
      obtain ⟨h1, h2⟩ := (hrd _).mp hv
      exact ⟨⟨v, h1, rfl⟩, h2⟩
    · rintro ⟨⟨v, hv, rfl⟩, h2⟩
      exact ⟨v, rfl, (hrd _).mpr ⟨hv, h2⟩⟩

end

-- ModelFns.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **A function's rest graph holds**: where every clause fails at values of its argument sorts,
`f` applied to them is the values `Eval` gives there (`result_fn`), and `Eval.rest` with
`FnDet` makes that the rest. -/
theorem sat_restGraph (h : HypModelCore c) {fn : Fn} {vs : List GroundTerm} (hfn : fn ∈ c.allFns)
    (hvs : c.sortsOf vs = some fn.args) (hnone : ∀ cl ∈ fn.clauses, Fails c vs cl) :
    stdI_T c T ⊧ᴵ (KoreAML.den (symApp c fn.label (GroundTerm.koreList c vs)) ≡ (match c.fnRest fn vs with
      | some v => den c v
      | none => ⊥)) := by
  obtain ⟨hc, hh, hp⟩ := h.fnApart hfn
  have hE : Eval c fn.label vs (c.fnRest fn vs) := .rest (h.lookupFn hfn) hnone
  have hmi := h.det
  intro e m
  rw [KoreAML.interp_equal defOK_std]
  intro a
  rw [show fn.label = fn.sig.name from rfl, symApp_val h (fn_sig_mem hfn) hvs (sortsOf_length hvs),
    result_fn (k := fn.sig) hc hh hp (c.isOvl_of_lookupFn (h.lookupFn hfn))]
  revert hE
  cases hr : c.fnRest fn vs with
  | none =>
    intro hE
    simp only [Pattern.interpret]
    constructor
    · rintro ⟨v, -, hv⟩; cases hmi _ _ _ _ hv hE
    · intro hf; exact hf.elim
  | some v =>
    intro hE
    dsimp only
    rw [den_val h v (Semantics.fnRest_sorted hr) e a]
    constructor
    · rintro ⟨v', rfl, hv'⟩; cases hmi _ _ _ _ hv' hE; rfl
    · rintro rfl; exact ⟨v, rfl, hE⟩

end

-- ModelFns.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **`SatFallbackGoal`**: the value model satisfies what the interpretation decides where the
text is silent: an interpreted symbol's result at its silent points (`sat_silentGraph`), and a
function's rest where every clause fails (`sat_restGraph`). -/
theorem satFallbackGoal (h : HypModelCore c) : (stdI_T c T ⊧ᴵP ΓFallback c) := by
  rintro φ (⟨k, vs, hk, hvs, hh, hs, rfl⟩ | ⟨fn, vs, hfn, hvs, hnone, rfl⟩)
  · exact sat_silentGraph h hk hvs hh hs
  · exact sat_restGraph h hfn hvs hnone

end

-- ModelFnsCl.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- `premise_iff` at the variables a predicate `P` names: the `requires` and the patterns read
only those, and σ gives them their values. -/
theorem premise_iffCl (h : HypModelCore c) {P : Nat → Prop} {vars args : List Srt} {req : Option Term}
    {pats : List Term} {tbl : KoreAML.VarTable} {e : Valuation Elem} {σR : Elem}
    (hR : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret (stdI_T c T) e a ↔ a = σR) (hRs : KoreAML.IsSort (stdI_T c T) σR)
    {σ : Subst}
    (hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c vars) i)).interpret (stdI_T c T) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v)
    (hreqOK : ∀ t, req = some t → TermOK c P t)
    (hpatOK : ∀ p ∈ pats, PatOK c P p) (hlen : pats.length = args.length)
    {ws : List GroundTerm} (hX : ArgsAt c tbl e args ws) (a : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (premise (args.map c.sortName) (req.map (Term.kore c (canonVars c vars)))
      (Term.koreList c (canonVars c vars) pats))).interpret (stdI_T c T) e a ↔
      KoreAML.Inh (stdI_T c T) σR a ∧ (∀ t, req = some t → EvalTerm c σ t (some (bool true))) ∧ PatVals c σ pats ws := by
  have hn := h.namesK
  have hwl : ws.length = args.length := sortsOf_len hX.sorts
  unfold premise
  rw [tr_and2, KoreAML.interp_sAnd]
  have hreq : (KoreAML.tr ⟨tbl, []⟩ (reqPat KoreAML.R (req.map (Term.kore c (canonVars c vars))))).interpret (stdI_T c T) e a ↔
      KoreAML.Inh (stdI_T c T) σR a ∧ ∀ t, req = some t → EvalTerm c σ t (some (bool true)) := by
    cases hq : req with
    | none =>
      simp only [Option.map_none, reqPat]
      rw [KoreAML.tr, KoreAML.interp_sTop defOK_std isFree_R, KoreAML.interp_inhOf_of hR]
      simp
    | some t =>
      simp only [Option.map_some]
      rw [reqPat_iff h hvar (hreqOK t hq) hR hRs]
      simp
  rw [hreq, argsConj_iff hR hRs 0 _ (fun n s p hn' => ?_)]
  · constructor
    · rintro ⟨⟨hi, hq⟩, -, hall⟩
      refine ⟨hi, hq, patVals_of_get (by rw [hlen, hwl]) fun n p w hp hw => ?_⟩
      have hlt : n < args.length := by rw [← hwl]; exact (List.getElem?_eq_some_iff.mp hw).1
      have hs : (args.map c.sortName)[n]? = some (c.sortName (args[n]'hlt)) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
      have hl : ((args.map c.sortName).zip (Term.koreList c (canonVars c vars) pats))[n]? =
          some (c.sortName (args[n]'hlt), Term.kore c (canonVars c vars) p) := by
        rw [List.getElem?_zip_eq_some]
        refine ⟨hs, ?_⟩
        rw [koreList_get hp]
      have := hall n _ _ hl
      rw [Nat.zero_add, hX.X n w _ hw hs] at this
      obtain ⟨v, hv, he⟩ := (tr_pat h hvar (hpatOK p (List.mem_of_getElem? hp)) _).mp this
      cases he
      exact hv
    · rintro ⟨hi, hq, hpv⟩
      refine ⟨⟨hi, hq⟩, hi, fun n s p hl => ?_⟩
      obtain ⟨hs, hp⟩ := List.getElem?_zip_eq_some.mp hl
      obtain ⟨p0, hp0, rfl⟩ := koreList_get_inv (c := c) hp
      rw [List.getElem?_map] at hs
      obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp hs
      obtain ⟨w, hw, -⟩ := sortsOf_get hX.sorts ha0
      rw [Nat.zero_add, hX.X n w _ hw (by rw [List.getElem?_map, ha0]; rfl)]
      exact (tr_pat h hvar (hpatOK p0 (List.mem_of_getElem? hp0)) _).mpr ⟨w, patVals_get hpv n p0 w hp0 hw, rfl⟩
  · obtain ⟨hs, -⟩ := List.getElem?_zip_eq_some.mp hn'
    rw [List.getElem?_map] at hs
    obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp hs
    have hnum := hX.num a0 (List.mem_of_getElem? ha0)
    obtain ⟨w, hw, hsw⟩ := sortsOf_get hX.sorts ha0
    refine ⟨.srt a0, fun b => by rw [trSort_srt]; exact sort_den hn hnum e b,
      (isSort_iff _).mpr ⟨a0, List.mem_range.mpr hnum, rfl⟩, ?_⟩
    rw [Nat.zero_add, hX.X n w _ hw (by rw [List.getElem?_map, ha0]; rfl), inh_srt]
    exact hsw

end

-- ModelFnsCl.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **The reading of an exclusion whose clause's patterns need not bind every variable**: at a
valuation giving the formal arguments the values `w̄`, the clause's exclusion
`∃ȳ. ⌈req = true⌉ ∧ X̄ ∈ p̄`, ȳ the variables of its patterns and conditions, holds exactly where
the patterns match `w̄` and the `requires` is `true` under a substitution well sorted on those
variables. -/
theorem exclusion_iffCl (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses)
    {tbl : KoreAML.VarTable} (hkeys : ∀ i < cl.vars.length, i ∈ cl.leftVars → canonKey c cl.vars i ∈ tbl)
    (hRkey : KoreAML.VarKey.sortVar "R" ∈ tbl)
    (hXkeys : ∀ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl)
    {e : Valuation Elem} (hRs : KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))))
    {ws : List GroundTerm} (hX : ArgsAt c tbl e fn.args ws) {a : Elem}
    (ha : KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a) :
    (KoreAML.tr ⟨tbl, []⟩ (exclusion c fn cl (canonClausePres cl))).interpret (stdI_T c T) e a ↔
      ∃ σ, c.WellSortedAt cl.vars cl.leftVars σ ∧ PatVals c σ cl.pats ws ∧
        ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)) := by
  have hn := h.namesK
  obtain ⟨hpats, -, L, hL, hreqs, -⟩ := clause_factsCl h hfn hcl
  have hnum := clause_vars_num h hfn hcl
  have hlen : cl.pats.length = fn.args.length := sortsOfTerms_length hpats
  let vs := canonVars c cl.vars
  let n := cl.vars.length
  let l := (List.range n).filter cl.leftVars.contains
  have hl : ∀ i ∈ l, i < n := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
  have hlm : ∀ i ∈ l, i ∈ cl.leftVars := fun i hi => by simpa using (List.mem_filter.mp hi).2
  have hml : ∀ i < n, i ∈ cl.leftVars → i ∈ l := fun i hi hil =>
    List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simpa using hil⟩
  have hnd : (((l.map (vs.getD · default)).map KoreAML.Var.kore).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    rw [List.map_map, List.map_map]
    refine nodup_map_of_injOn _ (fun i hi j hj he => ?_) (List.nodup_range.filter _)
    exact canonKey_inj (hl i hi) (hl j hj) (ev_inj (hkeys i (hl i hi) (hlm i hi)) (hkeys j (hl j hj) (hlm j hj)) he)
  have hsrt : ∀ b ∈ (l.map (vs.getD · default)).map KoreAML.Var.kore, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    show ∃ n, ((canonVars c cl.vars).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (hl i hi)]; exact ⟨_, rfl⟩
  -- the patterns and the `requires` read the variables of the patterns and the conditions only
  let P : Nat → Prop := fun i => i < n ∧ i ∈ cl.leftVars
  have hpatOK : ∀ p ∈ cl.pats, PatOK c P p := fun p hp =>
    (patOKs_of_sorted h hpats p hp).monoOpen fun i hi =>
      ⟨varOccsList_lt cl.pats hpats i (varOccsList_of_memOpen hp hi), List.mem_append_left _ (varOccsList_of_memOpen hp hi)⟩
  have hreqOK : ∀ t, cl.req = some t → TermOK c P t := fun t ht =>
    (termOK_of_sorted h hL (hreqs t ht)).monoOpen fun i hi =>
      ⟨varOccs_lt t (hreqs t ht) i hi, Clause.req_leftVars ht i hi⟩
  -- the keys that are not binders
  have hnotb : ∀ k, k ∈ tbl → (∀ i < n, k ≠ canonKey c cl.vars i) →
      ∀ b ∈ (l.map (vs.getD · default)).map KoreAML.Var.kore, tbl.ev k ≠ tbl.ev (KoreAML.evarKey b) := by
    intro k hk hne b hb heq
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact hne i (hl i hi) (ev_inj hk (hkeys i (hl i hi) (hlm i hi)) heq)
  have hRne : ∀ i < n, KoreAML.VarKey.sortVar "R" ≠ canonKey c cl.vars i := fun i hi he => by
    rw [canonKey_eq c hi] at he; cases he
  rw [exclusion_canon_mapCl]
  constructor
  · intro hm
    obtain ⟨e', hag, hguard, hbody⟩ := existsAll_elim defOK_std _ e a hnd hsrt hm
    have he'R : e'.evalEvar (tbl.ev (.sortVar "R")) = e.evalEvar (tbl.ev (.sortVar "R")) :=
      hag _ (hnotb _ hRkey hRne)
    have hX' : ArgsAt c tbl e' fn.args ws := ⟨hX.sorts, hX.num, fun j w s hw hs => by
      rw [hag _ (hnotb _ (hXkeys j s hs) (fun i hi => canonKey_ne_X' hi _ _))]; exact hX.X j w s hw hs⟩
    have hin : ∀ i < n, i ∈ cl.leftVars → InSort c (cl.vars.getD i 0) (e'.evalEvar (tbl.ev (canonKey c cl.vars i))) :=
      fun i hi hil => (inhOf_sort hn (hnum i hi) KoreAML.val0 _).mp
        (hguard _ (List.mem_map_of_mem (List.mem_map_of_mem (hml i hi hil))) _
          (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl))
    let σ := substE c tbl cl.vars e'
    have hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e' m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v := by
      rintro i ⟨hi, hil⟩ m
      obtain ⟨v, he, -⟩ := inSort_val (hin i hi hil)
      rw [var_read, substE_lookup hi]
      show m = e'.evalEvar (tbl.ev (canonKey c cl.vars i)) ↔ _
      rw [he]
      simp [toVal]
    have hσ : c.WellSortedAt cl.vars cl.leftVars σ := fun i hil s hs' => by
      have hi : i < n := (List.getElem?_eq_some_iff.mp hs').1
      obtain ⟨v, he, hsv⟩ := inSort_val (hin i hi hil)
      refine ⟨v, by rw [substE_lookup hi, he]; rfl, ?_⟩
      rwa [List.getD_eq_getElem?_getD, hs', Option.getD_some] at hsv
    obtain ⟨-, hq, hpv⟩ := (premise_iffCl h (R_read e') (by rw [he'R]; exact hRs) hvar hreqOK hpatOK hlen hX' a).mp
      hbody
    exact ⟨σ, hσ, hpv, hq⟩
  · rintro ⟨σ, hσ, hpv, hq⟩
    have hσv : ∀ i < n, i ∈ cl.leftVars → ∃ w, σ.lookup i = some w ∧ c.sortOf w = some (cl.vars.getD i 0) :=
      fun i hi hil => hσ i hil _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    let f : Nat → Elem := fun j => .val ((σ.lookup j).getD default)
    let e' := setV c tbl cl.vars cl.leftVars f e
    have hoff : ∀ k, k ∈ tbl → (∀ i < n, k ≠ canonKey c cl.vars i) → e'.evalEvar (tbl.ev k) = e.evalEvar (tbl.ev k) :=
      fun k hk hne => by
        show (if h : _ then _ else _) = _
        rw [dif_neg]
        rintro ⟨i, hi, hil, he⟩
        exact hne i hi (ev_inj hk (hkeys i hi hil) he)
    have hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e' m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v := by
      rintro i ⟨hi, hil⟩ m
      rw [var_read]
      show m = (setV c tbl cl.vars cl.leftVars f e).evalEvar (tbl.ev (canonKey c cl.vars i)) ↔ _
      rw [setV_on hkeys hi hil]
      obtain ⟨w, hw, -⟩ := hσv i hi hil
      simp [f, hw]
    have he'R : e'.evalEvar (tbl.ev (.sortVar "R")) = e.evalEvar (tbl.ev (.sortVar "R")) := hoff _ hRkey hRne
    have hX' : ArgsAt c tbl e' fn.args ws := ⟨hX.sorts, hX.num, fun j w s hw hs => by
      rw [hoff _ (hXkeys j s hs) (fun i hi => canonKey_ne_X' hi _ _)]; exact hX.X j w s hw hs⟩
    refine existsAll_intro _ e e' _ hnd hsrt (fun z hz => ?_) rfl (fun b hb k hk => ?_) ?_
    · show (if h : _ then _ else _) = _
      rw [dif_neg]
      rintro ⟨i, hi, hil, rfl⟩
      exact hz _ (List.mem_map_of_mem (List.mem_map_of_mem (hml i hi hil))) rfl
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
      obtain ⟨i, hil, rfl⟩ := List.mem_map.mp hv
      have hs' : ((canonVars c cl.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (cl.vars.getD i 0)) := by
        rw [canonVars_getD c (hl i hil)]; rfl
      change ((canonVars c cl.vars).getD i default).kore.sort = KoreAML.srt k at hk
      rw [hs'] at hk
      rw [← srt_inj hk]
      show InS (stdI_T c T) _ ((setV c tbl cl.vars cl.leftVars f e).evalEvar (tbl.ev (canonKey c cl.vars i)))
      rw [setV_on hkeys (hl i hil) (hlm i hil)]
      obtain ⟨w, hw, hws⟩ := hσv i (hl i hil) (hlm i hil)
      show InS (stdI_T c T) _ (Elem.val ((σ.lookup i).getD default))
      rw [hw, Option.getD_some]
      exact (inhOf_sort hn (hnum i (hl i hil)) KoreAML.val0 _).mpr hws
    · exact (premise_iffCl h (R_read e') (by rw [he'R]; exact hRs) hvar hreqOK hpatOK hlen hX' a).mpr
        ⟨by rw [he'R]; exact ha, hq, hpv⟩

end

-- ModelFnsCl.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns)
include h hfn
variable {T : GroundTerm → GroundTerm → Prop}

/-- **The equation of a clause with no clause of a smaller priority holds.** -/
theorem sat_clauseEq {cl : Clause} (hcl : cl ∈ fn.clauses) (hlow : lowerClauses fn cl = []) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv], .implies KoreAML.R
      (premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
        (Term.koreList c (canonVars c cl.vars) cl.pats))
      (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars))))), []⟩ : Kore.Axiom)⟩).pat := by
  obtain ⟨hpats, hocc, L, hL, hreqs, hrhs, hens⟩ := clause_factsCl h hfn hcl
  have hlen : cl.pats.length = fn.args.length := sortsOfTerms_length hpats
  refine sat_eqnCl h hfn (clause_vars_num h hfn hcl) (termOK_of_sorted h hL hrhs)
    (fun t ht => termOK_of_sorted h hL (hens t ht))
    (clause_keys_freeCl hlen hocc fun _ hk => hk) (clause_keys_varsCl hlen hocc fun _ hk => hk)
    fun tbl e ws a hEq _ ha hprem => ?_
  obtain ⟨hσ, hvar⟩ := substE_ok (T := T) hEq.vin
  obtain ⟨-, hq, hpv⟩ := (premise_iff h (R_read e) hEq.Rs hvar (fun t ht => termOK_of_sorted h hL (hreqs t ht))
    (patOKs_of_sorted h hpats) hlen hEq.args a).mp hprem
  refine eval_of_decides h hfn hcl hEq.args.sorts ⟨⟨hσ, hpv, hq⟩, fun cl' hcl' hna hlt => ?_⟩
  have : cl' ∈ lowerClauses fn cl := by simp [lowerClauses, hcl', hna, hlt]
  rw [hlow] at this
  exact absurd this List.not_mem_nil

end

-- ModelFnsCl.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns)
include h hfn
variable {T : GroundTerm → GroundTerm → Prop}

/-- Where a negated disjunction of exclusions holds, none of their clauses matches with a `true`
`requires` under a substitution well sorted on its patterns' and conditions' variables. -/
theorem fails_of_not_exclCl {cls : List Clause} (hcls : ∀ cl ∈ cls, cl ∈ fn.clauses)
    {tbl : KoreAML.VarTable} {e : Valuation Elem} {ws : List GroundTerm} (hEqR : KoreAML.VarKey.sortVar "R" ∈ tbl)
    (hXk : ∀ (j : Nat) (s : String), (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl)
    (hRs : KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R")))) (hX : ArgsAt c tbl e fn.args ws)
    (hkeys : ∀ cl ∈ cls, ∀ i < cl.vars.length, i ∈ cl.leftVars → canonKey c cl.vars i ∈ tbl) {a : Elem}
    (hnot : (KoreAML.tr ⟨tbl, []⟩ (.not KoreAML.R (KoreAML.anyOf
      (cls.map fun cl => exclusion c fn cl (canonClausePres cl))))).interpret (stdI_T c T) e a) :
    KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a ∧ ∀ cl ∈ cls, ∀ σ,
      ¬ (c.WellSortedAt cl.vars cl.leftVars σ ∧ PatVals c σ cl.pats ws ∧
        ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) := by
  rw [KoreAML.tr, KoreAML.interp_sNot, anyOf_eq, anyOfC_iff (R_read e) isFree_R, KoreAML.interp_inhOf_of (R_read e)]
    at hnot
  obtain ⟨hn1, hi⟩ := hnot
  refine ⟨hi, fun cl hcl σ hap => hn1 ⟨hi, _, List.mem_map.mpr ⟨cl, hcl, rfl⟩, ?_⟩⟩
  exact (exclusion_iffCl h hfn (hcls cl hcl) (hkeys cl hcl) hEqR hXk hRs hX hi).mpr ⟨σ, hap⟩

end

-- ModelFnsCl.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns)
include h hfn
variable {T : GroundTerm → GroundTerm → Prop}

/-- **The equation of a clause with clauses of a smaller priority holds**: where they all fail and
it applies. -/
theorem sat_competingEq {cl : Clause} (hcl : cl ∈ fn.clauses) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv], .implies KoreAML.R
      (competingPremise (fn.args.map c.sortName)
        ((lowerClauses fn cl).map fun cl' => exclusion c fn cl' (canonClausePres cl'))
        (cl.req.map (Term.kore c (canonVars c cl.vars))) (Term.koreList c (canonVars c cl.vars) cl.pats))
      (fnConcl c fn (Term.kore c (canonVars c cl.vars) cl.rhs)
        (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars))))), []⟩ : Kore.Axiom)⟩).pat := by
  have hdl : ∀ cl' ∈ lowerClauses fn cl, cl' ∈ fn.clauses := fun cl' h' => (List.mem_filter.mp h').1
  obtain ⟨hpats, hocc, L, hL, hreqs, hrhs, hens⟩ := clause_factsCl h hfn hcl
  have hlen : cl.pats.length = fn.args.length := sortsOfTerms_length hpats
  refine sat_eqnCl h hfn (clause_vars_num h hfn hcl) (termOK_of_sorted h hL hrhs)
    (fun t ht => termOK_of_sorted h hL (hens t ht))
    (clause_keys_freeCl hlen hocc fun _ hk => ?_) (clause_keys_varsCl hlen hocc fun _ hk => ?_)
    fun tbl e ws a hEq hvT ha hprem => ?_
  · unfold competingPremise
    simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append]
    exact Or.inr hk
  · unfold competingPremise
    exact varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hk
  · obtain ⟨hσ, hvar⟩ := substE_ok (T := T) hEq.vin
    unfold competingPremise at hprem
    rw [tr_and2, KoreAML.interp_sAnd] at hprem
    obtain ⟨hnot, hp⟩ := hprem
    obtain ⟨-, hfails⟩ := fails_of_not_exclCl (T := T) h hfn hdl hEq.R hEq.Xk hEq.Rs hEq.args
      (fun cl' hcl' i hi hil => hvT _ (by
        unfold competingPremise
        exact varsOf_and_mem (List.mem_cons_self ..) (varsOf_not_exclCl hcl' hi hil))) hnot
    obtain ⟨-, hq, hpv⟩ := (premise_iff h (R_read e) hEq.Rs hvar (fun t ht => termOK_of_sorted h hL (hreqs t ht))
      (patOKs_of_sorted h hpats) hlen hEq.args a).mp hp
    exact eval_of_decides h hfn hcl hEq.args.sorts ⟨⟨hσ, hpv, hq⟩, fun cl' hcl' hna hlt σ' hw hp' hq' =>
      hfails cl' (List.mem_filter.mpr ⟨hcl', by simp [hna, hlt]⟩) σ' ⟨hw, hp', hq'⟩⟩

end

-- ModelFnsCl.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

theorem sat_kernelItem_of {s : Kore.Sentence} {it : KoreAML.Item}
    (hit : (match s with
      | .axiom a => some (KoreAML.trAxiom [] [] ⟨0, "kernel", a⟩)
      | _ => none) = some it) {a : Kore.Axiom} (hs : s = .axiom a)
    (ha : stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", a⟩).pat) : stdI_T c T ⊧ᴵ it.pat := by
  subst hs
  cases hit
  exact ha

end

-- ModelFnsCl.lean
section
set_option autoImplicit false
open ML
variable {c : Semantics}
variable {T : GroundTerm → GroundTerm → Prop}

/-- **`SatFnsGoal`**: the value model satisfies the functions' equations. -/
theorem satFnsGoal (h : HypModelCore c) : (stdI_T c T ⊧ᴵP ΓFns c) := by
  refine sat_itemsPremises c fun it hit => ?_
  obtain ⟨fn, hfn, hit⟩ := List.mem_flatMap.mp hit
  obtain ⟨s, hs, hit⟩ := List.mem_filterMap.mp hit
  unfold fnEquationsK at hs
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hs
  by_cases hlow : (lowerClauses fn cl).isEmpty = true
  · rw [show prioEquation c fn cl = clauseEquation c fn cl from if_pos hlow] at hit
    exact sat_kernelItem_of hit rfl (sat_clauseEq h hfn hcl (List.isEmpty_iff.mp hlow))
  · rw [show prioEquation c fn cl = competingEquation c fn (lowerClauses fn cl) cl from if_neg hlow] at hit
    exact sat_kernelItem_of hit rfl (sat_competingEq h hfn hcl)

end

-- Confined.lean
section
set_option autoImplicit false
open ML Faithful
variable {T : GroundTerm → GroundTerm → Prop}

open Faithful.Model in
/-- **The value model satisfies the closure axiom** where Bool holds only literals: its elements of
Bool are the values of Bool, `true` and `false` (`boolValues`). -/
theorem boolClosed_model {c : Semantics} (h : HypModelCore c) (hc : c.coreOK = true)
    (hl : c.litSort Srt.bool = true) : stdI_T c T ⊧ᴵ boolClosed c := by
  intro e m
  unfold boolClosed
  rw [KoreAML.interp_included defOK_std]
  intro a ha
  have ha' := (inhOf_sort h.namesK (bool_numbered (c := c)) e a).mp ha
  obtain ⟨v, rfl, hv⟩ := inSort_val ha'
  obtain ⟨b, rfl⟩ := boolValues hc hl hv
  have hs := den_val (T := T) h (.dv Srt.bool (.bool b)) hv e
  simp only [Pattern.interpret]
  intro hn
  cases b with
  | true => exact absurd ((hs _).mpr rfl) hn
  | false => exact (hs _).mpr rfl

end
end AtT

open ML

variable {c : Semantics}

/-- **A value denotes its own element** in the value model at any transition `T`. -/
theorem den_val_T (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop) (v : GroundTerm) {s : Srt}
    (hv : c.sortOf v = some s) (e : Valuation Elem) (m : Elem) :
    (den c v).interpret (stdI_T c T) e m ↔ m = .val v :=
  AtT.den_val (T := T) h v hv e m

/-- `•φ` in the value model at `T`: the configurations with a `T` successor in `φ`. -/
theorem sNext_iff_T (T : GroundTerm → GroundTerm → Prop) (φ : KoreAML.P) (e : Valuation Elem) (x : GroundTerm) :
    (KoreAML.sNext φ).interpret (stdI_T c T) e (.val x) ↔
      ∃ y, φ.interpret (stdI_T c T) e (.val y) ∧ StepE_T c T (.val x) (.val y) :=
  AtT.sNext_iff φ e x

/-- **The value model at any transition `T` satisfies the parts of `Γ` and `Γcl` that do not read
the step**: the signature, the constructors, the domains, the collections, the functions, the
interpretation's values at silent points, and Bool's closure where Bool holds only its literals. -/
theorem model_parts_T (h : HypModelCore c) (hc : c.coreOK = true) (T : GroundTerm → GroundTerm → Prop) :
    (stdI_T c T ⊧ᴵP ΓSig c) ∧ (stdI_T c T ⊧ᴵP ΓCons c) ∧ (stdI_T c T ⊧ᴵP ΓDomains c) ∧
    (stdI_T c T ⊧ᴵP ΓColls c) ∧ (stdI_T c T ⊧ᴵP ΓFns c) ∧ (stdI_T c T ⊧ᴵP ΓFallback c) ∧
    (c.litSort Srt.bool = true → (stdI_T c T ⊧ᴵ boolClosed c)) :=
  ⟨AtT.satSigGoal h, AtT.satConsGoal h, AtT.satDomainsGoal h, AtT.satCollsGoal h, AtT.satFnsGoal h,
   AtT.satFallbackGoal h, AtT.boolClosed_model h hc⟩

end Model

end Faithful

end KCore
