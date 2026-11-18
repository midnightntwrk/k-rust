/-
  KCore. The laws of the overloading symbols' normal forms where an overload may be a function.

  `norm` leaves an application alone where the first overload covering its arguments is a
  function's: what the application denotes there is the function's value, which no function on
  values gives. The laws of OvlLaws.lean therefore hold of `norm f v̄` at the arguments `v̄` that no
  function overload of `f` covers (`fnCover f v̄ = none`), and they are proved here from what is
  stated of the declarations in `OvlFnFacts`, which excludes no function among the overloads:

  - the overloads are of the symbol's arity with sorts at most its own, each of a smaller rank,
    and any two of them agree (`ovlCoherent`);
  - an overloading symbol lists the functions that the overloading symbols it overloads list
    (`closed`).

  From these:

  - the function overload covering an argument list is the one function overload that does
    (`fnCover_of_covers_ovlF`): two function overloads cover no common argument list;
  - the function overload covering lifted arguments of an overloaded symbol `g` is the one covering
    them at `g` (`fnCover_liftAll_ovlF`), so arguments no function overload covers stay so along an
    overload step (`fnCover_strip_none_ovlF`);
  - at arguments no function overload covers: a normal form is a value (`sortOf_norm_ovlF`), every
    covering overload gives it (`norm_coherent_ovlF`, `norm_ovlEq_ovlF`), it is the lift of a raw
    application (`norm_decomp_ovlF`), `norm f` is injective (`norm_inj_ovlF`) and is the raw
    application exactly at uncovered arguments (`norm_eq_raw_iff_ovlF`).

  The order laws of the subsorts are read through `OvlHyp` (its `trans` and `irrefl`); nothing here
  reads its `ok`.
-/
import KcoreSpec.OvlLaws

set_option autoImplicit false

namespace KCore

namespace OvlLaws

variable {c : Semantics}

/-- **What the laws read of the overloading symbols' declarations**, a function among the overloads
or not: each is an overloading symbol of no other kind; each symbol it overloads has its arity,
argument and result sorts at most its own (`ovlPairOK`) and a smaller rank; any two overloads
agree (`ovlCoherent`); and it lists each function that an overloading symbol it overloads lists. -/
structure OvlFnFacts (c : Semantics) : Prop where
  isOvl : ∀ o ∈ c.ovls, c.isOvl o.sig.name = true
  over : ∀ o ∈ c.ovls, ∀ kg ∈ c.ovlOver o,
    c.ovlPairOK o kg = true ∧ ovlRank c kg.name < ovlRank c o.sig.name
  coh : ∀ o ∈ c.ovls, ∀ k1 ∈ c.ovlOver o, ∀ k2 ∈ c.ovlOver o, c.ovlCoherent k1 k2 = true
  closed : ∀ o ∈ c.ovls, ∀ kg ∈ c.ovlOver o, ∀ o', c.lookupOvl kg.name = some o' →
    ∀ kg' ∈ c.ovlOver o', c.ovlByFn kg' = true → kg' ∈ c.ovlOver o

/-- The facts hold where each overloaded symbol is a constructor or an overloading symbol
(`overloadsOK`). -/
theorem OvlHyp.fnFacts (H : OvlHyp c) : OvlFnFacts c where
  isOvl := fun o ho => by
    have := (ovl_facts H (lookupOvl_of_mem H ho)).2.1
    exact this
  over := fun o ho kg hkg => by
    have hlo := lookupOvl_of_mem H ho
    obtain ⟨-, -, -, -, hpos, hover, -⟩ := ovl_facts H hlo
    obtain ⟨-, hp, hr⟩ := hover kg hkg
    refine ⟨hp, ?_⟩
    rcases hr with h | h
    · rw [rank_of_none h]; exact hpos
    · exact h
  coh := fun o ho => (ovl_facts H (lookupOvl_of_mem H ho)).2.2.2.2.2.2
  closed := fun o ho kg hkg o' ho' kg' hkg' hb => by
    rw [ovlByFn_of_known (ovlOver_known H ho' hkg')] at hb
    cases hb

/-! ## The declarations -/

theorem mem_of_lookupOvl {f : Sym} {o : OvlSig} (h : c.lookupOvl f = some o) : o ∈ c.ovls := by
  obtain ⟨-, i, hi, he, -⟩ := lookupOvl_spec h
  exact he ▸ List.getElem_mem hi

/-- An overloading symbol listed once is the one its name finds. -/
theorem lookupOvl_of_nodup (hnd : (c.ovls.map (·.sig.name)).Nodup) {o : OvlSig} (ho : o ∈ c.ovls) :
    c.lookupOvl o.sig.name = some o := by
  unfold Semantics.lookupOvl
  cases hf : c.ovls.find? (·.sig.name == o.sig.name) with
  | none => exact absurd (List.find?_eq_none.mp hf o ho) (by simp)
  | some o' =>
    have hm := List.mem_of_find?_eq_some hf
    have hn : o'.sig.name = o.sig.name := by simpa using List.find?_some hf
    rw [Faithful.Model.inj_of_nodup_map hnd o' hm o ho hn]

/-- An overloaded symbol whose signature is no function's has it among the constructors and the
overloading symbols. -/
theorem known_of_not_byFn {o : OvlSig} {kg : CtorSig} (hkg : kg ∈ c.ovlOver o) (hb : c.ovlByFn kg = false) :
    KnownSig c kg := by
  obtain ⟨g, -, hgk⟩ := List.mem_filterMap.mp hkg
  have hkn : kg.name = g := by
    rw [lookupSig_eq] at hgk
    simpa using List.find?_some hgk
  have hs : (lookupSig (c.ctorSigs ++ c.ovlSigs) kg.name).isSome = true := by
    simp only [Semantics.ovlByFn, Option.isNone_eq_false_iff] at hb
    exact hb
  unfold KnownSig
  rw [← lookupSig_append_of_isSome hs, hkn]
  exact hgk

/-- A function's signature among the overloads is no overloading symbol's. -/
theorem lookupOvl_none_of_byFn {kg : CtorSig} (hb : c.ovlByFn kg = true) : c.lookupOvl kg.name = none := by
  simp only [Semantics.ovlByFn, Option.isNone_iff_eq_none] at hb
  rw [lookupSig_eq, List.find?_append] at hb
  cases hc : c.ctorSigs.find? (·.name == kg.name) with
  | some k => rw [hc] at hb; cases hb
  | none =>
    rw [hc, Option.none_or, find_ovlSigs] at hb
    cases ho : c.lookupOvl kg.name with
    | none => rfl
    | some o => rw [ho] at hb; cases hb

/-- A function's signature has nothing below it along the overloads but itself. -/
theorem ovlDown_of_byFn {kg : CtorSig} (hb : c.ovlByFn kg = true) : c.ovlDown kg = [kg] := by
  simp [Semantics.ovlDown, lookupOvl_none_of_byFn hb]

/-- A function's signature among the overloads is that of the function its name finds. -/
theorem byFn_fn {o : OvlSig} {kg : CtorSig} (hkg : kg ∈ c.ovlOver o) (hb : c.ovlByFn kg = true) :
    ∃ fn, fn ∈ c.fns ∧ c.lookupFn kg.name = some fn ∧ kg = ⟨fn.label, fn.args, fn.result⟩ := by
  obtain ⟨g, -, hgk⟩ := List.mem_filterMap.mp hkg
  have hkn : kg.name = g := by
    rw [lookupSig_eq] at hgk
    simpa using List.find?_some hgk
  simp only [Semantics.ovlByFn, Option.isNone_iff_eq_none] at hb
  rw [lookupSig_eq] at hb
  rw [lookupSig_eq, List.find?_append, ← hkn, hb, Option.none_or, List.find?_map] at hgk
  obtain ⟨fn, hfn, hsig⟩ := Option.map_eq_some_iff.mp hgk
  have hfn' : c.fns.find? (fun fn => fn.label == kg.name) = some fn := hfn
  refine ⟨fn, List.mem_of_find?_eq_some hfn', ?_, hsig.symm⟩
  rw [c.lookupFn_eq, Semantics.allFns, List.find?_append, hfn']
  rfl

/-- An overloading symbol with a function's signature among its overloads is function-overloaded. -/
theorem fnOvlSyms_of_byFn {o : OvlSig} (ho : o ∈ c.ovls) {kg : CtorSig} (hkg : kg ∈ c.ovlOver o)
    (hb : c.ovlByFn kg = true) : o.sig.name ∈ c.fnOvlSyms := by
  obtain ⟨fn, hfn, -, hsig⟩ := byFn_fn hkg hb
  unfold Semantics.fnOvlSyms
  refine List.mem_map.mpr ⟨o, List.mem_filter.mpr ⟨ho, List.any_eq_true.mpr ⟨kg.name, mem_ovlOver hkg, ?_⟩⟩, rfl⟩
  exact List.any_eq_true.mpr ⟨fn, hfn, by rw [hsig]; simp⟩

/-- No function overload covers anything at a symbol that is not function-overloaded. -/
theorem fnCover_none_of_not_fnOvl {f : Sym} (h : f ∉ c.fnOvlSyms) (vs : List GroundTerm) :
    c.fnCover f vs = none := by
  rw [c.fnCover_eq_none_iff]
  intro o ho kg hkg hb
  exact absurd ((lookupOvl_spec ho).1 ▸ fnOvlSyms_of_byFn (mem_of_lookupOvl ho) hkg hb) h

/-- Arguments that no overload covers are covered by no function overload. -/
theorem fnCover_none_of_uncovered {f : Sym} {vs : List GroundTerm} (hu : c.uncovered f vs = true) :
    c.fnCover f vs = none := by
  rw [Semantics.fnCover_eq_none_iff]
  intro o ho kg hkg _
  simp only [Semantics.uncovered, ho, List.all_eq_true, Bool.not_eq_true'] at hu
  exact hu kg hkg

/-- The function overload covering the arguments is among the overloads, a function's, and covers
them. -/
theorem fnCover_some_parts {f : Sym} {vs : List GroundTerm} {kg : CtorSig} (h : c.fnCover f vs = some kg) :
    ∃ o, c.lookupOvl f = some o ∧ kg ∈ c.ovlOver o ∧ c.ovlByFn kg = true ∧ c.ovlCovers o.sig kg vs = true := by
  unfold Semantics.fnCover at h
  cases ho : c.lookupOvl f with
  | none => rw [ho] at h; cases h
  | some o =>
    rw [ho] at h
    have hm := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [Bool.and_eq_true] at hp
    exact ⟨o, rfl, hm, hp.1, hp.2⟩

/-- Where no function overload covers the arguments, an overload covering them is no function's. -/
theorem not_byFn_of_fnCover_none {f : Sym} {o : OvlSig} {vs : List GroundTerm} {kg : CtorSig}
    (hnf : c.fnCover f vs = none) (ho : c.lookupOvl f = some o) (hkg : kg ∈ c.ovlOver o)
    (hc : c.ovlCovers o.sig kg vs = true) : c.ovlByFn kg = false := by
  cases hb : c.ovlByFn kg with
  | false => rfl
  | true =>
    have := c.fnCover_eq_none_iff.mp hnf o ho kg hkg hb
    rw [hc] at this; cases this

section
variable (F : OvlFnFacts c)
include F

/-- A known signature is a constructor's, which is no overloading symbol, or an overloading
symbol's. -/
theorem knownSig_cases_ovlF {k : CtorSig} (hk : KnownSig c k) :
    (lookupSig c.ctorSigs k.name = some k ∧ c.lookupOvl k.name = none) ∨
      (lookupSig c.ctorSigs k.name = none ∧ ∃ o, c.lookupOvl k.name = some o ∧ o.sig = k) := by
  unfold KnownSig at hk
  rw [lookupSig_eq, List.find?_append] at hk
  cases hc : c.ctorSigs.find? (·.name == k.name) with
  | some k' =>
    rw [hc, Option.some_or] at hk
    cases hk
    refine .inl ⟨by rw [lookupSig_eq, hc], ?_⟩
    cases ho : c.lookupOvl k.name with
    | none => rfl
    | some o =>
      have hio := F.isOvl o (mem_of_lookupOvl ho)
      rw [(lookupOvl_spec ho).1] at hio
      have := (c.isOvl_parts hio).1
      simp [Semantics.isCtor, lookupSig_eq, hc] at this
  | none =>
    rw [hc, Option.none_or, find_ovlSigs] at hk
    cases ho : c.lookupOvl k.name with
    | none => rw [ho] at hk; cases hk
    | some o =>
      rw [ho] at hk; cases hk
      exact .inr ⟨by rw [lookupSig_eq, hc], o, rfl, rfl⟩

/-- What the facts give of an overloading symbol's declaration. -/
theorem ovl_facts_ovlF {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) :
    o ∈ c.ovls ∧ o.sig.name = f ∧ c.isOvl f = true ∧ lookupSig c.ctorSigs f = none ∧ KnownSig c o.sig ∧
      0 < ovlRank c f := by
  obtain ⟨hn, i, hi, he, hr⟩ := lookupOvl_spec ho
  have hmem := mem_of_lookupOvl ho
  have hio := F.isOvl o hmem
  rw [hn] at hio
  have hct : lookupSig c.ctorSigs f = none := by
    have := (c.isOvl_parts hio).1
    simpa [Semantics.isCtor] using this
  have hks : KnownSig c o.sig := by
    unfold KnownSig
    rw [hn, lookupSig_eq, List.find?_append, ← lookupSig_eq, hct, Option.none_or, find_ovlSigs, ho]
    rfl
  exact ⟨hmem, hn, hio, hct, hks, by omega⟩

/-- An overload of `f`: well formed against `f`, and of a smaller rank. -/
theorem over_ovlF {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {kg : CtorSig} (hkg : kg ∈ c.ovlOver o) :
    kg.args.length = o.sig.args.length ∧ (kg.args.zip o.sig.args).all (fun (A, B) => c.le A B) = true ∧
      c.le kg.result o.sig.result = true ∧ ovlRank c kg.name < ovlRank c f := by
  obtain ⟨hp, hr⟩ := F.over o (mem_of_lookupOvl ho) kg hkg
  obtain ⟨hl, hle, hres⟩ := pairOK_parts hp
  rw [(lookupOvl_spec ho).1] at hr
  exact ⟨hl, hle, hres, hr⟩

/-- The overloading symbol a known overload of `f` is, where it is one. -/
theorem over_sig_ovlF {o ok : OvlSig} {kg : CtorSig} (hkg : kg ∈ c.ovlOver o)
    (hok : c.lookupOvl kg.name = some ok) : ok.sig = kg := by
  have hb : c.ovlByFn kg = false := by
    cases hb : c.ovlByFn kg with
    | false => rfl
    | true => rw [lookupOvl_none_of_byFn hb] at hok; cases hok
  rcases knownSig_cases_ovlF F (known_of_not_byFn hkg hb) with ⟨-, hn⟩ | ⟨-, o', ho', hos⟩
  · rw [hn] at hok; cases hok
  · rw [hok] at ho'; cases ho'; exact hos

/-- `normN` is stable from the symbol's rank on. -/
theorem normN_stable_ovlF : ∀ n f, ovlRank c f ≤ n → ∀ m, n ≤ m → ∀ vs, c.normN m f vs = c.normN n f vs
  | 0, f, hr, m, _, vs => by
    have hn := lookupOvl_none_of_rank (c := c) (f := f) (by omega)
    rw [normN_none hn, normN_none hn]
  | n + 1, f, hr, m, hm, vs => by
    cases ho : c.lookupOvl f with
    | none => rw [normN_none ho, normN_none ho]
    | some o =>
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      cases hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) with
      | none => simp only [Semantics.normN, ho, hf]
      | some kg =>
        cases hb : c.ovlByFn kg with
        | true => simp only [Semantics.normN, ho, hf, hb, ↓reduceIte]
        | false =>
          obtain ⟨-, -, -, hr'⟩ := over_ovlF F ho (List.mem_of_find?_eq_some hf)
          simp only [Semantics.normN, ho, hf, hb, Bool.false_eq_true, ↓reduceIte]
          rw [normN_stable_ovlF n kg.name (by omega) m (by omega)]

/-- **One overload step**: where the first overload covering the arguments is that of kg, no
function, f's normal form is kg's at the stripped arguments, lifted. -/
theorem norm_find_some_ovlF {f : Sym} {o : OvlSig} {vs : List GroundTerm} {kg : CtorSig}
    (ho : c.lookupOvl f = some o)
    (hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) = some kg) (hb : c.ovlByFn kg = false) :
    c.norm f vs = lift kg.result o.sig.result (c.norm kg.name (stripAll kg.args o.sig.args vs)) := by
  have hr := ovlRank_le (c := c) kg.name
  have e1 : ∀ xs, c.normN c.ovls.length kg.name xs = c.norm kg.name xs := by
    intro xs
    unfold Semantics.norm
    rw [normN_stable_ovlF F _ _ (Nat.le_refl _) c.ovls.length hr,
      normN_stable_ovlF F _ _ (Nat.le_refl _) (c.ovls.length + 1) (by omega)]
  unfold Semantics.norm
  simp only [Semantics.normN, ho, hf, hb, Bool.false_eq_true, ↓reduceIte]
  rw [e1]
  rfl

end

/-! ## Covering along an overload step -/

/-- A value of B lying in K, whose strip to K lies in A ≤ K, lies in A. -/
theorem lies_unstrip {A K B : Srt} {v : GroundTerm} (hv : c.sortOf v = some B)
    (hK : c.lies K B v = true) (hA : c.lies A K (strip K B v) = true) : c.lies A B v = true := by
  by_cases hKB : K = B
  · subst hKB; rw [strip_self] at hA; exact hA
  by_cases hAK : A = K
  · subst hAK; exact hK
  cases v with
  | inj C B' w =>
    obtain ⟨-, hw, -, rfl⟩ := sortOf_inj_iff.mp hv
    by_cases hCK : C = K
    · subst hCK
      simp only [strip, beq_iff_eq, hKB, ite_false, ite_true] at hA
      cases w with
      | inj => simp [GroundTerm.isInj] at hw
      | _ => simp [Semantics.lies, hAK] at hA
    · simp only [strip, beq_iff_eq, hKB, hCK, ite_false, Semantics.lies, beq_false_of_ne hAK,
        Bool.false_or] at hA
      simp [Semantics.lies, hA]
  | _ => simp [Semantics.lies, hKB] at hK

theorem lies_unstripAll {as ks bs : List Srt} {vs : List GroundTerm}
    (hl1 : as.length = ks.length) (hl2 : ks.length = bs.length) (hv : c.sortsOf vs = some bs)
    (hK : ((ks.zip bs).zip vs).all (fun ((A, B), v) => c.lies A B v) = true)
    (hA : ((as.zip ks).zip (stripAll ks bs vs)).all (fun ((A, B), v) => c.lies A B v) = true) :
    ((as.zip bs).zip vs).all (fun ((A, B), v) => c.lies A B v) = true := by
  obtain ⟨hvl, hvi⟩ := sortsOf_iff.mp hv
  have hKi := zip3_all_iff.mp hK
  have hAi := zip3_all_iff.mp hA
  refine zip3_all_iff.mpr fun i h1 h2 h3 => ?_
  have := hAi i h1 (by omega) (by simp [length_stripAll]; omega)
  rw [getElem_stripAll] at this
  exact lies_unstrip (hvi i h3 h2) (hKi i (by omega) h2 h3) this

section
variable (H : OvlHyp c) (F : OvlFnFacts c)
include H F

omit H in
/-- A symbol of `ovlDown k`, for an overload k of an overloading symbol: k, or one that k
overloads. -/
theorem down_parts_ovlF {o : OvlSig} {k h : CtorSig} (hk : k ∈ c.ovlOver o) (hh : h ∈ c.ovlDown k) :
    h.args.length = k.args.length ∧ (h.args.zip k.args).all (fun (A, B) => c.le A B) = true ∧
      c.le h.result k.result = true ∧
      (h = k ∨ ∃ ok, c.lookupOvl k.name = some ok ∧ ok.sig = k ∧ h ∈ c.ovlOver ok) := by
  unfold Semantics.ovlDown at hh
  rcases List.mem_cons.mp hh with rfl | hh
  · exact ⟨rfl, le_all_self _, OvlLaws.le_refl _, .inl rfl⟩
  · cases hn : c.lookupOvl k.name with
    | none => rw [hn] at hh; cases hh
    | some ok =>
      rw [hn] at hh
      have hos := over_sig_ovlF F hk hn
      obtain ⟨hl, hle, hres, -⟩ := over_ovlF F hn hh
      rw [hos] at hl hle hres
      exact ⟨hl, hle, hres, .inr ⟨ok, rfl, hos, hh⟩⟩

/-- Two overloads of one symbol that cover the same arguments have a common symbol below both,
among `ovlDown`, that covers them too (`ovlCoherent`). -/
theorem coherent_common_ovlF {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {k1 k2 : CtorSig}
    (hk1 : k1 ∈ c.ovlOver o) (hk2 : k2 ∈ c.ovlOver o) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some o.sig.args)
    (hc1 : c.ovlCovers o.sig k1 vs = true) (hc2 : c.ovlCovers o.sig k2 vs = true) :
    ∃ h, h ∈ c.ovlDown k1 ∧ h ∈ c.ovlDown k2 ∧ c.ovlCovers o.sig h vs = true := by
  have hcoh := F.coh o (mem_of_lookupOvl ho) k1 hk1 k2 hk2
  obtain ⟨hl1, hvl, hli1⟩ := covers_iff.mp hc1
  obtain ⟨hl2, -, hli2⟩ := covers_iff.mp hc2
  obtain ⟨-, hvi⟩ := sortsOf_iff.mp hvs
  have hli1 := zip3_all_iff.mp hli1
  have hli2 := zip3_all_iff.mp hli2
  have hpos : ∀ i (h1 : i < k1.args.length) (h2 : i < k2.args.length),
      ∃ C, C ∈ (k1.args[i] :: k2.args[i] :: c.subsorts.map (·.1)).filter
          (fun C => c.le C k1.args[i] && c.le C k2.args[i]) ∧
        ∀ X, c.le X (o.sig.args[i]'(by omega)) = true → c.le C X = true →
          c.lies X (o.sig.args[i]'(by omega)) (vs[i]'(by omega)) = true :=
    fun i h1 h2 => pos_lower H (hvi i (by omega) (by omega)) (hli1 i h1 (by omega) (by omega))
      (hli2 i h2 (by omega) (by omega))
  simp only [Semantics.ovlCoherent, Bool.or_eq_true] at hcoh
  rcases hcoh with hany | hall
  · exfalso
    obtain ⟨x, hmem, hemp⟩ := List.any_eq_true.mp hany
    obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hmem
    subst hie
    simp only [List.length_zip] at hi
    obtain ⟨C, hC, -⟩ := hpos i (by omega) (by omega)
    have : C ∈ ([] : List Srt) := by
      rw [← List.isEmpty_iff.mp hemp]
      simpa only [List.getElem_zip] using hC
    simp at this
  · obtain ⟨h, hmem, hb⟩ := List.any_eq_true.mp hall
    obtain ⟨hd1, hd2⟩ := List.mem_filter.mp hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    obtain ⟨hhl, hb⟩ := hb
    obtain ⟨hhl', hhle, -, -⟩ := down_parts_ovlF F hk1 hd1
    obtain ⟨-, hle1, -, -⟩ := over_ovlF F ho hk1
    have hhle := zip2_all_iff.mp hhle
    have hle1 := zip2_all_iff.mp hle1
    refine ⟨h, hd1, List.contains_iff_mem.mp hd2, covers_iff.mpr ⟨by omega, hvl,
      zip3_all_iff.mpr fun i hi1 hi2 hi3 => ?_⟩⟩
    obtain ⟨C, hC, hX⟩ := hpos i (by omega) (by omega)
    have hmem3 : ((h.args[i], k1.args[i]'(by omega)), k2.args[i]'(by omega)) ∈ (h.args.zip k1.args).zip k2.args := by
      have := List.getElem_mem (show i < ((h.args.zip k1.args).zip k2.args).length by simp; omega)
      simpa only [List.getElem_zip] using this
    have hb' := List.all_eq_true.mp hb _ hmem3
    have hCH := List.all_eq_true.mp hb' C hC
    exact hX _ (le_trans H (hhle i hi1 (by omega)) (hle1 i (by omega) hi2)) hCH

/-- **The function overload that covers the arguments is the one that does**: a function's
signature among the overloads of `f` that covers `vs` is `fnCover f vs`. Two function overloads
cover no common argument list, a function's signature having nothing below it but itself. -/
theorem fnCover_of_covers_ovlF {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {kg : CtorSig}
    (hkg : kg ∈ c.ovlOver o) (hb : c.ovlByFn kg = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some o.sig.args) (hc : c.ovlCovers o.sig kg vs = true) :
    c.fnCover f vs = some kg := by
  cases hf : c.fnCover f vs with
  | none =>
    have := c.fnCover_eq_none_iff.mp hf o ho kg hkg hb
    rw [hc] at this; cases this
  | some kg' =>
    obtain ⟨o', ho', hkg', hb', hc'⟩ := fnCover_some_parts hf
    rw [ho] at ho'; cases ho'
    obtain ⟨h, hd1, hd2, -⟩ := coherent_common_ovlF H F ho hkg' hkg hvs hc' hc
    rw [ovlDown_of_byFn hb'] at hd1
    rw [ovlDown_of_byFn hb] at hd2
    rw [← List.mem_singleton.mp hd1, List.mem_singleton.mp hd2]

/-- **The function overload covering lifted arguments** of an overloaded symbol `kg`, no function,
is the one covering them at `kg`: an overloading symbol lists the functions `kg` lists, and a
function overload of `f` that covers values of `kg`'s sorts is one of `kg`. -/
theorem fnCover_liftAll_ovlF {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {kg : CtorSig}
    (hkg : kg ∈ c.ovlOver o) (hb : c.ovlByFn kg = false) {as : List GroundTerm}
    (has : c.sortsOf as = some kg.args) :
    c.fnCover f (liftAll kg.args o.sig.args as) = c.fnCover kg.name as := by
  obtain ⟨hl, hle, -, -⟩ := over_ovlF F ho hkg
  have hal := (sortsOf_iff.mp has).1
  have hls := sortsOf_liftAll H hl has hle
  have hlies := lies_liftAll (c := c) hl has
  have hckg : c.ovlCovers o.sig kg (liftAll kg.args o.sig.args as) = true :=
    covers_iff.mpr ⟨hl, by simp [length_liftAll]; omega, hlies⟩
  cases hk : c.fnCover kg.name as with
  | none =>
    cases hf : c.fnCover f (liftAll kg.args o.sig.args as) with
    | none => rfl
    | some g =>
      exfalso
      obtain ⟨o', ho', hg, hbg, hcg⟩ := fnCover_some_parts hf
      rw [ho] at ho'; cases ho'
      obtain ⟨h, hd1, hd2, -⟩ := coherent_common_ovlF H F ho hg hkg hls hcg hckg
      rw [ovlDown_of_byFn hbg, List.mem_singleton] at hd1
      subst hd1
      obtain ⟨hlh, hleh, -, hor⟩ := down_parts_ovlF F hkg hd2
      rcases hor with rfl | ⟨ok, hok, hos, hmem⟩
      · rw [hb] at hbg; cases hbg
      · subst hos
        obtain ⟨-, -, hliesg⟩ := covers_iff.mp hcg
        have hst := lies_stripAll H hlh hl (by simp [length_liftAll]; omega) hleh hle hliesg
        rw [stripAll_liftAll H hl has] at hst
        have := c.fnCover_eq_none_iff.mp hk ok hok h hmem hbg
        rw [covers_iff.mpr ⟨hlh, hal, hst⟩] at this
        cases this
  | some g =>
    obtain ⟨ok, hok, hg, hbg, hcg⟩ := fnCover_some_parts hk
    have hos := over_sig_ovlF F hkg hok
    subst hos
    obtain ⟨hlg, hleg, -, -⟩ := over_ovlF F hok hg
    have hgo := F.closed o (mem_of_lookupOvl ho) ok.sig hkg ok hok g hg hbg
    obtain ⟨-, -, hliesg⟩ := covers_iff.mp hcg
    refine fnCover_of_covers_ovlF H F ho hgo hbg hls (covers_iff.mpr ⟨by omega, by simp [length_liftAll]; omega, ?_⟩)
    refine lies_unstripAll hlg hl hls hlies ?_
    rw [stripAll_liftAll H hl has]
    exact hliesg

/-- **Arguments no function overload covers stay so along an overload step**: stripped to the
sorts of an overload that covers them, no function overload of that symbol covers them. -/
theorem fnCover_strip_none_ovlF {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {kg : CtorSig}
    (hkg : kg ∈ c.ovlOver o) {vs : List GroundTerm} (hvs : c.sortsOf vs = some o.sig.args)
    (hc : c.ovlCovers o.sig kg vs = true) (hnf : c.fnCover f vs = none) :
    c.fnCover kg.name (stripAll kg.args o.sig.args vs) = none := by
  obtain ⟨hl, -, -, -⟩ := over_ovlF F ho hkg
  obtain ⟨-, -, hlies⟩ := covers_iff.mp hc
  rw [← fnCover_liftAll_ovlF H F ho hkg (not_byFn_of_fnCover_none hnf ho hkg hc) (sortsOf_stripAll hl hvs hlies),
    liftAll_stripAll hl hvs hlies]
  exact hnf

/-! ## Values -/

/-- **A normal form is a value** of the symbol's result sort, at arguments no function overload
covers. -/
theorem sortOf_norm_known_ovlF : ∀ n k, KnownSig c k → ovlRank c k.name ≤ n → ∀ vs,
    c.sortsOf vs = some k.args → c.fnCover k.name vs = none → c.sortOf (c.norm k.name vs) = some k.result
  | n, k, hk, hr, vs, hvs, hnf => by
    cases hn : c.lookupOvl k.name with
    | none =>
      rw [norm_none hn]
      rcases knownSig_cases_ovlF F hk with ⟨hc, -⟩ | ⟨-, o, ho, -⟩
      · exact c.sortOf_ctor_iff.mpr (.inl ⟨k, hc, hvs, rfl⟩)
      · rw [hn] at ho; cases ho
    | some o =>
      rcases knownSig_cases_ovlF F hk with ⟨-, hn'⟩ | ⟨hct, o', ho', hos⟩
      · rw [hn'] at hn; cases hn
      rw [hn] at ho'; cases ho'; subst hos
      cases hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) with
      | none =>
        rw [norm_find_none hn hf]
        exact c.sortOf_ctor_iff.mpr (.inr (.inl ⟨hct, o, hn, hvs, uncovered_of_find_none hn hf, rfl⟩))
      | some kg =>
        have hkg := List.mem_of_find?_eq_some hf
        have hcv := List.find?_some hf
        have hb := not_byFn_of_fnCover_none hnf hn hkg hcv
        rw [norm_find_some_ovlF F hn hf hb]
        obtain ⟨hl, hle, hres, hr'⟩ := over_ovlF F hn hkg
        obtain ⟨-, -, hlies⟩ := covers_iff.mp hcv
        match n with
        | 0 => omega
        | n + 1 =>
          exact sortOf_lift H (sortOf_norm_known_ovlF n kg (known_of_not_byFn hkg hb) (by omega) _
            (sortsOf_stripAll hl hvs hlies) (fnCover_strip_none_ovlF H F hn hkg hvs hcv hnf)) hres

theorem sortOf_norm_ovlF {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some o.sig.args) (hnf : c.fnCover f vs = none) :
    c.sortOf (c.norm f vs) = some o.sig.result := by
  obtain ⟨-, hn, -, -, hks, -⟩ := ovl_facts_ovlF F ho
  have := sortOf_norm_known_ovlF H F _ o.sig hks (ovlRank_le _) vs hvs (by rw [hn]; exact hnf)
  rwa [hn] at this

/-! ## Coherence -/

/-- **Coherence**: at arguments no function overload covers, every overload of f covering them
gives f's normal form, that of the overloaded symbol at the stripped arguments, lifted. -/
theorem norm_coherent_ovlF : ∀ n f o, c.lookupOvl f = some o → ovlRank c f ≤ n → ∀ vs,
    c.sortsOf vs = some o.sig.args → c.fnCover f vs = none →
    ∀ kg ∈ c.ovlOver o, c.ovlCovers o.sig kg vs = true →
    c.norm f vs = lift kg.result o.sig.result (c.norm kg.name (stripAll kg.args o.sig.args vs))
  | 0, f, o, ho, hr, _, _, _, _, _, _ => by
    obtain ⟨-, -, -, -, -, hpos⟩ := ovl_facts_ovlF F ho
    omega
  | n + 1, f, o, ho, hr, vs, hvs, hnf, kg, hkg, hcv => by
    have hvl := (sortsOf_iff.mp hvs).1
    -- the step from an overload k to a symbol h below it, both covering
    have down : ∀ k ∈ c.ovlOver o, c.ovlCovers o.sig k vs = true → ∀ h ∈ c.ovlDown k,
        c.ovlCovers o.sig h vs = true →
        lift k.result o.sig.result (c.norm k.name (stripAll k.args o.sig.args vs)) =
          lift h.result o.sig.result (c.norm h.name (stripAll h.args o.sig.args vs)) := by
      intro k hk hck h hh hch
      obtain ⟨hlk, hlek, hresk, hrk⟩ := over_ovlF F ho hk
      obtain ⟨hlh, hleh, hresh, hor⟩ := down_parts_ovlF F hk hh
      rcases hor with rfl | ⟨ok, hok, hos, hmem⟩
      · rfl
      subst hos
      obtain ⟨-, -, hlies⟩ := covers_iff.mp hck
      obtain ⟨-, -, hliesh⟩ := covers_iff.mp hch
      have hcov' : c.ovlCovers ok.sig h (stripAll ok.sig.args o.sig.args vs) = true :=
        covers_iff.mpr ⟨hlh, by simp [length_stripAll]; omega,
          lies_stripAll H hlh hlk (by omega) hleh hlek hliesh⟩
      rw [norm_coherent_ovlF n ok.sig.name ok hok (by omega) _ (sortsOf_stripAll hlk hvs hlies)
          (fnCover_strip_none_ovlF H F ho hk hvs hck hnf) h hmem hcov',
        lift_trans H hresh hresk, stripAll_trans H hlh hlk (by omega) hleh hlek hliesh]
    cases hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) with
    | none => exact absurd hcv (by simpa using List.find?_eq_none.mp hf kg hkg)
    | some k1 =>
      have hk1 := List.mem_of_find?_eq_some hf
      have hc1 := List.find?_some hf
      rw [norm_find_some_ovlF F ho hf (not_byFn_of_fnCover_none hnf ho hk1 hc1)]
      obtain ⟨h, hd1, hd2, hch⟩ := coherent_common_ovlF H F ho hk1 hkg hvs hc1 hcv
      rw [down k1 hk1 hc1 h hd1 hch, down kg hkg hcv h hd2 hch]

/-- **The overload equations**: for each symbol g that f overloads, `f(lift ā) = lift (g(ā))` at
arguments ā of g's sorts whose lifts no function overload of f covers. -/
theorem norm_ovlEq_ovlF {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {kg : CtorSig}
    (hkg : kg ∈ c.ovlOver o) {as : List GroundTerm} (has : c.sortsOf as = some kg.args)
    (hnf : c.fnCover f (liftAll kg.args o.sig.args as) = none) :
    c.norm f (liftAll kg.args o.sig.args as) = lift kg.result o.sig.result (c.norm kg.name as) := by
  obtain ⟨hl, hle, -, -⟩ := over_ovlF F ho hkg
  have hal := (sortsOf_iff.mp has).1
  rw [norm_coherent_ovlF H F _ f o ho (ovlRank_le f) _ (sortsOf_liftAll H hl has hle) hnf kg hkg
      (covers_iff.mpr ⟨hl, by simp [length_liftAll]; omega, lies_liftAll hl has⟩),
    stripAll_liftAll H hl has]

/-! ## Normal forms -/

/-- **A normal form is the lift of a raw application** `h(ū)`, at arguments no function overload
covers: of f itself at f's arguments where they are uncovered, otherwise of a symbol of smaller
rank; ū lifts to f's arguments. -/
theorem norm_decomp_ovlF : ∀ n k, KnownSig c k → ovlRank c k.name ≤ n → ∀ vs, c.sortsOf vs = some k.args →
    c.fnCover k.name vs = none →
    ∃ h us, KnownSig c h ∧ h.args.length = k.args.length ∧
      (h.args.zip k.args).all (fun (A, B) => c.le A B) = true ∧ c.le h.result k.result = true ∧
      c.norm k.name vs = lift h.result k.result (.ctor h.name us) ∧ vs = liftAll h.args k.args us ∧
      us.length = h.args.length ∧
      ((c.uncovered k.name vs = true ∧ h = k ∧ us = vs) ∨
        (c.uncovered k.name vs = false ∧ ovlRank c h.name < ovlRank c k.name)) ∧
      ∀ m, ovlRank c k.name ≤ m → h.name ∈ c.ovlReach m k.name
  | n, k, hk, hr, vs, hvs, hnf => by
    have hvl := (sortsOf_iff.mp hvs).1
    have raw : c.norm k.name vs = .ctor k.name vs → c.uncovered k.name vs = true →
        ∃ h us, KnownSig c h ∧ h.args.length = k.args.length ∧
          (h.args.zip k.args).all (fun (A, B) => c.le A B) = true ∧ c.le h.result k.result = true ∧
          c.norm k.name vs = lift h.result k.result (.ctor h.name us) ∧ vs = liftAll h.args k.args us ∧
          us.length = h.args.length ∧
          ((c.uncovered k.name vs = true ∧ h = k ∧ us = vs) ∨
            (c.uncovered k.name vs = false ∧ ovlRank c h.name < ovlRank c k.name)) ∧
          ∀ m, ovlRank c k.name ≤ m → h.name ∈ c.ovlReach m k.name :=
      fun he hu => ⟨k, vs, hk, rfl, le_all_self _, OvlLaws.le_refl _, by rw [he, lift_self],
        (liftAll_self _ hvl).symm, hvl, .inl ⟨hu, rfl, rfl⟩, fun m _ => ovlReach_head m _⟩
    cases hn : c.lookupOvl k.name with
    | none => exact raw (norm_none hn vs) (uncovered_of_none hn vs)
    | some o =>
      rcases knownSig_cases_ovlF F hk with ⟨-, hn'⟩ | ⟨hct, o', ho', hos⟩
      · rw [hn'] at hn; cases hn
      rw [hn] at ho'; cases ho'; subst hos
      cases hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) with
      | none => exact raw (norm_find_none hn hf) (uncovered_of_find_none hn hf)
      | some kg =>
        have hkg := List.mem_of_find?_eq_some hf
        have hcv := List.find?_some hf
        have hb := not_byFn_of_fnCover_none hnf hn hkg hcv
        obtain ⟨hl, hle, hres, hrk⟩ := over_ovlF F hn hkg
        obtain ⟨-, -, hlies⟩ := covers_iff.mp hcv
        match n with
        | 0 => omega
        | n + 1 =>
          obtain ⟨h, us, hkh, hlh, hleh, hresh, hne, hvs', hul, hor, hreach⟩ :=
            norm_decomp_ovlF n kg (known_of_not_byFn hkg hb) (by omega) _ (sortsOf_stripAll hl hvs hlies)
              (fnCover_strip_none_ovlF H F hn hkg hvs hcv hnf)
          refine ⟨h, us, hkh, by omega, le_all_trans H hlh hl hleh hle, le_trans H hresh hres, ?_, ?_, hul,
            .inr ⟨covered_of_mem hn hkg hcv, ?_⟩, fun m hm => ?_⟩
          · rw [norm_find_some_ovlF F hn hf hb, hne, lift_trans H hresh hres]
          · rw [← liftAll_trans H hlh hl hul hleh hle, ← hvs', liftAll_stripAll hl hvs hlies]
          · rcases hor with ⟨-, rfl, -⟩ | ⟨-, h'⟩ <;> omega
          · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
            have hin := hreach m (by omega)
            simp only [Semantics.ovlReach, hn, List.mem_cons, List.mem_flatMap]
            exact .inr ⟨kg.name, mem_ovlOver hkg, hin⟩

/-- **`norm` is injective** on argument lists of the symbol's sorts that no function overload
covers. -/
theorem norm_inj_known_ovlF {k : CtorSig} (hk : KnownSig c k) {vs ws : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hws : c.sortsOf ws = some k.args)
    (hnv : c.fnCover k.name vs = none) (hnw : c.fnCover k.name ws = none)
    (he : c.norm k.name vs = c.norm k.name ws) : vs = ws := by
  obtain ⟨h, us, hkh, -, -, -, hne, hv, -⟩ := norm_decomp_ovlF H F _ k hk (ovlRank_le _) vs hvs hnv
  obtain ⟨h', us', hkh', -, -, -, hne', hw, -⟩ := norm_decomp_ovlF H F _ k hk (ovlRank_le _) ws hws hnw
  rw [hne, hne'] at he
  obtain ⟨hn, rfl⟩ := lift_ctor_inj he
  rw [hv, hw, knownSig_inj hkh hkh' hn]

theorem norm_inj_ovlF {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {vs ws : List GroundTerm}
    (hvs : c.sortsOf vs = some o.sig.args) (hws : c.sortsOf ws = some o.sig.args)
    (hnv : c.fnCover f vs = none) (hnw : c.fnCover f ws = none)
    (he : c.norm f vs = c.norm f ws) : vs = ws := by
  obtain ⟨-, hn, -, -, hks, -⟩ := ovl_facts_ovlF F ho
  exact norm_inj_known_ovlF H F hks hvs hws (by rw [hn]; exact hnv) (by rw [hn]; exact hnw)
    (by rw [hn]; exact he)

/-- **A normal form is the raw application exactly where no overload covers the arguments**, at
arguments no function overload covers. -/
theorem norm_eq_raw_iff_ovlF {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some o.sig.args) (hnf : c.fnCover f vs = none) :
    c.norm f vs = .ctor f vs ↔ c.uncovered f vs = true := by
  obtain ⟨-, hn, -, -, hks, -⟩ := ovl_facts_ovlF F ho
  obtain ⟨h, us, -, -, -, -, hne, -, -, hor, -⟩ :=
    norm_decomp_ovlF H F _ o.sig hks (ovlRank_le _) vs hvs (by rw [hn]; exact hnf)
  rw [hn] at hne hor
  constructor
  · intro he
    rcases hor with ⟨hu, -⟩ | ⟨-, hlt⟩
    · exact hu
    · rw [he, ← lift_self o.sig.result (.ctor f vs)] at hne
      obtain ⟨rfl, -⟩ := lift_ctor_inj hne
      omega
  · intro hu
    rcases hor with ⟨-, rfl, rfl⟩ | ⟨hu', -⟩
    · rw [hne, lift_self, hn]
    · rw [hu] at hu'; cases hu'

/-- **A value is its own normal form.** -/
theorem norm_fixed_ovlF {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o) {vs : List GroundTerm} {s : Srt}
    (hv : c.sortOf (.ctor f vs) = some s) : c.norm f vs = .ctor f vs := by
  obtain ⟨-, -, -, hct, -⟩ := ovl_facts_ovlF F ho
  rcases c.sortOf_ctor_iff.mp hv with ⟨k, hk, -⟩ | ⟨-, o', ho', hvs, hu, -⟩ | ⟨-, ho', -⟩
  · rw [hct] at hk; cases hk
  · rw [ho] at ho'; cases ho'
    exact (norm_eq_raw_iff_ovlF H F ho hvs (fnCover_none_of_uncovered hu)).mpr hu
  · rw [ho] at ho'; cases ho'

/-- **A normal form's raw application is of a symbol in the overload closure.** -/
theorem norm_head_ovlF {k : CtorSig} (hk : KnownSig c k) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hnf : c.fnCover k.name vs = none) :
    ∃ A f us, c.norm k.name vs = lift A k.result (.ctor f us) ∧ f ∈ c.ovlClosure k.name := by
  obtain ⟨h, us, -, -, -, -, hne, -, -, -, hreach⟩ := norm_decomp_ovlF H F _ k hk (ovlRank_le _) vs hvs hnf
  exact ⟨h.result, h.name, us, hne, hreach _ (by have := ovlRank_le (c := c) k.name; omega)⟩

end

/-! ## Symbols with no function among their overloads -/

/-- No function's signature is among the overloads of `f` (true of a symbol that is no overloading
symbol). -/
def NoFnOver (c : Semantics) (f : Sym) : Prop :=
  ∀ o, c.lookupOvl f = some o → ∀ kg ∈ c.ovlOver o, c.ovlByFn kg = false

/-- A symbol that is not function-overloaded has no function among its overloads. -/
theorem noFnOver_of_not_fnOvl {f : Sym} (h : f ∉ c.fnOvlSyms) : NoFnOver c f := fun o ho kg hkg => by
  cases hb : c.ovlByFn kg with
  | false => rfl
  | true => exact absurd ((lookupOvl_spec ho).1 ▸ fnOvlSyms_of_byFn (mem_of_lookupOvl ho) hkg hb) h

/-- A symbol that is no overloading symbol has no function among its overloads. -/
theorem noFnOver_of_none {f : Sym} (h : c.lookupOvl f = none) : NoFnOver c f := fun o ho => by
  rw [h] at ho; cases ho

/-- No function overload covers anything at a symbol with no function among its overloads. -/
theorem NoFnOver.fnCover_none {f : Sym} (h : NoFnOver c f) (vs : List GroundTerm) : c.fnCover f vs = none := by
  rw [c.fnCover_eq_none_iff]
  intro o ho kg hkg hb
  rw [h o ho kg hkg] at hb
  cases hb

/-- A symbol that `f` overloads has no function among its overloads where `f` has none: an
overloading symbol lists the functions that the overloading symbols it overloads list. -/
theorem NoFnOver.over (F : OvlFnFacts c) {f : Sym} (h : NoFnOver c f) {o : OvlSig} (ho : c.lookupOvl f = some o)
    {kg : CtorSig} (hkg : kg ∈ c.ovlOver o) : NoFnOver c kg.name := fun o' ho' kg' hkg' => by
  cases hb : c.ovlByFn kg' with
  | false => rfl
  | true => rw [h o ho kg' (F.closed o (mem_of_lookupOvl ho) kg hkg o' ho' kg' hkg' hb)] at hb; cases hb

/-- **The function overload that covers.** Where a function overload `kg` of `f` covers the
arguments `vs` of `f`'s sorts, `kg` is the signature of the function its name finds, and the
stripped arguments are of that function's argument sorts. -/
theorem fnCover_fn_ovlF (F : OvlFnFacts c) {f : Sym} {o : OvlSig} (ho : c.lookupOvl f = some o)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some o.sig.args) {kg : CtorSig}
    (hcov : c.fnCover f vs = some kg) :
    ∃ fn, fn ∈ c.fns ∧ c.lookupFn kg.name = some fn ∧ kg = ⟨fn.label, fn.args, fn.result⟩ ∧
      kg ∈ c.ovlOver o ∧ c.ovlByFn kg = true ∧ c.ovlCovers o.sig kg vs = true ∧
      c.sortsOf (stripAll kg.args o.sig.args vs) = some fn.args := by
  obtain ⟨o', ho', hkg, hb, hcv⟩ := fnCover_some_parts hcov
  rw [ho] at ho'; cases ho'
  obtain ⟨fn, hfn, hlook, hsig⟩ := byFn_fn hkg hb
  obtain ⟨hlen, -, -, -⟩ := over_ovlF F ho hkg
  obtain ⟨-, -, hlies⟩ := covers_iff.mp hcv
  have hus := sortsOf_stripAll hlen hvs hlies
  refine ⟨fn, hfn, hlook, hsig, hkg, hb, hcv, ?_⟩
  have : kg.args = fn.args := by rw [hsig]
  rw [← this]; exact hus

end OvlLaws

/-- A function-overloaded symbol (`fnOvlSyms`, which reads the functions' labels) has a function's
signature among its overloads (`ovlByFn`). -/
theorem OvlOK.fnOver {c : Semantics} [h : OvlOK c] :
    ∀ o ∈ c.ovls, o.sig.name ∈ c.fnOvlSyms → ∃ kg ∈ c.ovlOver o, c.ovlByFn kg = true :=
  fun o _ hm => by rw [h.noFn] at hm; cases hm

/-- No overload of a symbol is a function's, where no overloading symbol overloads a function. -/
theorem OvlOK.noFnOver {c : Semantics} [h : OvlOK c] (f : Sym) : OvlLaws.NoFnOver c f :=
  OvlLaws.noFnOver_of_not_fnOvl (by rw [h.noFn]; exact List.not_mem_nil)

/-- No function overload covers anything, where no overloading symbol overloads a function. -/
theorem OvlOK.fnCover_none {c : Semantics} [OvlOK c] (f : Sym) (vs : List GroundTerm) : c.fnCover f vs = none :=
  (OvlOK.noFnOver f).fnCover_none vs

/-! ## Patterns that apply no function-overloaded symbol -/

/-- No symbol applied in `p` is function-overloaded: what `ovlPatsOK` holds of a rule's left side,
a clause's patterns and the pattern of an `exMatch`. -/
abbrev Semantics.NoFnOvlIn (c : Semantics) (p : Term) : Prop := (symOccs p).any c.fnOvlSyms.contains = false

/-- `NoFnOvlIn` of each term of a list. -/
abbrev Semantics.NoFnOvlInL (c : Semantics) (ps : List Term) : Prop :=
  (symOccsList ps).any c.fnOvlSyms.contains = false

namespace NoFnOvlIn
variable {c : Semantics}

theorem app {f : Sym} {ps : List Term} (h : c.NoFnOvlIn (.app f ps)) : f ∉ c.fnOvlSyms ∧ c.NoFnOvlInL ps := by
  unfold Semantics.NoFnOvlIn at h
  rw [symOccs, List.any_cons, Bool.or_eq_false_iff] at h
  exact ⟨fun hm => (by rw [List.contains_iff_mem.mpr hm] at h; exact Bool.noConfusion h.1), h.2⟩

theorem inj {a b : Srt} {p : Term} (h : c.NoFnOvlIn (.inj a b p)) : c.NoFnOvlIn p := by
  unfold Semantics.NoFnOvlIn at h; rw [symOccs] at h; exact h

theorem as {p : Term} {i : Nat} (h : c.NoFnOvlIn (.as p i)) : c.NoFnOvlIn p := by
  unfold Semantics.NoFnOvlIn at h; rw [symOccs] at h; exact h

theorem cons {p : Term} {ps : List Term} (h : c.NoFnOvlInL (p :: ps)) : c.NoFnOvlIn p ∧ c.NoFnOvlInL ps := by
  unfold Semantics.NoFnOvlInL at h
  rw [symOccsList, List.any_append, Bool.or_eq_false_iff] at h
  exact h

theorem nil : c.NoFnOvlInL [] := by
  unfold Semantics.NoFnOvlInL; rw [symOccsList]; rfl

theorem mk_cons {p : Term} {ps : List Term} (h : c.NoFnOvlIn p) (hs : c.NoFnOvlInL ps) : c.NoFnOvlInL (p :: ps) := by
  unfold Semantics.NoFnOvlInL
  rw [symOccsList, List.any_append, Bool.or_eq_false_iff]
  exact ⟨h, hs⟩

theorem mk_app {f : Sym} {ps : List Term} (hf : f ∉ c.fnOvlSyms) (hs : c.NoFnOvlInL ps) : c.NoFnOvlIn (.app f ps) := by
  unfold Semantics.NoFnOvlIn
  rw [symOccs, List.any_cons, Bool.or_eq_false_iff]
  refine ⟨?_, hs⟩
  cases hc : c.fnOvlSyms.contains f with
  | false => rfl
  | true => exact absurd (List.contains_iff_mem.mp hc) hf

theorem mem : ∀ {ps : List Term}, c.NoFnOvlInL ps → ∀ p ∈ ps, c.NoFnOvlIn p
  | _ :: _, h, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (cons h).1
    · exact mem (cons h).2 p hp

theorem of_each : ∀ {ps : List Term}, (∀ p ∈ ps, c.NoFnOvlIn p) → c.NoFnOvlInL ps
  | [], _ => nil
  | p :: ps, h => mk_cons (h p (List.mem_cons_self ..)) (of_each fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem append {ps qs : List Term} (h : c.NoFnOvlInL ps) (h' : c.NoFnOvlInL qs) : c.NoFnOvlInL (ps ++ qs) :=
  of_each fun p hp => (List.mem_append.mp hp).elim (mem h p) (mem h' p)

/-- No term applies a function-overloaded symbol where there is none. -/
theorem of_nil (h : c.fnOvlSyms = []) (p : Term) : c.NoFnOvlIn p := by
  unfold Semantics.NoFnOvlIn; rw [h]; simp

theorem ofL_nil (h : c.fnOvlSyms = []) (ps : List Term) : c.NoFnOvlInL ps := by
  unfold Semantics.NoFnOvlInL; rw [h]; simp

/-- No function overload covers an application of a symbol a pattern without function-overloaded
symbols applies. -/
theorem fnCover_none {f : Sym} {ps : List Term} (h : c.NoFnOvlIn (.app f ps)) (vs : List GroundTerm) :
    c.fnCover f vs = none := OvlLaws.fnCover_none_of_not_fnOvl (app h).1 vs

end NoFnOvlIn

namespace Semantics
variable {c : Semantics}

/-- `overloadsOK`'s condition on the patterns. -/
theorem overloadsOK_pats (h : c.overloadsOK = true) : c.ovlPatsOK = true := by
  unfold overloadsOK at h; exact (Bool.and_eq_true_iff.mp h).2

/-- A rule's left side applies no function-overloaded symbol. -/
theorem ovlPats_lhs (h : c.ovlPatsOK = true) {r : Rule} (hr : r ∈ c.rules) : c.NoFnOvlIn r.lhs := by
  simp only [ovlPatsOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  exact (h.1 r hr).1

/-- The pattern of an `exMatch` of a rule's `pre` or `post` applies no function-overloaded symbol. -/
theorem ovlPats_ruleCond (h : c.ovlPatsOK = true) {r : Rule} (hr : r ∈ c.rules) {p : Term}
    (hp : p ∈ condPats r.pre ++ condPats r.post) : c.NoFnOvlIn p := by
  simp only [ovlPatsOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  exact (h.1 r hr).2 p hp

/-- A clause's patterns apply no function-overloaded symbol. -/
theorem ovlPats_pats (h : c.ovlPatsOK = true) {f : Fn} (hf : f ∈ c.fns) {cl : Clause} (hcl : cl ∈ f.clauses) :
    c.NoFnOvlInL cl.pats := by
  simp only [ovlPatsOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  exact NoFnOvlIn.of_each (h.2 f hf cl hcl).1

/-- The pattern of an `exMatch` of a clause's `pre` or `post` applies no function-overloaded
symbol. -/
theorem ovlPats_clauseCond (h : c.ovlPatsOK = true) {f : Fn} (hf : f ∈ c.fns) {cl : Clause}
    (hcl : cl ∈ f.clauses) {p : Term} (hp : p ∈ condPats cl.pre ++ condPats cl.post) : c.NoFnOvlIn p := by
  simp only [ovlPatsOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  exact (h.2 f hf cl hcl).2 p hp

end Semantics

end KCore
