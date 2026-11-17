/-
  KCore. The value model at an overloading symbol one of whose overloads is a function.

  The overload's equation states `f(lift x̄) = lift (g(x̄))`. For a function `g` the application
  `f(v̄)` at arguments `g` covers therefore has `g`'s values at the stripped arguments, lifted
  (`ovlRes`), none where `g` has none and several where `g` has several; `Γ` states `f` functional
  and injective at the arguments no overload covers only (`funUncItem`, `injUncItem`). Here:

  - at arguments no overload covers, the symbol gives its raw application (`result_unc_ovlF`),
    which is a value of the symbol's result sort (`sortOf_unc_ovlF`);
  - the model satisfies `funUncItem` (`sat_funUnc_ovlF`) and `injUncItem` (`sat_injUnc_ovlF`) of
    the symbol: at uncovered arguments the raw application is one value, and a constructor term
    determines its arguments;
  - the model satisfies the overload equation of a function overload (`sat_ovlEq_ovlF`): both
    sides are the function's values lifted, whatever they are. Nothing is asked of the function:
    not that it has a value at the arguments, nor that it has one only, nor that it is injective;
  - the model satisfies `distUncItem` of two generators that build different values at the
    arguments their guards accept (`sat_distUnc_ovlF`), an overloading symbol with a function
    among its overloads being one (`genAt_ovlF`), a constructor (`genAt_ctor_ovlF`) or an
    injection (`genAt_inj_ovlF`) the other.

  The hypotheses are stated on the one overloading symbol (`OvlAtF`) and the one overload, and
  none of them excludes a function among the overloads.
-/
import KcoreSpec.ModelCons

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- **What the model's cases read of the overloading symbol `o`**: the symbols and sorts are
named apart, `o` is declared (`lookupOvl` finds it under its name, and the name is an overloading
symbol's and of no other kind), and its sorts and the argument sorts of the symbols it overloads
are numbered. Nothing is said of what kind the overloaded symbols are. -/
structure OvlAtF (c : Semantics) (o : OvlSig) : Prop where
  names : NamesApartK c
  mem : o ∈ c.ovls
  lookup : c.lookupOvl o.sig.name = some o
  isOvl : c.isOvl o.sig.name = true
  sorts : ∀ s ∈ o.sig.result :: o.sig.args, s < nRegSorts + c.sortNames.length
  over : ∀ kg ∈ c.ovlOver o, ∀ s ∈ kg.args, s < nRegSorts + c.sortNames.length

/-- Arguments no overload covers are covered by no function overload. -/
theorem fnCover_none_of_unc_ovlF {f : Sym} {vs : List GroundTerm} (hu : c.uncovered f vs = true) :
    c.fnCover f vs = none := by
  rw [Semantics.fnCover_eq_none_iff]
  intro o ho kg hkg _
  simp only [Semantics.uncovered, ho, List.all_eq_true, Bool.not_eq_true'] at hu
  exact hu kg hkg

/-- At arguments no overload covers the normal form is the raw application. -/
theorem norm_of_unc_ovlF {f : Sym} {vs : List GroundTerm} (hu : c.uncovered f vs = true) :
    c.norm f vs = .ctor f vs := by
  cases ho : c.lookupOvl f with
  | none => simp only [Semantics.norm, Semantics.normN, ho]
  | some o =>
    simp only [Semantics.uncovered, ho, List.all_eq_true, Bool.not_eq_true'] at hu
    have hf : (c.ovlOver o).find? (fun kg => c.ovlCovers o.sig kg vs) = none :=
      List.find?_eq_none.mpr fun kg hkg => by simp [hu kg hkg]
    simp only [Semantics.norm, Semantics.normN, ho, hf]

/-- **An overloading symbol at uncovered arguments, in the model**: its raw application. -/
theorem result_unc_ovlF {o : OvlSig} (hio : c.isOvl o.sig.name = true) {vs : List GroundTerm}
    (hu : c.uncovered o.sig.name vs = true) (x : Elem) :
    result c o.sig vs x ↔ x = .val (.ctor o.sig.name vs) := by
  rw [result_ovl hio (fnCover_none_of_unc_ovlF hu), norm_of_unc_ovlF hu]

/-- The raw application of an overloading symbol at uncovered arguments of its argument sorts is
a value of its result sort. -/
theorem sortOf_unc_ovlF {o : OvlSig} (hlo : c.lookupOvl o.sig.name = some o) (hio : c.isOvl o.sig.name = true)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some o.sig.args) (hu : c.uncovered o.sig.name vs = true) :
    c.sortOf (.ctor o.sig.name vs) = some o.sig.result := by
  have hct : lookupSig c.ctorSigs o.sig.name = none := by
    have := (c.isOvl_parts hio).1
    simpa [Semantics.isCtor] using this
  exact c.sortOf_ctor_iff.mpr (.inr (.inl ⟨hct, o, hlo, hvs, hu, rfl⟩))

/-- A value of A lifted to B and stripped back to A is itself, the subsorts irreflexive. -/
theorem strip_lift_ovlF (hirr : ∀ a, (a, a) ∉ c.subsorts) {A B : Srt} {u : GroundTerm}
    (hu : c.sortOf u = some A) : strip A B (lift A B u) = u := by
  by_cases hAB : A = B
  · subst hAB; rw [OvlLaws.lift_self, OvlLaws.strip_self]
  rw [OvlLaws.lift_ne hAB]
  cases u with
  | inj a' A' w =>
    obtain ⟨h1, -, -, rfl⟩ := OvlLaws.sortOf_inj_iff.mp hu
    have hne : a' ≠ A := fun he => hirr a' (he ▸ h1)
    simp [injNormal, strip, hAB, hne]
  | _ => simp [injNormal, strip, hAB]

theorem stripAll_liftAll_ovlF (hirr : ∀ a, (a, a) ∉ c.subsorts) {as bs : List Srt} {us : List GroundTerm}
    (hl : as.length = bs.length) (hu : c.sortsOf us = some as) :
    stripAll as bs (liftAll as bs us) = us := by
  obtain ⟨hul, hui⟩ := OvlLaws.sortsOf_iff.mp hu
  refine List.ext_getElem (by simp [OvlLaws.length_liftAll, OvlLaws.length_stripAll]; omega) fun i h1 h2 => ?_
  rw [OvlLaws.getElem_stripAll, OvlLaws.getElem_liftAll]
  exact strip_lift_ovlF hirr (hui i h2 (by omega))

/-- The overload of `kg` covers values of its argument sorts lifted to `kf`'s. -/
theorem covers_liftAll_ovlF {kf kg : CtorSig} {as : List GroundTerm} (hl : kg.args.length = kf.args.length)
    (has : c.sortsOf as = some kg.args) : c.ovlCovers kf kg (liftAll kg.args kf.args as) = true := by
  have hal := (OvlLaws.sortsOf_iff.mp has).1
  exact OvlLaws.covers_iff.mpr ⟨hl, by simp [OvlLaws.length_liftAll]; omega, OvlLaws.lies_liftAll hl has⟩

/-- The function overload that covers `vs` is `kg`, where `kg` is a function's signature among
the overloads, covers `vs`, and is the one such signature that does. -/
theorem fnCover_of_unique_ovlF {f : Sym} {o : OvlSig} {kg : CtorSig} {vs : List GroundTerm}
    (hlo : c.lookupOvl f = some o) (hkg : kg ∈ c.ovlOver o) (hfn : c.ovlByFn kg = true)
    (hc : c.ovlCovers o.sig kg vs = true)
    (hu : ∀ kg' ∈ c.ovlOver o, c.ovlByFn kg' = true → c.ovlCovers o.sig kg' vs = true → kg' = kg) :
    c.fnCover f vs = some kg := by
  unfold Semantics.fnCover
  rw [hlo]
  show (c.ovlOver o).find? (fun kg => c.ovlByFn kg && c.ovlCovers o.sig kg vs) = some kg
  cases hf : (c.ovlOver o).find? (fun kg => c.ovlByFn kg && c.ovlCovers o.sig kg vs) with
  | none =>
    have := List.find?_eq_none.mp hf kg hkg
    simp [hfn, hc] at this
  | some kg' =>
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true] at hp
    rw [hu kg' hm hp.1 hp.2]

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- The uncovered guard of an overloading generator, in the model: its arguments are covered by
none of its overloads, whatever kind the overloaded symbols are. -/
theorem uncGuard_ovlF {o : OvlSig} (H : OvlAtF c o) {x : List EVar} {z : EVar} (hz : z ∉ x) {e : Valuation Elem}
    {m : Elem} {vs : List GroundTerm} (hxs : x.map e.evalEvar = vs.map Elem.val)
    (hvs : c.sortsOf vs = some o.sig.args)
    (hg : (KoreAML.Cons.uncoveredP (o.sig.args.map c.sortName) ((c.ovlOver o).map fun kg => kg.args.map c.sortName)
      x z).interpret (stdI_T c T) e m) :
    c.uncovered o.sig.name vs = true := by
  have hn := H.names
  simp only [Semantics.uncovered, H.lookup, List.all_eq_true, Bool.not_eq_true']
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
  have hA := H.over kg hkg _ (List.getElem_mem (show i < kg.args.length by omega))
  have hB := H.sorts _ (List.mem_cons_of_mem _ (List.getElem_mem (show i < o.sig.args.length by omega)))
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

/-- The generator of an overloading symbol at uncovered arguments builds its raw application. -/
theorem gs_unc_ovlF {o : OvlSig} (H : OvlAtF c o) (N : String) {vs : List GroundTerm}
    (hl : vs.length = o.sig.args.length) (hu : c.uncovered o.sig.name vs = true) (m : Elem) :
    GS (stdI_T c T) N (Gen.toK c (.ctor o.sig)) (vs.map Elem.val) m ↔ m = .val (.ctor o.sig.name vs) := by
  rw [gs_ovl H.names H.mem H.isOvl N hl (fnCover_none_of_unc_ovlF hu) m, norm_of_unc_ovlF hu]

/-- **Cons-Fun at uncovered arguments holds** of an overloading symbol, a function among its
overloads or not: there its application is its raw application, a value of its result sort. -/
theorem sat_funUnc_ovlF {o : OvlSig} (H : OvlAtF c o) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.funUncItem (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig))
      ((c.ovlOver o).map fun kg => kg.args.map c.sortName)).pat := by
  have hn := H.names
  have hargs : ∀ s ∈ o.sig.args, s < nRegSorts + c.sortNames.length :=
    fun s hs => H.sorts s (List.mem_cons_of_mem _ hs)
  intro e m
  unfold KoreAML.Cons.funUncItem
  dsimp only
  simp only [toK_argSorts]
  refine guarded_intro fun hgd => ?_
  obtain ⟨vs, hxs, hvs⟩ := memGuards_vals (T := T) hn _ o.sig.args hargs (by simp [xs_length]; rfl)
    (fun w hw => hgd w (List.mem_append_left _ hw))
  have hu : c.uncovered o.sig.name vs = true :=
    uncGuard_ovlF H (notMem_xs_z (by omega)) hxs hvs (hgd _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
  rw [KoreAML.interp_sExists]
  refine ⟨.val (.ctor o.sig.name vs), ?_, ?_⟩
  · rw [KoreAML.interp_member defOK_std]
    simp only [Function.update_same]
    exact (inhOf_sort hn (H.sorts _ (List.mem_cons_self ..)) _ _).mpr (sortOf_unc_ovlF H.lookup H.isOvl hvs hu)
  · rw [KoreAML.interp_equal defOK_std]
    intro a
    rw [interp_genPat_vars, KoreAML.interp_evar]
    simp only [Function.update_same]
    rw [map_update_xs 0 _ _ _ _ (fun i hi he => by simp only [EVar.mk.injEq, List.length_map] at he hi; omega), hxs]
    exact gs_unc_ovlF H _ (sortsOf_len hvs) hu a

/-- **Cons-Inj at uncovered arguments holds** of an overloading symbol, a function among its
overloads or not: two raw applications that are one value have the same arguments. -/
theorem sat_injUnc_ovlF {o : OvlSig} (H : OvlAtF c o) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.injUncItem (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig))
      ((c.ovlOver o).map fun kg => kg.args.map c.sortName)).pat := by
  have hn := H.names
  have hargs : ∀ s ∈ o.sig.args, s < nRegSorts + c.sortNames.length :=
    fun s hs => H.sorts s (List.mem_cons_of_mem _ hs)
  intro e m
  unfold KoreAML.Cons.injUncItem
  dsimp only
  simp only [toK_argSorts]
  refine guarded_intro fun hgd => ?_
  obtain ⟨vs, hxs, hvs⟩ := memGuards_vals (T := T) hn _ o.sig.args hargs (by simp [xs_length]; rfl)
    (fun w hw => hgd w (List.mem_append_left _ (List.mem_append_left _ hw)))
  obtain ⟨ws, hys, hws⟩ := memGuards_vals (T := T) hn _ o.sig.args hargs (by simp [xs_length]; rfl)
    (fun w hw => hgd w (List.mem_append_left _ (List.mem_append_right _ hw)))
  have hu : c.uncovered o.sig.name vs = true :=
    uncGuard_ovlF H (notMem_xs_z (by omega)) hxs hvs (hgd _ (List.mem_append_right _ (List.mem_cons_self ..)))
  have hu' : c.uncovered o.sig.name ws = true :=
    uncGuard_ovlF H (notMem_xs_z (by omega)) hys hws
      (hgd _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))))
  rw [interpret_impl]
  intro heq
  rw [KoreAML.interp_equal defOK_std] at heq
  have hvw : vs = ws := by
    have := heq (.val (.ctor o.sig.name vs))
    rw [interp_genPat_vars, interp_genPat_vars, hxs, hys, gs_unc_ovlF H _ (sortsOf_len hvs) hu,
      gs_unc_ovlF H _ (sortsOf_len hws) hu'] at this
    exact (GroundTerm.ctor.inj (Elem.val.inj (this.mp rfl))).2
  subst hvw
  rw [← hys] at hxs
  apply KoreAML.interp_conjList
  intro w hw
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hw
  rw [KoreAML.interp_equal defOK_std]
  intro z
  rw [KoreAML.interp_evar, KoreAML.interp_evar, zip_map_eq e.evalEvar _ _ hxs _ hab]

/-- `inj{s,t}(φ)` at a pattern that denotes values: the injections of those values. -/
theorem inj_vals_ovlF (hn : NamesApartK c) {s t : Srt} (hs : s < nRegSorts + c.sortNames.length)
    (ht : t < nRegSorts + c.sortNames.length) {e : Valuation Elem} {φ : KoreAML.P} {S : GroundTerm → Prop}
    (hφ : ∀ m, φ.interpret (stdI_T c T) e m ↔ ∃ u, m = .val u ∧ S u) (m : Elem) :
    (KoreAML.appList (KoreAML.sym (.symbol "inj"))
      [KoreAML.Cons.sortP (c.sortName s), KoreAML.Cons.sortP (c.sortName t), φ]).interpret (stdI_T c T) e m ↔
      ∃ u, m = .val (injNormal s t u) ∧ S u := by
  rw [interp_injApp]
  constructor
  · rintro ⟨x, hx, hg⟩
    obtain ⟨u, rfl, hu⟩ := (hφ x).mp hx
    obtain ⟨v, hv, rfl⟩ := (gs_inj hn hs ht _ _).mp hg
    cases hv
    exact ⟨u, rfl, hu⟩
  · rintro ⟨u, rfl, hu⟩
    exact ⟨.val u, (hφ _).mpr ⟨u, rfl, hu⟩, (gs_inj hn hs ht _ _).mpr ⟨u, rfl, rfl⟩⟩

/-- **The overload equation of a function overload holds**: `f(lift x̄) = lift (g(x̄))` for the
overloading symbol `f` (`o`) and the function `g` (`kg`) whose overload covers the lifted
arguments (`hcov`). Both sides are the values of `g` at `x̄`, lifted: as many as `g` has there. -/
theorem sat_ovlEq_ovlF {o : OvlSig} (H : OvlAtF c o) {kg : CtorSig} (hk : kg ∈ kernelSyms c)
    (hkc : c.isCtor kg.name = false) (hkh : isHook kg.name = false) (hkp : c.isParam kg.name = false)
    (hko : c.isOvl kg.name = false)
    (hks : ∀ s ∈ kg.result :: kg.args, s < nRegSorts + c.sortNames.length)
    (hl : kg.args.length = o.sig.args.length) (hirr : ∀ a, (a, a) ∉ c.subsorts)
    (hcov : ∀ as, c.sortsOf as = some kg.args →
      c.fnCover o.sig.name (liftAll kg.args o.sig.args as) = some kg) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.ovlEqItem (toK c o.sig) (toK c kg)).pat := by
  have hn := H.names
  have hkn := fun s hs => hks s (List.mem_cons_of_mem _ hs)
  have hon := fun s hs => H.sorts s (List.mem_cons_of_mem _ hs)
  have hkr := hks _ (List.mem_cons_self ..)
  have hor := H.sorts _ (List.mem_cons_self ..)
  intro e m
  unfold KoreAML.Cons.ovlEqItem
  dsimp only
  simp only [toK, List.length_map]
  refine guarded_intro fun hgd => ?_
  obtain ⟨as, hxs, has⟩ := memGuards_vals (T := T) hn _ kg.args hkn (by simp [xs_length]) hgd
  have hal := (OvlLaws.sortsOf_iff.mp has).1
  have hin : ∀ m, (KoreAML.appList (KoreAML.sym (.symbol (c.symName kg.name)))
      ((KoreAML.Cons.xs 0 kg.args.length).map Pattern.evar)).interpret (stdI_T c T) e m ↔
      ∃ u, m = .val u ∧ Eval c kg.name as (some u) := fun m => by
    rw [interp_symList _ _ (as.map Elem.val) (evars_den _ _ hxs) m,
      symE_vals hn hk (by omega) m, result_fn hkc hkh hkp hko]
  rw [KoreAML.interp_equal defOK_std]
  intro b
  rw [interp_symList _ _ ((liftAll kg.args o.sig.args as).map Elem.val)
    (liftArgs_den hn _ (fun A B xi => rfl) kg.args o.sig.args _ as hkn hon hxs hl hal) b,
    symE_vals hn (ovl_kernel H.mem) (by simp [OvlLaws.length_liftAll]; omega) b,
    result_ovlFn H.isOvl H.lookup (hcov as has), stripAll_liftAll_ovlF hirr hl has]
  by_cases hres : kg.result = o.sig.result
  · simp only [hres, beq_self_eq_true, ↓reduceIte, OvlLaws.lift_self]
    exact (hin b).symm
  · have hne : (c.sortName kg.result == c.sortName o.sig.result) = false := by
      rw [beq_eq_false_iff_ne]
      intro hs
      exact hres (hn.2.2 _ (List.mem_range.mpr hkr) _ (List.mem_range.mpr hor) hs)
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [inj_vals_ovlF hn hkr hor hin b]
    simp only [OvlLaws.lift_ne hres]

/-- **What Cons-Dist at uncovered arguments reads of a generator** of the sort `N`, in the model:
its argument sorts are numbered, its uncovered guard (written for an overloading symbol) says no
overload covers the arguments, and at arguments the guard accepts it builds the one value
`val v̄`. -/
structure GenAtF (c : Semantics) (T : GroundTerm → GroundTerm → Prop) (N : Srt) (g : Gen)
    (val : List GroundTerm → GroundTerm) : Prop where
  args : ∀ s ∈ g.argSorts, s < nRegSorts + c.sortNames.length
  unc : ∀ (x : List EVar) (us : List GroundTerm) (z : EVar) (e : Valuation Elem) (m : Elem), z ∉ x →
    x.map e.evalEvar = us.map Elem.val → c.sortsOf us = some g.argSorts →
    (∀ w ∈ (match ovlArgsOf c g with
      | some covs => [KoreAML.Cons.uncoveredP (g.argSorts.map c.sortName) covs x z]
      | none => []), w.interpret (stdI_T c T) e m) → UncG c g us
  gs : ∀ (vs : List GroundTerm), c.sortsOf vs = some g.argSorts → UncG c g vs →
    ∀ m, GS (stdI_T c T) (c.sortName N) (Gen.toK c g) (vs.map Elem.val) m ↔ m = .val (val vs)

/-- An overloading symbol, a function among its overloads or not: at uncovered arguments its raw
application. -/
theorem genAt_ovlF {o : OvlSig} (H : OvlAtF c o) (N : Srt) :
    GenAtF c T N (.ctor o.sig) (fun vs => .ctor o.sig.name vs) where
  args := fun s hs => H.sorts s (List.mem_cons_of_mem _ hs)
  unc := fun x us z e m hz hx hus hw _ => by
    have hov : ovlArgsOf c (.ctor o.sig) = some ((c.ovlOver o).map fun kg => kg.args.map c.sortName) := by
      simp [ovlArgsOf, H.isOvl, H.lookup]
    rw [hov] at hw
    exact uncGuard_ovlF H hz hx hus (hw _ (List.mem_singleton_self _))
  gs := fun vs hvs hu m => gs_unc_ovlF H _ (sortsOf_len hvs) (hu H.isOvl) m

/-- A constructor: its term. -/
theorem genAt_ctor_ovlF (hn : NamesApartK c) {k : CtorSig} (hk : k ∈ c.ctorSigs)
    (hargs : ∀ s ∈ k.args, s < nRegSorts + c.sortNames.length) (N : Srt) :
    GenAtF c T N (.ctor k) (fun vs => .ctor k.name vs) where
  args := hargs
  unc := fun _ _ _ _ _ _ _ _ _ hio => by rw [isOvl_of_ctorSigs hk] at hio; cases hio
  gs := fun vs hvs _ m => gs_ctor hn hk _ (sortsOf_len hvs) m

/-- An injection: `injNormal` of its argument. -/
theorem genAt_inj_ovlF (hn : NamesApartK c) {a N : Srt} (ha : a < nRegSorts + c.sortNames.length)
    (hN : N < nRegSorts + c.sortNames.length) :
    GenAtF c T N (.inj a) (fun vs => injNormal a N (vs.headD (.ctor 0 []))) where
  args := fun s hs => by
    have : s = a := by simpa [Gen.argSorts] using hs
    rw [this]; exact ha
  unc := fun _ _ _ _ _ _ _ _ _ => trivial
  gs := fun vs hvs _ m => by
    obtain ⟨v, rfl, -⟩ := sortsOf_single hvs
    show GS (stdI_T c T) (c.sortName N) (.inj (c.sortName a)) [Elem.val v] m ↔ _
    rw [gs_inj hn ha hN]
    constructor
    · rintro ⟨v', hv', rfl⟩; cases hv'; rfl
    · rintro rfl; exact ⟨v, rfl, rfl⟩

/-- **Cons-Dist at uncovered arguments holds** of two generators that build different values at
the arguments their guards accept: for an overloading symbol with a function among its overloads
(`genAt_ovlF`) these are the arguments no overload covers, where it builds its raw application. -/
theorem sat_distUnc_ovlF (hn : NamesApartK c) {N : Srt} {g g' : Gen} {val val' : List GroundTerm → GroundTerm}
    (G : GenAtF c T N g val) (G' : GenAtF c T N g' val')
    (hne : ∀ vs ws, c.sortsOf vs = some g.argSorts → c.sortsOf ws = some g'.argSorts →
      UncG c g vs → UncG c g' ws → val vs ≠ val' ws) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.distUncItem (c.sortName N) (Gen.toK c g) (Gen.toK c g') (ovlArgsOf c g)
      (ovlArgsOf c g')).pat := by
  intro e m
  unfold KoreAML.Cons.distUncItem
  dsimp only
  simp only [toK_argSorts]
  refine guarded_intro fun hgd => ?_
  obtain ⟨vs, hxs, hvs⟩ := memGuards_vals (T := T) hn _ g.argSorts G.args (by simp [xs_length])
    (fun w hw => hgd w (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hw))))
  obtain ⟨ws, hys, hws⟩ := memGuards_vals (T := T) hn _ g'.argSorts G'.args (by simp [xs_length])
    (fun w hw => hgd w (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw))))
  have hu := G.unc (KoreAML.Cons.xs 0 (g.argSorts.map c.sortName).length) vs
    ⟨(g.argSorts.map c.sortName).length + (g'.argSorts.map c.sortName).length + 1⟩ e m
    (notMem_xs_z (by omega)) hxs hvs
    (fun w hw => hgd w (List.mem_append_left _ (List.mem_append_right _ hw)))
  have hu' := G'.unc (KoreAML.Cons.xs (g.argSorts.map c.sortName).length (g'.argSorts.map c.sortName).length) ws
    ⟨(g.argSorts.map c.sortName).length + (g'.argSorts.map c.sortName).length + 1⟩ e m
    (notMem_xs_z (by omega)) hys hws
    (fun w hw => hgd w (List.mem_append_right _ hw))
  rw [KoreAML.interp_notEqual defOK_std]
  intro heq
  have := heq (.val (val vs))
  rw [interp_genPat_vars, interp_genPat_vars, hxs, hys, G.gs vs hvs hu, G'.gs ws hws hu'] at this
  exact hne vs ws hvs hws hu hu' (Elem.val.inj (this.mp rfl))

end AtT

end Model

end Faithful

end KCore
