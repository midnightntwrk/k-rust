/-
  KCore. The overload equations in the value model, a function among the overloads or not.

  Read from `HypModelCore` through the facts of the declarations that exclude no function
  overload (`OvlLaws.OvlFnFacts`) and the order of the subsorts:

  - what the model's cases read of one overloading symbol (`ovlAtF_of`);
  - a constructor's or an overloading symbol's result at arguments no function overload covers
    is its normal form (`result_known_fnF`);
  - **`SatConsGoal`** (`satConsGoal`): the model satisfies the constructors' axioms. A generator
    that is a function-overloaded symbol has its functionality and injectivity items at uncovered
    arguments (`sat_funUnc_ovlF`, `sat_injUnc_ovlF`), every other generator at every argument;
  - **each overload equation holds** (`sat_ovlEq_fnF`), `f(lift x̄) = lift (g(x̄))`, in three cases:
    `g` is a function, both sides being its values lifted (`sat_ovlEq_ovlF`, the function overload
    covering lifted arguments of `g`'s sorts being `g`); `g` is a constructor or an overloading
    symbol and no function overload of `f` covers the lifted arguments, both sides being the
    normal form; or one does, a function `g` lists too, both sides being that function's values
    at the same stripped arguments, lifted.
-/
import KcoreSpec.ModelOvlFn
import KcoreSpec.OvlLawsFn

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- A function's signature among the overloads: a kernel symbol that is a function and of no
other kind. -/
theorem byFn_kinds_fnF (h : HypModelCore c) {o : OvlSig} {kg : CtorSig} (hkg : kg ∈ c.ovlOver o)
    (hb : c.ovlByFn kg = true) :
    kg ∈ kernelSyms c ∧ c.isCtor kg.name = false ∧ isHook kg.name = false ∧ c.isParam kg.name = false ∧
      c.isOvl kg.name = false := by
  obtain ⟨fn, hfn, hlf, hsig⟩ := OvlLaws.byFn_fn hkg hb
  have hmem : fn ∈ c.allFns := List.mem_append_left _ hfn
  have hk := List.all_eq_true.mp h.fns fn hmem
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
  have hl : fn.label = kg.name := by rw [hsig]
  rw [hl] at hk
  refine ⟨?_, hk.1.1, hk.1.2, hk.2, c.isOvl_of_lookupFn hlf⟩
  rw [hsig]
  exact fn_sig_mem hmem

/-- **What the model's cases read of an overloading symbol**, from `HypModelCore`. -/
theorem ovlAtF_of (h : HypModelCore c) {o : OvlSig} (ho : o ∈ c.ovls) : OvlAtF c o where
  names := h.namesK
  mem := ho
  lookup := OvlLaws.lookupOvl_of_nodup h.ovlsOnce ho
  isOvl := h.ovlHyp.fnFacts.isOvl o ho
  sorts := h.symSorts (ovl_kernel ho)
  over := fun kg hkg s hs => by
    cases hb : c.ovlByFn kg with
    | true => exact h.symSorts (byFn_kinds_fnF h hkg hb).1 s (List.mem_cons_of_mem _ hs)
    | false => exact h.symSorts (known_kernel (OvlLaws.known_of_not_byFn hkg hb)) s (List.mem_cons_of_mem _ hs)

/-- A constructor's or an overloading symbol's result at values no function overload covers is
its normal form. -/
theorem result_known_fnF (h : HypModelCore c) {k : CtorSig} (hk : OvlLaws.KnownSig c k) {vs : List GroundTerm}
    (hnf : c.fnCover k.name vs = none) (x : Elem) : result c k vs x ↔ x = .val (c.norm k.name vs) := by
  rcases OvlLaws.knownSig_cases_ovlF h.ovlHyp.fnFacts hk with ⟨hct, hn⟩ | ⟨-, o, hlo, rfl⟩
  · rw [result_ctor (by simp [Semantics.isCtor, hct]), OvlLaws.norm_none hn]
  · exact result_ovl (OvlLaws.ovl_facts_ovlF h.ovlHyp.fnFacts hlo).2.2.1 hnf x

/-- A generator that is a function-overloaded symbol: an overloading symbol of the list, of the
generator's sort, whose overloads' argument sorts are those its uncovered guard names. -/
theorem fnOvl_gen_fnF (h : HypModelCore c) {N : Srt} {g : Gen} (hg : g ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hf : c.fnOvl g = true) :
    ∃ o ∈ c.ovls, g = .ctor o.sig ∧ o.sig.result = N ∧
      (match g with
        | .ctor k => if c.isOvl k.name then (c.lookupOvl k.name).map fun o => (c.ovlOver o).map fun kg => kg.args.map c.sortName
          else none
        | .inj _ => none) = some ((c.ovlOver o).map fun kg => kg.args.map c.sortName) := by
  rcases mem_gensF h hg with ⟨k, hk, -, rfl⟩ | ⟨o, ho, hr, rfl⟩ | ⟨a, -, rfl⟩
  · simp [Semantics.fnOvl, isOvl_of_ctorSigs hk] at hf
  · refine ⟨o, ho, rfl, hr, ?_⟩
    simp [h.ovlHyp.fnFacts.isOvl o ho, OvlLaws.lookupOvl_of_nodup h.ovlsOnce ho]
  · simp [Semantics.fnOvl] at hf

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **Each overload equation holds**, `f(lift x̄) = lift (g(x̄))`, the overloaded `g` a function, a
constructor or an overloading symbol. -/
theorem sat_ovlEq_fnF (h : HypModelCore c) {o : OvlSig} (ho : o ∈ c.ovls) {kg : CtorSig} (hkg : kg ∈ c.ovlOver o) :
    stdI_T c T ⊧ᴵ (KoreAML.Cons.ovlEqItem (toK c o.sig) (toK c kg)).pat := by
  have hn := h.namesK
  have H := h.ovlHyp
  have F := H.fnFacts
  have HA := ovlAtF_of h ho
  have hlo := HA.lookup
  have hio := HA.isOvl
  obtain ⟨hl, hle, hres', -⟩ := OvlLaws.over_ovlF F hlo hkg
  cases hb : c.ovlByFn kg with
  | true =>
    obtain ⟨hk, hkc, hkh, hkp, hko⟩ := byFn_kinds_fnF h hkg hb
    exact sat_ovlEq_ovlF HA hk hkc hkh hkp hko (h.symSorts hk) hl H.irrefl fun as has =>
      OvlLaws.fnCover_of_covers_ovlF H F hlo hkg hb (OvlLaws.sortsOf_liftAll H hl has hle)
        (covers_liftAll_ovlF hl has)
  | false =>
    have hkk := OvlLaws.known_of_not_byFn hkg hb
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
      symE_vals hn (ovl_kernel ho) (by simp [OvlLaws.length_liftAll]; omega) b]
    -- the right side, from what `g(x̄)` denotes
    have tail : ∀ (S : GroundTerm → Prop),
        (∀ m, (KoreAML.appList (KoreAML.sym (.symbol (c.symName kg.name)))
          ((KoreAML.Cons.xs 0 kg.args.length).map Pattern.evar)).interpret (stdI_T c T) e m ↔
          ∃ u, m = .val u ∧ S u) →
        ((∃ u, b = .val (lift kg.result o.sig.result u) ∧ S u) ↔
          (if (c.sortName kg.result == c.sortName o.sig.result) = true then
            KoreAML.appList (KoreAML.sym (.symbol (c.symName kg.name)))
              ((KoreAML.Cons.xs 0 kg.args.length).map Pattern.evar)
          else KoreAML.appList (KoreAML.sym (.symbol "inj"))
            [KoreAML.Cons.sortP (c.sortName kg.result), KoreAML.Cons.sortP (c.sortName o.sig.result),
              KoreAML.appList (KoreAML.sym (.symbol (c.symName kg.name)))
                ((KoreAML.Cons.xs 0 kg.args.length).map Pattern.evar)]).interpret (stdI_T c T) e b) := by
      intro S hin
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
    have hfl := OvlLaws.fnCover_liftAll_ovlF H F hlo hkg hb has
    cases hfc : c.fnCover o.sig.name (liftAll kg.args o.sig.args as) with
    | none =>
      rw [result_ovl hio hfc, OvlLaws.norm_ovlEq_ovlF H F hlo hkg has hfc]
      refine Iff.trans ?_ (tail (fun u => u = c.norm kg.name as) fun m => ?_)
      · constructor
        · rintro rfl; exact ⟨_, rfl, rfl⟩
        · rintro ⟨u, rfl, rfl⟩; rfl
      · rw [interp_symList _ _ (as.map Elem.val) (evars_den _ _ hxs) m,
          symE_vals hn (known_kernel hkk) (by omega) m, result_known_fnF h hkk (by rw [← hfl]; exact hfc)]
        constructor
        · rintro rfl; exact ⟨_, rfl, rfl⟩
        · rintro ⟨u, rfl, rfl⟩; rfl
    | some g =>
      -- a function overload of `f` covers the lifted arguments: it is one of `g`, covering them
      -- there, and both sides are its values at the stripped arguments, lifted
      rw [hfc] at hfl
      obtain ⟨ok, hok, hg, hbg, hcg⟩ := OvlLaws.fnCover_some_parts hfl.symm
      have hos := OvlLaws.over_sig_ovlF F hkg hok
      subst hos
      obtain ⟨hlg, hleg, hresg, -⟩ := OvlLaws.over_ovlF F hok hg
      obtain ⟨-, -, hio', -⟩ := OvlLaws.ovl_facts_ovlF F hok
      obtain ⟨o2, ho2, hgo, -, hcgo⟩ := OvlLaws.fnCover_some_parts hfc
      rw [hlo] at ho2; cases ho2
      obtain ⟨-, -, hliesgo⟩ := OvlLaws.covers_iff.mp hcgo
      have hst : stripAll g.args o.sig.args (liftAll ok.sig.args o.sig.args as) = stripAll g.args ok.sig.args as := by
        rw [← OvlLaws.stripAll_trans H hlg hl (by simp [OvlLaws.length_liftAll]; omega) hleg hle hliesgo,
          OvlLaws.stripAll_liftAll H hl has]
      rw [result_ovlFn hio hlo hfc, hst]
      refine Iff.trans ?_ (tail (fun u => ∃ w, u = lift g.result ok.sig.result w ∧
        Eval c g.name (stripAll g.args ok.sig.args as) (some w)) fun m => ?_)
      · constructor
        · rintro ⟨v, rfl, hv⟩
          exact ⟨_, by rw [OvlLaws.lift_trans H hresg hres'], v, rfl, hv⟩
        · rintro ⟨u, rfl, w, rfl, hw⟩
          exact ⟨w, by rw [OvlLaws.lift_trans H hresg hres'], hw⟩
      · rw [interp_symList _ _ (as.map Elem.val) (evars_den _ _ hxs) m,
          symE_vals hn (known_kernel hkk) (by omega) m, result_ovlFn hio' hok hfl.symm]
        constructor
        · rintro ⟨w, rfl, hw⟩; exact ⟨_, rfl, w, rfl, hw⟩
        · rintro ⟨u, rfl, w, rfl, hw⟩; exact ⟨w, rfl, hw⟩

end AtT

/-! ## The constructors' axioms -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **`SatConsGoal`**: the value model satisfies the constructors' axioms, the law sentences
of the open generators where the interpretation satisfies the laws (`OpenLaws`). -/
theorem satConsGoal (h : HypModelCore c) (hl : OpenLaws c) : (stdI_T c T ⊧ᴵP ΓCons c) := by
  refine sat_itemsPremises c fun it hit => ?_
  unfold consItemsK at hit
  dsimp only at hit
  rcases List.mem_append.mp hit with hit | hit
  rotate_left
  · -- the open generators' law items, each from its conjunct of `OpenLaws`
    obtain ⟨k, hk, hit⟩ := List.mem_flatMap.mp hit
    split at hit
    · rename_i hraw
      rcases List.mem_append.mp hit with hit | hit
      · split at hit
        · rename_i ha
          rw [List.mem_singleton.mp hit]
          exact sat_assocItem h hk (h.law_binary hk hraw (.inl ha)) ((hl k hk hraw).1 ha)
        · exact absurd hit List.not_mem_nil
      · split at hit
        · rename_i hi
          rw [List.mem_singleton.mp hit]
          exact sat_idemItem h hk (h.law_binary hk hraw (.inr hi)) ((hl k hk hraw).2 hi)
        · exact absurd hit List.not_mem_nil
    · exact absurd hit List.not_mem_nil
  rcases List.mem_append.mp hit with hit | hit
  rotate_left
  · obtain ⟨o, ho, hit⟩ := List.mem_flatMap.mp hit
    obtain ⟨kg, hkg, rfl⟩ := List.mem_map.mp hit
    exact sat_ovlEq_fnF h ho hkg
  rcases List.mem_append.mp hit with hit | hit
  · obtain ⟨N, hN, hit⟩ := List.mem_flatMap.mp hit
    rcases List.mem_append.mp hit with hit | hit
    · rcases List.mem_append.mp hit with hit | hit
      · rcases List.mem_append.mp hit with hit | hit
        · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hit
          cases hf : c.fnOvl g with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact sat_funItem h hN hg hf
          | true =>
            obtain ⟨o, ho, rfl, rfl, hov⟩ := fnOvl_gen_fnF h hg hf
            simp only [↓reduceIte, hov, Option.getD_some]
            exact sat_funUnc_ovlF (ovlAtF_of h ho)
        · obtain ⟨g, hg', rfl⟩ := List.mem_map.mp hit
          have hg := (List.mem_filter.mp hg').1
          cases hf : c.fnOvl g with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact sat_injItem h hN hg hf
          | true =>
            obtain ⟨o, ho, rfl, rfl, hov⟩ := fnOvl_gen_fnF h hg hf
            simp only [↓reduceIte, hov, Option.getD_some]
            exact sat_injUnc_ovlF (ovlAtF_of h ho)
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

end AtT

/-- **`SatConsGoal`**: the value model satisfies the constructors' axioms, the law sentences of the
open generators where the interpretation satisfies the laws (`OpenLaws`). -/
theorem satConsGoal (h : HypModelCore c) (hl : OpenLaws c) : SatConsGoal c :=
  AtT.satConsGoal (c := c) (T := StepM c) (h := h) (hl := hl)

end Model

end Faithful

end KCore
