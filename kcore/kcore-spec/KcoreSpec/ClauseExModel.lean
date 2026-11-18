/-
  KCore. A clause with existential variables in the value model.

  The right side of its equation, `(∃ē. (rhs ∧ ens ∧ post)) ∧ ⊤` (`clauseRightEx`), holds at a
  valuation that reads the variables other than ē as values exactly the values the instances of
  the right side give: the value of `rhs` under a well-sorted σ' that is the valuation's
  substitution off ē, with a true `ensures` and `post` true in the value model
  (`AtT.clauseRightEx_read_T`). An equation of a function with any right side holds in the value
  model where, at every valuation of its guards under which its premise holds, the right side holds
  the values `Eval` gives the function at the arguments (`AtT.sat_eqnRightEx`). So the equation of
  a clause with existential variables holds where its premise gives a match under which the
  function's values are the values the instances give, which is what `eval_of_decides_ex`
  concludes where the clause decides (`AtT.sat_eqnClauseEx`): `f(ws)` is the one value an instance
  gives, and `⊥` where no instance gives one.
-/
import KcoreSpec.ClauseExDen
import KcoreSpec.SatRulePP
import KcoreSpec.ModelFnsPre

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **The right side of a clause with existential variables, read at T.** Under a valuation that
reads each variable of the clause but the existential ones as its value under σ, of its sort, an
element of the result sort is in `(∃ē. (rhs ∧ ens ∧ post)) ∧ ⊤` exactly where it is the value of
the right-hand side under a well-sorted σ' that agrees with σ off ē, with a true `ensures` and
`post` true in the value model (`TrueV`). -/
theorem clauseRightEx_read_T (h : HypModelCore c) {fn : Fn} {cl : Clause}
    (hres : fn.result < nRegSorts + c.sortNames.length)
    (hnum : ∀ i < cl.vars.length, cl.vars.getD i 0 < nRegSorts + c.sortNames.length)
    (hlt : ∀ i ∈ cl.exs, i < cl.vars.length) (hnd : cl.exs.Nodup)
    (hrhsOK : TermOK c (· < cl.vars.length) cl.rhs)
    (hensOK : ∀ t, cl.ens = some t → TermOK c (· < cl.vars.length) t)
    (hokQ : c.condOK cl.vars cl.post = true) (hbdQ : Cond.bound c cl.vars.length cl.post = true)
    (hrs : ∀ σ' y, c.WellSorted cl.vars σ' → EvalTerm c σ' cl.rhs (some y) → c.sortOf y = some fn.result)
    {tbl : KoreAML.VarTable} (hkeys : ∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl)
    (hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) (srtOf c fn.result) cl.post), k ∈ tbl)
    {e : Valuation Elem} {σ : Subst}
    (hσ : ∀ i < cl.vars.length, i ∉ cl.exs → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (cl.vars.getD i 0))
    (hvar : ∀ i < cl.vars.length, i ∉ cl.exs → ∀ m,
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c cl.vars) i)).interpret (stdI_T c T) e m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v) (m : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (clauseRightEx c fn cl)).interpret (stdI_T c T) e m ↔
      ∃ σ' y, (∀ i < cl.vars.length, i ∉ cl.exs → σ'.lookup i = σ.lookup i) ∧ c.WellSorted cl.vars σ' ∧
        EvalTerm c σ' cl.rhs (some y) ∧ (∀ t, cl.ens = some t → EvalTerm c σ' t (some (bool true))) ∧
        TrueV c cl.vars.length σ' cl.post ∧ m = .val y := by
  have hn := h.namesK
  let vs := canonVars c cl.vars
  let n := cl.vars.length
  have hnd' : ((clauseExBinders c cl).map fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
    unfold clauseExBinders
    rw [List.map_map]
    exact nodup_map_of_injOn _ (fun i hi j hj he =>
      canonKey_inj (hlt i hi) (hlt j hj) (ev_inj (hkeys i (hlt i hi)) (hkeys j (hlt j hj)) he)) hnd
  have hsrt : ∀ b ∈ clauseExBinders c cl, ∃ n, b.sort = KoreAML.srt n := fun b hb => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    show ∃ n, ((canonVars c cl.vars).getD i default).kore.sort = KoreAML.srt n
    rw [canonVars_getD c (hlt i hi)]; exact ⟨_, rfl⟩
  have hPk : ∀ i, i < n → i < cl.vars.length ∧ canonKey c cl.vars i ∈ tbl := fun i hi => ⟨hi, hkeys i hi⟩
  have hSres : ∀ (e' : Valuation Elem) b, (KoreAML.trSort tbl (srtOf c fn.result)).interpret (stdI_T c T) e' b ↔
      b = .srt fn.result := fun e' b => by unfold srtOf; rw [trSort_srt]; exact sort_den hn hres e' b
  have hresS : KoreAML.IsSort (stdI_T c T) (.srt fn.result) :=
    (isSort_iff _).mpr ⟨fn.result, List.mem_range.mpr hres, rfl⟩
  -- the body under a valuation reading every variable as σ'
  have hbody : ∀ {e' : Valuation Elem} {σ' : Subst} {y : GroundTerm}, c.WellSorted cl.vars σ' →
      c.sortOf y = some fn.result →
      (∀ i, i < n → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e' m ↔
        ∃ v, σ'.lookup i = some v ∧ m = .val v) →
      (((KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c vs)))).interpret
          (stdI_T c T) e' (.val y) ↔ ∀ t, cl.ens = some t → EvalTerm c σ' t (some (bool true))) ∧
       ((∀ φ ∈ Cond.conj c vs (srtOf c fn.result) cl.post,
          (KoreAML.tr ⟨tbl, []⟩ φ).interpret (stdI_T c T) e' (.val y)) ↔ TrueV c n σ' cl.post)) := by
    intro e' σ' y hσ' hys hvar'
    have hinh : KoreAML.Inh (stdI_T c T) (.srt fn.result) (.val y) := (inh_srt _ _).mpr hys
    constructor
    · cases hq : cl.ens with
      | none =>
        simp only [Option.map_none, reqPat]
        rw [KoreAML.tr, KoreAML.interp_sTop defOK_std (by unfold srtOf; rw [trSort_srt]; rfl),
          KoreAML.interp_inhOf_of (hSres e')]
        exact ⟨fun _ t ht => (nomatch ht), fun _ => hinh⟩
      | some t =>
        rw [Option.map_some, reqPat_iff h hvar' (hensOK t hq) (hSres e') hresS (.val y)]
        exact ⟨fun h' t' ht' => by cases ht'; exact h'.2, fun h' => ⟨hinh, h' t rfl⟩⟩
    · have hσs : ∀ i, i < n → ∃ v, σ'.lookup i = some v ∧ c.sortOf v = some (cl.vars.getD i 0) := fun i hi =>
        hσ' i (cl.vars.getD i 0) (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
      by_cases hT : cl.post.isTop = true
      · have hp : cl.post = .top := Cond.eq_top_of_isTop hT
        rw [hp]
        simp only [Cond.conj, Cond.isTop, if_true]
        exact ⟨fun _ => trivial, fun _ φ hφ => absurd hφ List.not_mem_nil⟩
      · have hc : Cond.conj c vs (srtOf c fn.result) cl.post =
            [Cond.kore c vs (srtOf c fn.result) cl.post] := by simp [Cond.conj, hT]
        rw [hc]
        simp only [List.mem_singleton, forall_eq]
        exact trueV_stdI h T cl.post hokQ hbdQ (P := (· < n)) (fun _ _ hl => hl)
          (readsT_of_hvar hPk hσs hvar') hkQ hres (.val y) (show InSort c fn.result (.val y) from hys)
  -- each variable but the existential ones reads as a value of its sort
  have hval : ∀ i < n, i ∉ cl.exs → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (cl.vars.getD i 0) ∧
      e.evalEvar (tbl.ev (canonKey c cl.vars i)) = .val v := by
    intro i hi hx
    obtain ⟨v, hv, hsv⟩ := hσ i hi hx
    obtain ⟨v', hv', he⟩ := (hvar i hi hx (e.evalEvar (tbl.ev (canonKey c cl.vars i)))).mp
      ((AtT.var_read (T := T) i _).mpr rfl)
    rw [hv] at hv'
    cases hv'
    exact ⟨v, hv, hsv, he⟩
  unfold clauseRightEx
  rw [tr_and2, KoreAML.interp_sAnd]
  constructor
  · rintro ⟨hm, -⟩
    obtain ⟨e', hoff, hguard, hb⟩ := existsAll_elim AtT.defOK_std _ e m hnd' hsrt hm
    have hoffK : ∀ i < n, i ∉ cl.exs →
        e'.evalEvar (tbl.ev (canonKey c cl.vars i)) = e.evalEvar (tbl.ev (canonKey c cl.vars i)) := by
      intro i hi hx
      refine hoff _ (fun b hb he => ?_)
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
      have hij : i = j := canonKey_inj hi (hlt j hj) (ev_inj (hkeys i hi) (hkeys j (hlt j hj)) he)
      rw [hij] at hx
      exact hx hj
    have hin : ∀ i < n, InSort c (cl.vars.getD i 0) (e'.evalEvar (tbl.ev (canonKey c cl.vars i))) := by
      intro i hi
      by_cases hx : i ∈ cl.exs
      · exact (AtT.inhOf_sort (T := T) hn (hnum i hi) KoreAML.val0 _).mp
          (hguard _ (List.mem_map_of_mem (f := fun i => ((canonVars c cl.vars).getD i default).kore) hx) _
            (by show (vs.getD i default).kore.sort = _; rw [canonVars_getD c hi]; rfl))
      · obtain ⟨v, -, hsv, he⟩ := hval i hi hx
        rw [hoffK i hi hx, he]
        exact hsv
    obtain ⟨hσ', hvar'⟩ := AtT.substE_ok (T := T) hin
    unfold clauseRhsBody at hb
    obtain ⟨hb1, hb2, hb3⟩ := (interp_bodyPP _ _ _ _ _ _).mp hb
    obtain ⟨y, hy, rfl⟩ := (AtT.tr_term h hvar' hrhsOK m).mp hb1
    have hys := hrs _ _ hσ' hy
    obtain ⟨hE, hQ⟩ := hbody hσ' hys hvar'
    refine ⟨substE c tbl cl.vars e', y, fun i hi hx => ?_, hσ', hy, hE.mp hb2, hQ.mp hb3, rfl⟩
    obtain ⟨v, hv, -, he⟩ := hval i hi hx
    rw [substE_lookup hi, hoffK i hi hx, he, hv]
    rfl
  · rintro ⟨σ', y, hag, hσ', hy, hens, hpo, rfl⟩
    have hk' : ∀ i < n, i ∈ cl.exs → canonKey c cl.vars i ∈ tbl := fun i hi _ => hkeys i hi
    let f : Nat → Elem := fun j => .val ((σ'.lookup j).getD default)
    let e' := setV c tbl cl.vars cl.exs f e
    have hvar' : ∀ i, i < n → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e' m ↔
        ∃ v, σ'.lookup i = some v ∧ m = .val v := by
      intro i hi m
      rw [AtT.var_read]
      show m = (setV c tbl cl.vars cl.exs f e).evalEvar (tbl.ev (canonKey c cl.vars i)) ↔ _
      by_cases hx : i ∈ cl.exs
      · rw [setV_on hk' hi hx]
        obtain ⟨w, hw, -⟩ := hσ' i (cl.vars.getD i 0)
          (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
        simp [f, hw]
      · obtain ⟨v, hv, -, he⟩ := hval i hi hx
        rw [setV_off hk' hi hx, hag i hi hx, he, hv]
        simp
    have hys := hrs _ _ hσ' hy
    obtain ⟨hE, hQ⟩ := hbody hσ' hys hvar'
    refine ⟨AtT.existsAll_intro _ e e' _ hnd' hsrt (fun z hz => ?_) rfl (fun b hb k hk => ?_) ?_, ?_⟩
    · show (if h : _ then _ else _) = _
      rw [dif_neg]
      rintro ⟨i, -, hix, rfl⟩
      exact hz _ (List.mem_map_of_mem (f := fun i => ((canonVars c cl.vars).getD i default).kore) hix) rfl
    · obtain ⟨i, hix, rfl⟩ := List.mem_map.mp hb
      have hi := hlt i hix
      have hs' : ((canonVars c cl.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (cl.vars.getD i 0)) := by
        rw [canonVars_getD c hi]; rfl
      change ((canonVars c cl.vars).getD i default).kore.sort = KoreAML.srt k at hk
      rw [hs'] at hk
      rw [← srt_inj hk]
      show InS (stdI_T c T) _ ((setV c tbl cl.vars cl.exs f e).evalEvar (tbl.ev (canonKey c cl.vars i)))
      rw [setV_on hk' hi hix]
      obtain ⟨w, hw, hws⟩ := hσ' i (cl.vars.getD i 0)
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
      show InS (stdI_T c T) _ (Elem.val ((σ'.lookup i).getD default))
      rw [hw, Option.getD_some]
      exact (AtT.inhOf_sort (T := T) hn (hnum i hi) KoreAML.val0 _).mpr hws
    · unfold clauseRhsBody
      exact (interp_bodyPP _ _ _ _ _ _).mpr ⟨(AtT.tr_term h hvar' hrhsOK _).mpr ⟨y, hy, rfl⟩, hE.mpr hens, hQ.mpr hpo⟩
    · simp only [reqPat]
      rw [KoreAML.tr, KoreAML.interp_sTop defOK_std (by unfold srtOf; rw [trSort_srt]; rfl),
        KoreAML.interp_inhOf_of (hSres e)]
      exact (inh_srt _ _).mpr hys

/-- **An equation of a function with any right side holds in the value model** where, at every
valuation of its guards under which its premise holds, the right side holds, among the elements of
the result sort, the values `Eval` gives the function at the arguments. The guards give an element
of its sort to each variable that is free in the axiom (`free`); a variable the right side binds
is not asked one. `sat_eqnCl` for a right side that is not `rhs ∧ ens`. -/
theorem sat_eqnRightEx (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {vars : List Srt} {free : Nat → Prop}
    (hnum : ∀ i < vars.length, free i → vars.getD i 0 < nRegSorts + c.sortNames.length)
    {prem right : Kore.Pattern}
    (hV : ∀ i < vars.length, free i →
      canonKey c vars i ∈ KoreAML.freeOf [] (.implies KoreAML.R prem (eqConclEx c fn right)))
    (hread : ∀ (tbl : KoreAML.VarTable) (e : Valuation Elem) (ws : List GroundTerm) (a : Elem),
      KoreAML.VarKey.sortVar "R" ∈ tbl →
      (∀ k ∈ KoreAML.varsOf (.implies KoreAML.R prem (eqConclEx c fn right)), k ∈ tbl) →
      KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) → ArgsAt c tbl e fn.args ws →
      (∀ i < vars.length, free i → InSort c (vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c vars i)))) →
      KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a →
      (KoreAML.tr ⟨tbl, []⟩ prem).interpret (stdI_T c T) e a →
      ∀ b, InSort c fn.result b →
        ((KoreAML.tr ⟨tbl, []⟩ right).interpret (stdI_T c T) e b ↔ ∃ v, b = .val v ∧ Eval c fn.label ws (some v))) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv],
      .implies KoreAML.R prem (eqConclEx c fn right), []⟩ : Kore.Axiom)⟩).pat := by
  have hn := h.namesK
  have hfs := h.fnSorts hfn
  intro e m
  unfold KoreAML.trAxiom
  dsimp only
  have hsortP : KoreAML.sortOf [] (.implies KoreAML.R prem (eqConclEx c fn right)) =
      some KoreAML.R := rfl
  simp only [hsortP]
  rw [interpret_impl]
  intro hgs
  generalize hP : (Kore.Pattern.implies KoreAML.R prem (eqConclEx c fn right)) = P at hgs ⊢
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
    unfold eqConclEx
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
    unfold eqConclEx
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
  have hvin : ∀ i < vars.length, free i →
      InSort c (vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c vars i))) := by
    intro i hi hfi
    have hk : canonKey c vars i ∈ KoreAML.freeOf [] P := hP ▸ hV i hi hfi
    have hg := hguard _ (hfreeP _ hk)
    have hkk := canonKey_eq c hi
    rw [hkk, KoreAML.interp_guard_evar defOK_std, trSort_srt, ← hkk] at hg
    exact (inhOf_sort hn (hnum i hi hfi) e _).mp hg
  have hres := hfs fn.result (List.mem_cons_self ..)
  rw [KoreAML.interp_equal defOK_std]
  intro a
  have hPtr : KoreAML.tr ⟨tbl, []⟩ P = KoreAML.sImp (KoreAML.trSort tbl KoreAML.R) (KoreAML.tr ⟨tbl, []⟩ prem)
      (KoreAML.tr ⟨tbl, []⟩ (eqConclEx c fn right)) := by
    rw [← hP, KoreAML.tr]
  rw [hPtr, KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun hprem => ?_⟩
    rw [KoreAML.interp_inhOf_of (R_read e)] at ha
    have hSres : ∀ b, (KoreAML.trSort tbl (KoreAML.srt (c.sortName fn.result))).interpret (stdI_T c T) e b ↔
        b = .srt fn.result := fun b => by rw [trSort_srt]; exact sort_den hn hres e b
    unfold eqConclEx
    rw [KoreAML.tr, KoreAML.interp_sEquals defOK_std sat_ceilDef hSres (R_read e)
      ((isSort_iff _).mpr ⟨fn.result, List.mem_range.mpr hres, rfl⟩) hRs]
    refine ⟨ha, fun b hb => ?_⟩
    rw [inh_srt] at hb
    rw [call_read h hfn hws.sorts hws.X]
    exact (hread tbl e ws a hRmem (fun k hk => hvarsP k (hP ▸ hk)) hRs hws hvin ha hprem b hb).symm

/-- **The equation of a clause with existential variables holds in the value model**, under any
premise, where at every valuation of the guards under which the premise holds there is a match σ,
which the valuation reads on the variables other than the existential ones, under which the
function's values are the values the instances of the right side give (`hprem`; what
`eval_of_decides_ex` concludes where the clause decides under σ). The right side's predicate has
a truth value at every well-sorted substitution (`hpostDec`). So `f` at the arguments is the value
an instance gives, and has no element where no instance gives one. -/
theorem sat_eqnClauseEx (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} {prem : Kore.Pattern}
    (hnum : ∀ i < cl.vars.length, cl.vars.getD i 0 < nRegSorts + c.sortNames.length)
    (hlt : ∀ i ∈ cl.exs, i < cl.vars.length) (hnd : cl.exs.Nodup)
    (hrhsOK : TermOK c (· < cl.vars.length) cl.rhs)
    (hensOK : ∀ t, cl.ens = some t → TermOK c (· < cl.vars.length) t)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hokQ : c.condOK cl.vars cl.post = true) (hbdQ : Cond.bound c cl.vars.length cl.post = true)
    (hrs : ∀ σ' y, c.WellSorted cl.vars σ' → EvalTerm c σ' cl.rhs (some y) → c.sortOf y = some fn.result)
    (hpostDec : ∀ σ', c.WellSorted cl.vars σ' → ∃ b, Holds c cl.vars.length σ' cl.post b)
    (hV : ∀ i < cl.vars.length, i ∉ cl.exs → canonKey c cl.vars i ∈
      KoreAML.freeOf [] (.implies KoreAML.R prem (eqConclEx c fn (clauseRightEx c fn cl))))
    (hVv : ∀ i < cl.vars.length, canonKey c cl.vars i ∈
      KoreAML.varsOf (.implies KoreAML.R prem (eqConclEx c fn (clauseRightEx c fn cl))))
    (hprem : ∀ (tbl : KoreAML.VarTable) (e : Valuation Elem) (ws : List GroundTerm) (a : Elem),
      KoreAML.VarKey.sortVar "R" ∈ tbl →
      (∀ k ∈ KoreAML.varsOf (.implies KoreAML.R prem (eqConclEx c fn (clauseRightEx c fn cl))), k ∈ tbl) →
      KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) → ArgsAt c tbl e fn.args ws →
      (∀ i < cl.vars.length, i ∉ cl.exs →
        InSort c (cl.vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c cl.vars i)))) →
      KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a →
      (KoreAML.tr ⟨tbl, []⟩ prem).interpret (stdI_T c T) e a →
      ∃ σ, (∀ i < cl.vars.length, i ∉ cl.exs → ∃ v, σ.lookup i = some v ∧
          e.evalEvar (tbl.ev (canonKey c cl.vars i)) = .val v) ∧
        ∀ v, Eval c fn.label ws (some v) ↔
          ∃ σ', AgreeOff cl.exs σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v) :
    stdI_T c T ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv],
      .implies KoreAML.R prem (eqConclEx c fn (clauseRightEx c fn cl)), []⟩ : Kore.Axiom)⟩).pat := by
  have hres := h.fnSorts hfn fn.result (List.mem_cons_self ..)
  refine sat_eqnRightEx h hfn (free := fun i => i ∉ cl.exs) (fun i hi _ => hnum i hi) hV
    fun tbl e ws a hR hk hRs hws hvin ha hp b hb => ?_
  obtain ⟨σ, hσe, hsolve⟩ := hprem tbl e ws a hR hk hRs hws hvin ha hp
  have hkeys : ∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl := fun i hi => hk _ (hVv i hi)
  have hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) (srtOf c fn.result) cl.post), k ∈ tbl := by
    intro k hk'
    cases hpt : cl.post.isTop with
    | false =>
      refine hk k (varsOf_body_inAxEx (varsOf_existsAll_bodyEx ?_ _))
      unfold clauseRhsBody
      exact varsOf_and_mem (by simp [Cond.conj, hpt]) hk'
    | true =>
      rw [Cond.eq_top_of_isTop hpt] at hk'
      simp [Cond.kore, KoreAML.varsOf, srtOf, KoreAML.srt, KoreAML.sortVarsOf, KoreAML.sortVarsOfList] at hk'
  have hσ : ∀ i < cl.vars.length, i ∉ cl.exs →
      ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (cl.vars.getD i 0) := fun i hi hx => by
    obtain ⟨v, hv, he⟩ := hσe i hi hx
    have := hvin i hi hx
    rw [he] at this
    exact ⟨v, hv, this⟩
  have hvar : ∀ i < cl.vars.length, i ∉ cl.exs → ∀ m,
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c cl.vars) i)).interpret (stdI_T c T) e m ↔
        ∃ v, σ.lookup i = some v ∧ m = .val v := fun i hi hx m => by
    obtain ⟨v, hv, he⟩ := hσe i hi hx
    rw [AtT.var_read]
    show m = e.evalEvar (tbl.ev (canonKey c cl.vars i)) ↔ _
    rw [he, hv]
    simp
  rw [clauseRightEx_read_T h hres hnum hlt hnd hrhsOK hensOK hokQ hbdQ hrs hkeys hkQ hσ hvar b]
  constructor
  · rintro ⟨σ', y, hag, hσ', hy, hens, hpo, rfl⟩
    refine ⟨y, rfl, (hsolve y).mpr ?_⟩
    have hl₁ : ∀ j, j < cl.vars.length → ∃ v, σ'.lookup j = some v := fun j hj => by
      obtain ⟨v, hv, -⟩ := hσ' j (cl.vars.getD j 0)
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl)
      exact ⟨v, hv⟩
    have hl₂ : ∀ j, j < cl.vars.length →
        (((List.range cl.vars.length).map fun j => (j, (σ'.lookup j).getD default)) ++ σ).lookup j = σ'.lookup j :=
      fun j hj => by
        obtain ⟨v, hv⟩ := hl₁ j hj
        simp [CE.lookup_overEV, hj, hv]
    obtain ⟨bq, hbq⟩ := hpostDec σ' hσ'
    have hbt : bq = true := (holds_trueV h.det hbq).mp hpo
    subst hbt
    refine ⟨((List.range cl.vars.length).map fun j => (j, (σ'.lookup j).getD default)) ++ σ, fun i hx => ?_,
      fun i s hs => ?_, ?_, fun t ht => ?_, ?_⟩
    · by_cases hil : i < cl.vars.length
      · rw [hl₂ i hil]; exact hag i hil hx
      · simp [CE.lookup_overEV, hil]
    · rw [hl₂ i (List.getElem?_eq_some_iff.mp hs).1]; exact hσ' i s hs
    · exact Exec.EvalTerm.congr hy fun i hi => (hl₂ i (hrhsv i hi)).symm
    · exact Exec.EvalTerm.congr (hens t ht) fun i hi => (hl₂ i (hensv t ht i hi)).symm
    · exact Holds.congr_NI hbq fun j hj => (hl₂ j (varOccsCond_lt_twoT cl.post hokQ j hj)).symm
  · rintro ⟨v, rfl, hE⟩
    obtain ⟨σ', ha', hw, grhs, gens, gpost⟩ := (hsolve v).mp hE
    exact ⟨σ', v, fun i _ hx => ha' i hx, hw, grhs, gens, (holds_trueV h.det gpost).mpr rfl, rfl⟩

end AtT

end Model

end Faithful

end KCore
