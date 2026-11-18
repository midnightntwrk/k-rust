/-
  A text `coreOKEx` accepts whose Γ has no model, with `FnDet`, `FnSolves`, `ClausePreDecided` and
  `OpenLaws`: the hypotheses of `consistent_of` other than its checker do not give `Consistent` of a
  text `coreOKEx` accepts. `consistent_of_coreEx` takes `ClausePostDecided` beside them, which the
  text lacks.

  The text `cCeU` has one function, `f() => ?B:Bool` with the right-side predicate `¬ (B ∈ f())`.
  Bool is a confined sort, so `clausePlainEx` holds of the clause (`cCeU_coreOKEx`).
  - `f_none`, `fC_none`, `post_undecided`: `f()` has no result and the predicate no truth value: a
    derivation of either holds a shorter one of the other. So `fnDet` and `fnSolves` hold with both
    sides empty; `preDecided` and `openLaws` hold as the predicate of the premise is `\top` and the
    text has no open generator.
  - `clause_rawEx`: the equation of a clause with existential variables and no clause of a smaller
    priority, read in a model: the elements of `f(ws)` are the elements of the result sort in
    `(∃ē. (rhs ∧ ens ∧ post)) ∧ ⊤`.
  - `body_read`: the body `B ∧ ⊤ ∧ ¬ (B ∈ f())` at a valuation holds `m` exactly where `m` is B's
    element and B's element is not in `f()`.
  - `no_model`: in a model of Γ the element of `true` is in `f()` exactly where it is not.
  - `not_consistent`, `coreEx_not_consistent`.
-/
import KcoreSpec.HypModelCoreEx
import KcoreSpec.ClauseExDenCEx
import KcoreSpec.CoreDecide

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.CeNoModel
open KCore GroundTerm Faithful Faithful.Model ML
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)


def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]
def base : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }
def fC : Sym := nRegSyms + 4
/-- `f() => ?B:Bool` with the right-side predicate `¬ (B ∈ f())`. -/
def clR : Clause :=
  { vars := [Srt.bool], pats := [], req := none, rhs := .var 0, ens := none, exs := [0],
    post := .not (.mem Srt.bool (.var 0) (.app fC [])) }
def fnR : Fn := { label := fC, args := [], result := Srt.bool, clauses := [clR] }
def cCeU : Semantics := { base with symNames := base.symNames ++ ["Lblf"], fns := [fnR] }

theorem cCeU_coreOKEx : cCeU.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap

theorem lookup_fC : cCeU.lookupFn fC = some fnR := by rw [Semantics.lookupFn_eq]; rfl
section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The equation of a clause with existential variables and no clause of a smaller priority, read
in a model: the elements of `f(ws)` are the elements of the result sort in the right side. -/
theorem clause_rawEx (hI : I ⊧ᴵP Γ c) (hnn : NamesNumbered c) (hsc : SortCtx c) [OvlOK c]
    (hph : patHooksApart c = true) {f : Sym} {fn : Fn} {cl : Clause} {ws : List GroundTerm} {σ' : Subst}
    (hfn : c.lookupFn f = some fn) (hcl : cl ∈ fn.clauses) (hlow' : lowerClauses fn cl = [])
    (hws : c.sortsOf ws = some fn.args) (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hpreOK : c.condOK cl.vars cl.pre = true) (hokQ : c.condOK cl.vars cl.post = true)
    (hne : cl.exs ≠ []) (hlt : ∀ i ∈ cl.exs, i < cl.vars.length)
    (hocc : ∀ i < cl.vars.length, i ∈ cl.exs ∨ i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post)
    (hreq : cl.req = none) (hpre : cl.pre.isTop = true)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (e0 : Valuation M) :
    ∃ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e' ∧
      (∀ i < cl.vars.length, canonKey c cl.vars i ∈ tbl) ∧
      (∀ k ∈ KoreAML.varsOf (clauseRhsBody c fn cl), k ∈ tbl) ∧
      ∀ m, (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e0 m ↔
        InS I (c.sortName fn.result) m ∧ (KoreAML.tr ⟨tbl, []⟩ (clauseRightEx c fn cl)).interpret I e' m := by
  have hfnm := (lookupFn_spec hfn).1
  have hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => by rw [hreq] at ht; cases ht
  have hpatsN := Semantics.pats_nf (OvlOK.hyp inferInstance hsc.trans) hfnm hcl hpats
  have hv := premise_varsCl (c := c) hpats hreqv
  have htr := hsc.trans
  have hmem := clauseEquation_mem (c := c) hcl hlow'
  unfold clauseEquation at hmem
  rw [clauseRhs_eqEx hne hlt] at hmem
  have hP : ∀ k, k ∈ KoreAML.varsOf (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) →
      k ∈ KoreAML.varsOf (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) := fun _ h => h
  have hVin := clause_keys_inAxEx (prem := withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) hpats hreqv hocc hP
  obtain ⟨tbl, e', hk, -, hag, hiff⟩ := eqn_atRightEx hI hnn hfn (eqn_item_mem hfnm hmem) hws hσ'
    (fun j s hj => HoldsShape.varsOf_withPre_prem (hv.1 j s hj)) hVin
    (fun k hk => freeOf_withPreCl hpreOK hpats hreqv hk)
    (fun k hk => freeOf_clauseRightEx hrhsv hensv hokQ hk)
    (fun tbl e σr m0 hk hag hX hRv hσr2 hm0 =>
        withPre_holdsCl (premise_holds4 hI hnn hph htr hfnm hws hσ' hmatch hpatsN hag hX hRv hσr2 hm0
          (fun t ht => by rw [hreq] at ht; cases ht))
          hk (fun hpt => by rw [hpre] at hpt; cases hpt)) e0
  exact ⟨tbl, e', hag, fun i hi => hk _ (hVin i hi),
    fun k hk' => hk _ (varsOf_body_inAxEx (Model.varsOf_existsAll_bodyEx hk' _)), hiff⟩

end

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The elements of `f()`. -/
def F (I : Interpretation KoreAML.Sym M) (m : M) : Prop :=
  (KoreAML.den (symApp cCeU fC (GroundTerm.koreList cCeU []))).interpret I KoreAML.val0 m

abbrev keyB : VarKey := canonKey cCeU clR.vars 0

theorem body_read (hI : I ⊧ᴵP Γ cCeU) {tbl : VarTable} {e : Valuation M} {m : M}
    (hB : InS I (cCeU.sortName Srt.bool) (e.evalEvar (tbl.ev keyB))) (hm : InS I (cCeU.sortName Srt.bool) m) :
    (KoreAML.tr ⟨tbl, []⟩ (clauseRhsBody cCeU fnR clR)).interpret I e m ↔
      m = e.evalEvar (tbl.ev keyB) ∧ ¬ F I (e.evalEvar (tbl.ev keyB)) := by
  haveI : OvlOK cCeU := (hypSoundEx_of_coreEx cCeU_coreOKEx).2.2.2.2.2.2.2.2
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cCeU))
  obtain ⟨σr, hσr1, hσr2⟩ := sortSing hI (c := cCeU) (s := Srt.bool) (by decide)
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf cCeU Srt.bool)).interpret I e b ↔ b = σr := by
    unfold srtOf; rw [trSort_srt]; exact hσr1
  have hinh : ∀ {a : M}, InS I (cCeU.sortName Srt.bool) a → Inh I σr a := fun {a} ha =>
    (KoreAML.interp_inhOf_of (S := KoreAML.sym _) (e := e) hσr1).mp ((inS_iff e).mpr ha)
  have hb : clauseRhsBody cCeU fnR clR = .and (srtOf cCeU Srt.bool)
      [Term.kore cCeU (canonVars cCeU clR.vars) (.var 0), reqPat (srtOf cCeU Srt.bool) none,
       .not (srtOf cCeU Srt.bool) (.in (srtOf cCeU Srt.bool) (srtOf cCeU Srt.bool)
         (Term.kore cCeU (canonVars cCeU clR.vars) (.var 0)) (symApp cCeU fC []))] := rfl
  have hF : ∀ a, (KoreAML.tr ⟨tbl, []⟩ (symApp cCeU fC [])).interpret I e a ↔ F I a := fun a => by
    show _ ↔ (KoreAML.den (symApp cCeU fC [])).interpret I KoreAML.val0 a
    unfold KoreAML.den
    rw [tr_symApp, tr_symApp]
    exact (symHead_closed (c := cCeU) fC).interp e KoreAML.val0 a
  have htop : (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf cCeU Srt.bool) none)).interpret I e m := by
    simp only [reqPat]
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hS]
    exact hinh hm
  have hvar : ∀ a, (KoreAML.tr ⟨tbl, []⟩ (Term.kore cCeU (canonVars cCeU clR.vars) (.var 0))).interpret I e a ↔
      a = e.evalEvar (tbl.ev keyB) := fun a => tr_var 0 a
  rw [hb, tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd, hvar]
  rw [KoreAML.tr, KoreAML.interp_sNot, KoreAML.tr,
    KoreAML.interp_sIn hD hc hS hS hσr2 hσr2 (fun a ha => by rw [(hvar a).mp ha]; exact hinh hB) m,
    KoreAML.interp_inhOf_of hS]
  constructor
  · rintro ⟨h1, -, h2, -⟩
    exact ⟨h1, fun hf => h2 ⟨⟨_, (hvar _).mpr rfl, (hF _).mpr hf⟩, hinh hm⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, htop, fun ⟨⟨a, ha, hfa⟩, _⟩ => h2 (by rw [← (hvar a).mp ha]; exact (hF a).mp hfa), hinh hm⟩

/-- **Γ of the text has no model**: its one equation states that the elements of `f()` are the
Bool elements that are not elements of `f()`, and `true`'s element is a Bool element. -/
theorem no_model (hI : I ⊧ᴵP Γ cCeU) : False := by
  obtain ⟨hok, hsr, hnn, hg, hph, -, -, -, hno⟩ := hypSoundEx_of_coreEx cCeU_coreOKEx
  haveI : OvlOK cCeU := hno
  have hsc := sortCtx_of_allCEx hok hsr (Semantics.ovlCase_of_coreEx cCeU_coreOKEx)
  have hD := defOK hI
  have hst : cCeU.sortOf (bool true) = some Srt.bool := by decide
  have hσ' : cCeU.WellSorted clR.vars [(0, bool true)] := fun i t hi => by
    match i, hi with
    | 0, hi => simp only [clR, List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact ⟨bool true, rfl, hst⟩
    | _ + 1, hi => simp [clR] at hi
  obtain ⟨tbl, e', hag, hkeys, hkB, hiff⟩ := clause_rawEx hI hnn hsc hph (f := fC) (fn := fnR) (cl := clR)
    (ws := []) (σ' := [(0, bool true)]) lookup_fC (by simp [fnR]) (by decide) (by decide) hσ' .nil
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) KoreAML.val0
  have htt := elemOf_spec hI hst e'
  have hinT : InS I (cCeU.sortName Srt.bool) (elemOf cCeU I (bool true)) := (inS_iff e').mp htt.2
  have hBe : e'.evalEvar (tbl.ev keyB) = elemOf cCeU I (bool true) :=
    ((htt.1 _).mp ((hag 0 (bool true) (by rw [canonVars_length]; decide) rfl _).mp rfl))
  have hlt : ∀ i ∈ clR.exs, i < clR.vars.length := by decide
  have hndB := binders_nodupEx hkeys hlt (l := clR.exs) (by decide)
  have hsB := binders_sortEx (c := cCeU) (vars := clR.vars) hlt
  have hsort : ∀ i ∈ clR.exs,
      ((canonVars cCeU clR.vars).getD i default).kore.sort = KoreAML.srt (cCeU.sortName (clR.vars.getD i 0)) :=
    fun i hi => by rw [canonVars_getD cCeU (hlt i hi)]; rfl
  have h0 : (0 : Nat) ∈ clR.exs := by decide
  have hright : ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRightEx cCeU fnR clR)).interpret I e' m →
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll (srtOf cCeU fnR.result) (clauseExBinders cCeU clR)
        (clauseRhsBody cCeU fnR clR))).interpret I e' m := fun m h => by
    unfold clauseRightEx at h
    rw [tr_and2, KoreAML.interp_sAnd] at h
    exact h.1
  by_cases hF : F I (elemOf cCeU I (bool true))
  · obtain ⟨e'', -, hguard, hbody⟩ := existsAll_elim hD (clauseExBinders cCeU clR) e' _ hndB hsB
      (hright _ ((hiff _).mp hF).2)
    have hB'' : InS I (cCeU.sortName Srt.bool) (e''.evalEvar (tbl.ev keyB)) :=
      hguard _ (List.mem_map_of_mem (f := fun i => ((canonVars cCeU clR.vars).getD i default).kore) h0) _ (hsort 0 h0)
    obtain ⟨h1, h2⟩ := (body_read hI hB'' hinT).mp hbody
    exact h2 (h1 ▸ hF)
  · refine hF ((hiff _).mpr ⟨hinT, ?_⟩)
    obtain ⟨σr, hσr1, hσr2⟩ := sortSing hI (c := cCeU) (s := Srt.bool) (by decide)
    have hS : ∀ b, (KoreAML.trSort tbl (srtOf cCeU Srt.bool)).interpret I e' b ↔ b = σr := by
      unfold srtOf; rw [trSort_srt]; exact hσr1
    unfold clauseRightEx
    rw [tr_and2, KoreAML.interp_sAnd]
    refine ⟨existsAll_intro_at hD (clauseExBinders cCeU clR) e' e' _ hndB hsB (fun _ _ => rfl) rfl (fun b hb n hn => ?_)
      ((body_read hI (hBe ▸ hinT) hinT).mpr ⟨hBe.symm, by rw [hBe]; exact hF⟩), ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      have hi0 : i = 0 := by simpa [clR] using hi
      subst hi0
      rw [hsort 0 h0] at hn
      rw [← srt_inj hn]
      exact hBe ▸ hinT
    · show (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf cCeU Srt.bool) none)).interpret I e' _
      simp only [reqPat]
      rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl)]
      show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf cCeU Srt.bool))).interpret I e' _
      rw [KoreAML.interp_inhOf_of hS]
      exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) (e := e') hσr1).mp ((inS_iff e').mpr hinT)
end

/-- **`Consistent` is false of the text.** -/
theorem not_consistent : ¬ Consistent cCeU :=
  fun ⟨_, _, _, hI⟩ => no_model fun φ hφ => hI φ (Or.inl (Or.inl hφ))


/-! ## The hypotheses of `consistent_of` hold of the text -/

theorem fC_flags : cCeU.isCtor fC = false ∧ isHook fC = false ∧ cCeU.isParam fC = false ∧
    cCeU.isOvl fC = false := by decide +kernel

/-- **`f()` has no result as a term**: each derivation of it holds a shorter one, through the truth
value of the predicate. -/
theorem f_none {σ : Subst} {r : Option GroundTerm} : ¬ EvalTerm cCeU σ (.app fC []) r := by
  obtain ⟨hk, hh, hp, ho⟩ := fC_flags
  intro hv
  exact EvalTerm.rec (c := cCeU)
    (motive_1 := fun f vs _ _ => f = fC → vs = [] → False)
    (motive_2 := fun _ _ _ => True) (motive_3 := fun _ _ _ => True)
    (motive_4 := fun _ t _ _ => t = .app fC [] → False)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ p _ _ => (p = clR.post ∨ p = .mem Srt.bool (.var 0) (.app fC [])) → False)
    (motive_7 := fun _ _ _ => True) (motive_8 := fun _ cl _ _ => cl = clR → False)
    (fun {_ _ _ _ _ _} hfn hmem _ _ _ _ _ hex _ _ _ _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [lookup_fC] at hfn; cases hfn
      change _ ∈ [clR] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      cases hex)
    (fun hfn hnone _ => fun hf hvs => by
      subst hf; subst hvs
      rw [lookup_fC] at hfn; cases hfn
      cases hnone clR (by simp [fnR]) with
      | intro h =>
        cases h [] (fun i hi => by simp [Clause.leftVars, Clause.condVars, clR, varOccsList, varOccsCond] at hi) .nil with
        | intro ht _ _ => cases ht
        | pre hp => exact absurd (Holds.top_eq hp) (by simp))
    (fun {_ _ _ _ _ _ _} hfn hmem _ _ _ _ _ hex _ _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [lookup_fC] at hfn; cases hfn
      change _ ∈ [clR] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      cases hex)
    (fun {_ _ _ _ _ _} hfn hmem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihpost _ => fun hf hvs => by
      subst hf; subst hvs
      rw [lookup_fC] at hfn; cases hfn
      change _ ∈ [clR] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact ihpost (Or.inl rfl))
    (fun {_ _ _ _ _} hfn hmem _ _ _ _ _ _ hsome _ _ _ _ ihall => fun hf hvs => by
      subst hf; subst hvs
      rw [lookup_fC] at hfn; cases hfn
      change _ ∈ [clR] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      obtain ⟨σ', ha, hw⟩ := hsome
      exact ihall σ' ha hw rfl)
    (fun _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ => trivial)
    (fun h => by cases h) (fun h => by cases h) (fun _ _ h => by cases h)
    (fun hk' _ _ h => by cases h; rw [hk] at hk'; cases hk')
    (fun _ hhk _ _ _ _ h => by cases h; rw [hh] at hhk; cases hhk)
    (fun _ _ hp' _ _ _ h => by cases h; rw [hp] at hp'; cases hp')
    (fun _ _ hts hvs _ _ _ ihf h => by
      cases h
      cases hts
      simp only [allSome, Option.some.injEq] at hvs
      exact ihf rfl hvs.symm)
    (fun _ _ hts hvs _ _ h => by
      cases h
      cases hts
      simp [allSome] at hvs)
    (fun _ ho' _ _ _ h => by cases h; rw [ho] at ho'; cases ho')
    (fun _ ho' _ _ _ _ _ _ _ h => by cases h; rw [ho] at ho'; cases ho')
    trivial (fun _ _ _ _ => trivial)
    (by intros; rename_i h; rcases h with h | h <;> cases h)
    (by intros; rename_i h; rcases h with h | h <;> cases h)
    (by intros; rename_i ih h; rcases h with h | h
        · cases h; exact ih (Or.inr rfl)
        · cases h)
    (by intros; rename_i h; rcases h with h | h <;> cases h)
    (by intros; rename_i h; rcases h with h | h <;> cases h)
    (by intros; rename_i h; rcases h with h | h <;> cases h)
    (by intros; rename_i h; rcases h with h | h <;> cases h)
    (by intros; rename_i h; rcases h with h | h <;> cases h)
    (by intros; rename_i ih1 ih2 h; rcases h with h | h
        · cases h
        · cases h; exact ih2 rfl)
    (by intros; rename_i h; rcases h with h | h <;> cases h)
    (by intros; rename_i h; rcases h with h | h <;> cases h)
    (by intros; rename_i h; rcases h with h | h <;> cases h)
    (by intros; rename_i h; rcases h with h | h <;> cases h)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; rename_i ihp _ hcl; subst hcl; exact ihp (Or.inl rfl))
    (by intros; rename_i ihp hcl; subst hcl; exact ihp (Or.inl rfl))
    hv rfl

/-- At no σ has the clause's predicate a truth value. -/
theorem post_undecided (σ : Subst) (b : Bool) : ¬ Holds cCeU 1 σ clR.post b := by
  intro h
  cases h with
  | not h =>
    cases h with
    | mem _ h' => exact f_none h'

theorem not_inst (σ : Subst) (r : Option GroundTerm) : ¬ InstIs cCeU σ clR r := by
  intro h
  cases h with
  | fails hp _ => exact post_undecided _ _ hp
  | gives _ _ hp => exact post_undecided _ _ hp

theorem clR_noRes (σ : Subst) (r : Option GroundTerm) : ¬ Clause.Res cCeU clR σ r := by
  rintro (⟨hex, -⟩ | ⟨-, (⟨σ', v, -, -, hg, -, -⟩ | ⟨-, ⟨σ', ha, hw⟩, hall⟩)⟩)
  · exact absurd hex (by decide)
  · exact post_undecided _ _ hg.2.2
  · exact not_inst _ _ (hall σ' ha hw)

/-- **`f()` has no result at all.** -/
theorem fC_none {r : Option GroundTerm} : ¬ Eval cCeU fC [] r := fun h =>
  f_none (σ := []) (EvalTerm.call fC_flags.1 fC_flags.2.1 .nil rfl h fC_flags.2.2.1)

theorem mem_fns {fn : Fn} (h : fn ∈ cCeU.fns) : fn = fnR := by simpa [cCeU] using h

theorem sortsOf_nil {vs : List GroundTerm} (h : cCeU.sortsOf vs = some []) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    rw [Semantics.sortsOf] at h
    split at h <;> cases h

/-- **Every function of the text has at most one result**: `f` has none. -/
theorem fnDet : FnDet cCeU :=
  fnDet_of_coherent (coherentAll_ofSelfCEx
    (fun fn hfn => by
      obtain rfl := mem_fns hfn
      intro a b hp _
      simp [fnR, pairs] at hp)
    (fun fn hfn cl hcl => by
      obtain rfl := mem_fns hfn
      simp only [fnR, List.mem_singleton] at hcl; subst hcl
      exact fun _ σ _ _ _ _ _ _ _ _ => .inr fun r _ hr _ => absurd hr (clR_noRes σ r)))

/-- **Evaluation solves the equation of the text**: both sides are empty. -/
theorem fnSolves : FnSolves cCeU := by
  intro fn hfn vs hvs cl hcl σ hdec v
  obtain rfl := mem_fns hfn
  simp only [fnR, List.mem_singleton] at hcl; subst hcl
  have h0 : vs = [] := sortsOf_nil hvs
  subst h0
  exact ⟨fun h => absurd h fC_none, fun ⟨_, _, _, hg⟩ => absurd hg.2.2 (post_undecided _ _)⟩

theorem preDecided : ClausePreDecided cCeU := clausePreDecided_of_isTop (by decide +kernel)

theorem openLaws : OpenLaws cCeU := openLaws_of_plain (by decide +kernel)

/-- **`coreOKEx`, `FnDet`, `FnSolves`, `ClausePreDecided` and `OpenLaws` do not give `Consistent`.** -/
theorem coreEx_not_consistent : ¬ ∀ c : Semantics, c.coreOKEx = true → FnDet c → FnSolves c → ClausePreDecided c →
    OpenLaws c → Consistent c :=
  fun h => not_consistent (h cCeU cCeU_coreOKEx fnDet fnSolves preDecided openLaws)

#check @cCeU_coreOKEx
#check @clause_rawEx
#check @body_read
#check @no_model
#check @not_consistent
#check @fnDet
#check @fnSolves
#check @preDecided
#check @openLaws
#check @coreEx_not_consistent

#print axioms no_model
#print axioms not_consistent
#print axioms fnDet
#print axioms fnSolves
#print axioms coreEx_not_consistent

end KCore.CeNoModel
