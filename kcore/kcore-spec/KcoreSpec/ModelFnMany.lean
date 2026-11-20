/-
  KCore. Consistency where one unary function's clause gives several values at one argument.

  `consistent_of_fnMany`: a semantics `coreOKEx` accepts is consistent where one function `f` of
  it takes one argument and has one clause, with existential variables, whose name is read as no
  instance and is no constant, such that
  - every premise of the theory but `f`'s own items (its equation and its arity item) holds no
    symbol named as `f` (`AvoidsOff`), and the clause's premise and right side apply none
    (`ownKokB`);
  - two matches of the clause at one argument list give one set of instance values (`hset`);
  - evaluation has one result at most (`FnDet`) and solves the equations of every other function
    (`FnSolvesAt`), and the clauses' predicates have truth values and the open generators meet their
    laws.
  The model is `stdIOver` with `f` at the value `w` read as the set of values the clause's
  instances give at a match at `[w]`: `f`'s equation holds there because its right side denotes in
  the value model exactly those values (`AtT.sat_clauseEqEx_over`, the reading of
  `sat_clauseEqEx` with the instances' values in place of evaluation's), its arity item because
  each instance's value is of the result sort, and every other premise as in the value model
  (`consistent_of_over`). `FnSolvesAt` is not asked of `f`: where two instances give two values,
  evaluation gives `f` no result there, and the model gives it both.

  `consistent_of_fnMany_agree`: the same where two matches at one argument list agree on the
  clause's variables off `exsFree`, which gives one set of instance values (`gives_set_of_agree`).

  `ownKokB_withHooks`, `coreOKEx_withHooks_fm`, `spareSymB_withHooks_fm`: the checks on the text do
  not read the interpretation of the hooks.
-/
import KcoreSpec.ModelFnOverEqn
import KcoreSpec.DataCmd

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- The premise and the right side of the equation of the clause `cl` of `fn` apply no symbol named
as `fn`. -/
def ownKokB (c : Semantics) (fn : Fn) (cl : Clause) : Bool :=
  GenEqs.Walk.kok (fun m => m != c.symName fn.label) (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) &&
    GenEqs.Walk.kok (fun m => m != c.symName fn.label) (clauseRightEx c fn cl)

-- The checks on the text under every interpretation of the hooks are the checks of the semantics.
kernel_rfl ownKokB_withHooks : ∀ (c : Semantics) (H : HookParams) (fn : Fn) (cl : Clause),
  ownKokB (c.withHooks H) fn cl = ownKokB c fn cl
kernel_rfl coreOKEx_withHooks_fm : ∀ (c : Semantics) (H : HookParams),
  (c.withHooks H).coreOKEx = c.coreOKEx
kernel_rfl spareSymB_withHooks_fm : ∀ (c : Semantics) (H : HookParams) (n : String),
  GenEqs.spareSymB (c.withHooks H) n = GenEqs.spareSymB c n

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **The equation of a unary function's clause with existential variables and no competitor holds
in `stdIOver`**, with the function read at `w` as the values `G [w]`, where the clause applying at
arguments gives as `G` of them exactly the values its instances give (`hsolve`). The function's
name is read as no instance and is no constant, and the clause's premise and right side apply no
symbol of that name (`hkp`, `hkr`). -/
theorem sat_clauseEqEx_over (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {a : Srt}
    (hargs : fn.args = [a]) (hplain : instDecode? (c.symName fn.label) = none)
    (hsym : GenEqs.spareSymB c (c.symName fn.label) = true) {cl : Clause} (F : EqnFactsEx c fn cl)
    (hkp : GenEqs.Walk.kok (fun m => m != c.symName fn.label)
      (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)) = true)
    (hkr : GenEqs.Walk.kok (fun m => m != c.symName fn.label) (clauseRightEx c fn cl) = true)
    (hdec : ∀ σ ws, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats ws →
      (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) → ∃ b, Holds c cl.vars.length σ cl.pre b)
    (hpostDec : ∀ σ', c.WellSorted cl.vars σ' → ∃ b, Holds c cl.vars.length σ' cl.post b)
    {G : List GroundTerm → GroundTerm → Prop}
    (hsolve : ∀ σ ws, c.sortsOf ws = some fn.args → cl.AppliesAt c σ ws →
      ∀ v, G ws v ↔ ∃ σ', AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v) :
    stdIOver c T (c.symName fn.label) (fun w m => ∃ y, m = .val y ∧ G [w] y) ⊧ᴵ
      (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv], .implies KoreAML.R
        (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl))
        (eqConclEx c fn (clauseRightEx c fn cl)), []⟩ : Kore.Axiom)⟩).pat := by
  obtain ⟨L, hL, hrhs, hens⟩ := F.concl
  obtain ⟨L', hL', hreqs⟩ := F.req
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := h.sound
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allClEx hok hsr (OvlOK.ovlCase hno)
  have hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht =>
    varOccs_lt t (hreqs t ht)
  have hVv := clause_keys_inAxEx (c := c) (prem := withPre c (canonVars c cl.vars) cl (clausePrem c fn cl))
    F.patsAll hreqv F.occ (fun _ hk => hk)
  have hres := h.fnSorts hfn fn.result (List.mem_cons_self ..)
  have hnum := vars_numEx h hfn F
  have hlt := F.exLt
  have hnd := F.exNodup
  have hrhsOK := termOK_of_sorted h hL hrhs
  have hensOK : ∀ t, cl.ens = some t → TermOK c (· < cl.vars.length) t := fun t ht => termOK_of_sorted h hL (hens t ht)
  have hrhsv := varOccs_lt cl.rhs hrhs
  have hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => varOccs_lt t (hens t ht)
  have hokQ := F.postOK
  have hbdQ := F.postBound
  have hrs : ∀ σ' y, c.WellSorted cl.vars σ' → EvalTerm c σ' cl.rhs (some y) → c.sortOf y = some fn.result :=
    fun σ' y hσ' hy => EvalTerm.sorted_at hsc hy hL (hσ'.at _) hrhs rfl
  refine sat_eqnRight_over h hfn hargs hplain hsym (free := fun i => i ∉ cl.exs) (fun i hi _ => hnum i hi)
    hkp hkr (clause_keys_freeEx F (fun _ hk => hk)) fun tbl e ws x hR hk hRs hws hvin ha hp b hb => ?_
  have hkP : ∀ k ∈ KoreAML.varsOf (withPre c (canonVars c cl.vars) cl (clausePrem c fn cl)), k ∈ tbl :=
    fun k hk' => hk k (by rw [KoreAML.varsOf]; exact List.mem_append_left _ (List.mem_append_right _ hk'))
  have happ := withPre_readEx h F.toExclFactsPre F.exLeft hdec hR hRs hws (fun i hi _ => hk _ (hVv i hi)) hvin
    hkP ha hp
  have hσe : ∀ i < cl.vars.length, i ∉ cl.exs → ∃ v, (substE c tbl cl.vars e).lookup i = some v ∧
      e.evalEvar (tbl.ev (canonKey c cl.vars i)) = .val v := fun i hi hx => by
    obtain ⟨v, he, -⟩ := inSort_val (hvin i hi hx)
    exact ⟨v, by rw [substE_lookup hi, he]; rfl, he⟩
  have hsolve' := hsolve _ ws hws.sorts happ
  rw [exsFree_eq_of_leftEx F.exLeft] at hsolve'
  generalize substE c tbl cl.vars e = σ at hσe hsolve'
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
  have hwl : ws.length = 1 := by rw [sortsOf_len hws.sorts, hargs]; rfl
  obtain ⟨w, rfl⟩ : ∃ w, ws = [w] := by
    match ws, hwl with
    | [w], _ => exact ⟨w, rfl⟩
  rw [clauseRightEx_read_T h hres hnum hlt hnd hrhsOK hensOK hokQ hbdQ hrs hkeys hkQ hσ hvar b]
  constructor
  · rintro ⟨σ', y, hag, hσ', hy, hens, hpo, rfl⟩
    refine ⟨w, rfl, y, rfl, (hsolve' y).mpr ?_⟩
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
  · rintro ⟨w', hw', v, rfl, hE⟩
    cases hw'
    obtain ⟨σ', ha', hw, grhs, gens, gpost⟩ := (hsolve' v).mp hE
    exact ⟨σ', v, fun i _ hx => ha' i hx, hw, grhs, gens, (holds_trueV h.det gpost).mpr rfl, rfl⟩

end AtT

/-- The values the instances of the clause `cl` give at a match at the arguments `ws`. -/
def instVals (c : Semantics) (cl : Clause) (ws : List GroundTerm) (v : GroundTerm) : Prop :=
  ∃ σ σ', cl.AppliesAt c σ ws ∧ AgreeOff cl.exsFree σ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v

/-- **The theory is consistent where one unary function's one clause gives a set of values**: for
a semantics `coreOKEx` accepts, a function `fn` labelled `f` with one clause `cl`, with existential
variables, taking one argument, whose name is read as no instance and is no constant (`hplain`,
`hsym`); every premise but `f`'s own items avoids the name (`hav`) and the clause's premise and
right side apply no symbol of it (`hk`); two matches of the clause at one argument list give one
set of instance values (`hset`); evaluation has one result at most (`FnDet`) and solves the
equations of every other function (`FnSolvesAt`), and the clauses' predicates have truth values
and the open generators meet their laws. The model reads `f` at `w` as `instVals c cl [w]`. -/
theorem consistent_of_fnMany {f : Sym} {fn : Fn} {cl : Clause} {a : Srt}
    (h : c.coreOKEx = true) (hmem : fn ∈ c.fns) (hlab : fn.label = f) (hcl : fn.clauses = [cl])
    (hargs : fn.args = [a]) (hex : cl.exs ≠ [])
    (hplain : instDecode? (c.symName f) = none) (hsym : GenEqs.spareSymB c (c.symName f) = true)
    (hav : AvoidsOff c f (c.symName f)) (hk : ownKokB c fn cl = true)
    (hd : FnDet c) (hs : ∀ g ∈ c.fns, g.label ≠ f → FnSolvesAt c g)
    (hset : ∀ ws σ₁ σ₂, cl.AppliesAt c σ₁ ws → cl.AppliesAt c σ₂ ws → ∀ v,
      (∃ σ', AgreeOff cl.exsFree σ₁ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v) →
      (∃ σ', AgreeOff cl.exsFree σ₂ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v))
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) (hl : OpenLaws c) : Consistent c := by
  subst hlab
  have hm := hypModelCore_of_coreEx h hd
  have hfnA : fn ∈ c.allFns := List.mem_append_left _ hmem
  have hclm : cl ∈ fn.clauses := by rw [hcl]; exact List.mem_singleton_self _
  obtain ⟨hcs, hcx, -⟩ := hypModelCore_clsFactsCe hm fn hmem cl hclm
  have hLh : HeadsOK c (c.fns.map Fn.sig) := fun k hk => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
    exact ⟨g, List.mem_append_left _ hg, rfl⟩
  have F : EqnFactsEx c fn cl := eqnFactsEx_of_sorted hm hfnA hLh hcs hcx
  obtain ⟨hkp, hkr⟩ := Bool.and_eq_true_iff.mp hk
  have hrs : ∀ σ' y, c.WellSorted cl.vars σ' → EvalTerm c σ' cl.rhs (some y) → c.sortOf y = some fn.result := by
    obtain ⟨L, hL, hrhs, -⟩ := F.concl
    obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hm.sound
    haveI : OvlOK c := hno
    have hsc := sortCtx_of_allClEx hok hsr (OvlOK.ovlCase hno)
    exact fun σ' y hσ' hy => EvalTerm.sorted_at hsc hy hL (hσ'.at _) hrhs rfl
  refine consistent_of_over (S := fun w m => ∃ y, m = .val y ∧ instVals c cl [w] y) h hd hs hp hq hl hav
    (fun φ _ ho => ?_)
  have huniq : ∀ g ∈ c.allFns, g.label = fn.label → g = fn := fun g hg hgl => by
    have h1 := hm.lookupFn hg
    rw [hgl, hm.lookupFn hfnA] at h1
    exact (Option.some.inj h1).symm
  rcases ho with ⟨g, hg, hgl, it, hit, rfl⟩ | ⟨g, hg, hgl, rfl⟩
  · obtain rfl := huniq g (List.mem_append_left _ hg) hgl
    obtain ⟨s, hs', hit⟩ := List.mem_filterMap.mp hit
    unfold fnEquationsK at hs'
    rw [hcl] at hs'
    obtain rfl : s = prioEquation c g cl := by simpa using hs'
    have hlow : (lowerClauses g cl).isEmpty = true := by simp [lowerClauses, hcl]
    rw [show prioEquation c g cl = clauseEquation c g cl from if_pos hlow, clauseEquation_axEx hex F.exLt] at hit
    cases hit
    refine AtT.sat_clauseEqEx_over hm hfnA hargs hplain hsym F hkp hkr
      (fun σ ws hσ hpv _ => hp g hmem cl hclm σ ws hσ hpv) (hq g hmem cl hclm) (fun σ ws _ happ v => ?_)
    constructor
    · rintro ⟨σ₀, σ', happ₀, hrest⟩
      exact hset ws σ₀ σ happ₀ happ v ⟨σ', hrest⟩
    · rintro ⟨σ', hrest⟩
      exact ⟨σ, σ', happ, hrest⟩
  · obtain rfl := huniq g hg hgl
    exact AtT.sat_arity_over hm hfnA hargs hplain hsym
      (fun w x _ ⟨y, hx, _, σ', _, _, hσ', hgv⟩ => by subst hx; exact hrs σ' y hσ' hgv.1)

/-- **Two substitutions that agree on the clause's variables off `exsFree` have one set of instance
values**: an instance at the one is moved to the other by taking its values on the clause's
variables. -/
theorem gives_set_of_agree {cl : Clause} (hokQ : c.condOK cl.vars cl.post = true)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    {σ₁ σ₂ : Subst} (hag : ∀ i < cl.vars.length, i ∉ cl.exsFree → σ₁.lookup i = σ₂.lookup i) {v : GroundTerm}
    (h : ∃ σ', AgreeOff cl.exsFree σ₁ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v) :
    ∃ σ', AgreeOff cl.exsFree σ₂ σ' ∧ c.WellSorted cl.vars σ' ∧ cl.Gives c σ' v := by
  obtain ⟨σ', ha, hw, hy, he, hp⟩ := h
  have hl₁ : ∀ j, j < cl.vars.length → ∃ u, σ'.lookup j = some u := fun j hj => by
    obtain ⟨u, hu, -⟩ := hw j (cl.vars.getD j 0)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl)
    exact ⟨u, hu⟩
  have hl₂ : ∀ j, j < cl.vars.length →
      (((List.range cl.vars.length).map fun j => (j, (σ'.lookup j).getD default)) ++ σ₂).lookup j = σ'.lookup j :=
    fun j hj => by
      obtain ⟨u, hu⟩ := hl₁ j hj
      simp [CE.lookup_overEV, hj, hu]
  refine ⟨((List.range cl.vars.length).map fun j => (j, (σ'.lookup j).getD default)) ++ σ₂, fun i hx => ?_,
    fun i s hs => ?_, ?_, fun t ht => ?_, ?_⟩
  · by_cases hil : i < cl.vars.length
    · rw [hl₂ i hil, ha i hx]; exact hag i hil hx
    · simp [CE.lookup_overEV, hil]
  · rw [hl₂ i (List.getElem?_eq_some_iff.mp hs).1]; exact hw i s hs
  · exact Exec.EvalTerm.congr hy fun i hi => (hl₂ i (hrhsv i hi)).symm
  · exact Exec.EvalTerm.congr (he t ht) fun i hi => (hl₂ i (hensv t ht i hi)).symm
  · exact Holds.congr_NI hp fun j hj => (hl₂ j (varOccsCond_lt_twoT cl.post hokQ j hj)).symm

/-- **`consistent_of_fnMany` where two matches at one argument list agree on the clause's variables
off `exsFree`** (`hagree`; for instance where those variables are the patterns' and the patterns
are variables): the two sets of instance values are then one (`gives_set_of_agree`). -/
theorem consistent_of_fnMany_agree {f : Sym} {fn : Fn} {cl : Clause} {a : Srt}
    (h : c.coreOKEx = true) (hmem : fn ∈ c.fns) (hlab : fn.label = f) (hcl : fn.clauses = [cl])
    (hargs : fn.args = [a]) (hex : cl.exs ≠ [])
    (hplain : instDecode? (c.symName f) = none) (hsym : GenEqs.spareSymB c (c.symName f) = true)
    (hav : AvoidsOff c f (c.symName f)) (hk : ownKokB c fn cl = true)
    (hd : FnDet c) (hs : ∀ g ∈ c.fns, g.label ≠ f → FnSolvesAt c g)
    (hagree : ∀ ws σ₁ σ₂, cl.AppliesAt c σ₁ ws → cl.AppliesAt c σ₂ ws →
      ∀ i < cl.vars.length, i ∉ cl.exsFree → σ₁.lookup i = σ₂.lookup i)
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) (hl : OpenLaws c) : Consistent c := by
  have hm := hypModelCore_of_coreEx h hd
  have hfnA : fn ∈ c.allFns := List.mem_append_left _ hmem
  have hclm : cl ∈ fn.clauses := by rw [hcl]; exact List.mem_singleton_self _
  obtain ⟨hcs, hcx, -⟩ := hypModelCore_clsFactsCe hm fn hmem cl hclm
  have hLh : HeadsOK c (c.fns.map Fn.sig) := fun k hk => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
    exact ⟨g, List.mem_append_left _ hg, rfl⟩
  have F : EqnFactsEx c fn cl := eqnFactsEx_of_sorted hm hfnA hLh hcs hcx
  obtain ⟨L, -, hrhs, hens⟩ := F.concl
  exact consistent_of_fnMany h hmem hlab hcl hargs hex hplain hsym hav hk hd hs
    (fun ws σ₁ σ₂ h1 h2 _ hv => gives_set_of_agree F.postOK (varOccs_lt cl.rhs hrhs)
      (fun t ht => varOccs_lt t (hens t ht)) (hagree ws σ₁ σ₂ h1 h2) hv) hp hq hl

end Model

end Faithful

end KCore
