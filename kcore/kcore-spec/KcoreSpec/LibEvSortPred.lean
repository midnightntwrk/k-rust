/-
  KCore, checked layer: the `functional` sentence of a sort predicate holds at values in every
  model of `Γc` (`EntailsAtValuesΓc`), with no hypothesis on the user's functions beyond the
  decided ones `eval_den4_coreCl` reads.

  kompile writes `\exists{R}(Val:SortBool{}, \equals{SortBool{}, R}(Val:SortBool{}, LblisX{}(K0:SortK{})))`
  for each sort predicate `isX`. KCore builds the sort predicates (`Semantics.sortPreds`): `isX`
  has two clauses over K, one whose pattern is `kseq(inj{X,KItem}(V), dotk)` with the right side
  `true` and an `owise` one with `false`; neither has a `requires`. Evaluation gives it a value at
  every K (`sortPreds_totalN`), and in a model of `Γc` the application of a function to the
  elements of arguments of its sorts is what its evaluation's result denotes (`eval_den4_coreCl`).
  So at a valuation sending `K0` to a value's element, `isX(K0)` denotes the element of a Bool
  value, which is the `Val` the sentence asks for.
  - `LibEv.predFunReg`: the sorts of the sentence's variables are the registry's, each is free in
    the sentence and in its table, and none is named `Val` (decided on a text).
  - `LibEv.predFunRegS`: the same with the sorts any sort of the semantics.
  - `LibEv.fnFun_evC`: the sentence `funPat c fn.sig` of a function `fn` with a value at every
    argument list of its sorts, over the one sort variable `R`, translated, holds in every model of
    `Γc c` at every valuation sending its free element variables to values.
  - `LibEv.sortPredFun_evC`: the same for a sort predicate, from its evaluation's values.
  - `LibEv.fnFun_evC_withHooks`: the same for a function of the text declared total, under an
    interpretation of the hooks where `FnHyp` holds, which gives it those values.
  A model of `Γc ∪ Γstep` is one of `Γc`, so the sentence holds at values there too.
-/
import KcoreSpec.LibEvFun
import KcoreSpec.OpenClauseFn
import KcoreSpec.Totals
import KcoreSpec.PreReadBound
import KcoreSpec.FnObligations

set_option autoImplicit false

namespace KCore

open ML Faithful in
/-- `φ` holds in every model of `Γc c` at every valuation that sends the free element variables of
the axiom `ad` to values (`AtValues`): `EntailsAtValues` over `Γc` in place of `Γ`. -/
def EntailsAtValuesΓc (c : Semantics) (ad : KoreAML.AxiomDecl) (φ : KoreAML.P) : Prop :=
  ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc c →
    ∀ e, AtValues c I e ad.ax → ∀ m, φ.interpret I e m

namespace LibEv

open ML Faithful

/-- The sorts of the variables of `funPat c k` and of its result are the registry's, each variable
is free in the sentence and in its table, and none is named `Val`. -/
def predFunReg (c : Semantics) (k : CtorSig) : Bool :=
  decide (k.result < nRegSorts) && (funVars k).all (fun p => decide (p.2 < nRegSorts)) &&
  (funVars k).all (fun p => (KoreAML.freeOf [] (funPat c k)).contains (.evar p.1 (srtOf c p.2)) &&
    (KoreAML.tableOf [KoreAML.Rv] (funPat c k)).contains (.evar p.1 (srtOf c p.2)) && p.1 != "Val")

/-- `predFunReg` with the sorts of the sentence's variables and of its result any sort of `c`
(registry or the text's), in place of the registry's. -/
def predFunRegS (c : Semantics) (k : CtorSig) : Bool :=
  decide (k.result < nRegSorts + c.sortNames.length) &&
  (funVars k).all (fun p => decide (p.2 < nRegSorts + c.sortNames.length)) &&
  (funVars k).all (fun p => (KoreAML.freeOf [] (funPat c k)).contains (.evar p.1 (srtOf c p.2)) &&
    (KoreAML.tableOf [KoreAML.Rv] (funPat c k)).contains (.evar p.1 (srtOf c p.2)) && p.1 != "Val")

theorem predFunRegS_of_reg {c : Semantics} {k : CtorSig} (h : predFunReg c k = true) :
    predFunRegS c k = true := by
  have hnum : ∀ {s : Srt}, s < nRegSorts → s < nRegSorts + c.sortNames.length :=
    fun hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  simp only [predFunReg, predFunRegS, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
  exact ⟨⟨hnum h.1.1, fun p hp => hnum (h.1.2 p hp)⟩, h.2⟩

/-- **`subst_of_atValues` for variables of any sorts of `c`**: a valuation that sends the free
element variables of `a` to values gives a substitution with a value of its sort for each variable,
whose element is the valuation's at the variable. -/
theorem subst_of_atValuesS {c : Semantics} (h : c.coreOK = true) {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) {e : Valuation M} {a : Kore.Axiom}
    (hat : AtValues c I e a) (vars : Vars) (hvS : ∀ p ∈ vars, p.2 < nRegSorts + c.sortNames.length)
    (hfv : ∀ i, i < vars.length → vkey c vars i ∈ KoreAML.freeOf [] a.pattern) :
    ∃ σ : Subst, (∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) ∧
      ∀ i v, i < vars.length → σ.lookup i = some v → c.sortOf v = some (vars.getD i ("", 0)).2 ∧
        elemOf c I v = e.evalEvar ((KoreAML.tableOf a.sortVars a.pattern).ev (vkey c vars i)) := by
  haveI : OvlOK c := ovlOK_of_core h
  obtain ⟨-, hfa, -, -, -⟩ := Semantics.coreOK_parts h
  obtain ⟨-, hg, -, -, -, hn, -, hsn, -, -, -, -⟩ := faithCoreOK_parts hfa
  unfold AtValues at hat
  generalize KoreAML.tableOf a.sortVars a.pattern = t at hat ⊢
  have hval : ∀ i, i < vars.length → ∃ v, c.sortOf v = some (vars.getD i ("", 0)).2 ∧
      elemOf c I v = e.evalEvar (t.ev (vkey c vars i)) := by
    intro i hi
    obtain ⟨v, S, hS, hv, hden⟩ := hat _ _ (List.mem_eraseDups.mpr (hfv i hi))
    have hp2 : (vars.getD i ("", 0)).2 < nRegSorts + c.sortNames.length := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact hvS _ (List.getElem_mem hi)
    have hSe : S = (vars.getD i ("", 0)).2 :=
      sort_eq_of_name hn (sortOf_numbered_ofCl hg hsn (Semantics.coreOK_ovls h) hv) hp2 (srt_inj hS)
    subst hSe
    exact ⟨v, hv, (((elemOf_spec hI hv e).1 _).mp hden).symm⟩
  let σ : Subst := (List.range vars.length).map fun i =>
    (i, pick c I (vars.getD i ("", 0)).2 (e.evalEvar (t.ev (vkey c vars i))))
  have hlk : ∀ i, σ.lookup i = if i < vars.length then
      some (pick c I (vars.getD i ("", 0)).2 (e.evalEvar (t.ev (vkey c vars i)))) else none := by
    intro i
    show ((List.range vars.length).map _).lookup i = _
    rw [List.range_eq_range', lookup_range']
    simp
  refine ⟨σ, fun i p hp' => ?_, fun i v hi hv => ?_⟩
  · have hi : i < vars.length := (List.getElem?_eq_some_iff.mp hp').1
    have hgd' : vars.getD i ("", 0) = p := by rw [List.getD_eq_getElem?_getD, hp']; rfl
    refine ⟨pick c I (vars.getD i ("", 0)).2 (e.evalEvar (t.ev (vkey c vars i))), ?_, ?_⟩
    · rw [hlk]; simp only [hi, ite_true]
    · rw [← hgd']
      exact (pick_spec (hval i hi)).1
  · rw [hlk] at hv
    simp only [hi, ite_true] at hv
    cases hv
    exact pick_spec (hval i hi)

/-- **The `functional` sentence of a function with a value at every argument list of its sorts
holds at values in every model of `Γc`.** For a semantics meeting `coreOK`, whose clauses'
predicates are `\top`, whose functions bind no variable by `\exists`, and whose clauses'
conditions are decided where `needsWitness` holds: for a function `fn` of the semantics (a user's
or a sort predicate) whose evaluation has a value at every argument list of its argument sorts,
the translation of an axiom declaration whose pattern is `funPat c fn.sig`, over the one sort
variable `R`, holds in every model of `Γc c` at every valuation that sends the axiom's free element
variables to values. -/
theorem fnFun_evC {c : Semantics} (h : c.coreOK = true) (hpreTop : c.clausesPreTop = true)
    (hnoEx : c.FnsNoExs)
    (hw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {fn : Fn} (hfn : fn ∈ c.allFns)
    (htot : ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c fn.label vs (some v))
    (hr : predFunRegS c fn.sig = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = funPat c fn.sig) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValuesΓc c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hIc e hat m
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  haveI hov : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨hok, hsr, -, -, hph, -, -, -, -⟩ := hypSound_of_core h
  have hokCl : c.sortedOKCl = true := Semantics.sortedOKCl_of_sortedOK_noExs hok hnoEx
  have hfa : c.faithCoreOK = true := (Semantics.coreOK_parts h).2.1
  have hsc : SortCtx c := sortCtx_of_allCl hokCl hsr (OvlOK.ovlCase hov)
  have hcN : EvalCtxN c := evalCtxN_of_all hpreTop hnoEx hok hsr (OvlOK.ovlCase hov)
  have hlook : c.lookupFn fn.label = some fn := lookupFn_of_memN hcN hfn
  generalize hk : fn.sig = k at hr hp
  have hkn : k.name = fn.label := by rw [← hk]; rfl
  have hka : k.args = fn.args := by rw [← hk]; rfl
  have hkr : k.result = fn.result := by rw [← hk]; rfl
  have hr' := hr
  simp only [predFunRegS, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at hr'
  obtain ⟨⟨hsR, hvR⟩, hvars⟩ := hr'
  have hmemv : ∀ i, i < (funVars k).length → (funVars k).getD i ("", 0) ∈ funVars k := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨σ, hσ, hel⟩ := subst_of_atValuesS h hI hat (funVars k) hvR (fun i hi => by
    rw [hp]
    exact List.mem_of_elem_eq_true (hvars _ (hmemv i hi)).1.1)
  unfold KoreAML.trAxiom
  dsimp only
  have htbl : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = KoreAML.tableOf [KoreAML.Rv] (funPat c k) := by
    rw [hsv, hp]
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hel htbl ⊢
  rw [interpret_impl]
  intro hgd
  have hRt : KoreAML.VarKey.sortVar "R" ∈ t := by
    rw [htbl]
    exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_singleton.mpr rfl))
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_singleton.mpr rfl)), rfl⟩))
  have hlen := funVars_length k
  have hsrts : srts? c (funVars k) (argVars 0 k.args.length) = some k.args := by
    rw [srts_argVars c (funVars k) k.args.length 0 (by omega), List.drop_zero]
    exact congrArg some (funVarsFrom_sorts 0 k.args)
  obtain ⟨ws, hws⟩ := vals_argVars c hσ k.args.length 0 (by omega)
  -- under the binder
  let ex : M → Valuation M := fun x =>
    ⟨Function.update e.evalEvar (t.ev (valKey (srtOf c k.result))) x, e.evalSvar⟩
  have hexR : ∀ x, (ex x).evalEvar (t.ev (.sortVar "R")) = e.evalEvar (t.ev (.sortVar "R")) := fun x =>
    Function.update_noteq (ev_ne hRt (by unfold valKey; exact fun hh => by cases hh)) _ _
  have hexK : ∀ x i, i < (funVars k).length →
      (ex x).evalEvar (t.ev (vkey c (funVars k) i)) = e.evalEvar (t.ev (vkey c (funVars k) i)) := fun x i hi =>
    Function.update_noteq (ev_ne (by
        rw [htbl]
        exact List.mem_of_elem_eq_true (hvars _ (hmemv i hi)).1.2)
      (by
        unfold vkey valKey
        intro hh
        injection hh with hh _
        exact (hvars _ (hmemv i hi)).2 hh)) _ _
  have hag : ∀ x i v, i < (funVars k).length → σ.lookup i = some v →
      ∀ m, m = (ex x).evalEvar (t.ev (vkey c (funVars k) i)) ↔ (den c v).interpret I (ex x) m := by
    intro x i v hi hv m'
    obtain ⟨h1, h2⟩ := hel i v hi hv
    rw [(elemOf_spec hI h1 (ex x)).1 m', h2, hexK x i hi]
  have hDA := fun x => (den_vals (tbl := t) (e := ex x) h hI hσ (hag x) (argVars 0 k.args.length) hsrts).1 ws hws
  have hwss : c.sortsOf ws = some fn.args := hka ▸ (hDA default).1
  -- the function's value at the arguments, and the model's reading of its application
  obtain ⟨v, hev⟩ := htot ws hwss
  have hvs : c.sortOf v = some k.result := hkr ▸ Eval.sorted hsc hev hlook hwss rfl
  have hDV : ∀ x b, (KoreAML.tr ⟨t, []⟩ (kore c (funVars k) (funTerm k))).interpret I (ex x) b ↔
      (den c v).interpret I (ex x) b := fun x b => by
    have hden := eval_den4_coreCl hIc hokCl hsr hfa hph hw (HoldsShape.preReadAll_of_core h hIc) hev hlook hwss
      (ex x) b
    unfold KoreAML.den at hden
    rw [tr_symApp] at hden
    unfold funTerm
    rw [kore, tr_symApp, hkn, (hDA x).2 _ _ (fun _ => Iff.rfl) b]
    exact hden
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI hsR
  have hRv : ∀ x b, (KoreAML.trSort t KoreAML.R).interpret I (ex x) b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun x b => by rw [trSort_R, KoreAML.interp_evar, hexR]
  have hRv0 : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  rw [hp]
  unfold funPat
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [KoreAML.tr, KoreAML.interp_sExists, KoreAML.interp_inhOf_of hRv0]
  constructor
  · rintro ⟨x, -, hx⟩
    rw [KoreAML.tr] at hx
    have hx' : (KoreAML.sEquals (KoreAML.trSort t (srtOf c k.result)) (KoreAML.trSort t KoreAML.R) _ _).interpret I
      (ex x) a := hx
    rw [KoreAML.interp_sEquals hD hc (hτ t (ex x)) (hRv x) hτsort hR] at hx'
    exact hx'.1
  · intro ha
    refine ⟨elemOf c I v, ?_, ?_⟩
    · rw [KoreAML.interp_member hD]
      show (KoreAML.inhOf (KoreAML.trSort t (srtOf c k.result))).interpret I (ex (elemOf c I v))
        (Function.update e.evalEvar (t.ev (valKey (srtOf c k.result))) (elemOf c I v) (t.ev (valKey (srtOf c k.result))))
      rw [Function.update_same, trSort_srtOf_twoT]
      exact (elemOf_spec hI hvs _).2
    · rw [KoreAML.tr]
      show (KoreAML.sEquals (KoreAML.trSort t (srtOf c k.result)) (KoreAML.trSort t KoreAML.R) _ _).interpret I
        (ex (elemOf c I v)) a
      rw [KoreAML.interp_sEquals hD hc (hτ t (ex (elemOf c I v))) (hRv (elemOf c I v)) hτsort hR]
      refine ⟨ha, fun b _ => ?_⟩
      rw [hDV (elemOf c I v) b, KoreAML.tr]
      show b = Function.update e.evalEvar (t.ev (valKey (srtOf c k.result))) (elemOf c I v)
        (t.ev (valKey (srtOf c k.result))) ↔ (den c v).interpret I (ex (elemOf c I v)) b
      rw [Function.update_same]
      exact ((elemOf_spec hI hvs _).1 b).symm

/-- **The `functional` sentence of a sort predicate holds at values in every model of `Γc`.** For
a semantics meeting `coreOK`, whose clauses' predicates are `\top`, whose functions bind no
variable by `\exists`, and whose clauses' conditions are decided where `needsWitness` holds: the
translation of an axiom declaration whose pattern is `funPat c fn.sig` for a sort predicate `fn`,
over the one sort variable `R`, holds in every model of `Γc c` at every valuation that sends the
axiom's free element variables to values. Evaluation gives a sort predicate a value at every K
(`sortPreds_totalN`). -/
theorem sortPredFun_evC {c : Semantics} (h : c.coreOK = true) (hpreTop : c.clausesPreTop = true)
    (hnoEx : c.FnsNoExs)
    (hw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {fn : Fn} (hfn : fn ∈ c.sortPreds) (hr : predFunReg c fn.sig = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = funPat c fn.sig) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValuesΓc c ad (KoreAML.trAxiom [] [] ad).pat := by
  haveI hov : OvlOK c := ovlOK_of_core h
  obtain ⟨hok, hsr, -, -, -, -, -, -, -⟩ := hypSound_of_core h
  have hcN : EvalCtxN c := evalCtxN_of_all hpreTop hnoEx hok hsr (OvlOK.ovlCase hov)
  have hmem : fn ∈ c.allFns := List.mem_append_right _ hfn
  exact fnFun_evC h hpreTop hnoEx hw hmem
    (fun vs hvs => sortPreds_totalN hcN hfn fn (lookupFn_of_memN hcN hmem) vs hvs) (predFunRegS_of_reg hr) ad hp
    hsv

/-! ## Under every interpretation of the hooks -/

set_option linter.unusedVariables false in
mutual
  /-- The translation of a term does not read the interpretation of the hooks. -/
  theorem kore_withHooksSP (c : Semantics) (H : HookParams) (vars : Vars) :
      ∀ t : Term, kore (c.withHooks H) vars t = kore c vars t
    | .var _ => by rw [kore, kore]; rfl
    | .app f ts => by rw [kore, kore, koreList_withHooksSP c H vars ts]; rfl
    | .dv _ _ => by rw [kore, kore]; rfl
    | .inj _ _ t => by rw [kore, kore, kore_withHooksSP c H vars t]
    | .as t _ => by rw [kore, kore, kore_withHooksSP c H vars t]
  theorem koreList_withHooksSP (c : Semantics) (H : HookParams) (vars : Vars) :
      ∀ ts : List Term, koreList (c.withHooks H) vars ts = koreList c vars ts
    | [] => by rw [koreList, koreList]
    | t :: ts => by rw [koreList, koreList, kore_withHooksSP c H vars t, koreList_withHooksSP c H vars ts]
end

theorem funPat_withHooksSP (c : Semantics) (H : HookParams) (k : CtorSig) :
    funPat (c.withHooks H) k = funPat c k := by
  unfold funPat; rw [kore_withHooksSP]; rfl

theorem predFunReg_withHooksSP (c : Semantics) (H : HookParams) (k : CtorSig) :
    predFunReg (c.withHooks H) k = predFunReg c k := by
  unfold predFunReg; rw [funPat_withHooksSP]; rfl

theorem predFunRegS_withHooksSP (c : Semantics) (H : HookParams) (k : CtorSig) :
    predFunRegS (c.withHooks H) k = predFunRegS c k := by
  unfold predFunRegS; rw [funPat_withHooksSP]; rfl

/-- **`sortPredFun_evC` under every interpretation of the hooks**, from the facts of `c`: the sort
predicates, their sentences and the conditions it reads do not read the interpretation. -/
theorem sortPredFun_evC_withHooks {c : Semantics} (H : HookParams) (h : c.coreOK = true)
    (hpreTop : c.clausesPreTop = true) (hnoEx : c.FnsNoExs)
    (hw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness (c.withHooks H) = true →
      cl.CondDecided (c.withHooks H))
    {fn : Fn} (hfn : fn ∈ c.sortPreds) (hr : predFunReg c fn.sig = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = funPat c fn.sig) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValuesΓc (c.withHooks H) ad (KoreAML.trAxiom [] [] ad).pat :=
  sortPredFun_evC (c := c.withHooks H) ((Semantics.coreOK_withHooks c H).trans h) hpreTop hnoEx hw hfn
    ((predFunReg_withHooksSP c H _).trans hr) ad (hp.trans (funPat_withHooksSP c H _).symm) hsv

/-- **The `functional` sentence of a function of `c` declared total holds at values in every model
of `Γc`, under every interpretation of the hooks where `FnHyp` holds**: `FnHyp` gives the function
a value at every argument list of its sorts and decides the clauses' conditions where
`needsWitness` holds, which `fnFun_evC` reads. -/
theorem fnFun_evC_withHooks {c : Semantics} (H : HookParams) (h : c.coreOK = true)
    (hpreTop : c.clausesPreTop = true) (hnoEx : c.FnsNoExs) (hf : FnHyp (c.withHooks H))
    {fn : Fn} (hfn : fn ∈ c.fns) (ht : fn.total = true) (hr : predFunRegS c fn.sig = true)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = funPat c fn.sig) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValuesΓc (c.withHooks H) ad (KoreAML.trAxiom [] [] ad).pat :=
  fnFun_evC (c := c.withHooks H) ((Semantics.coreOK_withHooks c H).trans h) hpreTop hnoEx hf.2.2.2.2.1.2
    (List.mem_append_left (c.withHooks H).sortPreds hfn) (hf.2.1 fn hfn ht)
    ((predFunRegS_withHooksSP c H _).trans hr) ad (hp.trans (funPat_withHooksSP c H _).symm) hsv

end LibEv

end KCore
