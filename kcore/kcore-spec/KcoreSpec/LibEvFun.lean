/-
  KCore, checked layer: the `functional` sentence of an interpreted hooked symbol is entailed at
  values (`EntailsAtValues`), for every semantics meeting `coreOK` whose values of the sorts the
  interpreted symbols read have their shapes (`shapesOK`).

  The sentence is the one kompile writes for a symbol the text declares `total`,
  `\exists{R}(Val:s, \equals{s, R}(Val:s, f(K0:s0, …)))`: at values of the variables `K0`, …, the
  application has a value.
  - `LibEv.subst_of_atValues`: a valuation that sends the free element variables of an axiom to
    values gives a substitution of values of the variables' sorts whose elements are the
    valuation's.
  - `LibEv.funPatR k`: the sentence of the symbol with signature `k`, over the registry's names.
  - `LibEv.functional_ev`: it is entailed at values where the symbol has a value at every argument
    list of its sorts: off `partialHooks` `hook`'s; for a symbol of `totalSilentKeys` `hook`'s or,
    at a silent point, the interpretation's, where the interpretation gives one (`silentTotal`);
    for `isNaN`, `precisionFloat` and `exponentBitsFloat` (`floatLitTotal`) `hook`'s, where every
    Float value is a Float literal (`floatShapeOK`).
-/
import KcoreSpec.LibEv
import KcoreSpec.LazySound
import KcoreSpec.ParamsTotal
import KcoreSpec.OpenCompete

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- **The substitution of a valuation at values.** For variables `vars` of registry sorts, each
free in the axiom `a`: a valuation that sends the free element variables of `a` to values
(`AtValues`) gives a substitution with a value of its sort for each variable, whose element is
the valuation's at the variable. -/
theorem subst_of_atValues {c : Semantics} (h : c.coreOK = true) {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) {e : Valuation M} {a : Kore.Axiom}
    (hat : AtValues c I e a) (vars : Vars) (hvR : ∀ p ∈ vars, p.2 < nRegSorts)
    (hfv : ∀ i, i < vars.length → vkey c vars i ∈ KoreAML.freeOf [] a.pattern) :
    ∃ σ : Subst, (∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) ∧
      ∀ i v, i < vars.length → σ.lookup i = some v → c.sortOf v = some (vars.getD i ("", 0)).2 ∧
        elemOf c I v = e.evalEvar ((KoreAML.tableOf a.sortVars a.pattern).ev (vkey c vars i)) := by
  haveI : OvlOK c := ovlOK_of_core h
  obtain ⟨-, hfa, -, -, -⟩ := Semantics.coreOK_parts h
  obtain ⟨-, hg, -, -, -, hn, -, hsn, -, -, -, -⟩ := faithCoreOK_parts hfa
  have hnum : ∀ {s : Srt}, s < nRegSorts → s < nRegSorts + c.sortNames.length :=
    fun hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  unfold AtValues at hat
  generalize KoreAML.tableOf a.sortVars a.pattern = t at hat ⊢
  have hval : ∀ i, i < vars.length → ∃ v, c.sortOf v = some (vars.getD i ("", 0)).2 ∧
      elemOf c I v = e.evalEvar (t.ev (vkey c vars i)) := by
    intro i hi
    obtain ⟨v, S, hS, hv, hden⟩ := hat _ _ (List.mem_eraseDups.mpr (hfv i hi))
    have hp2 : (vars.getD i ("", 0)).2 < nRegSorts := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact hvR _ (List.getElem_mem hi)
    have hSe : S = (vars.getD i ("", 0)).2 :=
      sort_eq_of_name hn (sortOf_numbered_ofCl hg hsn (Semantics.coreOK_ovls h) hv) (hnum hp2) (srt_inj hS)
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

/-! ## The `functional` sentence of an interpreted symbol -/

/-- The variables `K{i}`, `K{i+1}`, … of the sorts `ss`. -/
def funVarsFrom : Nat → List Srt → Vars
  | _, [] => []
  | i, s :: ss => (s!"K{i}", s) :: funVarsFrom (i + 1) ss

/-- The variables of the sentence of `k`: `K0`, `K1`, … of its argument sorts. -/
def funVars (k : CtorSig) : Vars := funVarsFrom 0 k.args

/-- The variables `i`, …, `i + n - 1` as terms. -/
def argVars : Nat → Nat → List Term
  | _, 0 => []
  | i, n + 1 => .var i :: argVars (i + 1) n

/-- The application of `k`'s symbol to its variables. -/
def funTerm (k : CtorSig) : Term := .app k.name (argVars 0 k.args.length)

/-- The key of the bound variable `Val` of the sort `s`. -/
def valKey (s : Kore.KSort) : KoreAML.VarKey := .evar "Val" s

/-- The `functional` sentence of `k` in the semantics `c`:
`\exists{R}(Val:s, \equals{s, R}(Val:s, f(K0:s0, …)))`. -/
def funPat (c : Semantics) (k : CtorSig) : Kore.Pattern :=
  .exist KoreAML.R (KoreAML.evar "Val" (srtOf c k.result))
    (.equals (srtOf c k.result) KoreAML.R (.var (.evar (KoreAML.evar "Val" (srtOf c k.result))))
      (kore c (funVars k) (funTerm k)))

/-- `funPat` with the registry's names. -/
def funPatR (k : CtorSig) : Kore.Pattern :=
  .exist KoreAML.R (KoreAML.evar "Val" (regSrtK k.result))
    (.equals (regSrtK k.result) KoreAML.R (.var (.evar (KoreAML.evar "Val" (regSrtK k.result))))
      (koreR (funVars k) (funTerm k)))

/-- The symbol and sorts of `k` are the registry's, each variable of its sentence is free in it
and in its table, and none is named `Val`. -/
def funReg (k : CtorSig) : Bool :=
  decide (k.result < nRegSorts) && (funVars k).all (fun p => decide (p.2 < nRegSorts)) && reg (funTerm k) &&
  (funVars k).all (fun p => (KoreAML.freeOf [] (funPatR k)).contains (.evar p.1 (regSrtK p.2)) &&
    (KoreAML.tableOf [KoreAML.Rv] (funPatR k)).contains (.evar p.1 (regSrtK p.2)) && p.1 != "Val")

theorem funPat_reg (c : Semantics) {k : CtorSig} (hr : funReg k = true) : funPat c k = funPatR k := by
  simp only [funReg, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr
  obtain ⟨⟨⟨hs, hv⟩, ht⟩, -⟩ := hr
  unfold funPat funPatR
  rw [kore_reg c hv _ ht, srtOf_reg c hs]

theorem funVarsFrom_sorts : ∀ (i : Nat) (ss : List Srt), (funVarsFrom i ss).map (·.2) = ss
  | _, [] => rfl
  | i, s :: ss => by rw [funVarsFrom, List.map_cons, funVarsFrom_sorts (i + 1) ss]

theorem funVars_length (k : CtorSig) : (funVars k).length = k.args.length := by
  have := congrArg List.length (funVarsFrom_sorts 0 k.args)
  rwa [List.length_map] at this

/-- The variables from `i` on have the sorts of `vars` from `i` on. -/
theorem srts_argVars (c : Semantics) (vars : Vars) : ∀ (n i : Nat), i + n = vars.length →
    srts? c vars (argVars i n) = some ((vars.drop i).map (·.2))
  | 0, i, hi => by
    rw [argVars, srts?, List.drop_of_length_le (by omega)]; rfl
  | n + 1, i, hi => by
    have hlt : i < vars.length := by omega
    rw [argVars, srts?, srt?, List.getElem?_eq_getElem hlt, srts_argVars c vars n (i + 1) (by omega),
      List.drop_eq_getElem_cons hlt]
    rfl

/-- Where each variable has a value, the variables from `i` on have values. -/
theorem vals_argVars (c : Semantics) {vars : Vars} {σ : Subst}
    (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) :
    ∀ (n i : Nat), i + n = vars.length → ∃ ws, allSome (valList c σ (argVars i n)) = some ws
  | 0, _, _ => ⟨[], rfl⟩
  | n + 1, i, hi => by
    have hlt : i < vars.length := by omega
    obtain ⟨v, hv, -⟩ := hσ i _ (List.getElem?_eq_getElem hlt)
    obtain ⟨ws, hws⟩ := vals_argVars c hσ n (i + 1) (by omega)
    exact ⟨v :: ws, by simp only [argVars, valList, val, allSome, hv, hws, Option.bind_some, Option.map_some]⟩

/-- **The `functional` sentence of an interpreted symbol with a value at every argument list of
its sorts is entailed at values.** For a semantics meeting `coreOK` and `shapesOK` and a symbol
`k` of `hookSigs` that is not partial, or is one of `totalSilentKeys` under an interpretation
giving a value at its silent points (`silentTotal`), or is `isNaN`, `precisionFloat` or
`exponentBitsFloat` where every Float value is a Float literal: the translation of any axiom
declaration whose pattern is `funPatR k`, over the one sort variable `R`, holds in every model of
`Γ c` at every valuation that sends the axiom's free element variables to values. -/
theorem functional_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) {k : CtorSig}
    (hk : k ∈ hookSigs)
    (hkind : partialHooks.contains k.name = false ∨ (k.name ∈ totalSilentKeys ∧ c.silentTotal) ∨
      (k.name ∈ floatLitTotal ∧ c.floatShapeOK = true))
    (hr : funReg k = true) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = funPatR k)
    (hsv : ad.ax.sortVars = [KoreAML.Rv]) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hI e hat m
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have hr' := hr
  simp only [funReg, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at hr'
  obtain ⟨⟨⟨hsR, hvR⟩, -⟩, hvars⟩ := hr'
  have hnum : ∀ {s : Srt}, s < nRegSorts → s < nRegSorts + c.sortNames.length :=
    fun hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  have hmemv : ∀ i, i < (funVars k).length → (funVars k).getD i ("", 0) ∈ funVars k := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  have hkeyR : ∀ i, i < (funVars k).length → vkey c (funVars k) i =
      .evar ((funVars k).getD i ("", 0)).1 (regSrtK ((funVars k).getD i ("", 0)).2) := fun i hi => by
    unfold vkey
    rw [srtOf_reg c (hvR _ (hmemv i hi))]
  obtain ⟨σ, hσ, hel⟩ := subst_of_atValues h hI hat (funVars k) hvR (fun i hi => by
    rw [hp, hkeyR i hi]
    exact List.mem_of_elem_eq_true (hvars _ (hmemv i hi)).1.1)
  have hpc : ad.ax.pattern = funPat c k := hp.trans (funPat_reg c hr).symm
  unfold KoreAML.trAxiom
  dsimp only
  have htbl : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = KoreAML.tableOf [KoreAML.Rv] (funPatR k) := by
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
  -- the value of the application
  have hlen := funVars_length k
  have hsrts : srts? c (funVars k) (argVars 0 k.args.length) = some k.args := by
    rw [srts_argVars c (funVars k) k.args.length 0 (by omega), List.drop_zero]
    exact congrArg some (funVarsFrom_sorts 0 k.args)
  have hsrt : srt? c (funVars k) (funTerm k) = some k.result := by
    unfold funTerm
    rw [srt?, hookSigs_lookup k hk]
    simp only [Option.bind_some, hsrts, beq_self_eq_true, ite_true]
  obtain ⟨ws, hws⟩ := vals_argVars c hσ k.args.length 0 (by omega)
  -- under the binder
  let ex : M → Valuation M := fun x =>
    ⟨Function.update e.evalEvar (t.ev (valKey (srtOf c k.result))) x, e.evalSvar⟩
  have hexR : ∀ x, (ex x).evalEvar (t.ev (.sortVar "R")) = e.evalEvar (t.ev (.sortVar "R")) := fun x =>
    Function.update_noteq (ev_ne hRt (by unfold valKey; exact fun hh => by cases hh)) _ _
  have hexK : ∀ x i, i < (funVars k).length →
      (ex x).evalEvar (t.ev (vkey c (funVars k) i)) = e.evalEvar (t.ev (vkey c (funVars k) i)) := fun x i hi =>
    Function.update_noteq (ev_ne (by
        rw [htbl, hkeyR i hi]
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
  have hDV := fun x => den_val (tbl := t) (e := ex x) h hI hσ (hag x) (funTerm k) hsrt
  have hwss : c.sortsOf ws = some k.args :=
    ((den_vals (tbl := t) (e := ex default) h hI hσ (hag default) (argVars 0 k.args.length) hsrts).1 ws hws).1
  obtain ⟨v, hv⟩ : ∃ v, c.hookRes k.name ws = some (some v) := by
    rcases hkind with hpar | ⟨hkey, ht⟩ | ⟨hf, hfs⟩
    · obtain ⟨v, hv⟩ := hook_total hs k hk hpar ws hwss
      exact ⟨v, Semantics.hookRes_of_value hv⟩
    · exact total_hook_value hs ht hk (Or.inr (Or.inl hkey)) hwss
    · rw [floatLitTotal_args k hk (List.contains_iff_mem.mpr hf)] at hwss
      obtain ⟨w, hw⟩ := fmt_total hfs hf hwss
      exact ⟨w, Semantics.hookRes_of_value hw⟩
  have hval : val c σ (funTerm k) = some v := by
    unfold funTerm
    rw [val, hws]
    simp only [Option.bind_some, Semantics.hv, hv, Option.join_some]
  have hvs : c.sortOf v = some k.result := (hDV default).2 v hval
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI (hnum hsR)
  have hRv : ∀ x b, (KoreAML.trSort t KoreAML.R).interpret I (ex x) b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun x b => by rw [trSort_R, KoreAML.interp_evar, hexR]
  have hRv0 : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  rw [hpc]
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
      rw [(hDV (elemOf c I v)).1 b, hval, KoreAML.tr]
      show b = Function.update e.evalEvar (t.ev (valKey (srtOf c k.result))) (elemOf c I v)
        (t.ev (valKey (srtOf c k.result))) ↔ (den c v).interpret I (ex (elemOf c I v)) b
      rw [Function.update_same]
      exact ((elemOf_spec hI hvs _).1 b).symm

end LibEv

end KCore
