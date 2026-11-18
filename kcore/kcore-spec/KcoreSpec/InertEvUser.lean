/-
  KCore, checked layer: an equation over interpreted hooked symbols and function symbols of the
  text is entailed at values (`EntailsAtValues`), for every semantics meeting `coreOK`, where each
  function symbol it applies has, at every argument list of its sorts, the result a value table
  names (`Eval`).

  The equation is of the form kompile writes for a rule that rewrites a term to a term (a
  `simplification` among them), `\implies{R}(premise, \equals{s, R}(lhs, \and{s}(rhs, \top{s}())))`,
  as `LibEv.Eqn` holds it; here its terms may apply a function of the semantics too.

  - `ValTable`: for a symbol, a function from argument lists to results, or none.
  - `valU`, `srtU?`: `LibEv.val` and `LibEv.srt?` where a symbol outside `hookSigs` that the table
    names has the table's result and the function's result sort.
  - `TableOK c F`: the table gives each function of `c` it names the result `Eval` gives at every
    argument list of the function's argument sorts.
  - `den_valU`: in a model of `Γ c`, at a valuation that gives each variable its value's element,
    the translated term denotes its value's element, or nothing where it has none: for a function
    symbol by `TiePair.eval_some_sound` and `eval_none_sound_core` (Γ entails the function's value,
    or its having none, at values).
  - `EqnU.entailed`: an equation whose two sides have the same value under `valU` at every
    substitution of values of the variables' sorts at which the `requires` is `true` is entailed
    at values, whatever axiom declaration of a text holds its pattern.
-/
import KcoreSpec.LibEv
import KcoreSpec.TiePairs

set_option autoImplicit false

namespace KCore

namespace InertEvUser

open ML Faithful LibEv

/-- For a symbol, the results of the function it names at argument lists, or none. -/
abbrev ValTable := Sym → Option (List GroundTerm → Option GroundTerm)

/-- The value of an application at the arguments' values: `Semantics.hv` for a symbol of
`hookSigs`, the table's otherwise. -/
def appU (c : Semantics) (F : ValTable) (f : Sym) (ws : List GroundTerm) : Option GroundTerm :=
  match lookupSig hookSigs f with
  | some _ => c.hv f ws
  | none => (F f).bind fun g => g ws

/-- The sort of an application at the arguments' sorts: an interpreted hooked symbol's result
sort, or the result sort of a function of the semantics the table names. -/
def srtAppU (c : Semantics) (F : ValTable) (f : Sym) (ss : Option (List Srt)) : Option Srt :=
  match lookupSig hookSigs f with
  | some k => if ss == some k.args then some k.result else none
  | none => match F f, c.lookupFn f with
    | some _, some fn => if ss == some fn.args then some fn.result else none
    | _, _ => none

mutual
  /-- `LibEv.val` with the table's results for the functions it names. -/
  def valU (c : Semantics) (F : ValTable) (σ : Subst) : Term → Option GroundTerm
    | .var i => σ.lookup i
    | .app f ts => (allSome (valUList c F σ ts)).bind (appU c F f)
    | .dv s lit => some (.dv s lit)
    | .inj _ _ _ => none
    | .as _ _ => none
    termination_by structural t => t
  def valUList (c : Semantics) (F : ValTable) (σ : Subst) : List Term → List (Option GroundTerm)
    | [] => []
    | t :: ts => valU c F σ t :: valUList c F σ ts
    termination_by structural ts => ts
end

mutual
  /-- `LibEv.srt?` with the result sorts of the functions the table names. -/
  def srtU? (c : Semantics) (F : ValTable) (vars : Vars) : Term → Option Srt
    | .var i => vars[i]?.map (·.2)
    | .app f ts => srtAppU c F f (srtsU? c F vars ts)
    | .dv s lit => if c.sortOf (.dv s lit) == some s then some s else none
    | .inj _ _ _ => none
    | .as _ _ => none
    termination_by structural t => t
  def srtsU? (c : Semantics) (F : ValTable) (vars : Vars) : List Term → Option (List Srt)
    | [] => some []
    | t :: ts => (srtU? c F vars t).bind fun s => (srtsU? c F vars ts).map (s :: ·)
    termination_by structural ts => ts
end

/-- The table gives each function of `c` it names, at every argument list of the function's
argument sorts, the result `Eval` gives there. -/
def TableOK (c : Semantics) (F : ValTable) : Prop :=
  ∀ f g fn ws, F f = some g → lookupSig hookSigs f = none → c.lookupFn f = some fn →
    c.sortsOf ws = some fn.args → Eval c f ws (g ws)

section
variable {c : Semantics} {F : ValTable} {f : Sym}

theorem appU_hook {k : CtorSig} (hk : lookupSig hookSigs f = some k) : appU c F f = c.hv f := by
  funext ws; unfold appU; rw [hk]

theorem appU_fn {g : List GroundTerm → Option GroundTerm} (hk : lookupSig hookSigs f = none)
    (hg : F f = some g) : appU c F f = g := by
  funext ws; unfold appU; rw [hk, hg]; rfl

theorem srtAppU_hook {k : CtorSig} (hk : lookupSig hookSigs f = some k) (ss : Option (List Srt)) :
    srtAppU c F f ss = if ss == some k.args then some k.result else none := by
  unfold srtAppU; rw [hk]

theorem srtAppU_fn {ss : Option (List Srt)} {s : Srt} (hk : lookupSig hookSigs f = none)
    (h : srtAppU c F f ss = some s) :
    ∃ g fn, F f = some g ∧ c.lookupFn f = some fn ∧ ss = some fn.args ∧ s = fn.result := by
  unfold srtAppU at h
  rw [hk] at h
  dsimp only at h
  split at h
  · rename_i g fn hg hfn
    by_cases he : ss = some fn.args
    · simp only [he, beq_self_eq_true, ite_true, Option.some.injEq] at h
      exact ⟨g, fn, hg, hfn, he, h.symm⟩
    · simp [he] at h
  · cases h
end

section
variable {c : Semantics} {F : ValTable} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (h : c.coreOK = true) (hok : c.ok = true) (hF : TableOK c F) (hI : I ⊧ᴵP Γ c) {vars : Vars}
  {σ : Subst} {tbl : KoreAML.VarTable} {e : Valuation M}
  (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
  (hag : ∀ i v, i < vars.length → σ.lookup i = some v →
    ∀ m, m = e.evalEvar (tbl.ev (vkey c vars i)) ↔ (den c v).interpret I e m)
include h hok hF hI hσ hag

set_option linter.unusedSectionVars false in
mutual
  /-- **A term denotes its value.** In a model of `Γ c`, at a valuation that gives each variable
  the element of its value under σ, the translation of a term of the sort `s` denotes the element
  of its value under `valU`, or nothing where it has none; and its value is of the sort `s`. -/
  theorem den_valU (hpreTop : c.clausesPreTop = true) : ∀ (t : Term) {s : Srt}, srtU? c F vars t = some s →
      (∀ m, (KoreAML.tr ⟨tbl, []⟩ (kore c vars t)).interpret I e m ↔ Res c I e (valU c F σ t) m) ∧
      (∀ v, valU c F σ t = some v → c.sortOf v = some s)
    | .var i, s, ht => by
      simp only [srtU?] at ht
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp ht
      obtain ⟨v, hv, hvs⟩ := hσ i p hp
      have hlt : i < vars.length := (List.getElem?_eq_some_iff.mp hp).1
      refine ⟨fun m => ?_, fun w hw => ?_⟩
      · rw [kore, KoreAML.tr, valU, hv]
        exact hag i v hlt hv m
      · rw [valU, hv] at hw
        cases hw
        exact hvs
    | .dv s' lit, s, ht => by
      simp only [srtU?] at ht
      by_cases hd : c.sortOf (.dv s' lit) = some s'
      · simp only [hd, beq_self_eq_true, ite_true, Option.some.injEq] at ht
        subst ht
        refine ⟨fun m => ?_, fun w hw => ?_⟩
        · rw [kore, valU]
          show _ ↔ (den c (.dv s' lit)).interpret I e m
          unfold den KoreAML.den
          rw [GroundTerm.kore]
          unfold srtOf
          rw [KoreAML.tr_dv, KoreAML.tr_dv]
        · rw [valU] at hw
          cases hw
          exact hd
      · simp [hd] at ht
    | .app f ts, s, ht => by
      simp only [srtU?] at ht
      cases hk : lookupSig hookSigs f with
      | some k =>
        rw [srtAppU_hook hk] at ht
        by_cases hargs : srtsU? c F vars ts = some k.args
        · simp only [hargs, beq_self_eq_true, ite_true, Option.some.injEq] at ht
          subst ht
          obtain ⟨hks, hkn⟩ := lookupSig_spec hk
          have hih := den_valsU (hpreTop := hpreTop) ts hargs
          have hhook : isHook f = true := by
            cases hh : isHook f with
            | true => rfl
            | false => rw [lookupSig_hookSigs_of_not_isHook hh] at hk; cases hk
          refine ⟨fun m => ?_, fun w hw => ?_⟩
          · rw [kore, tr_symApp, valU, appU_hook hk]
            cases hall : allSome (valUList c F σ ts) with
            | none =>
              simp only [Option.bind_none, Res, iff_false]
              exact hih.2 hall _ m
            | some ws =>
              obtain ⟨hws, hcong⟩ := hih.1 ws hall
              obtain ⟨o, ho⟩ := Semantics.hookRes_some (c := c) hhook ws
              have hax := sat_hookRes hI hks hws (by rw [hkn]; exact ho)
              have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
              rw [hkn] at hgr
              unfold KoreAML.den at hgr
              rw [tr_symApp] at hgr
              rw [hcong _ _ (fun _ => Iff.rfl) m, hgr]
              simp only [Option.bind_some, Semantics.hv, ho, Option.join_some]
              cases o with
              | none => simp [Res, Pattern.interpret]
              | some v => rfl
          · rw [valU, appU_hook hk] at hw
            cases hall : allSome (valUList c F σ ts) with
            | none => rw [hall] at hw; cases hw
            | some ws =>
              rw [hall] at hw
              obtain ⟨hws, -⟩ := hih.1 ws hall
              obtain ⟨o, ho⟩ := Semantics.hookRes_some (c := c) hhook ws
              have ho' : o = some w := by simpa [Semantics.hv, ho] using hw
              exact hookRes_sorted (fun _ => rangeBelow_of_core h) hk hws (ho' ▸ ho)
        · simp [hargs] at ht
      | none =>
        obtain ⟨g, fn, hg, hfn, hargs, rfl⟩ := srtAppU_fn hk ht
        have hih := den_valsU (hpreTop := hpreTop) ts hargs
        have hsc := hypSound_of_core h
        have hbc := Semantics.ok_clauseBinds hok
        refine ⟨fun m => ?_, fun w hw => ?_⟩
        · rw [kore, tr_symApp, valU, appU_fn hk hg]
          cases hall : allSome (valUList c F σ ts) with
          | none =>
            simp only [Option.bind_none, Res, iff_false]
            exact hih.2 hall _ m
          | some ws =>
            obtain ⟨hws, hcong⟩ := hih.1 ws hall
            have hE := hF f g fn ws hg hk hfn hws
            rw [hcong _ _ (fun _ => Iff.rfl) m]
            simp only [Option.bind_some]
            cases hgw : g ws with
            | none =>
              rw [hgw] at hE
              have hgr := (KoreAML.interp_equal (defOK hI)).mp
                (eval_none_sound_core (hpreTop := hpreTop) c hsc hbc hE hfn hws hI e default) m
              unfold KoreAML.den at hgr
              rw [tr_symApp] at hgr
              rw [hgr]
              simp [Res, Pattern.interpret]
            | some v =>
              rw [hgw] at hE
              have hgr := (KoreAML.interp_equal (defOK hI)).mp
                (TiePair.eval_some_sound (hpreTop := hpreTop) c hsc hbc hE hfn hws hI e default) m
              unfold KoreAML.den at hgr
              rw [tr_symApp] at hgr
              rw [hgr]
              rfl
        · rw [valU, appU_fn hk hg] at hw
          cases hall : allSome (valUList c F σ ts) with
          | none => rw [hall] at hw; cases hw
          | some ws =>
            rw [hall] at hw
            obtain ⟨hws, -⟩ := hih.1 ws hall
            have hE := hF f g fn ws hg hk hfn hws
            rw [Option.bind_some] at hw
            rw [hw] at hE
            obtain ⟨hso, hsr, -, -, -, -, -, -, hno⟩ := hsc
            exact Eval.sorted_of_all hso hsr (OvlOK.ovlCase hno) hE hfn hws
    | .inj _ _ _, s, ht => by simp [srtU?] at ht
    | .as _ _, s, ht => by simp [srtU?] at ht
  termination_by structural t => t
  /-- The arguments of an application: where each has a value, the values are of the argument
  sorts and the application of any head to the translated arguments is its application to the
  values' patterns; where one has none, the application denotes nothing. -/
  theorem den_valsU (hpreTop : c.clausesPreTop = true) : ∀ (ts : List Term) {ss : List Srt}, srtsU? c F vars ts = some ss →
      (∀ ws, allSome (valUList c F σ ts) = some ws → c.sortsOf ws = some ss ∧
        ∀ (acc acc' : KoreAML.P), (∀ m, acc.interpret I e m ↔ acc'.interpret I e m) →
          ∀ m, (KoreAML.trArgs ⟨tbl, []⟩ acc (koreList c vars ts)).interpret I e m ↔
            (KoreAML.trArgs ⟨[], []⟩ acc' (GroundTerm.koreList c ws)).interpret I e m) ∧
      (allSome (valUList c F σ ts) = none →
        ∀ (acc : KoreAML.P) m, ¬ (KoreAML.trArgs ⟨tbl, []⟩ acc (koreList c vars ts)).interpret I e m)
    | [], ss, ht => by
      simp only [srtsU?, Option.some.injEq] at ht
      subst ht
      refine ⟨fun ws hws => ?_, fun hn => by simp [valUList, allSome] at hn⟩
      simp only [valUList, allSome, Option.some.injEq] at hws
      subst hws
      refine ⟨sortsOf_nil, fun acc acc' hacc m => ?_⟩
      rw [koreList, GroundTerm.koreList, KoreAML.trArgs_nil, KoreAML.trArgs_nil]
      exact hacc m
    | t :: ts, ss, ht => by
      simp only [srtsU?] at ht
      obtain ⟨s, h1, hrest⟩ := Option.bind_eq_some_iff.mp ht
      obtain ⟨ss', h2, rfl⟩ := Option.map_eq_some_iff.mp hrest
      have ih1 := den_valU (hpreTop := hpreTop) t h1
      have ih2 := den_valsU (hpreTop := hpreTop) ts h2
      constructor
      · intro ws hws
        simp only [valUList, allSome, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hws
        obtain ⟨w, hw, ws', hws', rfl⟩ := hws
        obtain ⟨hs', hc'⟩ := ih2.1 ws' hws'
        refine ⟨sortsOf_cons.mpr ⟨s, ss', ih1.2 w hw, hs', rfl⟩, fun acc acc' hacc m => ?_⟩
        rw [koreList, GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_cons]
        exact hc' _ _ (KoreAML.interp_app_congr hacc (fun m => by rw [ih1.1 m, hw]; rfl)) m
      · intro hn acc m
        rw [koreList, KoreAML.trArgs_cons]
        cases hr : valU c F σ t with
        | none =>
          exact trArgs_empty (fun m' hm' => by
            obtain ⟨_, b, _, hb, _⟩ := KoreAML.interp_app.mp hm'
            have hb' := (ih1.1 b).mp hb
            rw [hr] at hb'
            exact hb') _ m
        | some w =>
          cases hrs : allSome (valUList c F σ ts) with
          | none => exact ih2.2 hrs _ m
          | some ws' => simp [valUList, allSome, hr, hrs] at hn
  termination_by structural ts => ts
end

end

/-! ## An equation over hooked symbols and functions of the text -/

namespace EqnU

/-- The equation is over registry sorts, its sides are terms of the sort `s` and its `requires` a
term of the sort Bool, under `srtU?`. -/
def typed (c : Semantics) (F : ValTable) (E : Eqn) : Bool :=
  decide (E.s < nRegSorts) && E.vars.all (fun p => decide (p.2 < nRegSorts)) &&
  srtU? c F E.vars E.lhs == some E.s && srtU? c F E.vars E.rhs == some E.s &&
  match E.req with
  | none => true
  | some q => srtU? c F E.vars q == some Srt.bool

/-- The two sides have the same value under `valU`, or both none, at every substitution of values
of the variables' sorts at which the `requires` has the value `true`. -/
def Holds (c : Semantics) (F : ValTable) (E : Eqn) : Prop :=
  ∀ σ : Subst, (∀ i p, E.vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) →
    (∀ q, E.req = some q → valU c F σ q = some (bool true)) → valU c F σ E.lhs = valU c F σ E.rhs

end EqnU

/-- **An equation over hooked symbols and functions of the text that holds of the values is
entailed at values.** For a semantics meeting `coreOK` and `ok`, a table that gives each function
it names `Eval`'s results (`TableOK`), and an equation `E` whose sides have equal values under
`valU` wherever its `requires` is true (`EqnU.Holds`): the translation of any axiom declaration
whose pattern is `E`'s, over the one sort variable `R` and with each variable of `E` free in it,
holds in every model of `Γ c` at every valuation that sends the axiom's free element variables to
values. -/
theorem EqnU.entailed {c : Semantics} (h : c.coreOK = true) (hok : c.ok = true) {F : ValTable}
    (hF : TableOK c F) (E : Eqn) (ht : EqnU.typed c F E = true) (hE : EqnU.Holds c F E)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.pattern c) (hsv : ad.ax.sortVars = [KoreAML.Rv])
    (hfv : ∀ i, i < E.vars.length → vkey c E.vars i ∈ KoreAML.freeOf [] ad.ax.pattern) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  have hpreTop := Semantics.preTop_of_okAll (Semantics.okAll_of_ok hok)
  intro M _ I hI e hat m
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨-, hfa, -, -, -⟩ := Semantics.coreOK_parts h
  obtain ⟨-, hg, -, -, -, hn, -, hsn, -, -, -, -⟩ := faithCoreOK_parts hfa
  simp only [EqnU.typed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨hsR, hvR⟩, htl⟩, htr⟩, htq⟩ := ht
  have hnum : ∀ {s : Srt}, s < nRegSorts → s < nRegSorts + c.sortNames.length :=
    fun hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  unfold AtValues at hat
  unfold KoreAML.trAxiom
  dsimp only
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hat ⊢
  rw [interpret_impl]
  intro hgd
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_singleton.mpr rfl)), rfl⟩))
  -- the values of the variables
  have hval : ∀ i, i < E.vars.length → ∃ v, c.sortOf v = some (E.vars.getD i ("", 0)).2 ∧
      elemOf c I v = e.evalEvar (t.ev (vkey c E.vars i)) := by
    intro i hi
    obtain ⟨v, S, hS, hv, hden⟩ := hat _ _ (List.mem_eraseDups.mpr (hfv i hi))
    have hp2 : (E.vars.getD i ("", 0)).2 < nRegSorts := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact hvR _ (List.getElem_mem hi)
    have hSe : S = (E.vars.getD i ("", 0)).2 :=
      sort_eq_of_name hn (sortOf_numbered_ofCl hg hsn (Semantics.coreOK_ovls h) hv) (hnum hp2) (srt_inj hS)
    subst hSe
    exact ⟨v, hv, (((elemOf_spec hI hv e).1 _).mp hden).symm⟩
  let σ : Subst := (List.range E.vars.length).map fun i =>
    (i, pick c I (E.vars.getD i ("", 0)).2 (e.evalEvar (t.ev (vkey c E.vars i))))
  have hlk : ∀ i, σ.lookup i = if i < E.vars.length then
      some (pick c I (E.vars.getD i ("", 0)).2 (e.evalEvar (t.ev (vkey c E.vars i)))) else none := by
    intro i
    show ((List.range E.vars.length).map _).lookup i = _
    rw [List.range_eq_range', lookup_range']
    simp
  have hσ : ∀ i p, E.vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2 := by
    intro i p hp'
    have hi : i < E.vars.length := (List.getElem?_eq_some_iff.mp hp').1
    have hgd' : E.vars.getD i ("", 0) = p := by rw [List.getD_eq_getElem?_getD, hp']; rfl
    refine ⟨pick c I (E.vars.getD i ("", 0)).2 (e.evalEvar (t.ev (vkey c E.vars i))), ?_, ?_⟩
    · rw [hlk]; simp only [hi, ite_true]
    · rw [← hgd']
      exact (pick_spec (hval i hi)).1
  have hag : ∀ i v, i < E.vars.length → σ.lookup i = some v →
      ∀ m, m = e.evalEvar (t.ev (vkey c E.vars i)) ↔ (den c v).interpret I e m := by
    intro i v hi hv m'
    rw [hlk] at hv
    simp only [hi, ite_true] at hv
    cases hv
    obtain ⟨h1, h2⟩ := pick_spec (hval i hi)
    rw [(elemOf_spec hI h1 e).1 m', h2]
  have hDV := fun (u : Term) (s : Srt) (hu : srtU? c F E.vars u = some s) =>
    den_valU (hpreTop := hpreTop) (tbl := t) (e := e) h hok hF hI hσ hag u hu
  -- the sorts
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI (hnum hsR)
  obtain ⟨τb, hτbsort, hτb⟩ := srt_den hI (hnum (show Srt.bool < nRegSorts by decide))
  have hdist : (distinctSorts c).contains Srt.bool = true := by
    refine List.elem_eq_true_of_mem ?_
    unfold distinctSorts
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  rw [hp]
  unfold Eqn.pattern
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [KoreAML.tr, KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun hprem => ?_⟩
    have hreq : ∀ q, E.req = some q → valU c F σ q = some (bool true) := by
      intro q hq
      unfold Eqn.premise at hprem
      rw [hq] at hprem htq
      dsimp only at hprem htq
      have htq' : srtU? c F E.vars q = some Srt.bool := eq_of_beq htq
      rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτb t e) hRv hτbsort hR] at hprem
      have hT : c.sortOf (bool true) = some Srt.bool := rmS_sortOf_bool c true
      obtain ⟨hT1, hT2⟩ := elemOf_spec hI hT e
      have hinh : KoreAML.Inh I τb (elemOf c I (bool true)) := by
        refine (KoreAML.interp_inhOf_of (fun a' => ?_)).mp hT2
        have := hτb t e a'
        rwa [trSort_srtOf_twoT] at this
      have hq1 := (hprem.2 _ hinh).mpr (by
        show (KoreAML.tr ⟨t, []⟩ (.dv (srtOf c Srt.bool) "true")).interpret I e _
        have : (den c (bool true)).interpret I e (elemOf c I (bool true)) := (hT1 _).mpr rfl
        unfold den KoreAML.den bool at this
        rw [GroundTerm.kore] at this
        unfold srtOf
        rw [KoreAML.tr_dv] at this ⊢
        exact this)
      rw [(hDV q _ htq').1] at hq1
      cases hvq : valU c F σ q with
      | none => rw [hvq] at hq1; exact hq1.elim
      | some w =>
        rw [hvq] at hq1
        have hw := (hDV q _ htq').2 w hvq
        by_cases hne : w = bool true
        · rw [hne]
        · exact absurd ⟨hq1, (hT1 _).mpr rfl⟩
            (dom_apart hI hdist hw hT hne e _)
    have heq := hE σ hσ hreq
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτ t e) hRv hτsort hR]
    refine ⟨(KoreAML.interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [(hDV E.lhs _ htl).1 b, heq, ← (hDV E.rhs _ htr).1 b, KoreAML.tr]
    show _ ↔ (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ (kore c E.vars E.rhs))
      (KoreAML.tr ⟨t, []⟩ (.top (srtOf c E.s)))).interpret I e b
    rw [KoreAML.interp_sAnd, show KoreAML.tr ⟨t, []⟩ (.top (srtOf c E.s)) =
      KoreAML.sTop (KoreAML.trSort t (srtOf c E.s)) from by rw [KoreAML.tr]]
    rw [KoreAML.interp_sTop hD (by rw [trSort_srtOf_twoT]; rfl), KoreAML.interp_inhOf_of (hτ t e)]
    exact ⟨fun h' => ⟨h', hb⟩, And.left⟩

end InertEvUser

end KCore
