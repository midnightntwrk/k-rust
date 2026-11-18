/-
  C3 'simplification x ensures' on the fixture c3-simp-ens-true: `rule f(X) => X [priority(40)]`
  beside `rule f(f(X)) => f(X) ensures f(X) ==Int X [simplification]`. The simplification is a true
  lemma of the text: its sentence (axiom 201)
  `\implies{R}(\top{R}(), \equals{SortInt{}, R}(f(f(X)), \and{SortInt{}}(f(X), \equals{SortBool{}, SortInt{}}(f(X) ==Int X, true))))`
  is entailed by Γ at values, for every H (`ens_entailed`): at an integer n, `f(f(n))` and `f(n)` are
  both n (`eval_all`: `f(n) = n`), and `f(n) ==Int n` is `true`, so the right side's conjunct
  `f(X) ==Int X = true` holds at every element of Int and the right side is `f(n)`.
  The text is `f2-examples/c3-simp-ens-true.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/c3-simp-ens-true/kompile.txt` records, with its paths restored.
  Run from the package root: `lake env lean -j1 test/C3SimpEnsTrue.lean`. Every statement is on the
  literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  - `ensEqn_entailed`: `InertEvUser.EqnU.entailed` for the pattern kompile writes for a rewrite with an
    `ensures`, `\implies{R}(premise, \equals{s, R}(lhs, \and{s}(rhs, \equals{Bool, s}(ens, true))))`
    (`ensPattern`): where the two sides have equal values (`EqnU.Holds`) and the `ensures` has the
    value `true` at every substitution of values at which the `requires` is `true`, the sentence is
    entailed at values.
  - `ens_class`: the reader classes the sentence inert simplification; `ens_text`: its pattern.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.C3SimpEnsTrue.Gen

open ML Faithful LibEv InertEvUser

/-- The pattern kompile writes for a rewrite of `lhs` to `rhs` with an `ensures` `ens`. -/
def ensPattern (c : Semantics) (E : Eqn) (ens : Term) : Kore.Pattern :=
  .implies KoreAML.R (E.premise c)
    (.equals (srtOf c E.s) KoreAML.R (LibEv.kore c E.vars E.lhs)
      (.and (srtOf c E.s) [LibEv.kore c E.vars E.rhs,
        .equals (srtOf c Srt.bool) (srtOf c E.s) (LibEv.kore c E.vars ens) (.dv (srtOf c Srt.bool) "true")]))

/-- **An equation with an `ensures` that holds of the values is entailed at values.** -/
theorem ensEqn_entailed {c : Semantics} (h : c.coreOK = true) (hok : c.ok = true) {F : ValTable}
    (hF : TableOK c F) (E : Eqn) (ens : Term) (ht : EqnU.typed c F E = true)
    (hens : srtU? c F E.vars ens = some Srt.bool) (hE : EqnU.Holds c F E)
    (hEns : ∀ σ : Subst, (∀ i p, E.vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) →
      (∀ q, E.req = some q → valU c F σ q = some (bool true)) → valU c F σ ens = some (bool true))
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = ensPattern c E ens) (hsv : ad.ax.sortVars = [KoreAML.Rv])
    (hfv : ∀ i, i < E.vars.length → vkey c E.vars i ∈ KoreAML.freeOf [] ad.ax.pattern) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
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
    den_valU (tbl := t) (e := e) h hok hF hI hσ hag u hu
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
  unfold ensPattern
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
    show _ ↔ (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ (LibEv.kore c E.vars E.rhs))
      (KoreAML.tr ⟨t, []⟩ (.equals (srtOf c Srt.bool) (srtOf c E.s) (LibEv.kore c E.vars ens)
        (.dv (srtOf c Srt.bool) "true")))).interpret I e b
    rw [KoreAML.interp_sAnd]
    have hEq : (KoreAML.tr ⟨t, []⟩ (.equals (srtOf c Srt.bool) (srtOf c E.s) (LibEv.kore c E.vars ens)
        (.dv (srtOf c Srt.bool) "true"))).interpret I e b := by
      rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτb t e) (hτ t e) hτbsort hτsort]
      refine ⟨hb, fun a _ => ?_⟩
      rw [(hDV ens _ hens).1 a, hEns σ hσ hreq]
      show (den c (bool true)).interpret I e a ↔ _
      unfold den KoreAML.den bool
      rw [GroundTerm.kore]
      unfold srtOf
      rw [KoreAML.tr_dv, KoreAML.tr_dv]
      rfl
    exact ⟨fun h' => ⟨h', hEq⟩, And.left⟩

end KCore.C3SimpEnsTrue.Gen

namespace KCore.C3SimpEnsTrue

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/c3-simp-ens-true.kompile.kore"
definition_of defn from "f2-examples/c3-simp-ens-true.kompile.kore"
user_axioms U from "f2-examples/c3-simp-ens-true.kompile.kore" module "C3-SIMP-ENS-TRUE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem hok : c.ok = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem shapesOK_c : c.shapesOK = true := by decide +kernel

def f : Sym := 384

theorem names : c.symName f = "Lblf" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem hfn : c.lookupFn f = some fn := rfl
theorem hfnH (H : HookParams) : (cH H).lookupFn f = some fn := by rw [Semantics.lookupFn_withHooks]; exact hfn
theorem fn_args : fn.args = [Srt.int] := by decide +kernel
theorem hkf : lookupSig hookSigs f = none := by decide +kernel

/-! ## `f`'s value at every integer -/

/-- `f`'s one clause: `f(X) => X [priority(40)]`. -/
noncomputable abbrev cl0 : Clause := fn.clauses[0]'(by decide +kernel)

theorem cl0_vars : cl0.vars = [Srt.int] := by decide +kernel
theorem cl0_pats : cl0.pats = [.var 0] := rfl
theorem cl0_req : cl0.req = none := rfl
theorem cl0_rhs : cl0.rhs = .var 0 := rfl
theorem cl0_pre : cl0.pre = .top := rfl
theorem cl0_ens : cl0.ens = none := rfl
theorem cl0_least : fn.clauses.all (fun cl' => !decide (cl'.prio < cl0.prio)) = true := by decide +kernel

/-- **`f(n) = n` at every integer n, for every H**: the clause matches and has no condition. -/
theorem eval_all (H : HookParams) (n : Int) : Eval (cH H) f [int n] (some (int n)) := by
  have hσ : (cH H).WellSorted cl0.vars [(0, int n)] := by
    intro i s hi
    rw [cl0_vars] at hi
    match i, hi with
    | 0, hi => cases hi; exact ⟨int n, rfl, rfl⟩
    | k + 1, hi => simp at hi
  have hm : PatVals (cH H) [(0, int n)] cl0.pats [int n] := by
    rw [cl0_pats]; exact .cons (.var rfl) .nil
  have hr : EvalTerm (cH H) [(0, int n)] cl0.rhs (some (int n)) := by
    rw [cl0_rhs]; exact .var
  exact .clause (cl := cl0) (σ := [(0, int n)]) (hfnH H) (List.getElem_mem _) hσ hm
    (fun t ht => by rw [cl0_req] at ht; cases ht) (by rw [cl0_pre]; exact .top)
    (fun cl' hcl' _ hlt => absurd hlt (by simpa using List.all_eq_true.mp cl0_least cl' hcl')) (by rfl) hr
    (fun t ht => by rw [cl0_ens] at ht; cases ht) (Clause.holds_postTop (by rfl) _)

/-- The value table of `f`: `f(n) = n`. -/
def fTable : InertEvUser.ValTable := fun s =>
  if s = f then some fun ws => match ws with
    | [.dv _ (.int n)] => some (int n)
    | _ => none
  else none

/-- **The table is `Eval`'s**, for every H. -/
theorem table_ok (H : HookParams) : InertEvUser.TableOK (cH H) fTable := by
  intro s g fn' ws hg _ hfn' hws
  by_cases hs : s = f
  · subst hs
    simp only [fTable, ite_true, Option.some.injEq] at hg
    subst hg
    have he : fn' = fn := Option.some.inj (hfn'.symm.trans (hfnH H))
    subst he
    rw [fn_args, Semantics.sortsOf_withHooks _ _ noRaw] at hws
    obtain ⟨w, ws', rfl, hw, hws'⟩ := sortsOf_inv_cons hws
    cases sortsOf_inv_nil hws'
    obtain ⟨n, rfl⟩ := shape_int shapesOK_c hw
    exact eval_all H n
  · simp [fTable, hs] at hg

/-! ## The sentence, entailed at values -/

/-- The sentence. -/
noncomputable abbrev ensAx : AxiomDecl := U.ax201

/-- The reader's class of the sentence. -/
theorem ens_class : Parse.classify (.axiom ensAx.ax) = .inert .simplification := by decide +kernel

def vars : LibEv.Vars := [("VarX", Srt.int)]
/-- `f(f(X)) => f(X)` as an equation over `f`. -/
def E : LibEv.Eqn := ⟨vars, Srt.int, none, .app f [.app f [.var 0]], .app f [.var 0]⟩
/-- The `ensures`: `f(X) ==Int X`. -/
def tG : Term := .app intEq [.app f [.var 0], .var 0]

theorem ens_text : ensAx.ax.pattern = Gen.ensPattern c E tG ∧ ensAx.ax.sortVars = [Rv] ∧
    (trS ensAx).pat = (trAxiom [] [] ensAx).pat ∧
    LibEv.vkey c E.vars 0 ∈ freeOf [] ensAx.ax.pattern := by
  decide +kernel

kernel_rfl pattern_wh : ∀ H : HookParams, Gen.ensPattern (cH H) E tG = Gen.ensPattern c E tG
kernel_rfl vkey_wh : ∀ H : HookParams, LibEv.vkey (cH H) E.vars 0 = LibEv.vkey c E.vars 0

theorem typed : InertEvUser.EqnU.typed c fTable E = true := by decide +kernel
kernel_rfl typed_wh : ∀ H : HookParams, InertEvUser.EqnU.typed (cH H) fTable E = InertEvUser.EqnU.typed c fTable E
theorem typedG : InertEvUser.srtU? c fTable E.vars tG = some Srt.bool := by decide +kernel
kernel_rfl typedG_wh : ∀ H : HookParams, InertEvUser.srtU? (cH H) fTable E.vars tG = InertEvUser.srtU? c fTable E.vars tG

theorem appU_f (H : HookParams) : InertEvUser.appU (cH H) fTable f = fun ws => match ws with
    | [.dv _ (.int n)] => some (int n)
    | _ => none := InertEvUser.appU_fn hkf (by simp [fTable])
theorem hkEq : lookupSig hookSigs intEq = some ⟨intEq, [Srt.int, Srt.int], Srt.bool⟩ := by decide +kernel

/-- `f(f(n)) = f(n)` at every integer n, under the table. -/
theorem holds (H : HookParams) : InertEvUser.EqnU.Holds (cH H) fTable E := by
  intro σ hσ _
  obtain ⟨v, hv, hvs⟩ := hσ 0 _ rfl
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hvs
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c hvs
  simp only [E, InertEvUser.valU, InertEvUser.valUList, allSome, hv, appU_f, Option.bind_some, Option.map_some]
  rfl

/-- `f(n) ==Int n` is `true` at every integer n, under the table. -/
theorem ens_true (H : HookParams) : ∀ σ : Subst,
    (∀ i p, E.vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ (cH H).sortOf v = some p.2) →
    (∀ q, E.req = some q → InertEvUser.valU (cH H) fTable σ q = some (bool true)) →
    InertEvUser.valU (cH H) fTable σ tG = some (bool true) := by
  intro σ hσ _
  obtain ⟨v, hv, hvs⟩ := hσ 0 _ rfl
  rw [Semantics.sortOf_withHooks _ _ noRaw] at hvs
  obtain ⟨n, rfl⟩ := shape_int shapesOK_c hvs
  simp only [tG, InertEvUser.valU, InertEvUser.valUList, allSome, hv, appU_f, Option.bind_some, Option.map_some,
    InertEvUser.appU_hook hkEq]
  show (cH H).hv intEq [int n, int n] = some (bool true)
  rw [LibEv.fhv_intEq]
  simp

/-- **The simplification sentence is entailed by Γ at values**, for every H. -/
theorem ens_entailed (H : HookParams) : EntailsAtValues (cH H) ensAx (trS ensAx).pat := by
  obtain ⟨hp, hsv, htr, hfv⟩ := ens_text
  rw [htr]
  refine Gen.ensEqn_entailed (coreOKH H) (hokH H) (table_ok H) E tG ((typed_wh H).trans typed)
    ((typedG_wh H).trans typedG) (holds H) (ens_true H) ensAx (hp.trans (pattern_wh H).symm) hsv (fun i hi => ?_)
  have : i = 0 := by simp [E, vars] at hi; omega
  subst this
  rw [vkey_wh H]; exact hfv

end KCore.C3SimpEnsTrue

#check @KCore.C3SimpEnsTrue.ens_entailed
/-- info: 'KCore.C3SimpEnsTrue.ens_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.C3SimpEnsTrue.ens_entailed
