/-
  KCore, outside the cone: the constructor sentences a text states of a function-overloaded symbol
  `f` (an overloading symbol `o`, one of whose overloads is a function), at values, against what
  evaluation gives the application `f(v̄)`.

  Γ holds the functionality, injectivity and distinctness of `f` at the arguments no overload
  covers only (`KcoreSpec/TieOvlFn.lean`). At arguments a function overload `g` covers, Γ says of
  `f(v̄)` what it says of `g` at the stripped arguments, lifted (the overload's equation). So what
  the text's sentences say there is a condition on the interpretation of the hooks' parameters,
  stated here over values:

  - `OvlFnRes c o vs r`: the result of `f(vs)`: the normal form where no function overload covers
    `vs`, the covering function's result at the stripped arguments, lifted, where one does (`none`
    where the function has no value). It is `EvalTerm.ovl` and `EvalTerm.ovlFn` at values.
  - `OvlFnTotal c o`: at every value list a function overload covers, the function has a value.
  - `OvlFnInj c o`: two value lists at which the application has one and the same value are equal.
  - `OvlFnDist c o k`: no value of the application is an application of the constructor `k`.

  In a model of `Γc` of a semantics with `coreOK` and `FnHyp`, the application of `f` to the
  elements of values is what `OvlFnRes` gives (`ovlFnRes_gs`). Hence, for a sentence in the form
  the shape predicates of `TieOvlFn.lean` decide:

  - under each predicate the sentence holds at values, `EntailsAtValuesΓc` (`ovlFnTotal_atValues`,
    `ovlFnInj_atValues`, `ovlFnDist_atValues`);
  - a witness at values against the predicate refutes the sentence: no model of `Γc` satisfies it
    (`ovlFnTotal_refuted`: a covered list where the result is `none`; `ovlFnInj_refuted`: two
    different lists with one value; `ovlFnDist_refuted`: a list whose value is `k(w̄)`). A witness
    is decided by `ovlFnResF` where evaluation is executable (`ovlFnRes_of_F`, under the decided
    `ovlFnExecB`).

  Where every symbol `f` overloads is a function of another result sort, `OvlFnDist` holds
  (`ovlFnDist_of_lifted`) and `OvlFnInj` is asked at covered value lists only (`ovlFnInj_of_cov`);
  where those functions are declared total, `OvlFnTotal` holds under `FnHyp`
  (`ovlFnTotal_of_total`). The three conditions are decided on the semantics.

  The theory is `Γc` and not `Γ`: what a model says of a function at values is read through
  evaluation, which reads the closure axiom of Bool where the semantics reads a confined sort.
  Where it reads none the two are one theory (`Γc_plain`).

  The different-constructors lemmas read the sentence that names the overloading symbol first, and
  `k` is a constructor of the symbol's result sort. The sentence in the other order is read by the
  same two lemmas with the generators exchanged (`ovlFnCov_dist_atValues`, `tieOvlFnDist_shared_at`
  take the two generators in the sentence's order); no text here writes it.

  Over `Γ` alone, with what the model says of the covering function given as a hypothesis, the
  application is read by `ovlFnCov_gs_norm` and `ovlFnCov_gs_fn`, and a sentence is refuted in a
  model of `Γ` from what the model says of the applications (`ovlFnTotal_refuted_gs`,
  `ovlFnInj_refuted_gs`, `ovlFnDist_refuted_gs`). The sentences are read at elements, in any
  interpretation, by `tieOvlFnFun_refuted_at`, `tieOvlFnInj_shared_at` and
  `tieOvlFnDist_shared_at`: none of them asks Cons-Fun of the generator, which Γ does not hold for
  a function-overloaded symbol.
-/
import KcoreSpec.TieOvlFn
import KcoreSpec.LibEvSortPred
import KcoreSpec.FamExCEx
import KcoreSpec.CollExecSound
import KcoreSpec.CollExecStep

set_option autoImplicit false

namespace KCore
open ML Faithful
namespace Faithful

/-! ## The application at values -/

/-- **The result of the overloading symbol `o` at the values `vs`**: where no function it
overloads covers them, the normal form (`norm`); where the function overload `kg` covers them, that
function's result at the stripped arguments, lifted to the symbol's result sort, and `none` where
the function has no value. -/
inductive OvlFnRes (c : Semantics) (o : OvlSig) (vs : List GroundTerm) : Option GroundTerm → Prop where
  | norm (hnf : c.fnCover o.sig.name vs = none) : OvlFnRes c o vs (some (c.norm o.sig.name vs))
  | fn {kg : CtorSig} {r : Option GroundTerm} (hcov : c.fnCover o.sig.name vs = some kg)
      (hev : Eval c kg.name (stripAll kg.args o.sig.args vs) r) :
      OvlFnRes c o vs (r.map (lift kg.result o.sig.result))

/-- **The covering functions of `o` have a value at covered values**: at every value list of the
symbol's argument sorts that a function overload covers, that function has a value at the stripped
arguments. What the text's `functional` sentence of the symbol says at values. -/
def OvlFnTotal (c : Semantics) (o : OvlSig) : Prop :=
  ∀ vs kg, c.sortsOf vs = some o.sig.args → c.fnCover o.sig.name vs = some kg →
    ∃ v, Eval c kg.name (stripAll kg.args o.sig.args vs) (some v)

/-- **The application of `o` is injective at values**: two value lists of the symbol's argument
sorts at which the application has one and the same value are equal. What the text's
same-constructor sentence of the symbol says at values. -/
def OvlFnInj (c : Semantics) (o : OvlSig) : Prop :=
  ∀ us vs v, c.sortsOf us = some o.sig.args → c.sortsOf vs = some o.sig.args →
    OvlFnRes c o us (some v) → OvlFnRes c o vs (some v) → us = vs

/-- **No value of the application of `o` is an application of the constructor `k`**, at value lists
of their argument sorts. What the text's different-constructors sentence of the two says at
values. -/
def OvlFnDist (c : Semantics) (o : OvlSig) (k : CtorSig) : Prop :=
  ∀ us ws, c.sortsOf us = some o.sig.args → c.sortsOf ws = some k.args →
    ¬ OvlFnRes c o us (some (.ctor k.name ws))

/-- The application has a value at every value list, under `OvlFnTotal`. -/
theorem OvlFnTotal.res {c : Semantics} {o : OvlSig} (ht : OvlFnTotal c o) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some o.sig.args) : ∃ v, OvlFnRes c o vs (some v) := by
  cases hcov : c.fnCover o.sig.name vs with
  | none => exact ⟨_, .norm hcov⟩
  | some kg =>
    obtain ⟨v, hv⟩ := ht vs kg hvs hcov
    exact ⟨_, .fn hcov hv⟩

/-! ## The predicates where every overload is a function -/

/-- A value lifted between two different sorts is an injection, not a constructor's term. -/
theorem ovlFnCov_lift_ne_ctor {A B : Srt} (h : A ≠ B) (v : GroundTerm) (f : Sym) (ws : List GroundTerm) :
    lift A B v ≠ .ctor f ws := by
  rw [OvlLaws.lift_ne h]
  cases v <;> simp [injNormal]

/-- Where every symbol the overloading symbol overloads is a function, the application's normal
form at values no function overload covers is the raw application. -/
theorem ovlFnRes_norm_raw {c : Semantics} {o : OvlSig} (hlo : c.lookupOvl o.sig.name = some o)
    (hall : ∀ kg ∈ c.ovlOver o, c.ovlByFn kg = true) {vs : List GroundTerm}
    (hnf : c.fnCover o.sig.name vs = none) : c.norm o.sig.name vs = .ctor o.sig.name vs := by
  refine Model.norm_of_unc_ovlF ?_
  simp only [Semantics.uncovered, hlo, List.all_eq_true, Bool.not_eq_true']
  exact fun kg hkg => (c.fnCover_eq_none_iff.mp hnf) o hlo kg hkg (hall kg hkg)

/-- **`OvlFnDist` where every overload is a function of another result sort** than the symbol's,
and `k` is not the symbol: the application's value is the raw application where no overload covers
the arguments, and an injection where one does; neither is a term of `k`. The condition is decided
on the semantics. -/
theorem ovlFnDist_of_lifted {c : Semantics} {o : OvlSig} (hlo : c.lookupOvl o.sig.name = some o)
    (hL : ((c.ovlOver o).all fun kg => c.ovlByFn kg && kg.result != o.sig.result) = true) {k : CtorSig}
    (hkne : k.name ≠ o.sig.name) : OvlFnDist c o k := by
  have hL' : ∀ kg ∈ c.ovlOver o, c.ovlByFn kg = true ∧ kg.result ≠ o.sig.result := fun kg hkg => by
    have := List.all_eq_true.mp hL kg hkg
    simpa using this
  intro us ws _ _ hres
  generalize hr : some (GroundTerm.ctor k.name ws) = r at hres
  cases hres with
  | norm hnf =>
    rw [ovlFnRes_norm_raw hlo (fun kg hkg => (hL' kg hkg).1) hnf] at hr
    injection hr with hr
    injection hr with hr
    exact hkne hr
  | @fn kg r' hcov hev =>
    obtain ⟨o', ho', hkg, -, -⟩ := OvlLaws.fnCover_some_parts hcov
    rw [hlo] at ho'; cases ho'
    cases r' with
    | none => cases hr
    | some v' =>
      injection hr with hr
      exact ovlFnCov_lift_ne_ctor (hL' kg hkg).2 v' _ _ hr.symm

/-- **`OvlFnInj` from the covered value lists, where every overload is a function of another
result sort** than the symbol's: two raw applications with one value have the same arguments, a raw
application is no injection, and what is left is two value lists that function overloads cover,
whose functions' values, lifted, are equal. -/
theorem ovlFnInj_of_cov {c : Semantics} {o : OvlSig} (hlo : c.lookupOvl o.sig.name = some o)
    (hL : ((c.ovlOver o).all fun kg => c.ovlByFn kg && kg.result != o.sig.result) = true)
    (hcov : ∀ us vs kg kg' v v', c.sortsOf us = some o.sig.args → c.sortsOf vs = some o.sig.args →
      c.fnCover o.sig.name us = some kg → c.fnCover o.sig.name vs = some kg' →
      Eval c kg.name (stripAll kg.args o.sig.args us) (some v) →
      Eval c kg'.name (stripAll kg'.args o.sig.args vs) (some v') →
      lift kg.result o.sig.result v = lift kg'.result o.sig.result v' → us = vs) : OvlFnInj c o := by
  have hL' : ∀ kg ∈ c.ovlOver o, c.ovlByFn kg = true ∧ kg.result ≠ o.sig.result := fun kg hkg => by
    have := List.all_eq_true.mp hL kg hkg
    simpa using this
  have hmem : ∀ {vs : List GroundTerm} {kg : CtorSig}, c.fnCover o.sig.name vs = some kg → kg ∈ c.ovlOver o :=
    fun hc => by
      obtain ⟨o', ho', hkg, -, -⟩ := OvlLaws.fnCover_some_parts hc
      rw [hlo] at ho'; cases ho'
      exact hkg
  intro us vs v hus hvs h1 h2
  generalize hr1 : some v = r1 at h1
  generalize hr2 : some v = r2 at h2
  cases h1 with
  | norm hnf1 =>
    rw [ovlFnRes_norm_raw hlo (fun kg hkg => (hL' kg hkg).1) hnf1] at hr1
    injection hr1 with hr1
    cases h2 with
    | norm hnf2 =>
      rw [ovlFnRes_norm_raw hlo (fun kg hkg => (hL' kg hkg).1) hnf2] at hr2
      injection hr2 with hr2
      rw [hr1] at hr2
      injection hr2
    | @fn kg' r' hcov2 hev2 =>
      cases r' with
      | none => cases hr2
      | some v' =>
        injection hr2 with hr2
        rw [hr1] at hr2
        exact absurd hr2.symm (ovlFnCov_lift_ne_ctor (hL' kg' (hmem hcov2)).2 v' _ _)
  | @fn kg r hcov1 hev1 =>
    cases r with
    | none => cases hr1
    | some w =>
      injection hr1 with hr1
      cases h2 with
      | norm hnf2 =>
        rw [ovlFnRes_norm_raw hlo (fun kg hkg => (hL' kg hkg).1) hnf2] at hr2
        injection hr2 with hr2
        rw [hr1] at hr2
        exact absurd hr2 (ovlFnCov_lift_ne_ctor (hL' kg (hmem hcov1)).2 w _ _)
      | @fn kg' r' hcov2 hev2 =>
        cases r' with
        | none => cases hr2
        | some w' =>
          injection hr2 with hr2
          exact hcov us vs kg kg' w w' hus hvs hcov1 hcov2 hev1 hev2 (hr1.symm.trans hr2)

/-! ## The application in a model of Γ -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- What the generator of an overloading symbol builds from the elements of values of its argument
sorts is what its raw application denotes. -/
theorem ovlFnCov_gs_den (hI : I ⊧ᴵP Γ c) [hO : OvlOK c] {o : OvlSig} (hlo : c.lookupOvl o.sig.name = some o)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some o.sig.args) (e : Valuation M) (m : M) :
    GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) (vs.map (elemOf c I)) m ↔
      (KoreAML.den (symApp c o.sig.name (GroundTerm.koreList c vs))).interpret I e m := by
  have hsym : KoreAML.den (symApp c o.sig.name (GroundTerm.koreList c vs)) = den c (.ctor o.sig.name vs) := by
    rw [symApp_noInst (OvlLaws.ovl_noInst_irs hO.ok hlo)]; rfl
  rw [hsym, den_sig_gs hI rfl hvs e m]

/-- **An application no function overload covers, in a model of Γ**: the element of its normal
form. -/
theorem ovlFnCov_gs_norm (hI : I ⊧ᴵP Γ c) [hO : OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {o : OvlSig} (hlo : c.lookupOvl o.sig.name = some o) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some o.sig.args) (hnf : c.fnCover o.sig.name vs = none) (m : M) :
    GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) (vs.map (elemOf c I)) m ↔
      m = elemOf c I (c.norm o.sig.name vs) := by
  have H : OvlLaws.OvlHyp c := hO.hyp htr
  rw [ovlFnCov_gs_den hI hlo hvs KoreAML.val0 m, (normDen_of hI htr).1 hlo hvs hnf KoreAML.val0 m]
  exact (elemOf_spec hI (OvlLaws.sortOf_norm_ovlF H H.fnFacts hlo hvs hnf) KoreAML.val0).1 m

/-- **An application a function overload covers, in a model of Γ**: what the model says the
function is at the stripped arguments (`hg`, the function's graph there), lifted to the symbol's
result sort; nothing where the function denotes nothing. -/
theorem ovlFnCov_gs_fn (hI : I ⊧ᴵP Γ c) [hO : OvlOK c]
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    (hnn : NamesNumbered c) {o : OvlSig} (hlo : c.lookupOvl o.sig.name = some o) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some o.sig.args) {kg : CtorSig} {r : Option GroundTerm}
    (hcov : c.fnCover o.sig.name vs = some kg) (hr : ∀ v, r = some v → c.sortOf v = some kg.result)
    (hg : ∀ m, (KoreAML.den (symApp c kg.name (GroundTerm.koreList c (stripAll kg.args o.sig.args vs)))).interpret I
      KoreAML.val0 m ↔ Res c I KoreAML.val0 r m) (m : M) :
    GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) (vs.map (elemOf c I)) m ↔
      Res c I KoreAML.val0 (r.map (lift kg.result o.sig.result)) m := by
  rw [ovlFnCov_gs_den hI hlo hvs KoreAML.val0 m]
  exact covDen_of hI htr hlo hvs hcov (namesNumbered_cover hnn hlo hcov) hr KoreAML.val0 hg m

/-- Two value lists of the same sorts with the same elements are equal. -/
theorem ovlFnCov_elems_inj (hI : I ⊧ᴵP Γ c) [OvlOK c] (hg : genWf c = true)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts) :
    ∀ {us vs : List GroundTerm} {ss : List Srt}, c.sortsOf us = some ss → c.sortsOf vs = some ss →
      us.map (elemOf c I) = vs.map (elemOf c I) → us = vs
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | u :: us, v :: vs, ss, hu, hv, h => by
    obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOf_cons.mp hu
    obtain ⟨s', ss'', h1', h2', he⟩ := sortsOf_cons.mp hv
    cases he
    simp only [List.map_cons, List.cons.injEq] at h
    rw [values_apart hI hg htr (apartSort_of_sorted hg h1) h1 h1' h.1, ovlFnCov_elems_inj hI hg htr h2 h2' h.2]

end

/-! ## The application in a model of Γc, by evaluation -/

/-- The value the application has is of the symbol's result sort. -/
theorem ovlFnRes_sorted {c : Semantics} (h : c.coreOK = true) {o : OvlSig} (hlo : c.lookupOvl o.sig.name = some o)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some o.sig.args) {r : Option GroundTerm} (hres : OvlFnRes c o vs r)
    {v : GroundTerm} (hv : r = some v) : c.sortOf v = some o.sig.result := by
  have hex := Semantics.coreOK_iff_ex.mp h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx hex
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have H : OvlLaws.OvlHyp c := hno.hyp hsc.trans
  cases hres with
  | norm hnf => cases hv; exact OvlLaws.sortOf_norm_ovlF H H.fnFacts hlo hvs hnf
  | @fn kg r' hcov hev =>
    obtain ⟨fn, hfn, hlook, hsig, hkg, hb, -, hus⟩ := OvlLaws.fnCover_fn_ovlF H.fnFacts hlo hvs hcov
    cases r' with
    | none => cases hv
    | some v' =>
      cases hv
      have hres : kg.result = fn.result := by rw [hsig]
      exact OvlLaws.sortOf_lift H (by rw [hres]; exact Eval.sorted hsc hev hlook hus rfl)
        (OvlLaws.over_ovlF H.fnFacts hlo hkg).2.2.1

/-- **The application has a result at every value list of the symbol's argument sorts**, under
`FnHyp`: each function has one at every argument list of its sorts. -/
theorem ovlFnRes_exists {c : Semantics} (h : c.coreOK = true) (hf : FnHyp c) {o : OvlSig}
    (hlo : c.lookupOvl o.sig.name = some o) {vs : List GroundTerm} (hvs : c.sortsOf vs = some o.sig.args) :
    ∃ r, OvlFnRes c o vs r := by
  have hex := Semantics.coreOK_iff_ex.mp h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx hex
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have H : OvlLaws.OvlHyp c := hno.hyp hsc.trans
  cases hcov : c.fnCover o.sig.name vs with
  | none => exact ⟨_, .norm hcov⟩
  | some kg =>
    obtain ⟨fn, hfn, hlook, hsig, hkg, hb, -, hus⟩ := OvlLaws.fnCover_fn_ovlF H.fnFacts hlo hvs hcov
    obtain ⟨r, hr⟩ := hf.1 fn hfn _ hus
    have hname : kg.name = fn.label := by rw [hsig]
    exact ⟨_, .fn hcov (hname ▸ hr)⟩

/-- **`OvlFnTotal` where the functions the symbol overloads are declared total**, under `FnHyp`,
which gives a `[total]` function a value at every argument list of its sorts. The condition is
decided on the semantics. -/
theorem ovlFnTotal_of_total {c : Semantics} (h : c.coreOK = true) (hf : FnHyp c) {o : OvlSig}
    (hlo : c.lookupOvl o.sig.name = some o)
    (htot : (c.fns.all fun fn => !(c.ovlOver o).any (·.name == fn.label) || fn.total) = true) :
    OvlFnTotal c o := by
  have hex := Semantics.coreOK_iff_ex.mp h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx hex
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have H : OvlLaws.OvlHyp c := hno.hyp hsc.trans
  intro vs kg hvs hcov
  obtain ⟨fn, hfn, hlook, hsig, hkg, hb, -, hus⟩ := OvlLaws.fnCover_fn_ovlF H.fnFacts hlo hvs hcov
  have hname : kg.name = fn.label := by rw [hsig]
  have ht : fn.total = true := by
    have h1 := List.all_eq_true.mp htot fn hfn
    rcases Bool.or_eq_true _ _ ▸ h1 with h2 | h2
    · have : (c.ovlOver o).any (·.name == fn.label) = true :=
        List.any_eq_true.mpr ⟨kg, hkg, by rw [hname]; exact beq_self_eq_true _⟩
      rw [this] at h2; cases h2
    · exact h2
  obtain ⟨v, hv⟩ := hf.2.1 fn hfn ht _ hus
  exact ⟨v, hname ▸ hv⟩

/-- **The result of the application, computed**: the normal form where no function overload covers
the values, and the executable evaluator's result of the covering function (`CExec.evalF`, with
the fuel `n`) at the stripped arguments, lifted, where one does. `none`: the fuel ran out. -/
def ovlFnResF (c : Semantics) (o : OvlSig) (n : Nat) (vs : List GroundTerm) : Option (Option GroundTerm) :=
  match c.fnCover o.sig.name vs with
  | none => some (some (c.norm o.sig.name vs))
  | some kg => (CExec.evalF c n kg.name (stripAll kg.args o.sig.args vs)).map (·.map (lift kg.result o.sig.result))

/-- **What the executable evaluator's soundness reads of the functions' clauses**, decided on the
semantics: their predicates are `\top` and they bind no variable by `\exists`, and the clauses'
matcher is complete (the overloading symbols well formed for matching, each clause's patterns in
the matcher's fragment and binding every variable). Nothing is asked of the rules. -/
def ovlFnExecB (c : Semantics) : Bool :=
  c.clausesPreTop && c.matchReadyO &&
  c.allFns.all fun fn => fn.clauses.all fun cl =>
    CExec.readyL c cl.vars cl.pats && binds cl.vars.length (varOccsList cl.pats) && cl.exs.isEmpty && cl.post.isTop

/-- **A result `ovlFnResF` computes is the application's** (`OvlFnRes`), for a semantics with
`coreOK` whose clauses `ovlFnExecB` accepts: the executable evaluator is sound there
(`CExec.evalF_sound`). A witness for a refutation is decided this way. -/
theorem ovlFnRes_of_F {c : Semantics} (h : c.coreOK = true) (hx : ovlFnExecB c = true) {o : OvlSig}
    (hlo : c.lookupOvl o.sig.name = some o) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some o.sig.args) {n : Nat} {r : Option GroundTerm} (hF : ovlFnResF c o n vs = some r) :
    OvlFnRes c o vs r := by
  have hex := Semantics.coreOK_iff_ex.mp h
  obtain ⟨hokx, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx hex
  have hok : c.sortedOK = true := (Semantics.coreOK_parts h).1
  have hsc := sortCtx_of_allCEx hokx hsr (OvlOK.ovlCase hno)
  have H : OvlLaws.OvlHyp c := hno.hyp hsc.trans
  unfold ovlFnExecB at hx
  rw [Bool.and_eq_true, Bool.and_eq_true] at hx
  obtain ⟨⟨hpreTop, hmr⟩, hfns⟩ := hx
  have hcl : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, CExec.readyL c cl.vars cl.pats = true ∧
      binds cl.vars.length (varOccsList cl.pats) = true ∧ cl.exs = [] ∧ cl.post = .top := fun fn hfn cl hcl => by
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp hfns fn hfn) cl hcl
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h1
    obtain ⟨⟨⟨h2, h3⟩, h4⟩, h5⟩ := h1
    refine ⟨h2, h3, List.isEmpty_iff.mp h4, ?_⟩
    cases hp : cl.post with
    | top => rfl
    | _ => rw [hp] at h5; exact absurd h5 (by simp [Cond.isTop])
  have hcc : CExec.CClauseCtx c := CExec.cclauseCtx_of hpreTop hok fun fn hfn cl hcl' => (hcl fn hfn cl hcl').2.2
  have hcm : CExec.ClauseComplete c := by
    intro fn hfn cl hcl' ws τ _ hτ hpv
    obtain ⟨h2, h3, -, -⟩ := hcl fn hfn cl hcl'
    exact CExec.cmatch_complete (Exec.matchCtxO_of hmr) (Clause.wellSorted_of_at h3 hτ) hpv h2 h3
      (CExec.clausePats_nf hok (Exec.matchCtxO_of hmr) hfn hcl')
  unfold ovlFnResF at hF
  cases hcov : c.fnCover o.sig.name vs with
  | none =>
    rw [hcov] at hF
    cases hF
    exact .norm hcov
  | some kg =>
    rw [hcov] at hF
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp hF
    obtain ⟨fn, hfn, hlook, hsig, hkg, hb, -, hus⟩ := OvlLaws.fnCover_fn_ovlF H.fnFacts hlo hvs hcov
    exact .fn hcov (CExec.evalF_sound hsc hcc hcm n hr' hlook hus)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The application of an overloading symbol to the elements of values, in a model of `Γc`**, is
what its result denotes: the value's element, or nothing where the covering function has no value.
For a semantics with `coreOK`, under `FnHyp`. -/
theorem ovlFnRes_gs (h : c.coreOK = true) (hf : FnHyp c) (hIc : I ⊧ᴵP Γc c) {o : OvlSig}
    (hlo : c.lookupOvl o.sig.name = some o) {vs : List GroundTerm} (hvs : c.sortsOf vs = some o.sig.args)
    {r : Option GroundTerm} (hres : OvlFnRes c o vs r) (m : M) :
    GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) (vs.map (elemOf c I)) m ↔
      Res c I KoreAML.val0 r m := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have hex := Semantics.coreOK_iff_ex.mp h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx hex
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have H : OvlLaws.OvlHyp c := hno.hyp hsc.trans
  cases hres with
  | norm hnf =>
    show _ ↔ (den c _).interpret I KoreAML.val0 m
    rw [ovlFnCov_gs_norm hI hsc.trans hlo hvs hnf m,
      (elemOf_spec hI (OvlLaws.sortOf_norm_ovlF H H.fnFacts hlo hvs hnf) KoreAML.val0).1 m]
  | @fn kg r' hcov hev =>
    obtain ⟨fn, hfn, hlook, hsig, hkg, hb, -, hus⟩ := OvlLaws.fnCover_fn_ovlF H.fnFacts hlo hvs hcov
    have hres : kg.result = fn.result := by rw [hsig]
    have hpre := HoldsShape.preReadAll_of_coreEx hex hIc
    have hneg := neg_of_coreClEx hIc (Semantics.sortedOKClEx_of_sortedOKEx hok) hsr (Semantics.coreOKEx_parts hex).2.1
      hph hf.2.2.2.2.1.2 hpre
    have hgd := eval_den4ClQ hI hnn hsc hph (clauseOpenFactsQ_of_sortedOKEx hok) hneg hpre
      (clauseExRead_all_of_coreEx hex hIc) hev hlook hus KoreAML.val0
    exact ovlFnCov_gs_fn hI hsc.trans hnn hlo hvs hcov
      (fun v hv => by rw [hres]; exact Eval.sorted hsc hev hlook hus hv) hgd m

/-- Where the application has a value, it holds that value's element only, an element of the
symbol's result sort. -/
theorem ovlFnRes_elem (h : c.coreOK = true) (hf : FnHyp c) (hIc : I ⊧ᴵP Γc c) {o : OvlSig}
    (hlo : c.lookupOvl o.sig.name = some o) {vs : List GroundTerm} (hvs : c.sortsOf vs = some o.sig.args)
    {v : GroundTerm} (hres : OvlFnRes c o vs (some v)) :
    InS I (c.sortName o.sig.result) (elemOf c I v) ∧
      ∀ m, GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) (vs.map (elemOf c I)) m ↔ m = elemOf c I v := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have hs := elemOf_spec hI (ovlFnRes_sorted h hlo hvs hres rfl) KoreAML.val0
  exact ⟨(inS_iff _).mp hs.2, fun m => (ovlFnRes_gs h hf hIc hlo hvs hres m).trans (hs.1 m)⟩

/-- Where the application has no value, it holds no element. -/
theorem ovlFnRes_empty (h : c.coreOK = true) (hf : FnHyp c) (hIc : I ⊧ᴵP Γc c) {o : OvlSig}
    (hlo : c.lookupOvl o.sig.name = some o) {vs : List GroundTerm} (hvs : c.sortsOf vs = some o.sig.args)
    (hres : OvlFnRes c o vs none) (m : M) :
    ¬ GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) (vs.map (elemOf c I)) m :=
  fun hm => (ovlFnRes_gs h hf hIc hlo hvs hres m).mp hm

/-- **Two applications that hold a common element have one and the same value.** -/
theorem ovlFnRes_shared (h : c.coreOK = true) (hf : FnHyp c) (hIc : I ⊧ᴵP Γc c) {o : OvlSig}
    (hlo : c.lookupOvl o.sig.name = some o) {us vs : List GroundTerm} (hus : c.sortsOf us = some o.sig.args)
    (hvs : c.sortsOf vs = some o.sig.args) {y : M}
    (h1 : GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) (us.map (elemOf c I)) y)
    (h2 : GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) (vs.map (elemOf c I)) y) :
    ∃ v, OvlFnRes c o us (some v) ∧ OvlFnRes c o vs (some v) := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have hex := Semantics.coreOK_iff_ex.mp h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx hex
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hgw : genWf c = true := (faithCoreOK_parts (Semantics.coreOK_parts h).2.1).2.1
  obtain ⟨r1, hr1⟩ := ovlFnRes_exists h hf hlo hus
  obtain ⟨r2, hr2⟩ := ovlFnRes_exists h hf hlo hvs
  cases r1 with
  | none => exact absurd h1 (ovlFnRes_empty h hf hIc hlo hus hr1 y)
  | some v1 =>
    cases r2 with
    | none => exact absurd h2 (ovlFnRes_empty h hf hIc hlo hvs hr2 y)
    | some v2 =>
      have e1 := ((ovlFnRes_elem h hf hIc hlo hus hr1).2 y).mp h1
      have e2 := ((ovlFnRes_elem h hf hIc hlo hvs hr2).2 y).mp h2
      have hv1 := ovlFnRes_sorted h hlo hus hr1 rfl
      have hv2 := ovlFnRes_sorted h hlo hvs hr2 rfl
      have : v1 = v2 := values_apart hI hgw hsc.trans (apartSort_of_sorted hgw hv1) hv1 hv2 (e1.symm.trans e2)
      subst this
      exact ⟨v1, hr1, hr2⟩

/-- **The application and a constructor's hold a common element only where the application's value
is the constructor's term.** -/
theorem ovlFnRes_shared_ctor (h : c.coreOK = true) (hf : FnHyp c) (hIc : I ⊧ᴵP Γc c) {o : OvlSig}
    (hlo : c.lookupOvl o.sig.name = some o) {k : CtorSig} (hk : lookupSig c.ctorSigs k.name = some k)
    (hkN : k.result = o.sig.result) {us ws : List GroundTerm} (hus : c.sortsOf us = some o.sig.args)
    (hws : c.sortsOf ws = some k.args) {y : M}
    (h1 : GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) (us.map (elemOf c I)) y)
    (h2 : GS I (c.sortName o.sig.result) (Gen.toK c (.ctor k)) (ws.map (elemOf c I)) y) :
    OvlFnRes c o us (some (.ctor k.name ws)) := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have hex := Semantics.coreOK_iff_ex.mp h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx hex
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hgw : genWf c = true := (faithCoreOK_parts (Semantics.coreOK_parts h).2.1).2.1
  have hkw : c.sortOf (.ctor k.name ws) = some o.sig.result := sortOf_ctor_intro ⟨k, hk, hws, hkN.symm⟩
  have e2 : y = elemOf c I (.ctor k.name ws) := by
    rw [← hkN] at h2
    exact ((elemOf_spec hI hkw KoreAML.val0).1 y).mp ((den_ctor_gs hI hk hws KoreAML.val0 y).mpr h2)
  obtain ⟨r1, hr1⟩ := ovlFnRes_exists h hf hlo hus
  cases r1 with
  | none => exact absurd h1 (ovlFnRes_empty h hf hIc hlo hus hr1 y)
  | some v1 =>
    have e1 := ((ovlFnRes_elem h hf hIc hlo hus hr1).2 y).mp h1
    have hv1 := ovlFnRes_sorted h hlo hus hr1 rfl
    have : v1 = .ctor k.name ws :=
      values_apart hI hgw hsc.trans (apartSort_of_sorted hgw hv1) hv1 hkw (e1.symm.trans e2)
    rw [this] at hr1
    exact hr1

/-- The valuation of a sentence at values (`AtValues`) sends variables of the sorts `ss` to the
elements of a value list of those sorts. -/
theorem ovlFnCov_vals (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {e : Valuation M} {a : Kore.Axiom}
    (hat : AtValues c I e a) :
    ∀ (ks : List Kore.EVar) (ss : List Srt), ks.map (·.sort) = (ss.map c.sortName).map KoreAML.srt →
      (∀ s ∈ ss, s < nRegSorts + c.sortNames.length) →
      (∀ k ∈ ks, KoreAML.evarKey k ∈ (KoreAML.freeOf [] a.pattern).eraseDups) →
      ∃ ws, c.sortsOf ws = some ss ∧ ws.map (elemOf c I) =
        (ks.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map e.evalEvar
  | [], [], _, _, _ => ⟨[], sortsOf_nil, rfl⟩
  | [], _ :: _, hs, _, _ => by simp at hs
  | _ :: _, [], hs, _, _ => by simp at hs
  | k :: ks, s :: ss, hs, hnum, hfree => by
    haveI : OvlOK c := ovlOK_of_core h
    obtain ⟨-, hfa, -, -, -⟩ := Semantics.coreOK_parts h
    obtain ⟨-, hg, -, -, -, hn, -, hsn, -, -, -, -⟩ := faithCoreOK_parts hfa
    simp only [List.map_cons, List.cons.injEq] at hs
    obtain ⟨ws, hws, hel⟩ := ovlFnCov_vals h hI hat ks ss hs.2
      (fun s' hs' => hnum s' (List.mem_cons_of_mem _ hs')) (fun k' hk' => hfree k' (List.mem_cons_of_mem _ hk'))
    obtain ⟨v, S, hS, hv, hden⟩ := hat k.var.ident.name k.sort (hfree k (List.mem_cons_self ..))
    have hSe : S = s :=
      sort_eq_of_name hn (sortOf_numbered_ofCl hg hsn (Semantics.coreOK_ovls h) hv)
        (hnum s (List.mem_cons_self ..)) (srt_inj (hS.trans hs.1))
    subst hSe
    refine ⟨v :: ws, sortsOf_cons.mpr ⟨_, _, hv, hws, rfl⟩, ?_⟩
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨(((elemOf_spec hI hv e).1 _).mp hden).symm, hel⟩

end

/-! ## The sentences at elements, in any interpretation -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {c : Semantics}

omit [Inhabited M] in
/-- Conjunctions `x ∧ y` of variables that take the same elements hold those elements. -/
theorem tieOvlFnCov_zipAnd_all2 {e : Valuation M} : ∀ (ix iy : List EVar),
    ix.map e.evalEvar = iy.map e.evalEvar →
    All2 (fun φ x => ∀ m, φ.interpret I e m ↔ m = x)
      ((ix.zip iy).map fun p => KoreAML.sAnd (.evar p.1) (.evar p.2)) (ix.map e.evalEvar)
  | [], [], _ => .nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: ix, y :: iy, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.zip_cons_cons, List.map_cons]
    refine .cons (fun m => ?_) (tieOvlFnCov_zipAnd_all2 ix iy h.2)
    rw [KoreAML.interp_sAnd, KoreAML.interp_evar, KoreAML.interp_evar]
    exact ⟨fun hm => hm.1, fun hm => ⟨hm, hm.trans h.1⟩⟩

/-- A generator applied to conjunctions `x ∧ y` of variables that take the same elements builds
what it builds from those elements. -/
theorem tieOvlFnCov_zipAnd_gs {e : Valuation M} (N : String) (g : KoreAML.Gen) (ix iy : List EVar)
    (h : ix.map e.evalEvar = iy.map e.evalEvar) (m : M) :
    (KoreAML.Cons.genPat N g ((ix.zip iy).map fun p => KoreAML.sAnd (.evar p.1) (.evar p.2))).interpret I e m ↔
      GS I N g (ix.map e.evalEvar) m := by
  rw [genPat_eq, interp_appList_sing _ _ (ix.map e.evalEvar) (tieOvlFnCov_zipAnd_all2 ix iy h)]
  unfold GS
  simp only [(genHead_closed N g).interp e KoreAML.val0]

/-- **A `functional` sentence is not satisfied where its generator builds nothing** from some
elements of its argument sorts: the sentence makes the application one element of N there
(`tieOvlFnFun_at`). In every interpretation with `TieOvlFnBase`. -/
theorem tieOvlFnFun_refuted_at {N : Srt} {g : KoreAML.Gen} {a : Kore.Axiom}
    (h : tieOvlFnFunShapeB c N g a = true) (hB : TieOvlFnBase I (c.sortName N))
    {xs : List M} (hl : xs.length = g.argSorts.length)
    (hxs : ∀ (i : Nat) x s, xs[i]? = some x → g.argSorts[i]? = some s → InS I s x)
    (hemp : ∀ m, ¬ GS I (c.sortName N) g xs m) {i : Nat} {mod : String} :
    ¬ (I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) := by
  intro hsent
  obtain ⟨σN, hσN1, hσN2⟩ := hB.sortN
  obtain ⟨σR, x0, hσR, hx0⟩ := hB.inh
  unfold tieOvlFnFunShapeB at h
  split at h
  · rename_i r val s r' val' body hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
    subst h1 h2 h3 h4
    obtain ⟨v, hv, hone⟩ := tieOvlFnFun_at hB.defOK hB.ceil hσN1 hσN2 hσR hx0 hp h6 h7 h8 h9 h10 h11 hsent hl hxs
    exact hemp v ((hone v hv).mpr rfl)
  · cases h

/-- **A same-constructor sentence, where two applications of its generator hold a common element
of N**: the two argument lists are equal. The sentence is `f(X̄) ∧ f(Ȳ) → f(X̄ ∧ Ȳ)`, read at the
valuation sending X̄ and Ȳ to the two lists. Cons-Fun of the generator is not asked. -/
theorem tieOvlFnInj_shared_at {N : Srt} {g : KoreAML.Gen} {a : Kore.Axiom}
    (h : tieOvlFnInjShapeB c N g a = true) (hD : KoreAML.DefOK I) {i : Nat} {mod : String}
    (hsent : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat)
    {us vs : List M} (hl : us.length = g.argSorts.length) (hl' : vs.length = g.argSorts.length)
    (hus : ∀ (i : Nat) x s, us[i]? = some x → g.argSorts[i]? = some s → InS I s x)
    (hvs : ∀ (i : Nat) x s, vs[i]? = some x → g.argSorts[i]? = some s → InS I s x)
    {y : M} (hyN : InS I (c.sortName N) y) (hy1 : GS I (c.sortName N) g us y) (hy2 : GS I (c.sortName N) g vs y) :
    us = vs := by
  unfold tieOvlFnInjShapeB at h
  split at h
  · rename_i s s' p1 p2 q hpat
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hfree⟩, hxs⟩, hys⟩, hp1⟩, hp2⟩, hq⟩, hnd⟩ := h
    subst h1 h2
    have hat := KoreAML.trAxiom_at hD hsent
    dsimp only at hat
    generalize ht : KoreAML.tableOf a.sortVars a.pattern = t at hat hp1 hp2 hq hnd
    rw [hfree] at hat
    obtain ⟨e, hv1, hv2, hg⟩ := tieOvlFn_val2 hD hxs hys hnd hl hl' hus hvs
    have h1 := hat e hg y
    rw [hpat] at h1
    change (KoreAML.sImp (KoreAML.trSort t (KoreAML.srt (c.sortName N)))
        (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ p1) (KoreAML.tr ⟨t, []⟩ p2)) (KoreAML.tr ⟨t, []⟩ q)).interpret I e y ↔
      (KoreAML.inhOf (KoreAML.trSort t (KoreAML.srt (c.sortName N)))).interpret I e y at h1
    rw [KoreAML.interp_sImp, KoreAML.interp_sAnd, hp1, hp2, tieGen_vars, tieGen_vars, hv1, hv2, trSort_srt] at h1
    have hq' := (h1.mpr ((inS_iff e).mpr hyN)).2 ⟨hy1, hy2⟩
    rw [hq, genPat_eq] at hq'
    have hlen : ((tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups).take g.argSorts.length |>.map
        fun k => t.ev (KoreAML.evarKey k)).length =
        ((tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups).drop g.argSorts.length |>.map
        fun k => t.ev (KoreAML.evarKey k)).length := by
      have e1 := congrArg List.length hxs
      have e2 := congrArg List.length hys
      simp only [List.length_map] at e1 e2
      rw [List.length_map, List.length_map, e1, e2]
    have hmap := tieOvlFn_zipAnd_eq _ _ hlen (tieOvlFn_appList_args _ _ _ hq')
    rw [hv1, hv2] at hmap
    exact hmap
  · cases h

/-- **A different-constructors sentence is not satisfied where the two applications hold a common
element of N.** The sentence is `¬(g(X̄) ∧ g'(Ȳ))`, read at the valuation sending X̄ and Ȳ to the two
lists. Cons-Fun of neither generator is asked. -/
theorem tieOvlFnDist_shared_at {N : Srt} {g g' : KoreAML.Gen} {a : Kore.Axiom}
    (h : tieOvlFnDistShapeB c N g g' a = true) (hD : KoreAML.DefOK I) {i : Nat} {mod : String}
    {us vs : List M} (hl : us.length = g.argSorts.length) (hl' : vs.length = g'.argSorts.length)
    (hus : ∀ (i : Nat) x s, us[i]? = some x → g.argSorts[i]? = some s → InS I s x)
    (hvs : ∀ (i : Nat) x s, vs[i]? = some x → g'.argSorts[i]? = some s → InS I s x)
    {y : M} (hyN : InS I (c.sortName N) y) (hy1 : GS I (c.sortName N) g us y) (hy2 : GS I (c.sortName N) g' vs y) :
    ¬ (I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) := by
  intro hsent
  unfold tieOvlFnDistShapeB at h
  split at h
  · rename_i s s' p1 p2 hpat
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hfree⟩, hxs⟩, hys⟩, hp1⟩, hp2⟩, hnd⟩ := h
    subst h1 h2
    have hat := KoreAML.trAxiom_at hD hsent
    dsimp only at hat
    generalize ht : KoreAML.tableOf a.sortVars a.pattern = t at hat hp1 hp2 hnd
    rw [hfree] at hat
    obtain ⟨e, hv1, hv2, hg⟩ := tieOvlFn_val2 hD hxs hys hnd hl hl' hus hvs
    have h1 := hat e hg y
    rw [hpat] at h1
    change (KoreAML.sNot (KoreAML.trSort t (KoreAML.srt (c.sortName N)))
        (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ p1) (KoreAML.tr ⟨t, []⟩ p2))).interpret I e y ↔
      (KoreAML.inhOf (KoreAML.trSort t (KoreAML.srt (c.sortName N)))).interpret I e y at h1
    rw [KoreAML.interp_sNot, KoreAML.interp_sAnd, hp1, hp2, tieGen_vars, tieGen_vars, hv1, hv2, trSort_srt] at h1
    exact (h1.mpr ((inS_iff e).mpr hyN)).1 ⟨hy1, hy2⟩
  · cases h

end

/-! ## The sentences at values, in a model of Γc -/

/-- A free element variable of an axiom, listed among its sort variables and free variables, is
among its free variables. -/
theorem ovlFnCov_free_mem {a : Kore.Axiom} {keys : List KoreAML.VarKey}
    (hfree : (a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups = keys) {k : Kore.EVar}
    (hk : KoreAML.evarKey k ∈ keys) : KoreAML.evarKey k ∈ (KoreAML.freeOf [] a.pattern).eraseDups := by
  rw [← hfree] at hk
  rcases List.mem_append.mp (List.mem_eraseDups.mp hk) with h1 | h1
  · obtain ⟨α, -, hα⟩ := List.mem_map.mp h1
    exact absurd hα (by simp [KoreAML.sortVarKey, KoreAML.evarKey])
  · exact List.mem_eraseDups.mpr h1

/-- The sorts of an overloading symbol are numbered. -/
theorem ovlFnCov_numbered {c : Semantics} (h : c.coreOK = true) {o : OvlSig} (hlo : c.lookupOvl o.sig.name = some o) :
    ∀ s ∈ o.sig.result :: o.sig.args, s < nRegSorts + c.sortNames.length := fun _ hs =>
  kernel_sort_lt (faithCoreOK_parts (Semantics.coreOK_parts h).2.1).2.2.2.2.2.2.2.1
    (List.mem_append_right _ (List.mem_map_of_mem (OvlLaws.mem_of_lookupOvl hlo))) hs

section
variable {c : Semantics}

/-- **Under `OvlFnTotal`, the `functional` sentence of the overloading symbol holds at values**, in
every model of `Γc` of a semantics with `coreOK`, under `FnHyp`: at values the application has a
value, whose element is the one the sentence asks for. The sentence is in the form
`tieOvlFnFunShapeB` decides. -/
theorem ovlFnTotal_atValues (h : c.coreOK = true) (hf : FnHyp c) {o : OvlSig}
    (hlo : c.lookupOvl o.sig.name = some o) (ht : OvlFnTotal c o) {ad : KoreAML.AxiomDecl}
    (hs : tieOvlFnFunShapeB c o.sig.result (Gen.toK c (.ctor o.sig)) ad.ax = true) :
    EntailsAtValuesΓc c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hIc e hat m
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have hnum := ovlFnCov_numbered h hlo
  unfold tieOvlFnFunShapeB at hs
  split at hs
  · rename_i r val0 s r' val body hpat
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hNlt⟩, hfree⟩, hval⟩, hks⟩, hbody⟩, hfresh⟩, hnd⟩ := hs
    subst h1 h2 h3 h4
    obtain ⟨σN, hσN1, hσN2⟩ := sortSing hI hNlt
    obtain ⟨ws, hws, hel⟩ := ovlFnCov_vals h hI hat _ o.sig.args hks (fun s' hs' => hnum s' (List.mem_cons_of_mem _ hs'))
      (fun k hk => ovlFnCov_free_mem hfree (List.mem_cons_of_mem _ (List.mem_map_of_mem hk)))
    obtain ⟨v, hv⟩ := ht.res hws
    obtain ⟨hyN, hy⟩ := ovlFnRes_elem h hf hIc hlo hws hv
    have hyN' : KoreAML.Inh I σN (elemOf c I v) :=
      (KoreAML.interp_inhOf_of (S := KoreAML.Cons.sortP (c.sortName o.sig.result)) (e := KoreAML.val0)
        (fun a => hσN1 a)).mp hyN
    unfold KoreAML.trAxiom
    dsimp only
    rw [interpret_impl]
    intro hgd
    have hR : KoreAML.IsSort I (e.evalEvar ((KoreAML.tableOf ad.ax.sortVars ad.ax.pattern).ev (.sortVar "R"))) :=
      (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
        by rw [hfree]; exact List.mem_cons_self .., rfl⟩))
    clear hgd
    generalize KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hbody hfresh hnd hel hR ⊢
    have hRv : ∀ (e' : Valuation M) b, (KoreAML.trSort t KoreAML.R).interpret I e' b ↔
        b = e'.evalEvar (t.ev (.sortVar "R")) := fun e' b => by rw [trSort_R, KoreAML.interp_evar]
    have hS : ∀ (e' : Valuation M) b, (KoreAML.trSort t (KoreAML.srt (c.sortName o.sig.result))).interpret I e' b ↔
        b = σN := fun e' b => by rw [trSort_srt]; exact hσN1 b
    have hne : t.ev (.sortVar "R") ≠ t.ev (KoreAML.evarKey val) := fun hh => hfresh (hh ▸ List.mem_cons_self ..)
    have hupd : ∀ x : M, (⟨Function.update e.evalEvar (t.ev (KoreAML.evarKey val)) x, e.evalSvar⟩ : Valuation M).evalEvar
        (t.ev (.sortVar "R")) = e.evalEvar (t.ev (.sortVar "R")) := fun x => Function.update_noteq hne _ _
    have hmap : ∀ x : M, ((tieKeyVars (KoreAML.freeOf [] ad.ax.pattern).eraseDups).map
          fun k => t.ev (KoreAML.evarKey k)).map
        (⟨Function.update e.evalEvar (t.ev (KoreAML.evarKey val)) x, e.evalSvar⟩ : Valuation M).evalEvar =
        ((tieKeyVars (KoreAML.freeOf [] ad.ax.pattern).eraseDups).map
          fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar := fun x =>
      List.map_congr_left fun z hz => Function.update_noteq
        (fun (hh : z = t.ev (KoreAML.evarKey val)) => hfresh (List.mem_cons_of_mem _ (hh ▸ hz))) _ _
    rw [hpat]
    show ((KoreAML.tr ⟨t, []⟩ (.exist KoreAML.R val (.equals (KoreAML.srt (c.sortName o.sig.result)) KoreAML.R
      (.var (.evar val)) body))) ≡ KoreAML.inhOf (KoreAML.trSort t KoreAML.R)).interpret I e m
    rw [KoreAML.interp_equal hD]
    intro a
    rw [KoreAML.tr, KoreAML.interp_sExists, KoreAML.interp_inhOf_of (hRv e)]
    constructor
    · rintro ⟨x, -, hx⟩
      rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hS _) (hRv _) hσN2 (by rw [hupd]; exact hR)] at hx
      rw [hupd] at hx
      exact hx.1
    · intro ha
      refine ⟨elemOf c I v, ?_, ?_⟩
      · rw [KoreAML.interp_member hD]
        simp only [Function.update_same]
        rw [hval]
        exact (KoreAML.interp_inhOf_of (hS _)).mpr hyN'
      · rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hS _) (hRv _) hσN2 (by rw [hupd]; exact hR)]
        refine ⟨by rw [hupd]; exact ha, fun b _ => ?_⟩
        rw [hbody, tieGen_vars, hmap, ← hel, KoreAML.tr, KoreAML.interp_evar]
        simp only [Function.update_same]
        exact (hy b).symm
  · cases hs

/-- **Under `OvlFnInj`, the same-constructor sentence of the overloading symbol holds at values**,
in every model of `Γc` of a semantics with `coreOK`, under `FnHyp`: two applications at values that
hold a common element have one value, so their arguments are equal. The sentence is in the form
`tieOvlFnInjShapeB` decides. -/
theorem ovlFnInj_atValues (h : c.coreOK = true) (hf : FnHyp c) {o : OvlSig}
    (hlo : c.lookupOvl o.sig.name = some o) (hinj : OvlFnInj c o) {ad : KoreAML.AxiomDecl}
    (hs : tieOvlFnInjShapeB c o.sig.result (Gen.toK c (.ctor o.sig)) ad.ax = true) :
    EntailsAtValuesΓc c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hIc e hat m
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hnum := ovlFnCov_numbered h hlo
  unfold tieOvlFnInjShapeB at hs
  split at hs
  · rename_i s s' p1 p2 q hpat
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hfree⟩, hxs⟩, hys⟩, hp1⟩, hp2⟩, hq⟩, hnd⟩ := hs
    subst h1 h2
    obtain ⟨us, hus, hel1⟩ := ovlFnCov_vals h hI hat _ o.sig.args hxs (fun s' hs' => hnum s' (List.mem_cons_of_mem _ hs'))
      (fun k hk => ovlFnCov_free_mem hfree (List.mem_map_of_mem (List.mem_append_left _ hk)))
    obtain ⟨vs, hvs, hel2⟩ := ovlFnCov_vals h hI hat _ o.sig.args hys (fun s' hs' => hnum s' (List.mem_cons_of_mem _ hs'))
      (fun k hk => ovlFnCov_free_mem hfree (List.mem_map_of_mem (List.mem_append_right _ hk)))
    unfold KoreAML.trAxiom
    dsimp only
    rw [interpret_impl]
    intro _
    generalize KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hp1 hp2 hq hnd hel1 hel2 ⊢
    rw [hpat]
    show ((KoreAML.sImp (KoreAML.trSort t (KoreAML.srt (c.sortName o.sig.result)))
        (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ p1) (KoreAML.tr ⟨t, []⟩ p2)) (KoreAML.tr ⟨t, []⟩ q)) ≡
      KoreAML.inhOf (KoreAML.trSort t (KoreAML.srt (c.sortName o.sig.result)))).interpret I e m
    rw [KoreAML.interp_equal hD]
    intro y
    rw [KoreAML.interp_sImp, KoreAML.interp_sAnd, hp1, hp2, tieGen_vars, tieGen_vars, ← hel1, ← hel2, trSort_srt]
    refine ⟨fun hh => hh.1, fun hy => ⟨hy, fun ⟨g1, g2⟩ => ?_⟩⟩
    obtain ⟨v, r1, r2⟩ := ovlFnRes_shared h hf hIc hlo hus hvs g1 g2
    have heq := hinj us vs v hus hvs r1 r2
    subst heq
    rw [hq, tieOvlFnCov_zipAnd_gs _ _ _ _ (by rw [← hel1, ← hel2]), ← hel1]
    exact g1
  · cases hs

/-- A different-constructors sentence of two generators holds at values where, at values, the two
applications hold no common element. -/
theorem ovlFnCov_dist_atValues {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {N : Srt} {g g' : KoreAML.Gen} {ss ss' : List Srt}
    (hg : g.argSorts = ss.map c.sortName) (hg' : g'.argSorts = ss'.map c.sortName)
    (hnum : ∀ s ∈ ss, s < nRegSorts + c.sortNames.length) (hnum' : ∀ s ∈ ss', s < nRegSorts + c.sortNames.length)
    {ad : KoreAML.AxiomDecl} (hs : tieOvlFnDistShapeB c N g g' ad.ax = true)
    (hno : ∀ us ws, c.sortsOf us = some ss → c.sortsOf ws = some ss' → ∀ y,
      GS I (c.sortName N) g (us.map (elemOf c I)) y → GS I (c.sortName N) g' (ws.map (elemOf c I)) y → False)
    {e : Valuation M} (hat : AtValues c I e ad.ax) (m : M) : (KoreAML.trAxiom [] [] ad).pat.interpret I e m := by
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  unfold tieOvlFnDistShapeB at hs
  split at hs
  · rename_i s s' p1 p2 hpat
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hfree⟩, hxs⟩, hys⟩, hp1⟩, hp2⟩, hnd⟩ := hs
    subst h1 h2
    obtain ⟨us, hus, hel1⟩ := ovlFnCov_vals h hI hat _ ss (hxs.trans (congrArg (List.map KoreAML.srt) hg)) hnum
      (fun k hk => ovlFnCov_free_mem hfree (List.mem_map_of_mem (List.mem_append_left _ hk)))
    obtain ⟨ws, hws, hel2⟩ := ovlFnCov_vals h hI hat _ ss' (hys.trans (congrArg (List.map KoreAML.srt) hg')) hnum'
      (fun k hk => ovlFnCov_free_mem hfree (List.mem_map_of_mem (List.mem_append_right _ hk)))
    unfold KoreAML.trAxiom
    dsimp only
    rw [interpret_impl]
    intro _
    generalize KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hp1 hp2 hnd hel1 hel2 ⊢
    rw [hpat]
    show ((KoreAML.sNot (KoreAML.trSort t (KoreAML.srt (c.sortName N)))
        (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ p1) (KoreAML.tr ⟨t, []⟩ p2))) ≡
      KoreAML.inhOf (KoreAML.trSort t (KoreAML.srt (c.sortName N)))).interpret I e m
    rw [KoreAML.interp_equal hD]
    intro y
    rw [KoreAML.interp_sNot, KoreAML.interp_sAnd, hp1, hp2, tieGen_vars, tieGen_vars, ← hel1, ← hel2, trSort_srt]
    exact ⟨fun hh => hh.2, fun hy => ⟨fun ⟨g1, g2⟩ => hno us ws hus hws y g1 g2, hy⟩⟩
  · cases hs

/-- **Under `OvlFnDist`, the different-constructors sentence of the overloading symbol and the
constructor `k` holds at values**, in every model of `Γc` of a semantics with `coreOK`, under
`FnHyp`: an application at values that holds an element of `k`'s application has `k`'s term as its
value. The sentence names the overloading symbol first, in the form `tieOvlFnDistShapeB` decides. -/
theorem ovlFnDist_atValues (h : c.coreOK = true) (hf : FnHyp c) {o : OvlSig}
    (hlo : c.lookupOvl o.sig.name = some o) {k : CtorSig} (hk : lookupSig c.ctorSigs k.name = some k)
    (hkN : k.result = o.sig.result) (hd : OvlFnDist c o k) {ad : KoreAML.AxiomDecl}
    (hs : tieOvlFnDistShapeB c o.sig.result (Gen.toK c (.ctor o.sig)) (Gen.toK c (.ctor k)) ad.ax = true) :
    EntailsAtValuesΓc c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hIc e hat m
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have hsn := (faithCoreOK_parts (Semantics.coreOK_parts h).2.1).2.2.2.2.2.2.2.1
  exact ovlFnCov_dist_atValues h hI rfl rfl
    (fun s hs' => ovlFnCov_numbered h hlo s (List.mem_cons_of_mem _ hs'))
    (fun s hs' => kernel_sort_lt hsn (Model.ctor_kernel (lookupSig_spec hk).1) (List.mem_cons_of_mem _ hs')) hs
    (fun us ws hus hws y g1 g2 => hd us ws hus hws (ovlFnRes_shared_ctor h hf hIc hlo hk hkN hus hws g1 g2)) hat m

/-! ## The refutations in a model of Γ, from what the model says of the applications -/

/-- **The `functional` sentence of the overloading symbol is not satisfied in a model of `Γ` where
the application holds no element at some values.** `w` is any value: the sentence is closed over a
sort variable, and a value's element gives a sort an inhabitant. -/
theorem ovlFnTotal_refuted_gs {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {o : OvlSig} (hlo : c.lookupOvl o.sig.name = some o)
    {ad : KoreAML.AxiomDecl} (hs : tieOvlFnFunShapeB c o.sig.result (Gen.toK c (.ctor o.sig)) ad.ax = true)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some o.sig.args)
    (hemp : ∀ m, ¬ GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) (vs.map (elemOf c I)) m)
    {w : GroundTerm} {s : Srt} (hw : c.sortOf w = some s) : ¬ (I ⊧ᴵ (KoreAML.trAxiom [] [] ad).pat) := by
  haveI : OvlOK c := ovlOK_of_core h
  obtain ⟨-, hgw, -, -, -, -, -, hsn, -, -, -, -⟩ := faithCoreOK_parts (Semantics.coreOK_parts h).2.1
  obtain ⟨σ, hσ1, hσ2⟩ := sortSing hI (sortOf_numbered_ofCl hgw hsn (Semantics.coreOK_ovls h) hw)
  have hx : KoreAML.Inh I σ (elemOf c I w) :=
    (KoreAML.interp_inhOf_of (S := KoreAML.Cons.sortP (c.sortName s)) (e := KoreAML.val0) (fun a => hσ1 a)).mp
      (elemOf_spec hI hw KoreAML.val0).2
  have hB := tieOvlFnBase_of_Γ hI (ovlFnCov_numbered h hlo _ (List.mem_cons_self ..)) ⟨σ, _, hσ2, hx⟩
  exact tieOvlFnFun_refuted_at hs hB (elems_length hI hvs) (elems_sorts hI hvs) hemp

/-- **The same-constructor sentence of the overloading symbol is not satisfied in a model of `Γ`
where the applications at two different value lists hold a common element of the symbol's sort**:
the sentence then makes the elements of the two lists equal, which different values' are not. -/
theorem ovlFnInj_refuted_gs {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {o : OvlSig}
    {ad : KoreAML.AxiomDecl} (hs : tieOvlFnInjShapeB c o.sig.result (Gen.toK c (.ctor o.sig)) ad.ax = true)
    {us vs : List GroundTerm} (hus : c.sortsOf us = some o.sig.args) (hvs : c.sortsOf vs = some o.sig.args)
    (hne : us ≠ vs) {y : M} (hyN : InS I (c.sortName o.sig.result) y)
    (hy1 : GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) (us.map (elemOf c I)) y)
    (hy2 : GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) (vs.map (elemOf c I)) y) :
    ¬ (I ⊧ᴵ (KoreAML.trAxiom [] [] ad).pat) := by
  intro hsent
  have hex := Semantics.coreOK_iff_ex.mp h
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx hex
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hgw : genWf c = true := (faithCoreOK_parts (Semantics.coreOK_parts h).2.1).2.1
  have heq := tieOvlFnInj_shared_at hs (defOK hI) hsent (elems_length hI hus) (elems_length hI hvs)
    (elems_sorts hI hus) (elems_sorts hI hvs) hyN hy1 hy2
  exact hne (ovlFnCov_elems_inj hI hgw hsc.trans hus hvs heq)

/-- **The different-constructors sentence of the overloading symbol and the constructor `k` is not
satisfied in a model of `Γ` where the application at some values holds the element of a term of
`k`.** The sentence names the overloading symbol first. -/
theorem ovlFnDist_refuted_gs {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {o : OvlSig} {k : CtorSig}
    (hk : lookupSig c.ctorSigs k.name = some k) (hkN : k.result = o.sig.result) {ad : KoreAML.AxiomDecl}
    (hs : tieOvlFnDistShapeB c o.sig.result (Gen.toK c (.ctor o.sig)) (Gen.toK c (.ctor k)) ad.ax = true)
    {us ws : List GroundTerm} (hus : c.sortsOf us = some o.sig.args) (hws : c.sortsOf ws = some k.args)
    (hy1 : GS I (c.sortName o.sig.result) (Gen.toK c (.ctor o.sig)) (us.map (elemOf c I))
      (elemOf c I (.ctor k.name ws))) : ¬ (I ⊧ᴵ (KoreAML.trAxiom [] [] ad).pat) := by
  haveI : OvlOK c := ovlOK_of_core h
  have hkw : c.sortOf (.ctor k.name ws) = some k.result := sortOf_ctor_intro ⟨k, hk, hws, rfl⟩
  have hy := elemOf_spec hI hkw KoreAML.val0
  have hy2 := (den_ctor_gs hI hk hws KoreAML.val0 _).mp ((hy.1 _).mpr rfl)
  have hyN := (inS_iff _).mp hy.2
  rw [hkN] at hy2 hyN
  exact tieOvlFnDist_shared_at hs (defOK hI) (elems_length hI hus) (elems_length hI hws)
    (elems_sorts hI hus) (elems_sorts hI hws) hyN hy1 hy2

/-! ## The refutations in the models of Γc, from a witness at values -/

/-- **A covered value list at which the covering function has no value refutes the `functional`
sentence of the overloading symbol**: no model of `Γc` satisfies it, for a semantics with `coreOK`,
under `FnHyp`. The application holds no element there, and the sentence makes it one element. `w`
is any value (`ovlFnTotal_refuted_gs`). -/
theorem ovlFnTotal_refuted (h : c.coreOK = true) (hf : FnHyp c) {o : OvlSig}
    (hlo : c.lookupOvl o.sig.name = some o) {ad : KoreAML.AxiomDecl}
    (hs : tieOvlFnFunShapeB c o.sig.result (Gen.toK c (.ctor o.sig)) ad.ax = true)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some o.sig.args) (hres : OvlFnRes c o vs none)
    {w : GroundTerm} {s : Srt} (hw : c.sortOf w = some s) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc c →
      ¬ (I ⊧ᴵ (KoreAML.trAxiom [] [] ad).pat) := fun _ _ _ hIc =>
  ovlFnTotal_refuted_gs h (fun φ hφ => hIc φ (Or.inl hφ)) hlo hs hvs (ovlFnRes_empty h hf hIc hlo hvs hres) hw

/-- **Two different value lists at which the application has one and the same value refute the
same-constructor sentence of the overloading symbol**: no model of `Γc` satisfies it, for a
semantics with `coreOK`, under `FnHyp`. The two applications hold the value's element
(`ovlFnInj_refuted_gs`). -/
theorem ovlFnInj_refuted (h : c.coreOK = true) (hf : FnHyp c) {o : OvlSig}
    (hlo : c.lookupOvl o.sig.name = some o) {ad : KoreAML.AxiomDecl}
    (hs : tieOvlFnInjShapeB c o.sig.result (Gen.toK c (.ctor o.sig)) ad.ax = true)
    {us vs : List GroundTerm} {v : GroundTerm} (hus : c.sortsOf us = some o.sig.args)
    (hvs : c.sortsOf vs = some o.sig.args) (hne : us ≠ vs) (h1 : OvlFnRes c o us (some v))
    (h2 : OvlFnRes c o vs (some v)) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc c →
      ¬ (I ⊧ᴵ (KoreAML.trAxiom [] [] ad).pat) := by
  intro M _ I hIc
  obtain ⟨hyN, hy1⟩ := ovlFnRes_elem h hf hIc hlo hus h1
  obtain ⟨-, hy2⟩ := ovlFnRes_elem h hf hIc hlo hvs h2
  exact ovlFnInj_refuted_gs h (fun φ hφ => hIc φ (Or.inl hφ)) hs hus hvs hne hyN ((hy1 _).mpr rfl) ((hy2 _).mpr rfl)

/-- **A value list at which the application's value is an application of the constructor `k`
refutes the different-constructors sentence of the two**: no model of `Γc` satisfies it, for a
semantics with `coreOK`, under `FnHyp`. The sentence names the overloading symbol first
(`ovlFnDist_refuted_gs`). -/
theorem ovlFnDist_refuted (h : c.coreOK = true) (hf : FnHyp c) {o : OvlSig}
    (hlo : c.lookupOvl o.sig.name = some o) {k : CtorSig} (hk : lookupSig c.ctorSigs k.name = some k)
    (hkN : k.result = o.sig.result) {ad : KoreAML.AxiomDecl}
    (hs : tieOvlFnDistShapeB c o.sig.result (Gen.toK c (.ctor o.sig)) (Gen.toK c (.ctor k)) ad.ax = true)
    {us ws : List GroundTerm} (hus : c.sortsOf us = some o.sig.args) (hws : c.sortsOf ws = some k.args)
    (hres : OvlFnRes c o us (some (.ctor k.name ws))) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc c →
      ¬ (I ⊧ᴵ (KoreAML.trAxiom [] [] ad).pat) := fun _ _ _ hIc =>
  ovlFnDist_refuted_gs h (fun φ hφ => hIc φ (Or.inl hφ)) hk hkN hs hus hws
    (((ovlFnRes_elem h hf hIc hlo hus hres).2 _).mpr rfl)

end

end Faithful

/-! ## The shape predicates do not read the hooks' parameters -/

kernel_rfl Faithful.tieOvlFnFunShapeB_withHooks : ∀ (c : Semantics) (H : HookParams) (N : Srt) (g : KoreAML.Gen)
  (a : Kore.Axiom), Faithful.tieOvlFnFunShapeB (c.withHooks H) N g a = Faithful.tieOvlFnFunShapeB c N g a

kernel_rfl Faithful.tieOvlFnInjShapeB_withHooks : ∀ (c : Semantics) (H : HookParams) (N : Srt) (g : KoreAML.Gen)
  (a : Kore.Axiom), Faithful.tieOvlFnInjShapeB (c.withHooks H) N g a = Faithful.tieOvlFnInjShapeB c N g a

kernel_rfl Faithful.tieOvlFnDistShapeB_withHooks : ∀ (c : Semantics) (H : HookParams) (N : Srt) (g g' : KoreAML.Gen)
  (a : Kore.Axiom), Faithful.tieOvlFnDistShapeB (c.withHooks H) N g g' a = Faithful.tieOvlFnDistShapeB c N g g' a

end KCore
