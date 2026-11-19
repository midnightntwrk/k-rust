/-
  KCore, checked layer: equations in the function form over terms that apply parameter symbols
  (`LibEv.koreP`, `LibEv.valP`), over sorts of the registry or of the text, entailed at values or
  refuted at values.

  `LibEv.FnEqn.entailedP` asks the equation's sorts to be registry sorts and its premise to be
  `\and{R}(req, ins)`. Here a sort is any numbered sort (`nRegSorts + c.sortNames.length`), so an
  equation at a sort of the text (an instance `ite{Foo}`, a collection sort of the text) is covered,
  and the premise is any pattern from which `\and{R}(req, ins)` follows, so an `[owise]` equation's
  premise, `\and{R}(owise, \and{R}(req, ins))`, is covered whatever its first conjunct says.

  - `FnEqn.typedPT`: `FnEqn.typedP` with every numbered sort.
  - `FnEqn.entailedPT_pre`: an equation whose sides have the same value (`FnEqn.HoldsP`) is entailed
    at values, its premise any pattern implying `\and{R}(req, ins)`; `FnEqn.entailedPT` for the
    premise `\and{R}(req, ins)` itself, `FnEqn.entailedPT_owise` for `\and{R}(N, \and{R}(req, ins))`
    with any `N`.
  - `FnEqn.refutedPT_at`: an equation whose sides have different values at a substitution of values
    at which its `requires` is `true` and its patterns match is refuted at values: in every model of
    `Γ c` it fails at the valuation giving each variable its value's element (and `R` the sort Bool),
    which meets `AtValues` and `SetVarsAtValues`.
-/
import KcoreSpec.LibEvParam
import KcoreSpec.LibEvFnOwise
import KcoreSpec.InertEv

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

namespace FnEqn

/-- Each pattern is a term (`srtP?`) of its argument's sort, a numbered sort, and so are the
argument variable and the `#as` variable. -/
def patsTypedPT (c : Semantics) (vs : Vars) : Nat → List FnPat → Bool
  | _, [] => true
  | k, p :: ps => decide (p.1 < nRegSorts + c.sortNames.length) && srtP? c vs (.var k) == some p.1 &&
      srtP? c vs p.2.1 == some p.1 &&
      (match p.2.2 with
        | none => true
        | some j => srtP? c vs (.var j) == some p.1) && patsTypedPT c vs (k + 1) ps

/-- The equation is over numbered sorts (the registry's or the text's), its sides are terms
(`srtP?`) of the sort `s`, its patterns terms of the argument sorts and its `requires` a term of the
sort Bool. -/
def typedPT (c : Semantics) (E : FnEqn) : Bool :=
  decide (E.s < nRegSorts + c.sortNames.length) &&
  E.av.all (fun p => decide (p.2 < nRegSorts + c.sortNames.length)) &&
  srtP? c E.av E.lhs == some E.s && srtP? c E.av E.rhs == some E.s &&
  patsTypedPT c E.av E.vars.length E.pats &&
  match E.req with
  | none => true
  | some q => srtP? c E.av q == some Srt.bool

/-- The conclusion of the equation's axiom (`koreP`): `f` at the argument variables equals the
right side. -/
def conclP (c : Semantics) (E : FnEqn) : Kore.Pattern :=
  .equals (srtOf c E.s) KoreAML.R (koreP c E.av E.lhs)
    (.and (srtOf c E.s) [koreP c E.av E.rhs, .top (srtOf c E.s)])

/-- The premise `\and{R}(req, ins)` of the equation's axiom (`koreP`). -/
def premP (c : Semantics) (E : FnEqn) : Kore.Pattern :=
  .and KoreAML.R [E.reqPP c, insP c E.av E.vars.length E.pats]

theorem patternP_eq (c : Semantics) (E : FnEqn) : E.patternP c = .implies KoreAML.R (E.premP c) (E.conclP c) := rfl

end FnEqn

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {vars : Vars} {σ : Subst} {tbl : KoreAML.VarTable} {e : Valuation M}
  (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
  (hag : ∀ i v, i < vars.length → σ.lookup i = some v →
    ∀ m, m = e.evalEvar (tbl.ev (vkey c vars i)) ↔ (den c v).interpret I e m)
  {m : M} (hR : KoreAML.IsSort I (e.evalEvar (tbl.ev (.sortVar "R"))))
  (hRm : KoreAML.Inh I (e.evalEvar (tbl.ev (.sortVar "R"))) m)
include h hI hσ hag hR hRm

/-- **A `requires` with the value `true` holds** (`koreP`) at an element of the sort `R`. -/
theorem reqPT_intro (q : Term) (hq : srtP? c vars q = some Srt.bool) (hv : valP c σ q = some (bool true)) :
    (KoreAML.tr ⟨tbl, []⟩ (.equals (srtOf c Srt.bool) KoreAML.R (koreP c vars q)
      (.dv (srtOf c Srt.bool) "true"))).interpret I e m := by
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e b ↔ b = e.evalEvar (tbl.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  obtain ⟨τb, hτbsort, hτb⟩ := srt_den hI
    (Nat.lt_of_lt_of_le (show Srt.bool < nRegSorts by decide) (Nat.le_add_right _ c.sortNames.length))
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτb tbl e) hRv hτbsort hR]
  refine ⟨hRm, fun b _ => ?_⟩
  rw [(den_valP h hI hσ hag q hq).1 b, hv]
  show (den c (bool true)).interpret I e b ↔ _
  unfold den KoreAML.den bool
  rw [GroundTerm.kore]
  unfold srtOf
  rw [KoreAML.tr_dv, KoreAML.tr_dv]
  rfl

/-- **Patterns that match hold** (`koreP`): where each pattern has the value of its argument
variable (and its `#as` variable that value too), the `\in` premises hold at an element of the sort
`R`. -/
theorem insPT_intro : ∀ (ps : List FnPat) (k : Nat), FnEqn.patsTypedPT c vars k ps = true →
    FnEqn.MatchesP c σ k ps → (KoreAML.tr ⟨tbl, []⟩ (FnEqn.insP c vars k ps)).interpret I e m
  | [], _, _, _ => by
    have hD := defOK hI
    rw [FnEqn.insP, show KoreAML.tr ⟨tbl, []⟩ (.top KoreAML.R) = KoreAML.sTop (KoreAML.trSort tbl KoreAML.R) from by
      rw [KoreAML.tr], KoreAML.interp_sTop hD isFree_R,
      KoreAML.interp_inhOf_of (fun b => by rw [trSort_R, KoreAML.interp_evar])]
    exact hRm
  | (s', u, as) :: ps, k, htp', hm => by
    haveI : OvlOK c := ovlOK_of_core h
    have hD := defOK hI
    have hc := sat_sigItem hI (sig_ceilDef (c := c))
    have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e b ↔ b = e.evalEvar (tbl.ev (.sortVar "R")) :=
      fun b => by rw [trSort_R, KoreAML.interp_evar]
    simp only [FnEqn.patsTypedPT, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htp'
    obtain ⟨⟨⟨⟨hpR, hxk⟩, hpt⟩, has⟩, hrest⟩ := htp'
    obtain ⟨hmu, hmas, hm'⟩ := hm
    simp only [FnEqn.insP]
    rw [tr_and2, KoreAML.interp_sAnd]
    refine ⟨?_, insPT_intro ps (k + 1) hrest hm'⟩
    obtain ⟨τp, hτpsort, hτp⟩ := srt_den hI hpR
    have hDk := den_valP h hI hσ hag (.var k) hxk
    have hk : ∃ w, σ.lookup k = some w := by
      simp only [srtP?] at hxk
      obtain ⟨p, hp, -⟩ := Option.map_eq_some_iff.mp hxk
      obtain ⟨w, hw, -⟩ := hσ k p hp
      exact ⟨w, hw⟩
    obtain ⟨w, hw⟩ := hk
    have hwv : valP c σ (.var k) = some w := by rw [fq_valP_var]; exact hw
    have hws := hDk.2 w hwv
    obtain ⟨hw1, hw2⟩ := elemOf_spec hI hws e
    have hφ : ∀ a', (KoreAML.tr ⟨tbl, []⟩ (koreP c vars (.var k))).interpret I e a' → KoreAML.Inh I τp a' := by
      intro a' ha'
      rw [hDk.1, hwv] at ha'
      rw [(hw1 a').mp ha']
      refine (KoreAML.interp_inhOf_of (fun a'' => ?_)).mp hw2
      have := hτp tbl e a''
      rwa [trSort_srtOf_twoT] at this
    have hdw : ∀ (u' : Term), valP c σ u' = some w → ∀ s'', srtP? c vars u' = some s'' →
        (KoreAML.tr ⟨tbl, []⟩ (koreP c vars u')).interpret I e (elemOf c I w) := by
      intro u' hu' s'' hs''
      rw [(den_valP h hI hσ hag u' hs'').1, hu']
      exact (hw1 _).mpr rfl
    rw [KoreAML.tr, KoreAML.interp_sIn hD hc (hτp tbl e) hRv hτpsort hR hφ]
    refine ⟨⟨elemOf c I w, hdw (.var k) hwv s' hxk, ?_⟩, hRm⟩
    have hu : valP c σ u = some w := hmu.trans hw
    cases as with
    | none =>
      simp only [FnEqn.patKP]
      exact hdw u hu s' hpt
    | some j =>
      simp only [FnEqn.patKP]
      rw [tr_and2, KoreAML.interp_sAnd]
      refine ⟨hdw u hu s' hpt, hdw (.var j) ?_ s' (eq_of_beq has)⟩
      rw [fq_valP_var]
      exact (hmas j rfl).trans hw

end

/-- **An equation over parameter symbols whose sides have the same value is entailed at values,
whatever premise implies its `requires` and patterns.** For a semantics meeting `coreOK` and an
equation `E` over numbered sorts with `FnEqn.HoldsP`: the translation of any axiom declaration whose
pattern is `\implies{R}(P, conclusion)`, where in every interpretation, table and valuation P implies
`\and{R}(req, ins)`, over the one sort variable `R`, with each variable of the equation free in it,
holds in every model of `Γ c` at every valuation that sends the axiom's free element variables to
values. -/
theorem FnEqn.entailedPT_pre {c : Semantics} (h : c.coreOK = true) (E : FnEqn) (ht : E.typedPT c = true)
    (hE : E.HoldsP c) (P : Kore.Pattern)
    (hP : ∀ {M : Type} (I : Interpretation KoreAML.Sym M) (t : KoreAML.VarTable) (e : Valuation M) (a : M),
      (KoreAML.tr ⟨t, []⟩ P).interpret I e a → (KoreAML.tr ⟨t, []⟩ (E.premP c)).interpret I e a)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = .implies KoreAML.R P (E.conclP c))
    (hsv : ad.ax.sortVars = [KoreAML.Rv])
    (hfv : ∀ i, i < E.av.length → vkey c E.av i ∈ KoreAML.freeOf [] ad.ax.pattern) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hI e hat m
  obtain ⟨hok, hsr, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  simp only [FnEqn.typedPT, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨hsR, hvR⟩, htl⟩, htr⟩, htp⟩, htq⟩ := ht
  obtain ⟨σ, hσ, hel⟩ := InertEv.atValues_subst h hI hat E.av hvR hfv
  unfold KoreAML.trAxiom
  dsimp only
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hel ⊢
  have hag : ∀ i v, i < E.av.length → σ.lookup i = some v →
      ∀ m, m = e.evalEvar (t.ev (vkey c E.av i)) ↔ (den c v).interpret I e m := by
    intro i v hi hv m'
    obtain ⟨v', hv', hvs⟩ := hσ i _ (List.getElem?_eq_getElem hi)
    rw [hv] at hv'
    cases hv'
    rw [← hel i v hi hv]
    exact ((elemOf_spec hI hvs e).1 m').symm
  rw [interpret_impl]
  intro hgd
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_singleton.mpr rfl)), rfl⟩))
  have hDV := fun (u : Term) (s : Srt) (hu : srtP? c E.av u = some s) =>
    den_valP (tbl := t) (e := e) h hI hσ hag u hu
  -- two terms of a sort that denote a common element have the same value
  have hsame : ∀ (u u' : Term) (s : Srt), srtP? c E.av u = some s → srtP? c E.av u' = some s → ∀ b,
      (KoreAML.tr ⟨t, []⟩ (koreP c E.av u)).interpret I e b →
      (KoreAML.tr ⟨t, []⟩ (koreP c E.av u')).interpret I e b → valP c σ u = valP c σ u' := by
    intro u u' s hu hu' b h1 h2
    rw [(hDV u s hu).1] at h1
    rw [(hDV u' s hu').1] at h2
    cases hv : valP c σ u with
    | none => rw [hv] at h1; exact h1.elim
    | some w =>
      cases hv' : valP c σ u' with
      | none => rw [hv'] at h2; exact h2.elim
      | some w' =>
        rw [hv] at h1
        rw [hv'] at h2
        have hw := (hDV u s hu).2 w hv
        have hw' := (hDV u' s hu').2 w' hv'
        exact congrArg some (values_apart hI hg hsc.trans (apartSort_of_sorted hg hw) hw hw'
          ((((elemOf_spec hI hw e).1 b).mp h1).symm.trans (((elemOf_spec hI hw' e).1 b).mp h2)))
  -- the sorts
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI hsR
  obtain ⟨τb, hτbsort, hτb⟩ := srt_den hI
    (Nat.lt_of_lt_of_le (show Srt.bool < nRegSorts by decide) (Nat.le_add_right _ c.sortNames.length))
  have hdist : (distinctSorts c).contains Srt.bool = true := by
    refine List.elem_eq_true_of_mem ?_
    unfold distinctSorts
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  -- the `\in` premises give the match
  have hmatch : ∀ (ps : List FnPat) (k : Nat) (a : M), FnEqn.patsTypedPT c E.av k ps = true →
      (KoreAML.tr ⟨t, []⟩ (FnEqn.insP c E.av k ps)).interpret I e a → FnEqn.MatchesP c σ k ps := by
    intro ps
    induction ps with
    | nil => intro k a _ _; trivial
    | cons p ps ih =>
      intro k a htp' hi
      obtain ⟨s', u, as⟩ := p
      simp only [FnEqn.patsTypedPT, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htp'
      obtain ⟨⟨⟨⟨hpR, hxk⟩, hpt⟩, has⟩, hrest⟩ := htp'
      simp only [FnEqn.insP] at hi
      rw [tr_and2, KoreAML.interp_sAnd] at hi
      obtain ⟨hin, hi'⟩ := hi
      obtain ⟨τp, hτpsort, hτp⟩ := srt_den hI hpR
      have hφ : ∀ a', (KoreAML.tr ⟨t, []⟩ (koreP c E.av (.var k))).interpret I e a' → KoreAML.Inh I τp a' := by
        intro a' ha'
        rw [(hDV (.var k) s' hxk).1] at ha'
        cases hv : valP c σ (.var k) with
        | none => rw [hv] at ha'; exact ha'.elim
        | some w =>
          rw [hv] at ha'
          have hw := (hDV (.var k) s' hxk).2 w hv
          obtain ⟨hw1, hw2⟩ := elemOf_spec hI hw e
          rw [(hw1 a').mp ha']
          refine (KoreAML.interp_inhOf_of (fun a'' => ?_)).mp hw2
          have := hτp t e a''
          rwa [trSort_srtOf_twoT] at this
      rw [KoreAML.tr, KoreAML.interp_sIn hD hc (hτp t e) hRv hτpsort hR hφ] at hin
      obtain ⟨⟨b, hxb, hpb⟩, -⟩ := hin
      cases as with
      | none =>
        simp only [FnEqn.patKP] at hpb
        refine ⟨?_, fun j hj => (by cases hj), ih (k + 1) a hrest hi'⟩
        have := hsame u (.var k) s' hpt hxk b hpb hxb
        rwa [fq_valP_var] at this
      | some j =>
        simp only [FnEqn.patKP] at hpb
        rw [tr_and2, KoreAML.interp_sAnd] at hpb
        refine ⟨?_, fun j' hj' => ?_, ih (k + 1) a hrest hi'⟩
        · have := hsame u (.var k) s' hpt hxk b hpb.1 hxb
          rwa [fq_valP_var] at this
        · cases hj'
          have := hsame (.var j) (.var k) s' (eq_of_beq has) hxk b hpb.2 hxb
          rwa [fq_valP_var, fq_valP_var] at this
  rw [hp]
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [KoreAML.tr, KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun hprem0 => ?_⟩
    have hprem := hP I t e a hprem0
    unfold FnEqn.premP at hprem
    rw [tr_and2, KoreAML.interp_sAnd] at hprem
    obtain ⟨hprem, hins⟩ := hprem
    have hreq : ∀ q, E.req = some q → valP c σ q = some (bool true) := by
      intro q hq
      unfold FnEqn.reqPP at hprem
      rw [hq] at hprem htq
      dsimp only at hprem htq
      have htq' : srtP? c E.av q = some Srt.bool := eq_of_beq htq
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
      cases hvq : valP c σ q with
      | none => rw [hvq] at hq1; exact hq1.elim
      | some w =>
        rw [hvq] at hq1
        have hw := (hDV q _ htq').2 w hvq
        by_cases hne : w = bool true
        · rw [hne]
        · exact absurd ⟨hq1, (hT1 _).mpr rfl⟩
            (dom_apart hI hdist hw hT hne e _)
    have heq := hE σ hσ hreq (hmatch E.pats E.vars.length a htp hins)
    unfold FnEqn.conclP
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτ t e) hRv hτsort hR]
    refine ⟨(KoreAML.interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [(hDV E.lhs _ htl).1 b, heq, ← (hDV E.rhs _ htr).1 b, KoreAML.tr]
    show _ ↔ (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ (koreP c E.av E.rhs))
      (KoreAML.tr ⟨t, []⟩ (.top (srtOf c E.s)))).interpret I e b
    rw [KoreAML.interp_sAnd, show KoreAML.tr ⟨t, []⟩ (.top (srtOf c E.s)) =
      KoreAML.sTop (KoreAML.trSort t (srtOf c E.s)) from by rw [KoreAML.tr]]
    rw [KoreAML.interp_sTop hD (by rw [trSort_srtOf_twoT]; rfl), KoreAML.interp_inhOf_of (hτ t e)]
    exact ⟨fun h' => ⟨h', hb⟩, And.left⟩

/-- **An equation over parameter symbols, at registry or text sorts, whose sides have the same value
is entailed at values**: `FnEqn.entailedPT_pre` at the premise `\and{R}(req, ins)`. -/
theorem FnEqn.entailedPT {c : Semantics} (h : c.coreOK = true) (E : FnEqn) (ht : E.typedPT c = true)
    (hE : E.HoldsP c) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patternP c)
    (hsv : ad.ax.sortVars = [KoreAML.Rv])
    (hfv : ∀ i, i < E.av.length → vkey c E.av i ∈ KoreAML.freeOf [] ad.ax.pattern) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailedPT_pre h E ht hE (E.premP c) (fun _ _ _ _ h' => h') ad (hp.trans (FnEqn.patternP_eq c E)) hsv hfv

/-- **An `[owise]` equation over parameter symbols whose sides have the same value at every
substitution meeting its `requires` and patterns is entailed at values**, whatever the first conjunct
`N` of its premise (the negation of the other equations' premises) states: `FnEqn.entailedPT_pre`
at the premise `\and{R}(N, \and{R}(req, ins))`. -/
theorem FnEqn.entailedPT_owise {c : Semantics} (h : c.coreOK = true) (E : FnEqn) (ht : E.typedPT c = true)
    (hE : E.HoldsP c) (N : Kore.Pattern) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = .implies KoreAML.R (.and KoreAML.R [N, E.premP c]) (E.conclP c))
    (hsv : ad.ax.sortVars = [KoreAML.Rv])
    (hfv : ∀ i, i < E.av.length → vkey c E.av i ∈ KoreAML.freeOf [] ad.ax.pattern) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailedPT_pre h E ht hE _ (fun _ _ _ _ h' => by
    rw [tr_and2, KoreAML.interp_sAnd] at h'
    exact h'.2) ad hp hsv hfv

/-- The keys of the variables `vs`, `R` first. -/
def keysRPT (c : Semantics) (vs : Vars) : List KoreAML.VarKey :=
  KoreAML.sortVarKey KoreAML.Rv :: vs.map fun p => .evar p.1 (srtOf c p.2)

theorem keysRPT_getElem? (c : Semantics) (vs : Vars) {i : Nat} (hi : i < vs.length) :
    (keysRPT c vs)[i + 1]? = some (vkey c vs i) := by
  simp only [keysRPT, List.getElem?_cons_succ, List.getElem?_map, Option.map_some,
    vkey, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- **An equation over parameter symbols whose sides have different values is refuted at values.**
For a semantics meeting `coreOK`, an equation `E` over numbered sorts and a substitution σ of
values of its variables' sorts at which its `requires` has the value `true`, its patterns match the
arguments and its two sides do not have the same value (`valP`; one of them may have none): for any
axiom declaration whose pattern is `E`'s, over the one sort variable `R`, whose free variables are
the equation's, and whose table gives `R` and the equation's variables distinct places, in every
model of `Γ c` the translated axiom fails at a valuation that sends each free element variable to
the element of its value under σ and has no free set variable's element. -/
theorem FnEqn.refutedPT_at {c : Semantics} (h : c.coreOK = true) (E : FnEqn) (ht : E.typedPT c = true)
    (σ : Subst) (hσ : ∀ i p, E.av[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
    (hreq : ∀ q, E.req = some q → valP c σ q = some (bool true))
    (hm : FnEqn.MatchesP c σ E.vars.length E.pats) (hne : valP c σ E.lhs ≠ valP c σ E.rhs)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patternP c) (hsv : ad.ax.sortVars = [KoreAML.Rv])
    (hfv : ∀ k ∈ KoreAML.freeOf [] ad.ax.pattern, ∃ i, i < E.av.length ∧ k = vkey c E.av i)
    (hap : ((keysRPT c E.av).map (KoreAML.tableOf ad.ax.sortVars ad.ax.pattern).idxOf).Nodup)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) :
    ∃ e : Valuation M, AtValues c I e ad.ax ∧ SetVarsAtValues c I e ad.ax ∧
      ¬ (KoreAML.trAxiom [] [] ad).pat.interpret I e default := by
  obtain ⟨hok, hsr, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  simp only [FnEqn.typedPT, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨hsR, hvR⟩, htl⟩, htr⟩, htp⟩, htq⟩ := ht
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hap
  obtain ⟨τb, hτbsort, hτb⟩ := srt_den hI
    (Nat.lt_of_lt_of_le (show Srt.bool < nRegSorts by decide) (Nat.le_add_right _ c.sortNames.length))
  -- two keys of the list with one place are one
  have hkey : ∀ i j, i < (keysRPT c E.av).length → j < (keysRPT c E.av).length →
      t.ev ((keysRPT c E.av)[i]?.getD (.sortVar "")) = t.ev ((keysRPT c E.av)[j]?.getD (.sortVar "")) → i = j := by
    intro i j hi hj hij
    have h1 := fo_ev_inj hij
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at h1
    simp only [Option.getD_some] at h1
    have hi' : i < ((keysRPT c E.av).map t.idxOf).length := by rw [List.length_map]; exact hi
    have hj' : j < ((keysRPT c E.av).map t.idxOf).length := by rw [List.length_map]; exact hj
    exact hap.eq_of_getElem_eq hi' hj' (by simp only [List.getElem_map]; exact h1)
  have hlen : (keysRPT c E.av).length = E.av.length + 1 := by simp [keysRPT]
  have hvk : ∀ i, i < E.av.length → t.ev ((keysRPT c E.av)[i + 1]?.getD (.sortVar "")) = t.ev (vkey c E.av i) :=
    fun i hi => by rw [keysRPT_getElem? c E.av hi]; rfl
  have hRk : t.ev ((keysRPT c E.av)[0]?.getD (.sortVar "")) = t.ev (.sortVar "R") := rfl
  -- the valuation
  let w : Nat → GroundTerm := fun i => (σ.lookup i).getD default
  let ee : EVar → M := fun x =>
    match (List.range E.av.length).find? (fun i => t.ev (vkey c E.av i) == x) with
    | some i => elemOf c I (w i)
    | none => τb
  let e : Valuation M := ⟨ee, fun _ _ => False⟩
  have hev : ∀ i, i < E.av.length → e.evalEvar (t.ev (vkey c E.av i)) = elemOf c I (w i) := by
    intro i hi
    show ee _ = _
    simp only [ee]
    cases hf : (List.range E.av.length).find? (fun j => t.ev (vkey c E.av j) == t.ev (vkey c E.av i)) with
    | none =>
      exact absurd (List.find?_eq_none.mp hf i (List.mem_range.mpr hi)) (by simp)
    | some j =>
      have hj := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      have hji := List.find?_some hf
      simp only [beq_iff_eq] at hji
      have := hkey (j + 1) (i + 1) (by omega) (by omega) (by rw [hvk j hj, hvk i hi]; exact hji)
      have hji' : j = i := by omega
      subst hji'
      rfl
  have heR : e.evalEvar (t.ev (.sortVar "R")) = τb := by
    show ee _ = _
    simp only [ee]
    cases hf : (List.range E.av.length).find? (fun j => t.ev (vkey c E.av j) == t.ev (.sortVar "R")) with
    | none => rfl
    | some j =>
      have hj := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      have hji := List.find?_some hf
      simp only [beq_iff_eq] at hji
      have := hkey (j + 1) 0 (by omega) (by omega) (by rw [hvk j hj, hRk]; exact hji)
      omega
  have hsrt : ∀ i, i < E.av.length → c.sortOf (w i) = some (E.av.getD i ("", 0)).2 ∧
      σ.lookup i = some (w i) := by
    intro i hi
    obtain ⟨v, hv, hvs⟩ := hσ i _ (List.getElem?_eq_getElem hi)
    have hw : w i = v := by simp only [w, hv, Option.getD_some]
    refine ⟨?_, by rw [hw, hv]⟩
    rw [hw, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hvs
  have hag : ∀ i v, i < E.av.length → σ.lookup i = some v →
      ∀ m, m = e.evalEvar (t.ev (vkey c E.av i)) ↔ (den c v).interpret I e m := by
    intro i v hi hv m'
    obtain ⟨hs, hl⟩ := hsrt i hi
    rw [hv] at hl
    cases hl
    rw [hev i hi]
    exact ((elemOf_spec hI hs e).1 m').symm
  have hinhV : ∀ i, i < E.av.length → ∀ τp : M,
      (∀ (tbl : KoreAML.VarTable) (e' : Valuation M) (a : M),
        (KoreAML.trSort tbl (srtOf c (E.av.getD i ("", 0)).2)).interpret I e' a ↔ a = τp) →
      KoreAML.Inh I τp (elemOf c I (w i)) := by
    intro i hi τp hτp
    obtain ⟨-, hw2⟩ := elemOf_spec hI (hsrt i hi).1 e
    refine (KoreAML.interp_inhOf_of (fun a'' => ?_)).mp hw2
    have := hτp t e a''
    rwa [trSort_srtOf_twoT] at this
  refine ⟨e, ?_, ?_, fun hax => ?_⟩
  · -- the free element variables are sent to values
    intro n s hk
    obtain ⟨i, hi, hki⟩ := hfv _ (List.mem_eraseDups.mp hk)
    obtain ⟨hs, -⟩ := hsrt i hi
    unfold vkey at hki
    injection hki with hn hs'
    subst hn hs'
    refine ⟨w i, _, rfl, hs, ?_⟩
    rw [htb]
    show (den c (w i)).interpret I e (e.evalEvar (t.ev (vkey c E.av i)))
    rw [hev i hi]
    exact ((elemOf_spec hI hs e).1 _).mpr rfl
  · intro _ _ _ _ hm'
    exact hm'.elim
  · unfold KoreAML.trAxiom at hax
    dsimp only at hax
    rw [htb] at hax
    rw [interpret_impl] at hax
    have hRs : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) := by rw [heR]; exact hτbsort
    have hT : c.sortOf (bool true) = some Srt.bool := rmS_sortOf_bool c true
    obtain ⟨hT1, hT2⟩ := elemOf_spec hI hT e
    have hinhT : KoreAML.Inh I τb (elemOf c I (bool true)) := by
      refine (KoreAML.interp_inhOf_of (fun a' => ?_)).mp hT2
      have := hτb t e a'
      rwa [trSort_srtOf_twoT] at this
    have hRm : KoreAML.Inh I (e.evalEvar (t.ev (.sortVar "R"))) (elemOf c I (bool true)) := by
      rw [heR]; exact hinhT
    have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
      fun b => by rw [trSort_R, KoreAML.interp_evar]
    have hgd := hax (KoreAML.interp_conjList fun g hg' => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg'
      rcases List.mem_append.mp (List.mem_eraseDups.mp hk) with hk | hk
      · rw [hsv] at hk
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hk
        subst hk
        exact (KoreAML.interp_guard_sortVar hD).mpr hRs
      · obtain ⟨i, hi, rfl⟩ := hfv _ hk
        obtain ⟨τp, hτpsort, hτp⟩ := srt_den hI (hvR (E.av.getD i ("", 0)) (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]; exact List.getElem_mem hi))
        unfold vkey KoreAML.guardOf
        rw [KoreAML.interp_member hD]
        show (KoreAML.inhOf (KoreAML.trSort t (srtOf c (E.av.getD i ("", 0)).2))).interpret I e
          (e.evalEvar (t.ev (vkey c E.av i)))
        rw [hev i hi, KoreAML.interp_inhOf_of (hτp t e)]
        exact hinhV i hi τp hτp)
    rw [hp, FnEqn.patternP_eq] at hgd
    simp only [KoreAML.sortOf] at hgd
    rw [KoreAML.interp_equal hD] at hgd
    have hA := (hgd (elemOf c I (bool true))).mpr ((KoreAML.interp_inhOf_of hRv).mpr hRm)
    rw [KoreAML.tr, KoreAML.interp_sImp] at hA
    have hσ' : ∀ i p, E.av[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2 := hσ
    have hEQ := hA.2 (by
      unfold FnEqn.premP
      rw [tr_and2, KoreAML.interp_sAnd]
      refine ⟨?_, insPT_intro h hI hσ' hag hRs hRm E.pats E.vars.length htp hm⟩
      unfold FnEqn.reqPP
      cases hq : E.req with
      | none =>
        rw [show KoreAML.tr ⟨t, []⟩ (.top KoreAML.R) = KoreAML.sTop (KoreAML.trSort t KoreAML.R) from by
          rw [KoreAML.tr], KoreAML.interp_sTop hD isFree_R, KoreAML.interp_inhOf_of hRv]
        exact hRm
      | some q =>
        rw [hq] at htq
        exact reqPT_intro h hI hσ' hag hRs hRm q (eq_of_beq htq) (hreq q hq))
    obtain ⟨τ, hτsort, hτ⟩ := srt_den hI hsR
    unfold FnEqn.conclP at hEQ
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτ t e) hRv hτsort hRs] at hEQ
    have hDL := den_valP (tbl := t) (e := e) h hI hσ' hag E.lhs htl
    have hDR := den_valP (tbl := t) (e := e) h hI hσ' hag E.rhs htr
    have hside : ∀ b, KoreAML.Inh I τ b → ((KoreAML.tr ⟨t, []⟩ (koreP c E.av E.lhs)).interpret I e b ↔
        (KoreAML.tr ⟨t, []⟩ (koreP c E.av E.rhs)).interpret I e b) := by
      intro b hb
      rw [hEQ.2 b hb, KoreAML.tr]
      show (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ (koreP c E.av E.rhs))
        (KoreAML.tr ⟨t, []⟩ (.top (srtOf c E.s)))).interpret I e b ↔ _
      rw [KoreAML.interp_sAnd, show KoreAML.tr ⟨t, []⟩ (.top (srtOf c E.s)) =
        KoreAML.sTop (KoreAML.trSort t (srtOf c E.s)) from by rw [KoreAML.tr]]
      rw [KoreAML.interp_sTop hD (by rw [trSort_srtOf_twoT]; rfl), KoreAML.interp_inhOf_of (hτ t e)]
      exact ⟨And.left, fun h' => ⟨h', hb⟩⟩
    have hinh : ∀ v, c.sortOf v = some E.s → KoreAML.Inh I τ (elemOf c I v) := by
      intro v hv
      obtain ⟨-, hw2⟩ := elemOf_spec hI hv e
      refine (KoreAML.interp_inhOf_of (fun a'' => ?_)).mp hw2
      have := hτ t e a''
      rwa [trSort_srtOf_twoT] at this
    cases hl : valP c σ E.lhs with
    | none =>
      cases hr : valP c σ E.rhs with
      | none => exact hne (hl.trans hr.symm)
      | some v =>
        have hvs := hDR.2 v hr
        have hb := (hside _ (hinh v hvs)).mpr (by
          rw [hDR.1, hr]; exact ((elemOf_spec hI hvs e).1 _).mpr rfl)
        rw [hDL.1, hl] at hb
        exact hb
    | some v =>
      have hvs := hDL.2 v hl
      have hb := (hside _ (hinh v hvs)).mp (by
        rw [hDL.1, hl]; exact ((elemOf_spec hI hvs e).1 _).mpr rfl)
      rw [hDR.1] at hb
      cases hr : valP c σ E.rhs with
      | none => rw [hr] at hb; exact hb
      | some v' =>
        rw [hr] at hb
        have hvs' := hDR.2 v' hr
        have hvv : v = v' := values_apart hI hg hsc.trans (apartSort_of_sorted hg hvs) hvs hvs'
          (((elemOf_spec hI hvs' e).1 _).mp hb)
        exact hne (by rw [hl, hr, hvv])

end LibEv

end KCore

