/-
  KCore, checked layer: a library equation between two predicates over interpreted hooked symbols
  is entailed at values (`EntailsAtValues`), for every semantics meeting `coreOK` and every
  interpretation.

  The equations are those of the form kompile writes for a `simplification` rule that rewrites a
  predicate to a predicate, over the sort variables `R` and `Q0`,
  `\implies{R}(\top{R}(), \equals{Q0, R}(lhs, \and{Q0}(rhs, \top{Q0}())))`, where `lhs` and `rhs` are
  built from `\equals{s, Q0}(t, u)` of two terms (`LibEv.kore`), `\not{Q0}` and `\and{Q0}` of two.

  - `LibEv.Pred`: such a predicate; `Pred.Holds`: what it says of the values, an equation that the
    two terms have the same value or both none.
  - `LibEv.Pred.den`: in a model of `Γ c`, at a valuation that gives each variable its value's
    element, the translated predicate holds every element of the sort `Q0` where `Pred.Holds`, and
    none otherwise. The equations are at sorts whose distinct values are distinct elements
    (`apartSort`).
  - `LibEv.PredEqn.entailed`, `entailed_reg`: an equation whose two sides hold at the same
    substitutions of values is entailed at values.
  - `LibEv.eqPred`: the sixteen equations of domains.md 1405 to 1412 and 2339 to 2346 (K 7.1.337)
    that read `==Int`, `=/=Int`, `==K`, `=/=K` at a literal as an equation of the arguments or its
    negation; `intEqPred_ev`, `kEqPred_ev`.
-/
import KcoreSpec.LibEvFun
import KcoreSpec.NamesApart

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- The sort variable `Q0` of a predicate's sentence. -/
def Q0v : Kore.SortVar := ⟨⟨⟨"Q0"⟩⟩⟩

/-- The sort `Q0`. -/
def Q0 : Kore.KSort := .var Q0v

theorem trSort_Q0 {tbl : KoreAML.VarTable} : KoreAML.trSort tbl Q0 = .evar (tbl.ev (.sortVar "Q0")) := rfl

/-- A predicate of a library sentence: an equation of two terms of the sort `s`, a negation, a
conjunction of two. -/
inductive Pred where
  | eq (s : Srt) (t u : Term)
  | not (p : Pred)
  | and (p q : Pred)

namespace Pred

/-- The predicate as a KORE pattern of the sort `Q0`. -/
def kore (c : Semantics) (vars : Vars) : Pred → Kore.Pattern
  | .eq s t u => .equals (srtOf c s) Q0 (LibEv.kore c vars t) (LibEv.kore c vars u)
  | .not p => .not Q0 (p.kore c vars)
  | .and p q => .and Q0 [p.kore c vars, q.kore c vars]

/-- `kore` with the registry's names. -/
def koreR (vars : Vars) : Pred → Kore.Pattern
  | .eq s t u => .equals (regSrtK s) Q0 (LibEv.koreR vars t) (LibEv.koreR vars u)
  | .not p => .not Q0 (p.koreR vars)
  | .and p q => .and Q0 [p.koreR vars, q.koreR vars]

/-- Each equation is between terms of its sort, a registry sort. -/
def typed (c : Semantics) (vars : Vars) : Pred → Bool
  | .eq s t u => decide (s < nRegSorts) && srt? c vars t == some s && srt? c vars u == some s
  | .not p => p.typed c vars
  | .and p q => p.typed c vars && q.typed c vars

/-- The terms are over the registry's symbols and sorts. -/
def reg : Pred → Bool
  | .eq s t u => decide (s < nRegSorts) && LibEv.reg t && LibEv.reg u
  | .not p => p.reg
  | .and p q => p.reg && q.reg

/-- Each equation is at a sort whose distinct values are distinct elements. -/
def Apart (c : Semantics) : Pred → Prop
  | .eq s _ _ => apartSort c s = true
  | .not p => p.Apart c
  | .and p q => p.Apart c ∧ q.Apart c

/-- What the predicate says at σ: an equation, that its terms have the same value or both none. -/
def Holds (c : Semantics) (σ : Subst) : Pred → Prop
  | .eq _ t u => val c σ t = val c σ u
  | .not p => ¬ p.Holds c σ
  | .and p q => p.Holds c σ ∧ q.Holds c σ

theorem kore_reg (c : Semantics) {vars : Vars} (hv : ∀ p ∈ vars, p.2 < nRegSorts) :
    ∀ p : Pred, p.reg = true → p.kore c vars = p.koreR vars
  | .eq s t u, h => by
    simp only [reg, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [kore, koreR, LibEv.kore_reg c hv t h.1.2, LibEv.kore_reg c hv u h.2, srtOf_reg c h.1.1]
  | .not p, h => by rw [kore, koreR, kore_reg c hv p h]
  | .and p q, h => by
    simp only [reg, Bool.and_eq_true] at h
    rw [kore, koreR, kore_reg c hv p h.1, kore_reg c hv q h.2]

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {vars : Vars} {σ : Subst} {tbl : KoreAML.VarTable} {e : Valuation M}
  (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
  (hag : ∀ i v, i < vars.length → σ.lookup i = some v →
    ∀ m, m = e.evalEvar (tbl.ev (vkey c vars i)) ↔ (KCore.den c v).interpret I e m)
  (hQ : KoreAML.IsSort I (e.evalEvar (tbl.ev (.sortVar "Q0"))))
include h hI hσ hag hQ

/-- **A library predicate denotes what it says of the values.** In a model of `Γ c`, at a
valuation that gives each variable the element of its value under σ and `Q0` a sort, the
translated predicate holds the elements of `Q0` where `Holds`, and none otherwise. -/
theorem den : ∀ (p : Pred), p.typed c vars = true → p.Apart c → ∀ a,
    (KoreAML.tr ⟨tbl, []⟩ (p.kore c vars)).interpret I e a ↔
      KoreAML.Inh I (e.evalEvar (tbl.ev (.sortVar "Q0"))) a ∧ p.Holds c σ
  | .eq s t u, ht, hap, a => by
    haveI : OvlOK c := ovlOK_of_core h
    have hD := defOK hI
    have hc := sat_sigItem hI (sig_ceilDef (c := c))
    obtain ⟨hok, hfa, -, -, hids⟩ := Semantics.coreOK_parts h
    obtain ⟨-, hg, -⟩ := faithCoreOK_parts hfa
    simp only [typed, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ht
    obtain ⟨⟨hs, h1⟩, h2⟩ := ht
    obtain ⟨τ, hτsort, hτ⟩ := srt_den hI (Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _))
    have hQv : ∀ b, (KoreAML.trSort tbl Q0).interpret I e b ↔ b = e.evalEvar (tbl.ev (.sortVar "Q0")) :=
      fun b => by rw [trSort_Q0, KoreAML.interp_evar]
    have d1 := den_val (tbl := tbl) (e := e) h hI hσ hag t h1
    have d2 := den_val (tbl := tbl) (e := e) h hI hσ hag u h2
    have hin : ∀ v, c.sortOf v = some s → KoreAML.Inh I τ (elemOf c I v) := fun v hv => by
      refine (KoreAML.interp_inhOf_of (fun a' => ?_)).mp (elemOf_spec hI hv e).2
      have := hτ tbl e a'
      rwa [trSort_srtOf_twoT] at this
    have hself : ∀ v, c.sortOf v = some s → Res c I e (some v) (elemOf c I v) :=
      fun v hv => ((elemOf_spec hI hv e).1 _).mpr rfl
    rw [kore, KoreAML.tr, KoreAML.interp_sEquals hD hc (hτ tbl e) hQv hτsort hQ]
    refine and_congr_right fun _ => ?_
    show _ ↔ val c σ t = val c σ u
    constructor
    · intro hall
      cases hv : val c σ t with
      | none =>
        cases hw : val c σ u with
        | none => rfl
        | some w =>
          have := (hall _ (hin w (d2.2 w hw))).mpr ((d2.1 _).mpr (by rw [hw]; exact hself w (d2.2 w hw)))
          rw [d1.1, hv] at this
          exact this.elim
      | some v =>
        have hx := (hall _ (hin v (d1.2 v hv))).mp ((d1.1 _).mpr (by rw [hv]; exact hself v (d1.2 v hv)))
        rw [d2.1] at hx
        cases hw : val c σ u with
        | none => rw [hw] at hx; exact hx.elim
        | some w =>
          rw [hw] at hx
          have he : elemOf c I v = elemOf c I w := ((elemOf_spec hI (d2.2 w hw) e).1 _).mp hx
          exact congrArg some (values_apart hI hg (NamesApart.subsorts_trans_of hids hok) hap (d1.2 v hv)
            (d2.2 w hw) he)
    · intro heq b _
      rw [d1.1, d2.1, heq]
  | .not p, ht, hap, a => by
    have hQv : ∀ b, (KoreAML.trSort tbl Q0).interpret I e b ↔ b = e.evalEvar (tbl.ev (.sortVar "Q0")) :=
      fun b => by rw [trSort_Q0, KoreAML.interp_evar]
    rw [kore, KoreAML.tr, KoreAML.interp_sNot, den p ht hap a, KoreAML.interp_inhOf_of hQv]
    constructor
    · rintro ⟨hn, hq⟩
      exact ⟨hq, fun hp => hn ⟨hq, hp⟩⟩
    · rintro ⟨hq, hn⟩
      exact ⟨fun hp => hn hp.2, hq⟩
  | .and p q, ht, hap, a => by
    simp only [typed, Bool.and_eq_true] at ht
    rw [kore, KoreAML.tr]
    simp only [KoreAML.trAndList]
    rw [KoreAML.interp_sAnd, den p ht.1 hap.1 a, den q ht.2 hap.2 a]
    constructor
    · rintro ⟨⟨hq, hp⟩, -, hq'⟩
      exact ⟨hq, hp, hq'⟩
    · rintro ⟨hq, hp, hq'⟩
      exact ⟨⟨hq, hp⟩, hq, hq'⟩

end

end Pred

/-! ## An equation between two predicates -/

/-- A library equation `lhs => rhs` between two predicates over the variables `vars`. -/
structure PredEqn where
  vars : Vars
  lhs : Pred
  rhs : Pred

namespace PredEqn

/-- The pattern of the equation's axiom, as kompile writes it over the sort variables `R`, `Q0`. -/
def pattern (c : Semantics) (E : PredEqn) : Kore.Pattern :=
  .implies KoreAML.R (.top KoreAML.R)
    (.equals Q0 KoreAML.R (E.lhs.kore c E.vars) (.and Q0 [E.rhs.kore c E.vars, .top Q0]))

/-- `pattern` with the registry's names. -/
def patR (E : PredEqn) : Kore.Pattern :=
  .implies KoreAML.R (.top KoreAML.R)
    (.equals Q0 KoreAML.R (E.lhs.koreR E.vars) (.and Q0 [E.rhs.koreR E.vars, .top Q0]))

/-- The variables are of registry sorts and the two sides are typed. -/
def typed (c : Semantics) (E : PredEqn) : Bool :=
  E.vars.all (fun p => decide (p.2 < nRegSorts)) && E.lhs.typed c E.vars && E.rhs.typed c E.vars

/-- The equation is over the registry's symbols and sorts, and each of its variables is free in
its pattern. -/
def regular (E : PredEqn) : Bool :=
  E.vars.all (fun p => decide (p.2 < nRegSorts)) && E.lhs.reg && E.rhs.reg &&
  E.vars.all (fun p => (KoreAML.freeOf [] E.patR).contains (.evar p.1 (regSrtK p.2)))

/-- The two sides hold at the same substitutions of values of the variables' sorts. -/
def Holds (c : Semantics) (E : PredEqn) : Prop :=
  ∀ σ : Subst, (∀ i p, E.vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) →
    (E.lhs.Holds c σ ↔ E.rhs.Holds c σ)

theorem pattern_reg (c : Semantics) {E : PredEqn} (hr : E.regular = true) : E.pattern c = E.patR := by
  simp only [regular, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr
  obtain ⟨⟨⟨hv, hl⟩, hrr⟩, -⟩ := hr
  unfold pattern patR
  rw [Pred.kore_reg c hv _ hl, Pred.kore_reg c hv _ hrr]

end PredEqn

/-- **A library equation between predicates that hold at the same values is entailed at values.**
For a semantics meeting `coreOK` and an equation `E` whose equations are at sorts of distinct
elements and whose two sides hold at the same substitutions of values (`PredEqn.Holds`): the
translation of any axiom declaration whose pattern is `E`'s, over the sort variables `R` and `Q0`
and with each variable of `E` free in it, holds in every model of `Γ c` at every valuation that
sends the axiom's free element variables to values. -/
theorem PredEqn.entailed {c : Semantics} (h : c.coreOK = true) (E : PredEqn) (ht : E.typed c = true)
    (hap : E.lhs.Apart c ∧ E.rhs.Apart c) (hE : E.Holds c) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = E.pattern c) (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v])
    (hfv : ∀ i, i < E.vars.length → vkey c E.vars i ∈ KoreAML.freeOf [] ad.ax.pattern) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hI e hat m
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  simp only [PredEqn.typed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
  obtain ⟨⟨hvR, htl⟩, htr⟩ := ht
  obtain ⟨σ, hσ, hel⟩ := subst_of_atValues h hI hat E.vars hvR hfv
  unfold KoreAML.trAxiom
  dsimp only
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hel ⊢
  rw [interpret_impl]
  intro hgd
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_cons_self ..)), rfl⟩))
  have hQ : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "Q0"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "Q0",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by
        rw [hsv]; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))), rfl⟩))
  have hag : ∀ i v, i < E.vars.length → σ.lookup i = some v →
      ∀ m, m = e.evalEvar (t.ev (vkey c E.vars i)) ↔ (den c v).interpret I e m := by
    intro i v hi hv m'
    obtain ⟨h1, h2⟩ := hel i v hi hv
    rw [(elemOf_spec hI h1 e).1 m', h2]
  have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  have hQv : ∀ b, (KoreAML.trSort t Q0).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "Q0")) :=
    fun b => by rw [trSort_Q0, KoreAML.interp_evar]
  rw [hp]
  unfold PredEqn.pattern
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [KoreAML.tr, KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun _ => ?_⟩
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hQv hRv hQ hR]
    refine ⟨(KoreAML.interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [Pred.den h hI hσ hag hQ E.lhs htl hap.1 b, KoreAML.tr]
    simp only [KoreAML.trAndList]
    rw [KoreAML.interp_sAnd, Pred.den h hI hσ hag hQ E.rhs htr hap.2 b, KoreAML.tr,
      KoreAML.interp_sTop hD (by rw [trSort_Q0]; simp [Pattern.isFreeEvar]; exact fun hh => ev_ne_top hh.symm),
      KoreAML.interp_inhOf_of hQv]
    have hiff := hE σ hσ
    constructor
    · rintro ⟨hq, hl⟩
      exact ⟨⟨hq, hiff.mp hl⟩, hq⟩
    · rintro ⟨⟨hq, hr⟩, -⟩
      exact ⟨hq, hiff.mpr hr⟩

/-- `PredEqn.entailed` for an equation over the registry's names: the axiom's pattern is compared
with a pattern that does not depend on the semantics. -/
theorem PredEqn.entailed_reg {c : Semantics} (h : c.coreOK = true) (E : PredEqn) (hr : E.regular = true)
    (ht : E.typed c = true) (hap : E.lhs.Apart c ∧ E.rhs.Apart c) (hE : E.Holds c) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = E.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  refine PredEqn.entailed h E ht hap hE ad (hp.trans (PredEqn.pattern_reg c hr).symm) hsv (fun i hi => ?_)
  have hr' := hr
  simp only [PredEqn.regular, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr'
  obtain ⟨⟨⟨hv, -⟩, -⟩, hf⟩ := hr'
  have hmem : E.vars.getD i ("", 0) ∈ E.vars := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  have := hf _ hmem
  rw [hp]
  unfold vkey
  rw [srtOf_reg c (hv _ hmem)]
  exact List.mem_of_elem_eq_true this

/-! ## An equality symbol at a literal is the equation of its arguments, or its negation -/

/-- The Bool literal `b` as a term. -/
def boolLit (b : Bool) : Term := .dv Srt.bool (.bool b)

/-- For a symbol `f` of two arguments of the sort `s` that decides their equality (`ne = false`)
or their difference (`ne = true`): the equation `f(K1, K2) = b` (the literal first where `flip`),
read as `K1 = K2` where `b` says so and as its negation otherwise. -/
def eqPred (s : Srt) (f : Sym) (ne b flip : Bool) : PredEqn :=
  ⟨[("VarK1", s), ("VarK2", s)],
    if flip then .eq Srt.bool (boolLit b) (.app f [.var 0, .var 1])
    else .eq Srt.bool (.app f [.var 0, .var 1]) (boolLit b),
    if b != ne then .eq s (.var 0) (.var 1) else .not (.eq s (.var 0) (.var 1))⟩

/-- `eqPred` holds where `f` has, at two values of the sort `s`, the value `true` exactly where
they are equal (`ne = false`) or differ (`ne = true`), and `false` otherwise. -/
theorem eqPred_holds {c : Semantics} {s : Srt} {f : Sym} {ne : Bool}
    (hf : ∀ v w, c.sortOf v = some s → c.sortOf w = some s →
      ∃ r : Bool, c.hv f [v, w] = some (bool r) ∧ (r = true ↔ ((v = w) ↔ ne = false)))
    (b flip : Bool) : (eqPred s f ne b flip).Holds c := by
  intro σ hσ
  have hvars : (eqPred s f ne b flip).vars = [("VarK1", s), ("VarK2", s)] := rfl
  rw [hvars] at hσ
  obtain ⟨v, hv, hvs⟩ := hσ 0 ("VarK1", s) rfl
  obtain ⟨w, hw, hws⟩ := hσ 1 ("VarK2", s) rfl
  obtain ⟨r, hr, hiff⟩ := hf v w hvs hws
  have hb : ∀ r b : Bool, some (bool r) = some (bool b) ↔ r = b := by
    intro r b
    cases r <;> cases b <;> simp [bool]
  have happ : val c σ (.app f [.var 0, .var 1]) = some (bool r) := by
    simp only [val, valList, allSome, hv, hw, Option.bind_some, Option.map_some, hr]
  have hlit : val c σ (boolLit b) = some (bool b) := rfl
  have h0 : val c σ (.var 0) = some v := by rw [val]; exact hv
  have h1 : val c σ (.var 1) = some w := by rw [val]; exact hw
  have hl : (eqPred s f ne b flip).lhs.Holds c σ ↔ r = b := by
    cases flip
    · show val c σ (.app f [.var 0, .var 1]) = val c σ (boolLit b) ↔ _
      rw [happ, hlit]
      exact hb r b
    · show val c σ (boolLit b) = val c σ (.app f [.var 0, .var 1]) ↔ _
      rw [happ, hlit]
      exact (hb b r).trans eq_comm
  have hrhs : (eqPred s f ne b flip).rhs.Holds c σ ↔ ((v = w) ↔ (b != ne) = true) := by
    unfold eqPred
    cases hbn : (b != ne)
    · show ¬ (val c σ (.var 0) = val c σ (.var 1)) ↔ _
      rw [h0, h1]
      simp
    · show val c σ (.var 0) = val c σ (.var 1) ↔ _
      rw [h0, h1]
      simp
  rw [hl, hrhs]
  clear hl hrhs hr hf hσ hv hw hvs hws hb happ hlit h0 h1 hvars
  revert hiff
  by_cases hvw : v = w <;> cases r <;> cases b <;> cases ne <;> simp [hvw]

/-- `==Int` and `=/=Int` at two Int values. -/
theorem intEq_graph {c : Semantics} (hs : c.shapesOK = true) (ne : Bool) (v w : GroundTerm)
    (hv : c.sortOf v = some Srt.int) (hw : c.sortOf w = some Srt.int) :
    ∃ r : Bool, c.hv (if ne then intNe else intEq) [v, w] = some (bool r) ∧
      (r = true ↔ ((v = w) ↔ ne = false)) := by
  obtain ⟨x, rfl⟩ := shape_int hs hv
  obtain ⟨y, rfl⟩ := shape_int hs hw
  have hxy : int x = int y ↔ x = y :=
    ⟨fun hh => by unfold int at hh; injection hh with _ hh; injection hh, fun hh => by rw [hh]⟩
  cases ne
  · exact ⟨decide (x = y), hv_of_value rfl, by simp [hxy]⟩
  · exact ⟨decide (x ≠ y), hv_of_value rfl, by simp [hxy]⟩

/-- `==K` and `=/=K` at two values. -/
theorem kEq_graph {c : Semantics} (ne : Bool) (v w : GroundTerm) :
    ∃ r : Bool, c.hv (if ne then kNe else kEq) [v, w] = some (bool r) ∧
      (r = true ↔ ((v = w) ↔ ne = false)) := by
  cases ne
  · exact ⟨GroundTerm.cmp v w == .eq, hv_of_value rfl, by simp [KCore.cmp_eq_iff]⟩
  · exact ⟨GroundTerm.cmp v w != .eq, hv_of_value rfl, by simp [KCore.cmp_eq_iff]⟩

/-- **domains.md 1405 to 1412**: `K1 ==Int K2` and `K1 =/=Int K2` at `true` or `false`, the
literal on either side, as `K1 = K2` or its negation, are entailed at values. -/
theorem intEqPred_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ne b flip : Bool)
    (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = (eqPred Srt.int (if ne then intNe else intEq) ne b flip).patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  haveI : OvlOK c := ovlOK_of_core h
  have hbool : apartSort c Srt.bool = true := apart_of_distinct bool_distinct
  have hint : apartSort c Srt.int = true := apart_of_distinct int_distinct
  refine PredEqn.entailed_reg h _ (by cases ne <;> cases b <;> cases flip <;> decide)
    (by cases ne <;> cases b <;> cases flip <;> rfl) ?_
    (eqPred_holds (fun v w hv hw => intEq_graph hs ne v w hv hw) b flip) ad hp hsv
  cases ne <;> cases b <;> cases flip <;> exact ⟨hbool, hint⟩

/-- **domains.md 2339 to 2346**: `K1 ==K K2` and `K1 =/=K K2` at `true` or `false`, the literal
on either side, as `K1 = K2` or its negation, are entailed at values. -/
theorem kEqPred_ev {c : Semantics} (h : c.coreOK = true) (ne b flip : Bool) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = (eqPred Srt.k (if ne then kNe else kEq) ne b flip).patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv, Q0v]) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  haveI : OvlOK c := ovlOK_of_core h
  have hbool : apartSort c Srt.bool = true := apart_of_distinct bool_distinct
  have hk : apartSort c Srt.k = true := by simp [apartSort]
  refine PredEqn.entailed_reg h _ (by cases ne <;> cases b <;> cases flip <;> decide)
    (by cases ne <;> cases b <;> cases flip <;> rfl) ?_
    (eqPred_holds (fun v w _ _ => kEq_graph ne v w) b flip) ad hp hsv
  cases ne <;> cases b <;> cases flip <;> exact ⟨hbool, hk⟩

end LibEv

end KCore
