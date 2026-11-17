/-
  KCore, checked layer: a library equation in the function form is entailed at values
  (`EntailsAtValues`), for every semantics meeting `coreOK` and every interpretation.

  The function form is what kompile writes for a rule of the builtin files that defines a function
  symbol by its arguments' patterns and is no `simplification`:

    \implies{R}(\and{R}(prem, \and{R}(\in{s0, R}(X0:s0, p0), … \and{R}(\in{sn, R}(Xn:sn, pn), \top{R}()))),
                \equals{s, R}(f(X0:s0, …, Xn:sn), \and{s}(rhs, \top{s}())))

  `prem` is `\top{R}()` or `\equals{SortBool, R}(req, \dv{SortBool}("true"))`; a pattern `pi` is a
  term over element variables, domain values and interpreted hooked symbols, or `\and{si}(t, V)`
  for the K pattern `t #as V`. The premise `\in{si, R}(Xi, pi)` holds where the element of `Xi` is
  the one `pi` denotes.

  - `LibEv.FnEqn`: such an equation; its variables are those of the patterns, then `X0 … Xn`.
  - `FnEqn.Matches`: at a substitution, each pattern has the value of its argument variable (and
    its `#as` variable that value too).
  - `FnEqn.Holds`: at every substitution of values of the variables' sorts at which the `requires`
    has the value `true` and the patterns match, `f` at the argument variables has the value of
    the right side, or both none. A statement about `hook` and the interpretation only.
  - `FnEqn.entailed`, `FnEqn.entailed_reg`: an equation that holds is entailed at values, whatever
    axiom declaration of a text holds its pattern.

  The form with an `owise` premise (the negation of the other rules' premises) is not covered.
-/
import KcoreSpec.LibEv

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

theorem fq_val_var (c : Semantics) (σ : Subst) (k : Nat) : val c σ (.var k) = σ.lookup k := by rw [val]

/-- **The values of an axiom's variables.** At a valuation that sends the free element variables
of the axiom to values, for variables `vars` of registry sorts that are free in its pattern: a
substitution of values of the variables' sorts, each the value whose element the valuation gives
the variable. -/
theorem fq_subst {c : Semantics} (h : c.coreOK = true) {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) (vars : Vars) (hvR : ∀ p ∈ vars, p.2 < nRegSorts)
    (a : Kore.Axiom) (hfv : ∀ i, i < vars.length → vkey c vars i ∈ KoreAML.freeOf [] a.pattern)
    (e : Valuation M) (hat : AtValues c I e a) :
    ∃ σ : Subst, (∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) ∧
      (∀ i v, i < vars.length → σ.lookup i = some v →
        ∀ m, m = e.evalEvar ((KoreAML.tableOf a.sortVars a.pattern).ev (vkey c vars i)) ↔
          (den c v).interpret I e m) := by
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
  refine ⟨σ, fun i p hp' => ?_, fun i v hi hv m' => ?_⟩
  · have hi : i < vars.length := (List.getElem?_eq_some_iff.mp hp').1
    have hgd' : vars.getD i ("", 0) = p := by rw [List.getD_eq_getElem?_getD, hp']; rfl
    refine ⟨pick c I (vars.getD i ("", 0)).2 (e.evalEvar (t.ev (vkey c vars i))), ?_, ?_⟩
    · rw [hlk]; simp only [hi, ite_true]
    · rw [← hgd']
      exact (pick_spec (hval i hi)).1
  · rw [hlk] at hv
    simp only [hi, ite_true] at hv
    cases hv
    obtain ⟨h1, h2⟩ := pick_spec (hval i hi)
    rw [(elemOf_spec hI h1 e).1 m', h2]

/-- A pattern of the function form at an argument: the argument's sort, the pattern's term, and
the variable of a `#as`. -/
abbrev FnPat := Srt × Term × Option Nat

/-- A library equation in the function form: `f(p0, …, pn) => rhs requires req` over the patterns'
variables `vars`, the result of the sort `s`. -/
structure FnEqn where
  vars : Vars
  f : Sym
  pats : List FnPat
  s : Srt
  req : Option Term
  rhs : Term

namespace FnEqn

/-- The name kompile gives the i-th argument variable. -/
def xName (i : Nat) : String :=
  ["X0", "X1", "X2", "X3", "X4", "X5", "X6", "X7", "X8", "X9"].getD i "X"

/-- The argument variables from the i-th on. -/
def xVars : Nat → List FnPat → Vars
  | _, [] => []
  | i, p :: ps => (xName i, p.1) :: xVars (i + 1) ps

/-- The equation's variables: the patterns', then the argument variables. -/
def av (E : FnEqn) : Vars := E.vars ++ xVars 0 E.pats

/-- The argument variables as terms, from the variable `k` on. -/
def xTerms : Nat → List FnPat → List Term
  | _, [] => []
  | k, _ :: ps => .var k :: xTerms (k + 1) ps

/-- The left side: `f` at the argument variables. -/
def lhs (E : FnEqn) : Term := .app E.f (xTerms E.vars.length E.pats)

/-- A pattern as KORE: its term, or `\and{s}(t, V)` for `t #as V`. -/
def patK (c : Semantics) (vs : Vars) (s : Srt) (t : Term) : Option Nat → Kore.Pattern
  | none => kore c vs t
  | some j => .and (srtOf c s) [kore c vs t, kore c vs (.var j)]

/-- The conjunction of the `\in` premises, the first argument variable the variable `k`. -/
def ins (c : Semantics) (vs : Vars) : Nat → List FnPat → Kore.Pattern
  | _, [] => .top KoreAML.R
  | k, p :: ps => .and KoreAML.R
      [.in (srtOf c p.1) KoreAML.R (kore c vs (.var k)) (patK c vs p.1 p.2.1 p.2.2), ins c vs (k + 1) ps]

/-- The first conjunct of the premise: `\top{R}()` without a `requires`, `req = true` with one. -/
def reqP (c : Semantics) (E : FnEqn) : Kore.Pattern :=
  match E.req with
  | none => .top KoreAML.R
  | some q => .equals (srtOf c Srt.bool) KoreAML.R (kore c E.av q) (.dv (srtOf c Srt.bool) "true")

/-- The pattern of the equation's axiom, as kompile writes it over the sort variable `R`. -/
def pattern (c : Semantics) (E : FnEqn) : Kore.Pattern :=
  .implies KoreAML.R (.and KoreAML.R [E.reqP c, ins c E.av E.vars.length E.pats])
    (.equals (srtOf c E.s) KoreAML.R (kore c E.av E.lhs)
      (.and (srtOf c E.s) [kore c E.av E.rhs, .top (srtOf c E.s)]))

/-- Each pattern is a term of its argument's sort, a registry sort, and so are the argument
variable and the `#as` variable. -/
def patsTyped (c : Semantics) (vs : Vars) : Nat → List FnPat → Bool
  | _, [] => true
  | k, p :: ps => decide (p.1 < nRegSorts) && srt? c vs (.var k) == some p.1 &&
      srt? c vs p.2.1 == some p.1 &&
      (match p.2.2 with
        | none => true
        | some j => srt? c vs (.var j) == some p.1) && patsTyped c vs (k + 1) ps

/-- The equation is over registry sorts, its left and right sides are terms of the sort `s`, its
patterns terms of the argument sorts and its `requires` a term of the sort Bool. -/
def typed (c : Semantics) (E : FnEqn) : Bool :=
  decide (E.s < nRegSorts) && E.av.all (fun p => decide (p.2 < nRegSorts)) &&
  srt? c E.av E.lhs == some E.s && srt? c E.av E.rhs == some E.s &&
  patsTyped c E.av E.vars.length E.pats &&
  match E.req with
  | none => true
  | some q => srt? c E.av q == some Srt.bool

/-- At σ, each pattern has the value of its argument variable (the first the variable `k`), and
the variable of a `#as` has that value too. -/
def Matches (c : Semantics) (σ : Subst) : Nat → List FnPat → Prop
  | _, [] => True
  | k, p :: ps => val c σ p.2.1 = σ.lookup k ∧ (∀ j, p.2.2 = some j → σ.lookup j = σ.lookup k) ∧
      Matches c σ (k + 1) ps

/-- `f` at the argument variables and the right side have the same value, or both none, at every
substitution of values of the variables' sorts at which the `requires` has the value `true` and
the patterns match the arguments. -/
def Holds (c : Semantics) (E : FnEqn) : Prop :=
  ∀ σ : Subst, (∀ i p, E.av[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) →
    (∀ q, E.req = some q → val c σ q = some (bool true)) → Matches c σ E.vars.length E.pats →
    val c σ E.lhs = val c σ E.rhs

end FnEqn

/-- **A library equation in the function form that holds of the values is entailed at values.**
For a semantics meeting `coreOK` and an equation `E` with `FnEqn.Holds`: the translation of any
axiom declaration whose pattern is `E`'s, over the one sort variable `R` and with each variable
of `E` free in it, holds in every model of `Γ c` at every valuation that sends the axiom's free
element variables to values. -/
theorem FnEqn.entailed {c : Semantics} (h : c.coreOK = true) (E : FnEqn) (ht : E.typed c = true)
    (hE : E.Holds c) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.pattern c)
    (hsv : ad.ax.sortVars = [KoreAML.Rv])
    (hfv : ∀ i, i < E.av.length → vkey c E.av i ∈ KoreAML.freeOf [] ad.ax.pattern) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hI e hat m
  obtain ⟨hok, hsr, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  simp only [FnEqn.typed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨hsR, hvR⟩, htl⟩, htr⟩, htp⟩, htq⟩ := ht
  have hnum : ∀ {s : Srt}, s < nRegSorts → s < nRegSorts + c.sortNames.length :=
    fun hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  obtain ⟨σ, hσ, hag⟩ := fq_subst h hI E.av hvR ad.ax hfv e hat
  unfold KoreAML.trAxiom
  dsimp only
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hag ⊢
  rw [interpret_impl]
  intro hgd
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_singleton.mpr rfl)), rfl⟩))
  have hDV := fun (u : Term) (s : Srt) (hu : srt? c E.av u = some s) =>
    den_val (tbl := t) (e := e) h hI hσ hag u hu
  -- two terms of a sort that denote a common element have the same value
  have hsame : ∀ (u u' : Term) (s : Srt), srt? c E.av u = some s → srt? c E.av u' = some s → ∀ b,
      (KoreAML.tr ⟨t, []⟩ (kore c E.av u)).interpret I e b →
      (KoreAML.tr ⟨t, []⟩ (kore c E.av u')).interpret I e b → val c σ u = val c σ u' := by
    intro u u' s hu hu' b h1 h2
    rw [(hDV u s hu).1] at h1
    rw [(hDV u' s hu').1] at h2
    cases hv : val c σ u with
    | none => rw [hv] at h1; exact h1.elim
    | some w =>
      cases hv' : val c σ u' with
      | none => rw [hv'] at h2; exact h2.elim
      | some w' =>
        rw [hv] at h1
        rw [hv'] at h2
        have hw := (hDV u s hu).2 w hv
        have hw' := (hDV u' s hu').2 w' hv'
        exact congrArg some (values_apart hI hg hsc.trans (apartSort_of_sorted hg hw) hw hw'
          ((((elemOf_spec hI hw e).1 b).mp h1).symm.trans (((elemOf_spec hI hw' e).1 b).mp h2)))
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
  -- the `\in` premises give the match
  have hmatch : ∀ (ps : List FnPat) (k : Nat) (a : M), FnEqn.patsTyped c E.av k ps = true →
      (KoreAML.tr ⟨t, []⟩ (FnEqn.ins c E.av k ps)).interpret I e a → FnEqn.Matches c σ k ps := by
    intro ps
    induction ps with
    | nil => intro k a _ _; trivial
    | cons p ps ih =>
      intro k a htp' hi
      obtain ⟨s', u, as⟩ := p
      simp only [FnEqn.patsTyped, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htp'
      obtain ⟨⟨⟨⟨hpR, hxk⟩, hpt⟩, has⟩, hrest⟩ := htp'
      simp only [FnEqn.ins] at hi
      rw [tr_and2, KoreAML.interp_sAnd] at hi
      obtain ⟨hin, hi'⟩ := hi
      obtain ⟨τp, hτpsort, hτp⟩ := srt_den hI (hnum hpR)
      have hφ : ∀ a', (KoreAML.tr ⟨t, []⟩ (kore c E.av (.var k))).interpret I e a' → KoreAML.Inh I τp a' := by
        intro a' ha'
        rw [(hDV (.var k) s' hxk).1] at ha'
        cases hv : val c σ (.var k) with
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
        simp only [FnEqn.patK] at hpb
        refine ⟨?_, fun j hj => (by cases hj), ih (k + 1) a hrest hi'⟩
        have := hsame u (.var k) s' hpt hxk b hpb hxb
        rwa [fq_val_var] at this
      | some j =>
        simp only [FnEqn.patK] at hpb
        rw [tr_and2, KoreAML.interp_sAnd] at hpb
        refine ⟨?_, fun j' hj' => ?_, ih (k + 1) a hrest hi'⟩
        · have := hsame u (.var k) s' hpt hxk b hpb.1 hxb
          rwa [fq_val_var] at this
        · cases hj'
          have := hsame (.var j) (.var k) s' (eq_of_beq has) hxk b hpb.2 hxb
          rwa [fq_val_var, fq_val_var] at this
  rw [hp]
  unfold FnEqn.pattern
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [KoreAML.tr, KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun hprem => ?_⟩
    rw [tr_and2, KoreAML.interp_sAnd] at hprem
    obtain ⟨hprem, hins⟩ := hprem
    have hreq : ∀ q, E.req = some q → val c σ q = some (bool true) := by
      intro q hq
      unfold FnEqn.reqP at hprem
      rw [hq] at hprem htq
      dsimp only at hprem htq
      have htq' : srt? c E.av q = some Srt.bool := eq_of_beq htq
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
      cases hvq : val c σ q with
      | none => rw [hvq] at hq1; exact hq1.elim
      | some w =>
        rw [hvq] at hq1
        have hw := (hDV q _ htq').2 w hvq
        by_cases hne : w = bool true
        · rw [hne]
        · exact absurd ⟨hq1, (hT1 _).mpr rfl⟩
            (dom_apart hI hdist hw hT hne e _)
    have heq := hE σ hσ hreq (hmatch E.pats E.vars.length a htp hins)
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτ t e) hRv hτsort hR]
    refine ⟨(KoreAML.interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [(hDV E.lhs _ htl).1 b, heq, ← (hDV E.rhs _ htr).1 b, KoreAML.tr]
    show _ ↔ (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ (kore c E.av E.rhs))
      (KoreAML.tr ⟨t, []⟩ (.top (srtOf c E.s)))).interpret I e b
    rw [KoreAML.interp_sAnd, show KoreAML.tr ⟨t, []⟩ (.top (srtOf c E.s)) =
      KoreAML.sTop (KoreAML.trSort t (srtOf c E.s)) from by rw [KoreAML.tr]]
    rw [KoreAML.interp_sTop hD (by rw [trSort_srtOf_twoT]; rfl), KoreAML.interp_inhOf_of (hτ t e)]
    exact ⟨fun h' => ⟨h', hb⟩, And.left⟩

/-! ## Over the registry's names -/

namespace FnEqn

/-- `patK` with the registry's names. -/
def patKR (vs : Vars) (s : Srt) (t : Term) : Option Nat → Kore.Pattern
  | none => koreR vs t
  | some j => .and (regSrtK s) [koreR vs t, koreR vs (.var j)]

/-- `ins` with the registry's names. -/
def insR (vs : Vars) : Nat → List FnPat → Kore.Pattern
  | _, [] => .top KoreAML.R
  | k, p :: ps => .and KoreAML.R
      [.in (regSrtK p.1) KoreAML.R (koreR vs (.var k)) (patKR vs p.1 p.2.1 p.2.2), insR vs (k + 1) ps]

/-- `pattern` with the registry's names. -/
def patR (E : FnEqn) : Kore.Pattern :=
  .implies KoreAML.R
    (.and KoreAML.R
      [match E.req with
        | none => .top KoreAML.R
        | some q => .equals (regSrtK Srt.bool) KoreAML.R (koreR E.av q) (.dv (regSrtK Srt.bool) "true"),
       insR E.av E.vars.length E.pats])
    (.equals (regSrtK E.s) KoreAML.R (koreR E.av E.lhs)
      (.and (regSrtK E.s) [koreR E.av E.rhs, .top (regSrtK E.s)]))

/-- The patterns are over the registry's symbols and sorts. -/
def patsReg : List FnPat → Bool
  | [] => true
  | p :: ps => decide (p.1 < nRegSorts) && reg p.2.1 && patsReg ps

/-- The equation is over the registry's symbols and sorts, and each of its variables is free in
its pattern. -/
def regular (E : FnEqn) : Bool :=
  decide (E.s < nRegSorts) && E.av.all (fun p => decide (p.2 < nRegSorts)) &&
  reg E.lhs && reg E.rhs && patsReg E.pats && (match E.req with | none => true | some q => reg q) &&
  E.av.all (fun p => (KoreAML.freeOf [] E.patR).contains (.evar p.1 (regSrtK p.2)))

theorem ins_reg (c : Semantics) {vs : Vars} (hv : ∀ p ∈ vs, p.2 < nRegSorts) :
    ∀ (ps : List FnPat) (k : Nat), patsReg ps = true → ins c vs k ps = insR vs k ps
  | [], _, _ => by rw [ins, insR]
  | (s, t, as) :: ps, k, hr => by
    simp only [patsReg, Bool.and_eq_true, decide_eq_true_eq] at hr
    obtain ⟨⟨hs, ht⟩, hps⟩ := hr
    have hk : kore c vs (.var k) = koreR vs (.var k) := kore_reg c hv _ (by rw [reg])
    have hpk : patK c vs s t as = patKR vs s t as := by
      cases as with
      | none => simp only [patK, patKR]; exact kore_reg c hv _ ht
      | some j =>
        simp only [patK, patKR]
        rw [kore_reg c hv _ ht, kore_reg c hv (.var j) (by rw [reg]), srtOf_reg c hs]
    simp only [ins, insR]
    rw [hk, hpk, srtOf_reg c hs, ins_reg c hv ps (k + 1) hps]

theorem pattern_reg (c : Semantics) {E : FnEqn} (hr : E.regular = true) : E.pattern c = E.patR := by
  simp only [regular, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨hs, hv⟩, hl⟩, hrr⟩, hps⟩, hq⟩, -⟩ := hr
  unfold pattern patR reqP
  rw [kore_reg c hv _ hl, kore_reg c hv _ hrr, srtOf_reg c hs, ins_reg c hv _ _ hps]
  cases hreq : E.req with
  | none => rfl
  | some q =>
    rw [hreq] at hq
    dsimp only at hq ⊢
    rw [kore_reg c hv _ hq, srtOf_reg c (by decide : Srt.bool < nRegSorts)]

end FnEqn

/-- `FnEqn.entailed` for an equation over the registry's names: the axiom's pattern is compared
with a pattern that does not depend on the semantics. -/
theorem FnEqn.entailed_reg {c : Semantics} (h : c.coreOK = true) (E : FnEqn) (hr : E.regular = true)
    (ht : E.typed c = true) (hE : E.Holds c) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv]) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  refine FnEqn.entailed h E ht hE ad (hp.trans (FnEqn.pattern_reg c hr).symm) hsv (fun i hi => ?_)
  have hr' := hr
  simp only [FnEqn.regular, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr'
  obtain ⟨⟨⟨⟨⟨⟨-, hv⟩, -⟩, -⟩, -⟩, -⟩, hf⟩ := hr'
  have hmem : E.av.getD i ("", 0) ∈ E.av := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  have := hf _ hmem
  rw [hp]
  unfold vkey
  rw [srtOf_reg c (hv _ hmem)]
  exact List.mem_of_elem_eq_true this

end LibEv

end KCore
