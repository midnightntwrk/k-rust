/-
  KCore, checked layer: a library equation over interpreted hooked symbols is entailed at values
  (`EntailsAtValues`), for every semantics meeting `coreOK` and every interpretation.

  The equations are those of the form kompile writes for a rule of the builtin files that rewrites
  a term to a term, `\implies{R}(premise, \equals{s, R}(lhs, \and{s}(rhs, \top{s}())))`, where the
  premise is `\top{R}()` or `\equals{SortBool, R}(req, \dv{SortBool}("true"))` and `lhs`, `rhs`,
  `req` are built from element variables, domain values and interpreted hooked symbols (`hookSigs`).

  - `LibEv.kore`: such a term as a KORE pattern, its variables under the names the text gives them.
  - `LibEv.val`: its value at a substitution: a variable's value, a domain value, the value Γ states
    of an interpreted symbol at its arguments' values (`Semantics.hv`: `hook`'s, and at a silent
    point the interpretation's), none where an argument has none.
  - `LibEv.den_val`: in a model of `Γ c`, at a valuation that gives each variable its value's
    element, the translated term denotes its value's element, or nothing where it has no value.
  - `LibEv.Eqn.entailed`: an equation whose two sides have the same value at every substitution of
    values of the variables' sorts at which the `requires` has the value `true` (`Eqn.Holds`, a
    statement about `hook` and the interpretation only) is entailed at values, whatever axiom
    declaration of a text holds its pattern.
-/
import KcoreSpec.CondPred
import KcoreSpec.HypWf
import KcoreSpec.TieDefs
import KcoreSpec.LibAdmitted
import KcoreSpec.OpenClauseFam
import KcoreSpec.CoreDecide

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- The variables of a library sentence: the name the text gives each and its sort. -/
abbrev Vars := List (String × Srt)

/-- The key of the i-th variable. -/
def vkey (c : Semantics) (vars : Vars) (i : Nat) : KoreAML.VarKey :=
  .evar (vars.getD i ("", 0)).1 (srtOf c (vars.getD i ("", 0)).2)

mutual
  /-- A term over variables, domain values and interpreted hooked symbols as a KORE pattern, the
  i-th variable under its name in `vars`. An injection and an `as` pattern are not such terms
  (`srt?` gives them no sort). -/
  def kore (c : Semantics) (vars : Vars) : Term → Kore.Pattern
    | .var i => .var (.evar (KoreAML.evar (vars.getD i ("", 0)).1 (srtOf c (vars.getD i ("", 0)).2)))
    | .app f ts => symApp c f (koreList c vars ts)
    | .dv s lit => .dv (srtOf c s) lit.text
    | .inj _ _ t => kore c vars t
    | .as t _ => kore c vars t
    termination_by structural t => t
  def koreList (c : Semantics) (vars : Vars) : List Term → List Kore.Pattern
    | [] => []
    | t :: ts => kore c vars t :: koreList c vars ts
    termination_by structural ts => ts
end

mutual
  /-- The value of such a term at σ: Γ's value of an interpreted symbol at its arguments' values
  (`Semantics.hv`), none where an argument has none. -/
  def val (c : Semantics) (σ : Subst) : Term → Option GroundTerm
    | .var i => σ.lookup i
    | .app f ts => (allSome (valList c σ ts)).bind (c.hv f)
    | .dv s lit => some (.dv s lit)
    | .inj _ _ _ => none
    | .as _ _ => none
    termination_by structural t => t
  def valList (c : Semantics) (σ : Subst) : List Term → List (Option GroundTerm)
    | [] => []
    | t :: ts => val c σ t :: valList c σ ts
    termination_by structural ts => ts
end

mutual
  /-- The sort of such a term: a variable's, a domain value's where it is a value of its sort, the
  result sort of an interpreted hooked symbol applied to terms of its argument sorts. -/
  def srt? (c : Semantics) (vars : Vars) : Term → Option Srt
    | .var i => vars[i]?.map (·.2)
    | .app f ts => (lookupSig hookSigs f).bind fun k =>
        if srts? c vars ts == some k.args then some k.result else none
    | .dv s lit => if c.sortOf (.dv s lit) == some s then some s else none
    | .inj _ _ _ => none
    | .as _ _ => none
    termination_by structural t => t
  def srts? (c : Semantics) (vars : Vars) : List Term → Option (List Srt)
    | [] => some []
    | t :: ts => (srt? c vars t).bind fun s => (srts? c vars ts).map (s :: ·)
    termination_by structural ts => ts
end

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {vars : Vars} {σ : Subst} {tbl : KoreAML.VarTable} {e : Valuation M}
  (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
  (hag : ∀ i v, i < vars.length → σ.lookup i = some v →
    ∀ m, m = e.evalEvar (tbl.ev (vkey c vars i)) ↔ (den c v).interpret I e m)
include h hI hσ hag

set_option linter.unusedSectionVars false in
mutual
  /-- **A library term denotes its value.** In a model of `Γ c`, at a valuation that gives each
  variable the element of its value under σ, the translation of a term of the sort `s` denotes
  the element of its value, or nothing where it has none; and its value is of the sort `s`. -/
  theorem den_val : ∀ (t : Term) {s : Srt}, srt? c vars t = some s →
      (∀ m, (KoreAML.tr ⟨tbl, []⟩ (kore c vars t)).interpret I e m ↔ Res c I e (val c σ t) m) ∧
      (∀ v, val c σ t = some v → c.sortOf v = some s)
    | .var i, s, ht => by
      simp only [srt?] at ht
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp ht
      obtain ⟨v, hv, hvs⟩ := hσ i p hp
      have hlt : i < vars.length := (List.getElem?_eq_some_iff.mp hp).1
      refine ⟨fun m => ?_, fun w hw => ?_⟩
      · rw [kore, KoreAML.tr, val, hv]
        exact hag i v hlt hv m
      · rw [val, hv] at hw
        cases hw
        exact hvs
    | .dv s' lit, s, ht => by
      simp only [srt?] at ht
      by_cases hd : c.sortOf (.dv s' lit) = some s'
      · simp only [hd, beq_self_eq_true, ite_true, Option.some.injEq] at ht
        subst ht
        refine ⟨fun m => ?_, fun w hw => ?_⟩
        · rw [kore, val]
          show _ ↔ (den c (.dv s' lit)).interpret I e m
          unfold den KoreAML.den
          rw [GroundTerm.kore]
          unfold srtOf
          rw [KoreAML.tr_dv, KoreAML.tr_dv]
        · rw [val] at hw
          cases hw
          exact hd
      · simp [hd] at ht
    | .app f ts, s, ht => by
      simp only [srt?] at ht
      obtain ⟨k, hk, hk2⟩ := Option.bind_eq_some_iff.mp ht
      by_cases hargs : srts? c vars ts = some k.args
      · simp only [hargs, beq_self_eq_true, ite_true, Option.some.injEq] at hk2
        subst hk2
        obtain ⟨hks, hkn⟩ := lookupSig_spec hk
        have hih := den_vals ts hargs
        have hhook : isHook f = true := by
          cases hh : isHook f with
          | true => rfl
          | false => rw [lookupSig_hookSigs_of_not_isHook hh] at hk; cases hk
        refine ⟨fun m => ?_, fun w hw => ?_⟩
        · rw [kore, tr_symApp, val]
          cases hall : allSome (valList c σ ts) with
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
        · rw [val] at hw
          cases hall : allSome (valList c σ ts) with
          | none => rw [hall] at hw; cases hw
          | some ws =>
            rw [hall] at hw
            obtain ⟨hws, -⟩ := hih.1 ws hall
            obtain ⟨o, ho⟩ := Semantics.hookRes_some (c := c) hhook ws
            have ho' : o = some w := by simpa [Semantics.hv, ho] using hw
            exact hookRes_sorted (fun _ => rangeBelow_of_core h) hk hws (ho' ▸ ho)
      · simp [hargs] at hk2
    | .inj _ _ _, s, ht => by simp [srt?] at ht
    | .as _ _, s, ht => by simp [srt?] at ht
  termination_by structural t => t
  /-- The arguments of an application: where each has a value, the values are of the argument
  sorts and the application of any head to the translated arguments is its application to the
  values' patterns; where one has none, the application denotes nothing. -/
  theorem den_vals : ∀ (ts : List Term) {ss : List Srt}, srts? c vars ts = some ss →
      (∀ ws, allSome (valList c σ ts) = some ws → c.sortsOf ws = some ss ∧
        ∀ (acc acc' : KoreAML.P), (∀ m, acc.interpret I e m ↔ acc'.interpret I e m) →
          ∀ m, (KoreAML.trArgs ⟨tbl, []⟩ acc (koreList c vars ts)).interpret I e m ↔
            (KoreAML.trArgs ⟨[], []⟩ acc' (GroundTerm.koreList c ws)).interpret I e m) ∧
      (allSome (valList c σ ts) = none →
        ∀ (acc : KoreAML.P) m, ¬ (KoreAML.trArgs ⟨tbl, []⟩ acc (koreList c vars ts)).interpret I e m)
    | [], ss, ht => by
      simp only [srts?, Option.some.injEq] at ht
      subst ht
      refine ⟨fun ws hws => ?_, fun hn => by simp [valList, allSome] at hn⟩
      simp only [valList, allSome, Option.some.injEq] at hws
      subst hws
      refine ⟨sortsOf_nil, fun acc acc' hacc m => ?_⟩
      rw [koreList, GroundTerm.koreList, KoreAML.trArgs_nil, KoreAML.trArgs_nil]
      exact hacc m
    | t :: ts, ss, ht => by
      simp only [srts?] at ht
      obtain ⟨s, h1, hrest⟩ := Option.bind_eq_some_iff.mp ht
      obtain ⟨ss', h2, rfl⟩ := Option.map_eq_some_iff.mp hrest
      have ih1 := den_val t h1
      have ih2 := den_vals ts h2
      constructor
      · intro ws hws
        simp only [valList, allSome, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hws
        obtain ⟨w, hw, ws', hws', rfl⟩ := hws
        obtain ⟨hs', hc'⟩ := ih2.1 ws' hws'
        refine ⟨sortsOf_cons.mpr ⟨s, ss', ih1.2 w hw, hs', rfl⟩, fun acc acc' hacc m => ?_⟩
        rw [koreList, GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_cons]
        exact hc' _ _ (KoreAML.interp_app_congr hacc (fun m => by rw [ih1.1 m, hw]; rfl)) m
      · intro hn acc m
        rw [koreList, KoreAML.trArgs_cons]
        cases hr : val c σ t with
        | none =>
          exact trArgs_empty (fun m' hm' => by
            obtain ⟨_, b, _, hb, _⟩ := KoreAML.interp_app.mp hm'
            have hb' := (ih1.1 b).mp hb
            rw [hr] at hb'
            exact hb') _ m
        | some w =>
          cases hrs : allSome (valList c σ ts) with
          | none => exact ih2.2 hrs _ m
          | some ws' => simp [valList, allSome, hr, hrs] at hn
  termination_by structural ts => ts
end

end

/-! ## An equation between two terms -/

/-- A library equation `lhs => rhs requires req` over the variables `vars`, its sides of the
sort `s`. -/
structure Eqn where
  vars : Vars
  s : Srt
  req : Option Term
  lhs : Term
  rhs : Term

namespace Eqn

/-- The premise kompile writes: `\top{R}()` without a `requires`, `req = true` with one. -/
def premise (c : Semantics) (E : Eqn) : Kore.Pattern :=
  match E.req with
  | none => .top KoreAML.R
  | some q => .equals (srtOf c Srt.bool) KoreAML.R (kore c E.vars q) (.dv (srtOf c Srt.bool) "true")

/-- The pattern of the equation's axiom, as kompile writes it over the sort variable `R`. -/
def pattern (c : Semantics) (E : Eqn) : Kore.Pattern :=
  .implies KoreAML.R (E.premise c)
    (.equals (srtOf c E.s) KoreAML.R (kore c E.vars E.lhs)
      (.and (srtOf c E.s) [kore c E.vars E.rhs, .top (srtOf c E.s)]))

/-- The equation is over registry sorts, its sides are terms of the sort `s` and its `requires` a
term of the sort Bool. -/
def typed (c : Semantics) (E : Eqn) : Bool :=
  decide (E.s < nRegSorts) && E.vars.all (fun p => decide (p.2 < nRegSorts)) &&
  srt? c E.vars E.lhs == some E.s && srt? c E.vars E.rhs == some E.s &&
  match E.req with
  | none => true
  | some q => srt? c E.vars q == some Srt.bool

/-- The two sides have the same value, or both none, at every substitution of values of the
variables' sorts at which the `requires` has the value `true`. -/
def Holds (c : Semantics) (E : Eqn) : Prop :=
  ∀ σ : Subst, (∀ i p, E.vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) →
    (∀ q, E.req = some q → val c σ q = some (bool true)) → val c σ E.lhs = val c σ E.rhs

end Eqn

/-- **A library equation that holds of the values is entailed at values.** For a semantics
meeting `coreOK` and an equation `E` whose sides have equal values wherever its `requires` is
true (`Eqn.Holds`): the translation of any axiom declaration whose pattern is `E`'s, over the one
sort variable `R` and with each variable of `E` free in it, holds in every model of `Γ c` at
every valuation that sends the axiom's free element variables to values. -/
theorem Eqn.entailed {c : Semantics} (h : c.coreOK = true) (E : Eqn) (ht : E.typed c = true)
    (hE : E.Holds c) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.pattern c)
    (hsv : ad.ax.sortVars = [KoreAML.Rv])
    (hfv : ∀ i, i < E.vars.length → vkey c E.vars i ∈ KoreAML.freeOf [] ad.ax.pattern) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hI e hat m
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨-, hfa, -, -, -⟩ := Semantics.coreOK_parts h
  obtain ⟨-, hg, -, -, -, hn, -, hsn, -, -, -, -⟩ := faithCoreOK_parts hfa
  simp only [Eqn.typed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at ht
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
  have hDV := fun (u : Term) (s : Srt) (hu : srt? c E.vars u = some s) =>
    den_val (tbl := t) (e := e) h hI hσ hag u hu
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
    have hreq : ∀ q, E.req = some q → val c σ q = some (bool true) := by
      intro q hq
      unfold Eqn.premise at hprem
      rw [hq] at hprem htq
      dsimp only at hprem htq
      have htq' : srt? c E.vars q = some Srt.bool := eq_of_beq htq
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

/-! ## Terms over the registry's names

A term whose symbols and sorts are the registry's is the same pattern in every semantics: the
registry's names are the semantics' names for them. -/

mutual
  /-- `kore` with the registry's names, for a term over registry symbols and sorts. -/
  def koreR (vars : Vars) : Term → Kore.Pattern
    | .var i => .var (.evar (KoreAML.evar (vars.getD i ("", 0)).1 (regSrtK (vars.getD i ("", 0)).2)))
    | .app f ts => .app ⟨⟨regSymNames.getD f ""⟩⟩ [] (koreRList vars ts)
    | .dv s lit => .dv (regSrtK s) lit.text
    | .inj _ _ t => koreR vars t
    | .as t _ => koreR vars t
    termination_by structural t => t
  def koreRList (vars : Vars) : List Term → List Kore.Pattern
    | [] => []
    | t :: ts => koreR vars t :: koreRList vars ts
    termination_by structural ts => ts
end

mutual
  /-- The term's symbols and sorts are the registry's, and none of its symbols is named like an
  `ite` at a sort. -/
  def reg : Term → Bool
    | .var _ => true
    | .app f ts => decide (f < nRegSyms) && (iteSort? (regSymNames.getD f "")).isNone && regList ts
    | .dv s _ => decide (s < nRegSorts)
    | .inj _ _ _ => false
    | .as _ _ => false
    termination_by structural t => t
  def regList : List Term → Bool
    | [] => true
    | t :: ts => reg t && regList ts
    termination_by structural ts => ts
end

theorem srtOf_reg (c : Semantics) {s : Srt} (hs : s < nRegSorts) : srtOf c s = regSrtK s := by
  unfold srtOf regSrtK Semantics.sortName
  simp only [hs, ↓reduceIte]

theorem symName_reg (c : Semantics) {f : Sym} (hf : f < nRegSyms) : c.symName f = regSymNames.getD f "" := by
  unfold Semantics.symName
  simp only [hf, ↓reduceIte]

theorem getD_reg {vars : Vars} (hv : ∀ p ∈ vars, p.2 < nRegSorts) (i : Nat) :
    (vars.getD i ("", 0)).2 < nRegSorts := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : vars[i]? with
  | none => exact (by decide : (0 : Nat) < nRegSorts)
  | some p => exact hv p (List.mem_of_getElem? hi)

mutual
  theorem kore_reg (c : Semantics) {vars : Vars} (hv : ∀ p ∈ vars, p.2 < nRegSorts) :
      ∀ t : Term, reg t = true → kore c vars t = koreR vars t
    | .var i, _ => by rw [kore, koreR, srtOf_reg c (getD_reg hv i)]
    | .app f ts, ht => by
      simp only [reg, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at ht
      rw [kore, koreR, koreList_reg c hv ts ht.2,
        symApp_noInst (by rw [symName_reg c ht.1.1]; exact Faithful.regSym_noInst_irs ht.1.1), symName_reg c ht.1.1]
    | .dv s lit, ht => by
      simp only [reg, decide_eq_true_eq] at ht
      rw [kore, koreR, srtOf_reg c ht]
    | .inj _ _ _, ht => by simp [reg] at ht
    | .as _ _, ht => by simp [reg] at ht
  termination_by structural t => t
  theorem koreList_reg (c : Semantics) {vars : Vars} (hv : ∀ p ∈ vars, p.2 < nRegSorts) :
      ∀ ts : List Term, regList ts = true → koreList c vars ts = koreRList vars ts
    | [], _ => by rw [koreList, koreRList]
    | t :: ts, ht => by
      simp only [regList, Bool.and_eq_true] at ht
      rw [koreList, koreRList, kore_reg c hv t ht.1, koreList_reg c hv ts ht.2]
  termination_by structural ts => ts
end

namespace Eqn

/-- `pattern` with the registry's names. -/
def patR (E : Eqn) : Kore.Pattern :=
  .implies KoreAML.R
    (match E.req with
      | none => .top KoreAML.R
      | some q => .equals (regSrtK Srt.bool) KoreAML.R (koreR E.vars q) (.dv (regSrtK Srt.bool) "true"))
    (.equals (regSrtK E.s) KoreAML.R (koreR E.vars E.lhs)
      (.and (regSrtK E.s) [koreR E.vars E.rhs, .top (regSrtK E.s)]))

/-- The equation is over the registry's symbols and sorts, and each of its variables is free in
its pattern. -/
def regular (E : Eqn) : Bool :=
  decide (E.s < nRegSorts) && E.vars.all (fun p => decide (p.2 < nRegSorts)) &&
  reg E.lhs && reg E.rhs && (match E.req with | none => true | some q => reg q) &&
  E.vars.all (fun p => (KoreAML.freeOf [] E.patR).contains (.evar p.1 (regSrtK p.2)))

theorem pattern_reg (c : Semantics) {E : Eqn} (hr : E.regular = true) : E.pattern c = E.patR := by
  simp only [regular, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨hs, hv⟩, hl⟩, hrr⟩, hq⟩, -⟩ := hr
  unfold pattern patR premise
  rw [kore_reg c hv _ hl, kore_reg c hv _ hrr, srtOf_reg c hs]
  cases hreq : E.req with
  | none => rfl
  | some q =>
    rw [hreq] at hq
    dsimp only at hq ⊢
    rw [kore_reg c hv _ hq, srtOf_reg c (by decide : Srt.bool < nRegSorts)]

end Eqn

/-- `Eqn.entailed` for an equation over the registry's names: the axiom's pattern is compared
with a pattern that does not depend on the semantics. -/
theorem Eqn.entailed_reg {c : Semantics} (h : c.coreOK = true) (E : Eqn) (hr : E.regular = true)
    (ht : E.typed c = true) (hE : E.Holds c) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv]) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  refine Eqn.entailed h E ht hE ad (hp.trans (Eqn.pattern_reg c hr).symm) hsv (fun i hi => ?_)
  have hr' := hr
  simp only [Eqn.regular, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr'
  obtain ⟨⟨⟨⟨⟨-, hv⟩, -⟩, -⟩, -⟩, hf⟩ := hr'
  have hmem : E.vars.getD i ("", 0) ∈ E.vars := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  have := hf _ hmem
  rw [hp]
  unfold vkey
  rw [srtOf_reg c (hv _ hmem)]
  exact List.mem_of_elem_eq_true this

end LibEv

end KCore
