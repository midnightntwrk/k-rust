/-
  Library sentences that apply symbols Γ lacks, at values, in one interpretation.

  `LibEv`'s terms read an application of an interpreted hooked symbol through `Semantics.hv`, the
  value Γ states of it. Here a term may also apply a symbol of a list `ls` of signatures, read
  through a partial function `G` on values: in an interpretation `I` of `Γ c` in which each symbol
  of `ls` applied to values of its argument sorts denotes `G`'s value there, or nothing where `G`
  has none (`LackedDen`), a term denotes its value (`den_valLk`).

  - `valLk`, `srtLk?`: the value and the sort of a term, an interpreted symbol read as `LibEv.val`
    reads it, another symbol by its signature in `ls` and by `G`.
  - `FnEqn.entailedLk`, `FnEqn.entailedLk_reg`: a library equation in the function form whose two
    sides have the same value under `G` wherever its `requires` is true and its patterns match
    (`FnEqn.HoldsLk`) holds in `I` at every valuation that sends the axiom's free element
    variables to values.
  - `functionalLk`: the `functional` sentence of a symbol of `ls` holds in `I` at values where
    `G` has a value at every argument list of its sorts.
  - `Eqn.entailedLk`, `Eqn.entailedLk_reg`: a library equation between two terms whose two sides
    have the same value under `G` wherever its `requires` is true (`Eqn.HoldsLk`) holds in `I` at
    every valuation that sends the axiom's free element variables to values.

  The statements are about one interpretation, not every model of `Γ c`: `LackedDen` is a fact of
  `I` at the symbols `ls` names, which Γ need not state.
-/
import KcoreSpec.LibEvFn
import KcoreSpec.LibEvFun

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- The signature of a term's head: an interpreted hooked symbol's in `hookSigs`, another
symbol's in `ls`. -/
def sigLk (ls : List CtorSig) (f : Sym) : Option CtorSig :=
  if isHook f then lookupSig hookSigs f else lookupSig ls f

mutual
  /-- The value of a term at σ: an interpreted hooked symbol's as `LibEv.val` reads it
  (`Semantics.hv`), another symbol's `G`'s at its arguments' values, none where an argument has
  none. -/
  def valLk (c : Semantics) (G : Sym → List GroundTerm → Option GroundTerm) (σ : Subst) :
      Term → Option GroundTerm
    | .var i => σ.lookup i
    | .app f ts => (allSome (valListLk c G σ ts)).bind (if isHook f then c.hv f else G f)
    | .dv s lit => some (.dv s lit)
    | .inj _ _ _ => none
    | .as _ _ => none
    termination_by structural t => t
  def valListLk (c : Semantics) (G : Sym → List GroundTerm → Option GroundTerm) (σ : Subst) :
      List Term → List (Option GroundTerm)
    | [] => []
    | t :: ts => valLk c G σ t :: valListLk c G σ ts
    termination_by structural ts => ts
end

mutual
  /-- The sort of a term: a variable's, a domain value's where it is a value of its sort under
  `so` (a semantics' `sortOf`), the result sort of its head's signature (`sigLk`) applied to
  terms of its argument sorts. -/
  def srtLk? (so : GroundTerm → Option Srt) (ls : List CtorSig) (vars : Vars) : Term → Option Srt
    | .var i => vars[i]?.map (·.2)
    | .app f ts => (sigLk ls f).bind fun k =>
        if srtsLk? so ls vars ts == some k.args then some k.result else none
    | .dv s lit => if so (.dv s lit) == some s then some s else none
    | .inj _ _ _ => none
    | .as _ _ => none
    termination_by structural t => t
  def srtsLk? (so : GroundTerm → Option Srt) (ls : List CtorSig) (vars : Vars) : List Term → Option (List Srt)
    | [] => some []
    | t :: ts => (srtLk? so ls vars t).bind fun s => (srtsLk? so ls vars ts).map (s :: ·)
    termination_by structural ts => ts
end

/-- **In `I`, each symbol of `ls` at values denotes `G`'s value**: applied to values of its
argument sorts, the symbol denotes the element of `G`'s value there, or nothing where `G` has
none, and `G`'s values are of its result sort. -/
def LackedDen (c : Semantics) (ls : List CtorSig) (G : Sym → List GroundTerm → Option GroundTerm)
    {M : Type} (I : Interpretation KoreAML.Sym M) : Prop :=
  ∀ k ∈ ls, ∀ ws, c.sortsOf ws = some k.args →
    (∀ (e : Valuation M) m, (KoreAML.den (symApp c k.name (GroundTerm.koreList c ws))).interpret I e m ↔
      Res c I e (G k.name ws) m) ∧
    (∀ v, G k.name ws = some v → c.sortOf v = some k.result)

section
variable {c : Semantics} {ls : List CtorSig} {G : Sym → List GroundTerm → Option GroundTerm} {M : Type}
  [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) (hL : LackedDen c ls G I) {vars : Vars} {σ : Subst}
  {tbl : KoreAML.VarTable} {e : Valuation M}
  (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
  (hag : ∀ i v, i < vars.length → σ.lookup i = some v →
    ∀ m, m = e.evalEvar (tbl.ev (vkey c vars i)) ↔ (den c v).interpret I e m)
include h hI hL hσ hag

set_option linter.unusedSectionVars false in
mutual
  /-- **A term denotes its value**: in `I`, at a valuation that gives each variable the element of
  its value under σ, the translation of a term of the sort `s` denotes the element of its value
  (`valLk`), or nothing where it has none; and its value is of the sort `s`. -/
  theorem den_valLk : ∀ (t : Term) {s : Srt}, srtLk? c.sortOf ls vars t = some s →
      (∀ m, (KoreAML.tr ⟨tbl, []⟩ (kore c vars t)).interpret I e m ↔ Res c I e (valLk c G σ t) m) ∧
      (∀ v, valLk c G σ t = some v → c.sortOf v = some s)
    | .var i, s, ht => by
      simp only [srtLk?] at ht
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp ht
      obtain ⟨v, hv, hvs⟩ := hσ i p hp
      have hlt : i < vars.length := (List.getElem?_eq_some_iff.mp hp).1
      refine ⟨fun m => ?_, fun w hw => ?_⟩
      · rw [kore, KoreAML.tr, valLk, hv]
        exact hag i v hlt hv m
      · rw [valLk, hv] at hw
        cases hw
        exact hvs
    | .dv s' lit, s, ht => by
      simp only [srtLk?] at ht
      by_cases hd : c.sortOf (.dv s' lit) = some s'
      · simp only [hd, beq_self_eq_true, ite_true, Option.some.injEq] at ht
        subst ht
        refine ⟨fun m => ?_, fun w hw => ?_⟩
        · rw [kore, valLk]
          show _ ↔ (den c (.dv s' lit)).interpret I e m
          unfold den KoreAML.den
          rw [GroundTerm.kore]
          unfold srtOf
          rw [KoreAML.tr_dv, KoreAML.tr_dv]
        · rw [valLk] at hw
          cases hw
          exact hd
      · simp [hd] at ht
    | .app f ts, s, ht => by
      simp only [srtLk?] at ht
      obtain ⟨k, hk, hk2⟩ := Option.bind_eq_some_iff.mp ht
      by_cases hargs : srtsLk? c.sortOf ls vars ts = some k.args
      · simp only [hargs, beq_self_eq_true, ite_true, Option.some.injEq] at hk2
        subst hk2
        have hih := den_valsLk ts hargs
        unfold sigLk at hk
        cases hhook : isHook f with
        | true =>
          simp only [hhook, ite_true] at hk
          obtain ⟨hks, hkn⟩ := lookupSig_spec hk
          refine ⟨fun m => ?_, fun w hw => ?_⟩
          · rw [kore, tr_symApp, valLk]
            simp only [hhook, ite_true]
            cases hall : allSome (valListLk c G σ ts) with
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
          · rw [valLk] at hw
            simp only [hhook, ite_true] at hw
            cases hall : allSome (valListLk c G σ ts) with
            | none => rw [hall] at hw; cases hw
            | some ws =>
              rw [hall] at hw
              obtain ⟨hws, -⟩ := hih.1 ws hall
              obtain ⟨o, ho⟩ := Semantics.hookRes_some (c := c) hhook ws
              have ho' : o = some w := by simpa [Semantics.hv, ho] using hw
              exact hookRes_sorted (fun _ => rangeBelow_of_core h) hk hws (ho' ▸ ho)
        | false =>
          simp only [hhook, Bool.false_eq_true, ite_false] at hk
          obtain ⟨hkl, hkn⟩ := lookupSig_spec hk
          refine ⟨fun m => ?_, fun w hw => ?_⟩
          · rw [kore, tr_symApp, valLk]
            simp only [hhook, Bool.false_eq_true, ite_false]
            cases hall : allSome (valListLk c G σ ts) with
            | none =>
              simp only [Option.bind_none, Res, iff_false]
              exact hih.2 hall _ m
            | some ws =>
              obtain ⟨hws, hcong⟩ := hih.1 ws hall
              have hgr := (hL k hkl ws hws).1 e m
              rw [hkn] at hgr
              unfold KoreAML.den at hgr
              rw [tr_symApp] at hgr
              rw [hcong _ _ (fun _ => Iff.rfl) m, hgr]
              rfl
          · rw [valLk] at hw
            simp only [hhook, Bool.false_eq_true, ite_false] at hw
            cases hall : allSome (valListLk c G σ ts) with
            | none => rw [hall] at hw; cases hw
            | some ws =>
              rw [hall] at hw
              obtain ⟨hws, -⟩ := hih.1 ws hall
              have := (hL k hkl ws hws).2 w
              rw [hkn] at this
              exact this hw
      · simp [hargs] at hk2
    | .inj _ _ _, s, ht => by simp [srtLk?] at ht
    | .as _ _, s, ht => by simp [srtLk?] at ht
  termination_by structural t => t
  /-- The arguments of an application: where each has a value, the values are of the argument
  sorts and the application of any head to the translated arguments is its application to the
  values' patterns; where one has none, the application denotes nothing. -/
  theorem den_valsLk : ∀ (ts : List Term) {ss : List Srt}, srtsLk? c.sortOf ls vars ts = some ss →
      (∀ ws, allSome (valListLk c G σ ts) = some ws → c.sortsOf ws = some ss ∧
        ∀ (acc acc' : KoreAML.P), (∀ m, acc.interpret I e m ↔ acc'.interpret I e m) →
          ∀ m, (KoreAML.trArgs ⟨tbl, []⟩ acc (koreList c vars ts)).interpret I e m ↔
            (KoreAML.trArgs ⟨[], []⟩ acc' (GroundTerm.koreList c ws)).interpret I e m) ∧
      (allSome (valListLk c G σ ts) = none →
        ∀ (acc : KoreAML.P) m, ¬ (KoreAML.trArgs ⟨tbl, []⟩ acc (koreList c vars ts)).interpret I e m)
    | [], ss, ht => by
      simp only [srtsLk?, Option.some.injEq] at ht
      subst ht
      refine ⟨fun ws hws => ?_, fun hn => by simp [valListLk, allSome] at hn⟩
      simp only [valListLk, allSome, Option.some.injEq] at hws
      subst hws
      refine ⟨sortsOf_nil, fun acc acc' hacc m => ?_⟩
      rw [koreList, GroundTerm.koreList, KoreAML.trArgs_nil, KoreAML.trArgs_nil]
      exact hacc m
    | t :: ts, ss, ht => by
      simp only [srtsLk?] at ht
      obtain ⟨s, h1, hrest⟩ := Option.bind_eq_some_iff.mp ht
      obtain ⟨ss', h2, rfl⟩ := Option.map_eq_some_iff.mp hrest
      have ih1 := den_valLk t h1
      have ih2 := den_valsLk ts h2
      constructor
      · intro ws hws
        simp only [valListLk, allSome, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hws
        obtain ⟨w, hw, ws', hws', rfl⟩ := hws
        obtain ⟨hs', hc'⟩ := ih2.1 ws' hws'
        refine ⟨sortsOf_cons.mpr ⟨s, ss', ih1.2 w hw, hs', rfl⟩, fun acc acc' hacc m => ?_⟩
        rw [koreList, GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_cons]
        exact hc' _ _ (KoreAML.interp_app_congr hacc (fun m => by rw [ih1.1 m, hw]; rfl)) m
      · intro hn acc m
        rw [koreList, KoreAML.trArgs_cons]
        cases hr : valLk c G σ t with
        | none =>
          exact trArgs_empty (fun m' hm' => by
            obtain ⟨_, b, _, hb, _⟩ := KoreAML.interp_app.mp hm'
            have hb' := (ih1.1 b).mp hb
            rw [hr] at hb'
            exact hb') _ m
        | some w =>
          cases hrs : allSome (valListLk c G σ ts) with
          | none => exact ih2.2 hrs _ m
          | some ws' => simp [valListLk, allSome, hr, hrs] at hn
  termination_by structural ts => ts
end

end

/-! ## An equation in the function form -/

namespace FnEqn

/-- `FnEqn.patsTyped` with the sorts of `srtLk?`. -/
def patsTypedLk (so : GroundTerm → Option Srt) (ls : List CtorSig) (vs : Vars) : Nat → List FnPat → Bool
  | _, [] => true
  | k, p :: ps => decide (p.1 < nRegSorts) && srtLk? so ls vs (.var k) == some p.1 &&
      srtLk? so ls vs p.2.1 == some p.1 &&
      (match p.2.2 with
        | none => true
        | some j => srtLk? so ls vs (.var j) == some p.1) && patsTypedLk so ls vs (k + 1) ps

/-- `FnEqn.typed` with the sorts of `srtLk?`, the domain values' under `so`. -/
def typedLk (so : GroundTerm → Option Srt) (ls : List CtorSig) (E : FnEqn) : Bool :=
  decide (E.s < nRegSorts) && E.av.all (fun p => decide (p.2 < nRegSorts)) &&
  srtLk? so ls E.av E.lhs == some E.s && srtLk? so ls E.av E.rhs == some E.s &&
  patsTypedLk so ls E.av E.vars.length E.pats &&
  match E.req with
  | none => true
  | some q => srtLk? so ls E.av q == some Srt.bool

/-- `FnEqn.Matches` with the values of `valLk`. -/
def MatchesLk (c : Semantics) (G : Sym → List GroundTerm → Option GroundTerm) (σ : Subst) :
    Nat → List FnPat → Prop
  | _, [] => True
  | k, p :: ps => valLk c G σ p.2.1 = σ.lookup k ∧ (∀ j, p.2.2 = some j → σ.lookup j = σ.lookup k) ∧
      MatchesLk c G σ (k + 1) ps

/-- `f` at the argument variables and the right side have the same value under `G`, or both
none, at every substitution of values of the variables' sorts at which the `requires` has the
value `true` and the patterns match the arguments. -/
def HoldsLk (c : Semantics) (G : Sym → List GroundTerm → Option GroundTerm) (E : FnEqn) : Prop :=
  ∀ σ : Subst, (∀ i p, E.av[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) →
    (∀ q, E.req = some q → valLk c G σ q = some (bool true)) → MatchesLk c G σ E.vars.length E.pats →
    valLk c G σ E.lhs = valLk c G σ E.rhs

end FnEqn

theorem fq_valLk_var (c : Semantics) (G : Sym → List GroundTerm → Option GroundTerm) (σ : Subst) (k : Nat) :
    valLk c G σ (.var k) = σ.lookup k := by rw [valLk]

/-- **A library equation in the function form that holds under `G` holds at values in `I`.** For
a semantics meeting `coreOK`, an interpretation `I` of `Γ c` in which the symbols of `ls` denote
`G` at values (`LackedDen`), and an equation `E` with `FnEqn.HoldsLk`: the translation of any
axiom declaration whose pattern is `E`'s, over the one sort variable `R` and with each variable of
`E` free in it, holds in `I` at every valuation that sends the axiom's free element variables to
values. -/
theorem FnEqn.entailedLk {c : Semantics} (h : c.coreOK = true) {ls : List CtorSig}
    {G : Sym → List GroundTerm → Option GroundTerm} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ c) (hL : LackedDen c ls G I) (E : FnEqn) (ht : E.typedLk c.sortOf ls = true)
    (hE : E.HoldsLk c G) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.pattern c)
    (hsv : ad.ax.sortVars = [KoreAML.Rv])
    (hfv : ∀ i, i < E.av.length → vkey c E.av i ∈ KoreAML.freeOf [] ad.ax.pattern) :
    ∀ e, AtValues c I e ad.ax → ∀ m, (KoreAML.trAxiom [] [] ad).pat.interpret I e m := by
  intro e hat m
  obtain ⟨hok, hsr, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  simp only [FnEqn.typedLk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at ht
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
  have hDV := fun (u : Term) (s : Srt) (hu : srtLk? c.sortOf ls E.av u = some s) =>
    den_valLk (tbl := t) (e := e) h hI hL hσ hag u hu
  -- two terms of a sort that denote a common element have the same value
  have hsame : ∀ (u u' : Term) (s : Srt), srtLk? c.sortOf ls E.av u = some s → srtLk? c.sortOf ls E.av u' = some s → ∀ b,
      (KoreAML.tr ⟨t, []⟩ (kore c E.av u)).interpret I e b →
      (KoreAML.tr ⟨t, []⟩ (kore c E.av u')).interpret I e b → valLk c G σ u = valLk c G σ u' := by
    intro u u' s hu hu' b h1 h2
    rw [(hDV u s hu).1] at h1
    rw [(hDV u' s hu').1] at h2
    cases hv : valLk c G σ u with
    | none => rw [hv] at h1; exact h1.elim
    | some w =>
      cases hv' : valLk c G σ u' with
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
  have hmatch : ∀ (ps : List FnPat) (k : Nat) (a : M), FnEqn.patsTypedLk c.sortOf ls E.av k ps = true →
      (KoreAML.tr ⟨t, []⟩ (FnEqn.ins c E.av k ps)).interpret I e a → FnEqn.MatchesLk c G σ k ps := by
    intro ps
    induction ps with
    | nil => intro k a _ _; trivial
    | cons p ps ih =>
      intro k a htp' hi
      obtain ⟨s', u, as⟩ := p
      simp only [FnEqn.patsTypedLk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htp'
      obtain ⟨⟨⟨⟨hpR, hxk⟩, hpt⟩, has⟩, hrest⟩ := htp'
      simp only [FnEqn.ins] at hi
      rw [tr_and2, KoreAML.interp_sAnd] at hi
      obtain ⟨hin, hi'⟩ := hi
      obtain ⟨τp, hτpsort, hτp⟩ := srt_den hI (hnum hpR)
      have hφ : ∀ a', (KoreAML.tr ⟨t, []⟩ (kore c E.av (.var k))).interpret I e a' → KoreAML.Inh I τp a' := by
        intro a' ha'
        rw [(hDV (.var k) s' hxk).1] at ha'
        cases hv : valLk c G σ (.var k) with
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
        rwa [fq_valLk_var] at this
      | some j =>
        simp only [FnEqn.patK] at hpb
        rw [tr_and2, KoreAML.interp_sAnd] at hpb
        refine ⟨?_, fun j' hj' => ?_, ih (k + 1) a hrest hi'⟩
        · have := hsame u (.var k) s' hpt hxk b hpb.1 hxb
          rwa [fq_valLk_var] at this
        · cases hj'
          have := hsame (.var j) (.var k) s' (eq_of_beq has) hxk b hpb.2 hxb
          rwa [fq_valLk_var, fq_valLk_var] at this
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
    have hreq : ∀ q, E.req = some q → valLk c G σ q = some (bool true) := by
      intro q hq
      unfold FnEqn.reqP at hprem
      rw [hq] at hprem htq
      dsimp only at hprem htq
      have htq' : srtLk? c.sortOf ls E.av q = some Srt.bool := eq_of_beq htq
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
      cases hvq : valLk c G σ q with
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

/-- `FnEqn.entailedLk` for an equation over the registry's names: the axiom's pattern is compared
with a pattern that does not depend on the semantics. -/
theorem FnEqn.entailedLk_reg {c : Semantics} (h : c.coreOK = true) {ls : List CtorSig}
    {G : Sym → List GroundTerm → Option GroundTerm} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ c) (hL : LackedDen c ls G I) (E : FnEqn) (hr : E.regular = true)
    (ht : E.typedLk c.sortOf ls = true) (hE : E.HoldsLk c G) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    ∀ e, AtValues c I e ad.ax → ∀ m, (KoreAML.trAxiom [] [] ad).pat.interpret I e m := by
  refine FnEqn.entailedLk h hI hL E ht hE ad (hp.trans (FnEqn.pattern_reg c hr).symm) hsv (fun i hi => ?_)
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

/-! ## The `functional` sentence of a symbol of `ls` -/

/-- The variables from `i` on have the sorts of `vars` from `i` on. -/
theorem srtsLk_argVars (c : Semantics) (ls : List CtorSig) (vars : Vars) : ∀ (n i : Nat), i + n = vars.length →
    srtsLk? c.sortOf ls vars (argVars i n) = some ((vars.drop i).map (·.2))
  | 0, i, hi => by
    rw [argVars, srtsLk?, List.drop_of_length_le (by omega)]; rfl
  | n + 1, i, hi => by
    have hlt : i < vars.length := by omega
    rw [argVars, srtsLk?, srtLk?, List.getElem?_eq_getElem hlt, srtsLk_argVars c ls vars n (i + 1) (by omega),
      List.drop_eq_getElem_cons hlt]
    rfl

/-- Where each variable has a value, the variables from `i` on have values. -/
theorem valsLk_argVars (c : Semantics) (G : Sym → List GroundTerm → Option GroundTerm) {vars : Vars} {σ : Subst}
    (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) :
    ∀ (n i : Nat), i + n = vars.length → ∃ ws, allSome (valListLk c G σ (argVars i n)) = some ws
  | 0, _, _ => ⟨[], rfl⟩
  | n + 1, i, hi => by
    have hlt : i < vars.length := by omega
    obtain ⟨v, hv, -⟩ := hσ i _ (List.getElem?_eq_getElem hlt)
    obtain ⟨ws, hws⟩ := valsLk_argVars c G hσ n (i + 1) (by omega)
    exact ⟨v :: ws, by simp only [argVars, valListLk, valLk, allSome, hv, hws, Option.bind_some, Option.map_some]⟩

/-- **The `functional` sentence of a symbol of `ls` with a value under `G` at every argument list
of its sorts holds at values in `I`.** For a semantics meeting `coreOK`, an interpretation `I` of
`Γ c` in which the symbols of `ls` denote `G` at values, and a signature `k` of `ls` that is no
interpreted hooked symbol and that `ls` lists first under its number: the translation of any
axiom declaration whose pattern is `funPatR k`, over the one sort variable `R`, holds in `I` at
every valuation that sends the axiom's free element variables to values. -/
theorem functionalLk {c : Semantics} (h : c.coreOK = true) {ls : List CtorSig}
    {G : Sym → List GroundTerm → Option GroundTerm} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ c) (hL : LackedDen c ls G I) {k : CtorSig} (hnh : isHook k.name = false)
    (hk : sigLk ls k.name = some k)
    (htot : ∀ ws, c.sortsOf ws = some k.args → ∃ v, G k.name ws = some v)
    (hr : funReg k = true) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = funPatR k)
    (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    ∀ e, AtValues c I e ad.ax → ∀ m, (KoreAML.trAxiom [] [] ad).pat.interpret I e m := by
  intro e hat m
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
  have hsrts : srtsLk? c.sortOf ls (funVars k) (argVars 0 k.args.length) = some k.args := by
    rw [srtsLk_argVars c ls (funVars k) k.args.length 0 (by omega), List.drop_zero]
    exact congrArg some (funVarsFrom_sorts 0 k.args)
  have hsrt : srtLk? c.sortOf ls (funVars k) (funTerm k) = some k.result := by
    unfold funTerm
    rw [srtLk?, hk]
    simp only [Option.bind_some, hsrts, beq_self_eq_true, ite_true]
  obtain ⟨ws, hws⟩ := valsLk_argVars c G hσ k.args.length 0 (by omega)
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
  have hDV := fun x => den_valLk (tbl := t) (e := ex x) h hI hL hσ (hag x) (funTerm k) hsrt
  have hwss : c.sortsOf ws = some k.args :=
    ((den_valsLk (tbl := t) (e := ex default) h hI hL hσ (hag default) (argVars 0 k.args.length) hsrts).1 ws hws).1
  obtain ⟨v, hv⟩ := htot ws hwss
  have hval : valLk c G σ (funTerm k) = some v := by
    unfold funTerm
    rw [valLk, hws]
    simp only [Option.bind_some, hnh, Bool.false_eq_true, ite_false, hv]
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


/-! ## An equation between two terms -/

namespace Eqn

/-- `Eqn.typed` with the sorts of `srtLk?`, the domain values' under `so`. -/
def typedLk (so : GroundTerm → Option Srt) (ls : List CtorSig) (E : Eqn) : Bool :=
  decide (E.s < nRegSorts) && E.vars.all (fun p => decide (p.2 < nRegSorts)) &&
  srtLk? so ls E.vars E.lhs == some E.s && srtLk? so ls E.vars E.rhs == some E.s &&
  match E.req with
  | none => true
  | some q => srtLk? so ls E.vars q == some Srt.bool

/-- The two sides have the same value under `G`, or both none, at every substitution of values of
the variables' sorts at which the `requires` has the value `true`. -/
def HoldsLk (c : Semantics) (G : Sym → List GroundTerm → Option GroundTerm) (E : Eqn) : Prop :=
  ∀ σ : Subst, (∀ i p, E.vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) →
    (∀ q, E.req = some q → valLk c G σ q = some (bool true)) → valLk c G σ E.lhs = valLk c G σ E.rhs

end Eqn

/-- **A library equation that holds under `G` holds at values in `I`.** For a semantics meeting
`coreOK`, an interpretation `I` of `Γ c` in which the symbols of `ls` denote `G` at values
(`LackedDen`), and an equation `E` with `Eqn.HoldsLk`: the translation of any axiom declaration
whose pattern is `E`'s, over the one sort variable `R` and with each variable of `E` free in it,
holds in `I` at every valuation that sends the axiom's free element variables to values. -/
theorem Eqn.entailedLk {c : Semantics} (h : c.coreOK = true) {ls : List CtorSig}
    {G : Sym → List GroundTerm → Option GroundTerm} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ c) (hL : LackedDen c ls G I) (E : Eqn) (ht : E.typedLk c.sortOf ls = true)
    (hE : E.HoldsLk c G) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.pattern c)
    (hsv : ad.ax.sortVars = [KoreAML.Rv])
    (hfv : ∀ i, i < E.vars.length → vkey c E.vars i ∈ KoreAML.freeOf [] ad.ax.pattern) :
    ∀ e, AtValues c I e ad.ax → ∀ m, (KoreAML.trAxiom [] [] ad).pat.interpret I e m := by
  intro e hat m
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  simp only [Eqn.typedLk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨hsR, hvR⟩, htl⟩, htr⟩, htq⟩ := ht
  have hnum : ∀ {s : Srt}, s < nRegSorts → s < nRegSorts + c.sortNames.length :=
    fun hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  obtain ⟨σ, hσ, hag⟩ := fq_subst h hI E.vars hvR ad.ax hfv e hat
  unfold KoreAML.trAxiom
  dsimp only
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hag ⊢
  rw [interpret_impl]
  intro hgd
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_singleton.mpr rfl)), rfl⟩))
  have hDV := fun (u : Term) (s : Srt) (hu : srtLk? c.sortOf ls E.vars u = some s) =>
    den_valLk (tbl := t) (e := e) h hI hL hσ hag u hu
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
    have hreq : ∀ q, E.req = some q → valLk c G σ q = some (bool true) := by
      intro q hq
      unfold Eqn.premise at hprem
      rw [hq] at hprem htq
      dsimp only at hprem htq
      have htq' : srtLk? c.sortOf ls E.vars q = some Srt.bool := eq_of_beq htq
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
      cases hvq : valLk c G σ q with
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

/-- `Eqn.entailedLk` for an equation over the registry's names: the axiom's pattern is compared
with a pattern that does not depend on the semantics. -/
theorem Eqn.entailedLk_reg {c : Semantics} (h : c.coreOK = true) {ls : List CtorSig}
    {G : Sym → List GroundTerm → Option GroundTerm} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ c) (hL : LackedDen c ls G I) (E : Eqn) (hr : E.regular = true)
    (ht : E.typedLk c.sortOf ls = true) (hE : E.HoldsLk c G) (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = E.patR)
    (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    ∀ e, AtValues c I e ad.ax → ∀ m, (KoreAML.trAxiom [] [] ad).pat.interpret I e m := by
  refine Eqn.entailedLk h hI hL E ht hE ad (hp.trans (Eqn.pattern_reg c hr).symm) hsv (fun i hi => ?_)
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
