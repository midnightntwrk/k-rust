/-
  `HypModelCore` for a semantics whose clause binds a variable by `\exists`, from `coreOKEx`
  (`hypModelCore_of_coreEx`), kernel-checked on two texts. The definitions of `cCeG` are those of
  test/CoreOKEx.lean.

  - `cCeG`: `f() => g(?Z:Int)` with `post := Z ∈ lp()`, beside `lp() => lp()` and `g(X:Int) => X`.
    `lp()` has no result, so `f()` has none and the clause's `post` has no truth value at any
    instance. Every two competing clauses are coherent (the clause of `f` has no result at any
    match), so `FnDet`; at each function both sides of `FnSolves` are empty or `g`'s value. So
    `HypModelCore cCeG`, `ClausePreDecided cCeG` and `OpenLaws cCeG` hold, and `ClausePostDecided
    cCeG` does not: the value-model consistency theorem does not apply to it. `HypModel cCeG` does
    not hold either (`HypModel` asks every clause to bind no variable by `\exists`).
  - `cCeV`: the same with `lp() => 0`. The clause's `post` is `Z = 0` at each instance, `f()` is 0
    by `clauseEx`, and `HypModelCore`, `ClausePreDecided`, `ClausePostDecided` and `OpenLaws` hold, so
    the theory is consistent (`consistent_of_coreEx`).
-/
import KcoreSpec.HypModelCoreEx
import KcoreSpec.CoreDecide

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.HypModelCoreExTest
open KCore GroundTerm Faithful Faithful.Model

/-! ## The statements -/

example (c : Semantics) (h : c.coreOKEx = true) (hd : FnDet c) : HypModelCore c :=
  hypModelCore_of_coreEx h hd
example (c : Semantics) (h : c.sortedOKEx = true) : c.sortedOKClEx = true := Semantics.sortedOKClEx_of_sortedOKEx h
example (c : Semantics) (h : HypModel c) : c.FnsNoExs := h.fnsNoExs
example (c : Semantics) (h : c.coreOKEx = true) (hd : FnDet c) (hs : FnSolves c) (hp : ClausePreDecided c)
    (hq : ClausePostDecided c) (hl : OpenLaws c) : Consistent c :=
  consistent_of_coreEx h hd hs hp hq hl

/-! ## The texts -/

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]
def base : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }
def fC : Sym := nRegSyms + 4
def lpS : Sym := nRegSyms + 5
def gS : Sym := nRegSyms + 6
def clCf : Clause :=
  { vars := [Srt.int], pats := [], req := none, rhs := .app gS [.var 0], ens := none, exs := [0],
    post := .mem Srt.int (.var 0) (.app lpS []) }
def clLp : Clause := { vars := [], pats := [], req := none, rhs := .app lpS [], ens := none }
def fnCf : Fn := { label := fC, args := [], result := Srt.int, clauses := [clCf] }
def fnLp : Fn := { label := lpS, args := [], result := Srt.int, clauses := [clLp] }
def clG : Clause := { vars := [Srt.int], pats := [.var 0], req := none, rhs := .var 0, ens := none }
def fnG : Fn := { label := gS, args := [Srt.int], result := Srt.int, clauses := [clG] }
def cCeG : Semantics :=
  { base with symNames := base.symNames ++ ["Lblf", "Lbllp", "Lblg"], fns := [fnCf, fnLp, fnG] }
def clLp0 : Clause := { vars := [], pats := [], req := none, rhs := .dv Srt.int (.int 0), ens := none }
def fnLp0 : Fn := { label := lpS, args := [], result := Srt.int, clauses := [clLp0] }
def cCeV : Semantics :=
  { base with symNames := base.symNames ++ ["Lblf", "Lbllp", "Lblg"], fns := [fnCf, fnLp0, fnG] }

theorem cCeG_coreOKEx : cCeG.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap
theorem cCeV_coreOKEx : cCeV.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap

/-! ## Facts shared by the two texts -/

section Shared
variable {d : Semantics}

theorem lookup_cons_self (i : Nat) (v : GroundTerm) (σ : Subst) : ((i, v) :: σ : Subst).lookup i = some v := by
  simp [List.lookup]

theorem lookup_cons_ne {i j : Nat} (v : GroundTerm) (σ : Subst) (h : i ≠ j) :
    ((j, v) :: σ : Subst).lookup i = σ.lookup i := by
  have hb : (i == j) = false := by simp [h]
  simp [List.lookup, hb]

theorem sameResult_some {v w : GroundTerm} : sameResult (some v) (some w) = true ↔ v = w := by
  simp [sameResult, cmp_eq_iff]

theorem holds_cast {n : Nat} {σ : Subst} {p : Cond} {b b' : Bool}
    (h : Holds d n σ p b) (e : b = b') : Holds d n σ p b' := e ▸ h

theorem sortsOf_nil {vs : List GroundTerm} (h : d.sortsOf vs = some []) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    rw [Semantics.sortsOf] at h
    split at h <;> cases h

theorem match0 {σ : Subst} {vs : List GroundTerm} (h : PatVals d σ [.var 0] vs) :
    ∃ v, vs = [v] ∧ σ.lookup 0 = some v := by
  obtain ⟨v, vs', rfl, hv, hs⟩ := PatVals.cons_inv h
  rw [PatVals.nil_inv hs]
  exact ⟨v, rfl, PatVal.var_inv hv⟩

theorem clCf_free : Clause.exsFree clCf = [0] := by decide

/-- The extension of σ that gives `Z` the value `z`: σ off `Z`, and well sorted where z is an Int. -/
theorem ext_agree (z : GroundTerm) (σ : Subst) : AgreeOff clCf.exsFree σ ((0, z) :: σ) := by
  rw [clCf_free]
  intro i hi
  exact lookup_cons_ne _ _ (fun h => hi (by simp [h]))

theorem ext_sorted {z : GroundTerm} (hz : d.sortOf z = some Srt.int) (σ : Subst) :
    d.WellSorted [Srt.int] ((0, z) :: σ) := by
  intro i s h
  match i, h with
  | 0, h => cases h; exact ⟨_, lookup_cons_self _ _ _, hz⟩

/-- `g`'s clause is coherent with itself: two matches at one argument give X one value. -/
theorem clG_coherent : Coherent d clG clG := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨v, rfl, hl⟩ := match0 ha.2.1
  obtain ⟨w, hw, hl'⟩ := match0 ha'.2.1
  cases hw
  refine .inl ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht => nomatch ht⟩
  have : i = 0 := by simpa [clG, varOccs] using hi
  rw [this, hl, hl']

/-- A clause with no variable and a constant right-hand side is coherent with itself. -/
theorem const_coherent {cl : Clause} (hex : cl.exs = []) (hv : varOccs cl.rhs = []) (hen : cl.ens = none) :
    Coherent d cl cl := by
  intro _ _ _ _ _ _ _ _ _ _
  refine .inl ⟨hex, hex, rfl, rfl, fun i hi => ?_, fun t ht => ?_⟩
  · rw [hv] at hi; nomatch hi
  · rw [hen] at ht; nomatch ht

/-- A function of one clause has its clauses agree. -/
theorem agree_one {fn : Fn} {cl : Clause} (h : fn.clauses = [cl]) : ClausesAgree d fn := by
  intro a b hp _
  rw [h] at hp
  simp [pairs] at hp

/-- **`g` solves its equation** where it is found under its label and its results are one. -/
theorem g_solves (hl : d.lookupFn gS = some fnG) (hd : FnDet d) {vs : List GroundTerm} {σ : Subst}
    (hdec : clG.DecidesAt d fnG σ vs) (v : GroundTerm) :
    Eval d fnG.label vs (some v) ↔ ∃ σ', AgreeOff clG.exsFree σ σ' ∧ d.WellSorted clG.vars σ' ∧ clG.Gives d σ' v := by
  have hσ := (wellSortedAt_univ (cl := clG) rfl).mp hdec.1.1
  refine Iff.trans ?_ (Clause.gives_iff_noExs (cl := clG) rfl rfl hσ v).symm
  have hev : Eval d gS vs (σ.lookup 0) :=
    .clause (fn := fnG) (cl := clG) hl (List.mem_singleton_self _) hσ hdec.1.2.1 (fun t ht => nomatch ht)
      hdec.1.2.2.2
      (fun cl' hcl' _ hlt => by
        obtain rfl := List.mem_singleton.mp hcl'
        exact absurd hlt (Nat.lt_irrefl _))
      rfl .var (fun t ht => nomatch ht) .top
  constructor
  · intro h
    have he : some v = σ.lookup 0 := hd _ _ _ _ h hev
    refine ⟨?_, fun t ht => nomatch ht⟩
    rw [he]; exact .var
  · rintro ⟨hr, -⟩
    have he : some v = σ.lookup 0 := EvalTerm.var_inv hr
    rw [he]; exact hev

end Shared

/-! ## `cCeG`: `lp() => lp()` -/

namespace G

theorem lookup_lp : cCeG.lookupFn lpS = some fnLp := by rw [Semantics.lookupFn_eq]; rfl
theorem lookup_fC : cCeG.lookupFn fC = some fnCf := by rw [Semantics.lookupFn_eq]; rfl
theorem lookup_g : cCeG.lookupFn gS = some fnG := by rw [Semantics.lookupFn_eq]; rfl

theorem lp_flags : cCeG.isCtor lpS = false ∧ isHook lpS = false ∧ cCeG.isParam lpS = false ∧
    cCeG.isOvl lpS = false := by decide +kernel

/-- **`lp()` has no result**: each derivation of it holds a shorter one. -/
theorem lp_none {σ : Subst} {r : Option GroundTerm} : ¬ EvalTerm cCeG σ (.app lpS []) r := by
  obtain ⟨hk, hh, hp, ho⟩ := lp_flags
  intro hv
  exact EvalTerm.rec (c := cCeG)
    (motive_1 := fun f vs _ _ => f = lpS → vs = [] → False)
    (motive_2 := fun _ _ _ => True) (motive_3 := fun _ _ _ => True)
    (motive_4 := fun _ t _ _ => t = .app lpS [] → False)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ => True) (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun {_ _ _ _ _ _} hfn hmem _ _ _ _ _ _ _ _ _ _ _ _ ihrhs _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [lookup_lp] at hfn; cases hfn
      change _ ∈ [clLp] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact ihrhs rfl)
    (fun hfn hnone _ => fun hf hvs => by
      subst hf; subst hvs
      rw [lookup_lp] at hfn; cases hfn
      cases hnone clLp (by simp [fnLp]) with
      | intro h =>
        cases h [] (fun i hi => by simp [Clause.leftVars, Clause.condVars, clLp, varOccsList, varOccsCond] at hi) .nil with
        | intro ht _ _ => cases ht
        | pre hp => exact absurd (Holds.top_eq hp) (by simp))
    (fun {_ _ _ _ _ _ _} hfn hmem _ _ _ _ _ _ ht _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [lookup_lp] at hfn; cases hfn
      change _ ∈ [clLp] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      cases ht)
    (fun {_ _ _ _ _ _} hfn hmem _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [lookup_lp] at hfn; cases hfn
      change _ ∈ [clLp] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact hne rfl)
    (fun {_ _ _ _ _} hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [lookup_lp] at hfn; cases hfn
      change _ ∈ [clLp] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact hne rfl)
    (fun _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ => trivial)
    (fun h => by cases h) (fun h => by cases h) (fun _ _ h => by cases h)
    (fun hk' _ _ h => by cases h; rw [hk] at hk'; cases hk')
    (fun _ hhk _ _ _ _ h => by cases h; rw [hh] at hhk; cases hhk)
    (fun _ _ hp' _ _ _ h => by cases h; rw [hp] at hp'; cases hp')
    (fun _ _ hts hvs _ _ _ ihf h => by
      cases h
      cases hts
      simp only [allSome, Option.some.injEq] at hvs
      exact ihf rfl hvs.symm)
    (fun _ _ hts hvs _ _ h => by
      cases h
      cases hts
      simp [allSome] at hvs)
    (fun _ ho' _ _ _ h => by cases h; rw [ho] at ho'; cases ho')
    (fun _ ho' _ _ _ _ _ _ _ h => by cases h; rw [ho] at ho'; cases ho')
    trivial (fun _ _ _ _ => trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    hv rfl

theorem lp_eval_none {vs : List GroundTerm} {r : Option GroundTerm} (hvs : vs = []) : ¬ Eval cCeG lpS vs r := by
  subst hvs
  intro h
  exact lp_none (σ := []) (EvalTerm.call lp_flags.1 lp_flags.2.1 .nil rfl h lp_flags.2.2.1)

/-- At no σ has the clause's `post` a truth value. -/
theorem post_undecided (σ : Subst) (b : Bool) : ¬ Holds cCeG 1 σ clCf.post b := by
  intro h
  cases h with
  | mem _ h' => exact lp_none h'

theorem not_inst (σ : Subst) (r : Option GroundTerm) : ¬ InstIs cCeG σ clCf r := by
  intro h
  cases h with
  | fails hp _ => exact post_undecided _ _ hp
  | gives _ _ hp => exact post_undecided _ _ hp

/-- The clause of `f` has no result at any match. -/
theorem clCf_noRes (σ : Subst) (r : Option GroundTerm) : ¬ Clause.Res cCeG clCf σ r := by
  rintro (⟨hex, -⟩ | ⟨-, (⟨σ', v, -, -, hg, -, -⟩ | ⟨-, ⟨σ', ha, hw⟩, hall⟩)⟩)
  · exact absurd hex (by decide)
  · exact post_undecided _ _ hg.2.2
  · exact not_inst _ _ (hall σ' ha hw)

/-- **`f()` has no result at all.** -/
theorem fC_none {r : Option GroundTerm} : ¬ Eval cCeG fC [] r := by
  intro h
  cases h with
  | @clause _ fn _ cl σ _ hfn hmem hσ hmatch hreq hpre hprio hex =>
    rw [lookup_fC] at hfn; cases hfn; simp [fnCf] at hmem; subst hmem; cases hex
  | @rest _ fn _ hfn hnone =>
    rw [lookup_fC] at hfn; cases hfn
    cases hnone clCf (by simp [fnCf]) with
    | intro h =>
      cases h [] (fun i hi => by simp [Clause.leftVars, Clause.condVars, clCf, varOccsList, varOccsCond] at hi) .nil with
      | intro ht _ _ => cases ht
      | pre hp => exact absurd (Holds.top_eq hp) (by simp)
  | @ensFails _ fn _ cl σ t w hfn hmem hσ hmatch hreq hpre hprio hex =>
    rw [lookup_fC] at hfn; cases hfn; simp [fnCf] at hmem; subst hmem; cases hex
  | @clauseEx _ fn _ cl σ v hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost =>
    rw [lookup_fC] at hfn; cases hfn; simp [fnCf] at hmem; subst hmem
    exact post_undecided _ _ hpost
  | @exNone _ fn _ cl σ hfn hmem hne hσ hmatch hreq hpre hprio hsome hall =>
    rw [lookup_fC] at hfn; cases hfn; simp [fnCf] at hmem; subst hmem
    obtain ⟨σ', ha, hw⟩ := hsome
    exact not_inst _ _ (hall σ' ha hw)

theorem mem_fns {fn : Fn} (h : fn ∈ cCeG.fns) : fn = fnCf ∨ fn = fnLp ∨ fn = fnG := by
  simpa [cCeG] using h

/-- **Every function of `cCeG` has at most one result**: the clauses that compete are coherent. -/
theorem fnDet : FnDet cCeG :=
  fnDet_of_coherent (coherentAll_ofSelfCEx
    (fun fn hfn => by rcases mem_fns hfn with rfl | rfl | rfl <;> exact agree_one rfl)
    (fun fn hfn cl hcl => by
      rcases mem_fns hfn with rfl | rfl | rfl <;> simp only [fnCf, fnLp, fnG, List.mem_singleton] at hcl <;> subst hcl
      · exact fun _ σ _ _ _ _ _ _ _ _ => .inr fun r _ hr _ => absurd hr (clCf_noRes σ r)
      · exact const_coherent rfl rfl rfl
      · exact clG_coherent))

/-- **Evaluation solves the equations of `cCeG`**: at `f` and at `lp` both sides are empty, and `g`
solves its own. -/
theorem fnSolves : FnSolves cCeG := by
  intro fn hfn vs hvs cl hcl σ hdec v
  rcases mem_fns hfn with rfl | rfl | rfl <;> simp only [fnCf, fnLp, fnG, List.mem_singleton] at hcl <;> subst hcl
  · have h0 : vs = [] := sortsOf_nil hvs
    subst h0
    exact ⟨fun h => absurd h fC_none, fun ⟨_, _, _, hg⟩ => absurd hg.2.2 (post_undecided _ _)⟩
  · exact ⟨fun h => absurd h (lp_eval_none (sortsOf_nil hvs)), fun ⟨_, _, _, hg⟩ => absurd hg.1 lp_none⟩
  · exact g_solves lookup_g fnDet hdec v

/-- **`HypModelCore cCeG`.** -/
theorem hypModelCore : HypModelCore cCeG := hypModelCore_of_coreEx cCeG_coreOKEx fnDet

theorem preDecided : ClausePreDecided cCeG := clausePreDecided_of_isTop (by decide +kernel)

theorem openLaws : OpenLaws cCeG := openLaws_of_plain (by decide +kernel)

theorem σ0_sorted : cCeG.WellSorted [Srt.int] [(0, int 0)] := ext_sorted (sortOf_int 0) []

/-- **`ClausePostDecided cCeG` does not hold**: at `Z = 0` the clause's `post` `Z ∈ lp()` has no truth
value, `lp()` having no result. -/
theorem not_postDecided : ¬ ClausePostDecided cCeG := fun h => by
  obtain ⟨b, hb⟩ := h fnCf (by simp [cCeG]) clCf (by simp [fnCf]) [(0, int 0)] σ0_sorted
  exact post_undecided _ _ hb

/-- `HypModel cCeG` does not hold: its clause of `f` binds `Z` by `\exists`. -/
theorem not_hypModel : ¬ HypModel cCeG :=
  not_hypModel_of_exs (fn := fnCf) (by simp [cCeG]) (cl := clCf) (by simp [fnCf]) (by decide)

/-- The clause of `f` is not match independent: it decides under the empty match and has no result
there. -/
theorem not_matchIndependent : ¬ MatchIndependent cCeG clCf := fun h => by
  have hw : cCeG.WellSortedAt clCf.vars clCf.univ [] := fun i hi => by simp [Clause.univ, clCf] at hi
  have hp : Holds cCeG clCf.vars.length [] clCf.pre true := Holds.top
  have happ : clCf.AppliesAt cCeG [] [] := ⟨hw, PatVals.nil, (fun t ht => nomatch ht), hp⟩
  have hdec : clCf.Decides cCeG fnCf [] [] := ⟨happ, fun cl' hcl' _ hlt => by
    simp only [fnCf, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _)⟩
  obtain ⟨r, hr⟩ := h.2 (by decide) fC fnCf [] [] lookup_fC (by simp [fnCf]) hdec
  exact clCf_noRes _ _ hr

end G

/-! ## `cCeV`: `lp() => 0`

The clause's `post` `Z ∈ lp()` is `Z = 0` at each instance, so the one instance that gives a value
is `Z = 0`, which gives `g(0) = 0`; every other instance fails by its `post`. -/

namespace V

abbrev i0 : GroundTerm := .dv Srt.int (.int 0)

theorem i0_int : cCeV.sortOf i0 = some Srt.int := sortOf_int 0

theorem lookup_lp : cCeV.lookupFn lpS = some fnLp0 := by rw [Semantics.lookupFn_eq]; rfl
theorem lookup_fC : cCeV.lookupFn fC = some fnCf := by rw [Semantics.lookupFn_eq]; rfl
theorem lookup_g : cCeV.lookupFn gS = some fnG := by rw [Semantics.lookupFn_eq]; rfl

theorem flags : cCeV.isCtor lpS = false ∧ isHook lpS = false ∧ cCeV.isParam lpS = false ∧
    cCeV.isOvl lpS = false ∧ cCeV.isCtor gS = false ∧ isHook gS = false ∧ cCeV.isParam gS = false ∧
    cCeV.isOvl gS = false := by decide +kernel

/-- `lp()` is 0. -/
theorem evalLp : Eval cCeV lpS [] (some i0) :=
  .clause (fn := fnLp0) (cl := clLp0) (σ := []) lookup_lp (List.mem_singleton_self _)
    (fun i s h => by simp [clLp0] at h) .nil (fun t ht => nomatch ht) Holds.top
    (fun cl' hcl' _ hlt => by
      simp only [fnLp0, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl .dv (fun t ht => nomatch ht) Holds.top

/-- `lp()` has no other result. -/
theorem evalLp_inv {r : Option GroundTerm} (h : Eval cCeV lpS [] r) : r = some i0 := by
  cases h with
  | clause hfn hmem _ _ _ _ _ _ hrhs _ _ =>
    rw [lookup_lp] at hfn; cases hfn
    simp only [fnLp0, List.mem_singleton] at hmem; subst hmem
    exact EvalTerm.dv_inv hrhs
  | rest hfn hnone =>
    rw [lookup_lp] at hfn; cases hfn
    cases hnone clLp0 (by simp [fnLp0]) with
    | intro h =>
      cases h [] (fun i hi => by simp [Clause.leftVars, Clause.condVars, clLp0, varOccsList, varOccsCond] at hi) .nil with
      | intro ht _ _ => cases ht
      | pre hp => exact absurd (Holds.top_eq hp) (by simp)
  | ensFails hfn hmem _ _ _ _ _ _ ht _ _ =>
    rw [lookup_lp] at hfn; cases hfn
    simp only [fnLp0, List.mem_singleton] at hmem; subst hmem
    cases ht
  | clauseEx hfn hmem _ _ _ _ _ hne _ _ _ _ =>
    rw [lookup_lp] at hfn; cases hfn
    simp only [fnLp0, List.mem_singleton] at hmem; subst hmem
    exact absurd rfl hne
  | exNone hfn hmem hne _ _ _ _ _ _ _ =>
    rw [lookup_lp] at hfn; cases hfn
    simp only [fnLp0, List.mem_singleton] at hmem; subst hmem
    exact absurd rfl hne

theorem termLp (σ : Subst) : EvalTerm cCeV σ (.app lpS []) (some i0) :=
  .call flags.1 flags.2.1 .nil rfl evalLp flags.2.2.1

theorem termLp_inv {σ : Subst} {r : Option GroundTerm} (h : EvalTerm cCeV σ (.app lpS []) r) : r = some i0 := by
  cases h with
  | ctor hc _ => exact absurd hc (by decide +kernel)
  | hook _ hhk _ _ _ => exact absurd hhk (by decide +kernel)
  | param _ _ hp _ _ => exact absurd hp (by decide +kernel)
  | call _ _ hts hvs hf _ =>
    cases hts
    simp only [allSome, Option.some.injEq] at hvs
    subst hvs
    exact evalLp_inv hf
  | callUndef _ _ hts hvs _ =>
    cases hts
    simp [allSome] at hvs
  | ovl _ ho _ _ => exact absurd ho (by decide +kernel)
  | ovlFn _ ho _ _ _ _ _ => exact absurd ho (by decide +kernel)

/-- `g(w)` is w at an Int w. -/
theorem evalG {w : GroundTerm} (hw : cCeV.sortOf w = some Srt.int) : Eval cCeV gS [w] (some w) := by
  have hr : EvalTerm cCeV [(0, w)] (.var 0) (some w) := by
    have := EvalTerm.var (c := cCeV) (σ := [(0, w)]) (i := 0); rwa [lookup_cons_self] at this
  exact .clause (fn := fnG) (cl := clG) (σ := [(0, w)]) lookup_g (List.mem_singleton_self _)
    (ext_sorted hw []) (.cons (.var (lookup_cons_self _ _ _)) .nil) (fun t ht => nomatch ht) Holds.top
    (fun cl' hcl' _ hlt => by
      simp only [fnG, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl hr (fun t ht => nomatch ht) Holds.top

/-- `g(w)` has no other result at an Int w. -/
theorem evalG_inv {w : GroundTerm} (hw : cCeV.sortOf w = some Srt.int) {r : Option GroundTerm}
    (h : Eval cCeV gS [w] r) : r = some w := by
  cases h with
  | clause hfn hmem _ hm _ _ _ _ hrhs _ _ =>
    rw [lookup_g] at hfn; cases hfn
    simp only [fnG, List.mem_singleton] at hmem; subst hmem
    obtain ⟨v, hv, hl⟩ := match0 hm
    cases hv
    rw [EvalTerm.var_inv hrhs, hl]
  | rest hfn hnone =>
    rw [lookup_g] at hfn; cases hfn
    cases hnone clG (by simp [fnG]) with
    | intro h =>
      cases h [(0, w)] (fun i _ s hs => ext_sorted hw [] i s hs) (.cons (.var (lookup_cons_self _ _ _)) .nil) with
      | intro ht _ _ => cases ht
      | pre hp => exact absurd (Holds.top_eq hp) (by simp)
  | ensFails hfn hmem _ _ _ _ _ _ ht _ _ =>
    rw [lookup_g] at hfn; cases hfn
    simp only [fnG, List.mem_singleton] at hmem; subst hmem
    cases ht
  | clauseEx hfn hmem _ _ _ _ _ hne _ _ _ _ =>
    rw [lookup_g] at hfn; cases hfn
    simp only [fnG, List.mem_singleton] at hmem; subst hmem
    exact absurd rfl hne
  | exNone hfn hmem hne _ _ _ _ _ _ _ =>
    rw [lookup_g] at hfn; cases hfn
    simp only [fnG, List.mem_singleton] at hmem; subst hmem
    exact absurd rfl hne

theorem termG {σ : Subst} {w : GroundTerm} (hl : σ.lookup 0 = some w) (hw : cCeV.sortOf w = some Srt.int) :
    EvalTerm cCeV σ (.app gS [.var 0]) (some w) := by
  have ht : EvalTerms cCeV σ [.var 0] [some w] := .cons (hl ▸ EvalTerm.var) .nil
  exact .call flags.2.2.2.2.1 flags.2.2.2.2.2.1 ht rfl (evalG hw) flags.2.2.2.2.2.2.1

theorem termG_inv {σ : Subst} {w : GroundTerm} (hl : σ.lookup 0 = some w) (hw : cCeV.sortOf w = some Srt.int)
    {r : Option GroundTerm} (h : EvalTerm cCeV σ (.app gS [.var 0]) r) : r = some w := by
  cases h with
  | ctor hc _ => exact absurd hc (by decide +kernel)
  | hook _ hhk _ _ _ => exact absurd hhk (by decide +kernel)
  | param _ _ hp _ _ => exact absurd hp (by decide +kernel)
  | call _ _ hts hvs hf _ =>
    cases hts with
    | cons h1 h2 =>
      cases h2; cases h1
      rw [hl] at hvs
      simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
      subst hvs
      exact evalG_inv hw hf
  | callUndef _ _ hts hvs _ =>
    cases hts with
    | cons h1 h2 =>
      cases h2; cases h1
      rw [hl] at hvs
      simp [allSome] at hvs
  | ovl _ ho _ _ => exact absurd ho (by decide +kernel)
  | ovlFn _ ho _ _ _ _ _ => exact absurd ho (by decide +kernel)

/-- The clause's `post` at σ: whether σ gives `Z` the value 0. -/
theorem post_holds (σ : Subst) :
    Holds cCeV 1 σ clCf.post ((σ.lookup 0).isSome && sameResult (σ.lookup 0) (some i0)) :=
  Holds.mem EvalTerm.var (termLp σ)

theorem post_inv {σ : Subst} {b : Bool} (h : Holds cCeV 1 σ clCf.post b) :
    b = ((σ.lookup 0).isSome && sameResult (σ.lookup 0) (some i0)) := by
  cases h with
  | mem h1 h2 =>
    have e1 := EvalTerm.var_inv h1
    have e2 := termLp_inv h2
    subst e1; subst e2; rfl

theorem post_true {σ : Subst} (h : Holds cCeV 1 σ clCf.post true) : σ.lookup 0 = some i0 := by
  have e := post_inv h
  cases hl : σ.lookup 0 with
  | none => rw [hl] at e; simp at e
  | some z =>
    rw [hl] at e
    simp only [Option.isSome_some, Bool.true_and] at e
    rw [sameResult_some.mp e.symm]

theorem sr_i0 : sameResult (some i0) (some i0) = true := sameResult_some.mpr rfl

theorem post_at0 (σ : Subst) : Holds cCeV 1 ((0, i0) :: σ) clCf.post true :=
  holds_cast (post_holds _) (by rw [lookup_cons_self, sr_i0]; rfl)

/-- **The clause of `f` has the one result 0 at each match.** -/
theorem res_eq (σ : Subst) (r : Option GroundTerm) (h : Clause.Res cCeV clCf σ r) : r = some i0 := by
  rcases h with ⟨hex, -⟩ | ⟨-, (⟨σ', v, -, -, ⟨hrhs, -, hpost⟩, -, rfl⟩ | ⟨rfl, -, hall⟩)⟩
  · exact absurd hex (by decide)
  · exact termG_inv (post_true hpost) i0_int hrhs
  · exfalso
    have hl : ((0, i0) :: σ : Subst).lookup 0 = some i0 := lookup_cons_self _ _ _
    have hi := hall ((0, i0) :: σ) (ext_agree _ _) (ext_sorted i0_int _)
    cases hi with
    | fails _ hf =>
      cases hf with
      | ens ht _ _ => cases ht
      | post hp =>
        have e := post_inv hp
        rw [hl, sr_i0] at e
        simp at e
      | rhs h => cases termG_inv hl i0_int h

/-- **`f()` is 0**, by `clauseEx`: the instance at `Z = 0` gives 0, and every other instance fails
by its `post`. -/
theorem evalF : Eval cCeV fC [] (some i0) := by
  refine .clauseEx (fn := fnCf) (cl := clCf) (σ := [(0, i0)]) lookup_fC (List.mem_singleton_self _)
    (ext_sorted i0_int []) .nil (fun t ht => nomatch ht) Holds.top
    (fun cl' hcl' _ hlt => by
      simp only [fnCf, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    (by decide) (termG (lookup_cons_self _ _ _) i0_int) (fun t ht => nomatch ht) (post_at0 []) ?_
  intro σ' _ hw
  obtain ⟨z, hz, hzs⟩ := hw 0 Srt.int rfl
  cases hb : sameResult (some z) (some i0) with
  | true =>
    have hzi : z = i0 := sameResult_some.mp hb
    subst hzi
    exact .gives (termG hz i0_int) (fun t ht => nomatch ht) (holds_cast (post_holds σ') (by rw [hz, hb]; rfl))
  | false =>
    exact .fails (post_holds σ') (.post (holds_cast (post_holds σ') (by rw [hz, hb]; rfl)))

theorem mem_fns {fn : Fn} (h : fn ∈ cCeV.fns) : fn = fnCf ∨ fn = fnLp0 ∨ fn = fnG := by
  simpa [cCeV] using h

/-- **Every function of `cCeV` has at most one result.** -/
theorem fnDet : FnDet cCeV :=
  fnDet_of_coherent (coherentAll_ofSelfCEx
    (fun fn hfn => by rcases mem_fns hfn with rfl | rfl | rfl <;> exact agree_one rfl)
    (fun fn hfn cl hcl => by
      rcases mem_fns hfn with rfl | rfl | rfl <;> simp only [fnCf, fnLp0, fnG, List.mem_singleton] at hcl <;> subst hcl
      · exact fun _ σ σ' _ _ _ _ _ _ _ => .inr fun r r' hr hr' => (res_eq σ r hr).trans (res_eq σ' r' hr').symm
      · exact const_coherent rfl rfl rfl
      · exact clG_coherent))

/-- **Evaluation solves the equations of `cCeV`.** -/
theorem fnSolves : FnSolves cCeV := by
  intro fn hfn vs hvs cl hcl σ hdec v
  rcases mem_fns hfn with rfl | rfl | rfl <;> simp only [fnCf, fnLp0, fnG, List.mem_singleton] at hcl <;> subst hcl
  · have h0 : vs = [] := sortsOf_nil hvs
    subst h0
    constructor
    · intro h
      obtain rfl := Option.some.inj (fnDet _ _ _ _ h evalF)
      exact ⟨(0, i0) :: σ, ext_agree _ _, ext_sorted i0_int _, termG (lookup_cons_self _ _ _) i0_int,
        (fun t ht => nomatch ht), post_at0 σ⟩
    · rintro ⟨σ', -, -, hrhs, -, hpost⟩
      obtain rfl := Option.some.inj (termG_inv (post_true hpost) i0_int hrhs)
      exact evalF
  · have h0 : vs = [] := sortsOf_nil hvs
    subst h0
    have hσ := (wellSortedAt_univ (cl := clLp0) rfl).mp hdec.1.1
    refine Iff.trans ?_ (Clause.gives_iff_noExs (cl := clLp0) rfl rfl hσ v).symm
    constructor
    · intro h
      obtain rfl := Option.some.inj (evalLp_inv h)
      exact ⟨.dv, fun t ht => nomatch ht⟩
    · rintro ⟨hr, -⟩
      obtain rfl := Option.some.inj (EvalTerm.dv_inv hr)
      exact evalLp
  · exact g_solves lookup_g fnDet hdec v

/-- **`HypModelCore cCeV`.** -/
theorem hypModelCore : HypModelCore cCeV := hypModelCore_of_coreEx cCeV_coreOKEx fnDet

theorem preDecided : ClausePreDecided cCeV := clausePreDecided_of_isTop (by decide +kernel)

/-- **`ClausePostDecided cCeV`**: the clause's `post` is `Z = 0` at each σ (`post_holds`); the other
clauses' are `\top`. -/
theorem postDecided : ClausePostDecided cCeV := by
  intro fn hfn cl hcl σ _
  rcases mem_fns hfn with rfl | rfl | rfl <;> simp only [fnCf, fnLp0, fnG, List.mem_singleton] at hcl <;> subst hcl
  · exact ⟨_, post_holds σ⟩
  · exact ⟨true, Holds.top⟩
  · exact ⟨true, Holds.top⟩

theorem openLaws : OpenLaws cCeV := openLaws_of_plain (by decide +kernel)

/-- **The theory of `cCeV` is consistent**, its clause of `f` binding `Z` by `\exists`. -/
theorem consistent : Consistent cCeV :=
  consistent_of_coreEx cCeV_coreOKEx fnDet fnSolves preDecided postDecided openLaws

end V

/-- info: 'KCore.Faithful.Model.hypModelCore_of_coreEx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hypModelCore_of_coreEx
/-- info: 'KCore.Faithful.Model.consistent_of_coreEx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consistent_of_coreEx
/-- info: 'KCore.HypModelCoreExTest.G.hypModelCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms G.hypModelCore
/-- info: 'KCore.HypModelCoreExTest.G.not_postDecided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms G.not_postDecided
/-- info: 'KCore.HypModelCoreExTest.G.not_hypModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms G.not_hypModel
/-- info: 'KCore.HypModelCoreExTest.G.not_matchIndependent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms G.not_matchIndependent
/-- info: 'KCore.HypModelCoreExTest.V.hypModelCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms V.hypModelCore
/-- info: 'KCore.HypModelCoreExTest.V.postDecided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms V.postDecided
/-- info: 'KCore.HypModelCoreExTest.V.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms V.consistent

end KCore.HypModelCoreExTest
