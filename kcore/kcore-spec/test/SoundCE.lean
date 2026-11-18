/-
  `sound_at_ce`, `complete_at_ce` and `famEx_closed_ce` at the semantics of `f() => g(?Z:Int)` with
  `post := Z ∈ lp()`, beside `lp() => lp()` and `g(X:Int) => X` (test/CoreOKEx.lean's `cCeG`), kernel-checked.
  `coreOKEx` accepts it and `coreOK` does not.

  - `cCeG` has no rule: with the step's closure no configuration has a successor in any model
    (`complete_at_ce`, `cCeG_stuck`).
  - `cCeR` adds two rules of the same priority: `r0` rewrites the counter to `f()`, `r1` rewrites a
    configuration to itself. `f()` has no result (`fC_none`: `lp()` has none, so `post` has no
    truth value at any instance), so `r0` makes no step (`r0_noStep`) and the evaluations a step at
    a configuration reads have no result there (`cCeR_not_decided`); `r1` steps, and at its step
    `sound_at_ce` and `famEx_closed_ce` hold (`sound_r1`, `famEx_r1`).
-/
import KcoreSpec.SoundCE
import KcoreSpec.CoreDecide

set_option autoImplicit false

namespace KCore.SoundCETest
open KCore GroundTerm
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def kcS : Sym := nRegSyms + 2
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨kcS, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
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

/-- `<k> K </k> <counter> N </counter> => <k> K </k> <counter> f() </counter>` -/
def r0 : Rule :=
  { vars := [Srt.k, Srt.int], lhs := .app topLabel [.app kcS [.var 0], .app counterLabel [.var 1]],
    req := none, rhs := .app topLabel [.app kcS [.var 0], .app counterLabel [.app fC []]], ens := none, prio := 50 }
/-- `<k> K </k> C => <k> K </k> C` -/
def r1 : Rule :=
  { vars := [Srt.k, Srt.counter], lhs := .app topLabel [.app kcS [.var 0], .var 1], req := none,
    rhs := .app topLabel [.app kcS [.var 0], .var 1], ens := none, prio := 50 }
def cCeR : Semantics := { cCeG with rules := [r0, r1] }

theorem clCf_exs : clCf.exs ≠ [] := by decide

/-! ## What `coreOKEx` and `coreOK` say -/

theorem cCeG_coreOKEx : cCeG.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap

theorem cCeG_not_coreOK : cCeG.coreOK = false := by
  have : cCeG.clausesPlain = false := by decide +kernel
  simp only [Semantics.coreOK, Semantics.sortedOK, this, Bool.and_false, Bool.false_and]

theorem cCeR_coreOKEx : cCeR.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap

theorem cCeR_not_coreOK : cCeR.coreOK = false := by
  have : cCeR.clausesPlain = false := by decide +kernel
  simp only [Semantics.coreOK, Semantics.sortedOK, this, Bool.and_false, Bool.false_and]

/-- No clause of either semantics needs a witness, so `sound_at`'s clause hypothesis holds. -/
theorem noWit (c : Semantics) (hf : c.fns = [fnCf, fnLp, fnG]) :
    ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c := by
  rw [hf]
  intro fn hfn cl hcl hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl <;> simp only [fnCf, fnLp, fnG, List.mem_singleton] at hcl <;> subst hcl <;>
    simp [Clause.needsWitness, Clause.reqOpen, Clause.openCondVars, Clause.opens, Clause.condVars, clCf, clLp,
      clG, varOccsList, varOccs, varOccsCond] at hw

/-! ## `f()` has no result (ExClauses.lean's facts, at any semantics with these functions) -/

section
variable {c : Semantics} (hf : c.fns = [fnCf, fnLp, fnG])
  (hflags : c.isCtor lpS = false ∧ isHook lpS = false ∧ c.isParam lpS = false ∧ c.isOvl lpS = false ∧
    c.isCtor fC = false ∧ isHook fC = false ∧ c.isParam fC = false ∧ c.isOvl fC = false)
include hf hflags

omit hflags in
theorem lookup_lp : c.lookupFn lpS = some fnLp := by
  rw [Semantics.lookupFn_eq]; unfold Semantics.allFns; rw [hf]; rfl
omit hflags in
theorem lookup_fC : c.lookupFn fC = some fnCf := by
  rw [Semantics.lookupFn_eq]; unfold Semantics.allFns; rw [hf]; rfl

/-- **`lp()` has no result.** -/
theorem lp_none {σ : Subst} {r : Option GroundTerm} : ¬ EvalTerm c σ (.app lpS []) r := by
  obtain ⟨hk, hh, hp, ho, -⟩ := id hflags
  have hlp := lookup_lp hf
  intro hv
  exact EvalTerm.rec (c := c)
    (motive_1 := fun f vs _ _ => f = lpS → vs = [] → False)
    (motive_2 := fun _ _ _ => True) (motive_3 := fun _ _ _ => True)
    (motive_4 := fun _ t _ _ => t = .app lpS [] → False)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ => True) (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun {_ _ _ _ _ _} hfn hmem _ _ _ _ _ _ _ _ _ _ _ _ ihrhs _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [hlp] at hfn; cases hfn
      change _ ∈ [clLp] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact ihrhs rfl)
    (fun hfn hnone _ => fun hf hvs => by
      subst hf; subst hvs
      rw [hlp] at hfn; cases hfn
      cases hnone clLp (by simp [fnLp]) with
      | intro h =>
        cases h [] (fun i hi => by simp [Clause.leftVars, Clause.condVars, clLp, varOccsList, varOccsCond] at hi) .nil with
        | intro ht _ _ => cases ht
        | pre hp => exact absurd (Holds.top_eq hp) (by simp))
    (fun {_ _ _ _ _ _ _} hfn hmem _ _ _ _ _ _ ht _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [hlp] at hfn; cases hfn
      change _ ∈ [clLp] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      cases ht)
    (fun {_ _ _ _ _ _} hfn hmem _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [hlp] at hfn; cases hfn
      change _ ∈ [clLp] at hmem
      obtain rfl := List.mem_singleton.mp hmem
      exact hne rfl)
    (fun {_ _ _ _ _} hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => fun hf hvs => by
      subst hf; subst hvs
      rw [hlp] at hfn; cases hfn
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

/-- At no σ has `clCf`'s `post` a truth value. -/
theorem clCf_post_undecided (σ : Subst) (b : Bool) : ¬ Holds c 1 σ clCf.post b := by
  intro h
  cases h with
  | mem _ h' => exact lp_none hf hflags h'

theorem clCf_not_inst (σ : Subst) (r : Option GroundTerm) : ¬ InstIs c σ clCf r := by
  intro h
  cases h with
  | fails hp _ => exact clCf_post_undecided hf hflags _ _ hp
  | gives _ _ hp => exact clCf_post_undecided hf hflags _ _ hp

/-- **`f()` has no result at all.** -/
theorem fC_none {r : Option GroundTerm} : ¬ Eval c fC [] r := by
  have hfc := lookup_fC hf
  intro h
  cases h with
  | @clause _ fn _ cl σ _ hfn hmem hσ hmatch hreq hpre hprio hex =>
    rw [hfc] at hfn; cases hfn; simp [fnCf] at hmem; subst hmem; cases hex
  | @rest _ fn _ hfn hnone =>
    rw [hfc] at hfn; cases hfn
    cases hnone clCf (by simp [fnCf]) with
    | intro h =>
      cases h [] (fun i hi => by simp [Clause.leftVars, Clause.condVars, clCf, varOccsList, varOccsCond] at hi) .nil with
      | intro ht _ _ => cases ht
      | pre hp => exact absurd (Holds.top_eq hp) (by simp)
  | @ensFails _ fn _ cl σ t w hfn hmem hσ hmatch hreq hpre hprio hex =>
    rw [hfc] at hfn; cases hfn; simp [fnCf] at hmem; subst hmem; cases hex
  | @clauseEx _ fn _ cl σ v hfn hmem hσ hmatch hreq hpre hprio hne hrhs hens hpost =>
    rw [hfc] at hfn; cases hfn; simp [fnCf] at hmem; subst hmem
    exact clCf_post_undecided hf hflags _ _ hpost
  | @exNone _ fn _ cl σ hfn hmem hne hσ hmatch hreq hpre hprio hsome hall =>
    rw [hfc] at hfn; cases hfn; simp [fnCf] at hmem; subst hmem
    obtain ⟨σ', ha, hw⟩ := hsome
    exact clCf_not_inst hf hflags _ _ (hall σ' ha hw)

/-- The term `f()` has no evaluation. -/
theorem fC_term_none {σ : Subst} {r : Option GroundTerm} : ¬ EvalTerm c σ (.app fC []) r := by
  obtain ⟨-, -, -, -, hk, hh, hp, ho⟩ := id hflags
  intro h
  cases h with
  | ctor h' _ => rw [hk] at h'; cases h'
  | hook _ h' _ _ _ => rw [hh] at h'; cases h'
  | param _ _ h' _ _ => rw [hp] at h'; cases h'
  | call _ _ hts hvs hev _ =>
    cases hts
    simp only [allSome, Option.some.injEq] at hvs
    subst hvs
    exact fC_none hf hflags hev
  | callUndef _ _ hts hvs _ => cases hts; simp [allSome] at hvs
  | ovl _ h' _ _ => rw [ho] at h'; cases h'
  | ovlFn _ h' _ _ _ _ _ => rw [ho] at h'; cases h'

end

theorem flagsG : cCeG.isCtor lpS = false ∧ isHook lpS = false ∧ cCeG.isParam lpS = false ∧ cCeG.isOvl lpS = false ∧
    cCeG.isCtor fC = false ∧ isHook fC = false ∧ cCeG.isParam fC = false ∧ cCeG.isOvl fC = false := by
  decide +kernel
theorem flagsR : cCeR.isCtor lpS = false ∧ isHook lpS = false ∧ cCeR.isParam lpS = false ∧ cCeR.isOvl lpS = false ∧
    cCeR.isCtor fC = false ∧ isHook fC = false ∧ cCeR.isParam fC = false ∧ cCeR.isOvl fC = false := by
  decide +kernel

/-- **In `cCeG`, `f()` has no result.** -/
theorem cCeG_fC_none {r : Option GroundTerm} : ¬ Eval cCeG fC [] r := fC_none rfl flagsG

/-- A constructor application's evaluation evaluates its arguments. -/
theorem ctor_args {c : Semantics} {σ : Subst} {f : Sym} {ts : List Term} {r : Option GroundTerm}
    (hc : c.isCtor f = true) (h : EvalTerm c σ (.app f ts) r) : ∃ rs, EvalTerms c σ ts rs := by
  cases h with
  | ctor _ hts => exact ⟨_, hts⟩
  | hook h' _ _ _ _ => rw [hc] at h'; cases h'
  | param h' _ _ _ _ => rw [hc] at h'; cases h'
  | call h' _ _ _ _ _ => rw [hc] at h'; cases h'
  | callUndef h' _ _ _ _ => rw [hc] at h'; cases h'
  | ovl h' _ _ _ => rw [hc] at h'; cases h'
  | ovlFn h' _ _ _ _ _ _ => rw [hc] at h'; cases h'

theorem ctorsR : cCeR.isCtor topLabel = true ∧ cCeR.isCtor counterLabel = true ∧ cCeR.isCtor kcS = true := by
  decide +kernel

/-- **`r0`'s right side has no evaluation**: its counter is `f()`. -/
theorem r0_rhs_none {σ : Subst} {r : Option GroundTerm} : ¬ EvalTerm cCeR σ r0.rhs r := by
  intro h
  obtain ⟨rs, hrs⟩ := ctor_args ctorsR.1 h
  obtain ⟨_, _, -, hrs2⟩ : ∃ r1 rs1, EvalTerm cCeR σ (.app kcS [.var 0]) r1 ∧
      EvalTerms cCeR σ [.app counterLabel [.app fC []]] rs1 := by
    cases hrs with | cons h1 hs => exact ⟨_, _, h1, hs⟩
  cases hrs2 with
  | cons h2 _ =>
    obtain ⟨rs2, hrs3⟩ := ctor_args ctorsR.2.1 h2
    cases hrs3 with
    | cons h3 _ => exact fC_term_none rfl flagsR h3

/-- **`r0` makes no step**: a step to `<counter> f() </counter>` would need a result of `f()`. -/
theorem r0_noStep {σ : Subst} {x y : Config cCeR} : ¬ StepBy cCeR r0 σ x y :=
  fun hs => r0_rhs_none hs.heval

/-! ## The configuration `<k> . </k> <counter> 0 </counter>` -/

def xv : GroundTerm := .ctor topLabel [.ctor kcS [.ctor dotk []], .ctor counterLabel [.dv Srt.int (.int 0)]]
def xG : Config cCeG := ⟨xv, by decide +kernel⟩
def xR : Config cCeR := ⟨xv, by decide +kernel⟩

/-- **In `cCeG` no configuration has a successor**, in any model of the theory with the step's
closure: `complete_at_ce` with no outcome. -/
theorem cCeG_stuck (x : Config cCeG) :
    (Faithful.Γc cCeG ∪ Faithful.Γstep cCeG) ⊧
      (den cCeG x.val ⇒ KoreAML.allNext (KoreAML.disjList (([] : List Outcome).map (Outcome.pat cCeG)))) :=
  complete_at_ce cCeG cCeG_coreOKEx x (fun r hr => by cases hr) []
    (fun _ _ _ _ hs => absurd hs.mem (by simp [cCeG, base])) (fun r hr => by cases hr) (noWit cCeG rfl)

/-- `r0` matches at `xR` (K := `.`, N := 0), and its right side has no evaluation there: the
evaluations a step at `xR` reads do not all have results. -/
theorem cCeR_not_decided : ¬ StepDecided cCeR xR.val := by
  intro hd
  have hm : PatVal cCeR [(0, .ctor dotk []), (1, .dv Srt.int (.int 0))] r0.lhs xR.val :=
    .ctor ctorsR.1 (.cons (.ctor ctorsR.2.2 (.cons (.var rfl) .nil)) (.cons (.ctor ctorsR.2.1 (.cons (.var rfl) .nil)) .nil))
  have hσ : cCeR.WellSorted r0.vars [(0, .ctor dotk []), (1, .dv Srt.int (.int 0))] := fun i s hs => by
    match i, hs with
    | 0, hs => cases (show some Srt.k = some s from hs); exact ⟨_, rfl, by decide +kernel⟩
    | 1, hs => cases (show some Srt.int = some s from hs); exact ⟨_, rfl, by decide +kernel⟩
    | _ + 2, hs => cases (show (none : Option Srt) = some s from hs)
  obtain ⟨⟨v, hv⟩, -⟩ := (hd r0 (by simp [cCeR]) (fun r' hr' hlt => by
      simp only [cCeR, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl <;> exact absurd hlt (by decide))).2 _ hσ hm (fun t ht => by cases ht) .top
  exact r0_rhs_none hv

/-- K := `.`, C := `<counter> 0 </counter>`. -/
def σ1 : Subst := [(0, .ctor dotk []), (1, .ctor counterLabel [.dv Srt.int (.int 0)])]

/-- **`r1` steps `xR` to itself.** -/
theorem stepR1 : StepBy cCeR r1 σ1 xR xR where
  mem := by simp [cCeR]
  hσ := fun i s hs => by
    match i, hs with
    | 0, hs => cases (show some Srt.k = some s from hs); exact ⟨_, rfl, by decide +kernel⟩
    | 1, hs => cases (show some Srt.counter = some s from hs); exact ⟨_, rfl, by decide +kernel⟩
    | _ + 2, hs => cases (show (none : Option Srt) = some s from hs)
  hmatch := .ctor ctorsR.1 (.cons (.ctor ctorsR.2.2 (.cons (.var rfl) .nil)) (.cons (.var rfl) .nil))
  hreq := fun t ht => by cases ht
  hpre := .top
  heval := .ctor ctorsR.1 (.cons (.ctor ctorsR.2.2 (.cons .var .nil)) (.cons .var .nil))
  hens := fun t ht => by cases ht
  hpost := .top
  hprio := fun r' hr' hlt => by
    simp only [cCeR, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl <;> exact absurd hlt (by decide)

/-- **`sound_at_ce` at `r1`'s step**: no rule has a smaller priority, and no clause needs a
witness. -/
theorem sound_r1 :
    (Faithful.Γc cCeR ⊧ (den cCeR xR.val ⇒ KoreAML.sNext (Faithful.famEx cCeR r1 σ1))) ∧
      (Faithful.Γc cCeR ⊧ (den cCeR xR.val ⇒ Faithful.famEx cCeR r1 σ1)) :=
  sound_at_ce cCeR cCeR_coreOKEx xR xR r1 σ1 stepR1
    (fun r' hr' hlt => by
      simp only [cCeR, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl <;> exact absurd hlt (by decide))
    (noWit cCeR rfl)

/-- **`famEx_closed_ce` at `r1`'s step.** -/
theorem famEx_r1 : Faithful.Γc cCeR ⊧ (Faithful.famEx cCeR r1 σ1 ≡ den cCeR xR.val) :=
  famEx_closed_ce cCeR cCeR_coreOKEx stepR1 rfl (noWit cCeR rfl)

/-- **`sound_at_ce` at every step of `cCeR`** (only `r1`'s exist, `r0_noStep`). -/
theorem sound_cCeR (x y : Config cCeR) (r : Rule) (σ : Subst) (hs : StepBy cCeR r σ x y) :
    (Faithful.Γc cCeR ⊧ (den cCeR x.val ⇒ KoreAML.sNext (Faithful.famEx cCeR r σ))) ∧
      (Faithful.Γc cCeR ⊧ (den cCeR y.val ⇒ Faithful.famEx cCeR r σ)) :=
  sound_at_ce cCeR cCeR_coreOKEx x y r σ hs
    (fun r' hr' hlt => by
      have hr := hs.mem
      simp only [cCeR, List.mem_cons, List.not_mem_nil, or_false] at hr' hr
      rcases hr' with rfl | rfl <;> rcases hr with rfl | rfl <;> exact absurd hlt (by decide))
    (noWit cCeR rfl)

end KCore.SoundCETest

#print axioms KCore.sound_at_ce
#print axioms KCore.complete_at_ce
#print axioms KCore.famEx_closed_ce
#print axioms KCore.HoldsShape.termSoundEx
#print axioms KCore.SoundCETest.cCeG_stuck
#print axioms KCore.SoundCETest.sound_r1
#print axioms KCore.SoundCETest.famEx_r1
#print axioms KCore.SoundCETest.sound_cCeR
#print axioms KCore.SoundCETest.cCeR_not_decided
#print axioms KCore.SoundCETest.r0_noStep
