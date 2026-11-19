/-
  The owed `CondDecided` of the rule `<k> a() => b() ... </k> requires isMk(X:S)`, beside
  `<k> a() => c() ... </k> [owise]`, where `syntax Empty` has no production and
  `S ::= mk(Empty) | k()`, `isMk(mk(_)) => true`, `isMk(k()) => false`: it is false. Run from the
  package root: `lake env lean -j1 test/OwedGenlessFalse.lean`. Kernel-checked (`decide +kernel`).

  The text is read twice, as the same proof on two texts whose semantics differ only in what the
  proof does not read:
  - `Genless`: fixture e2-open-genless, `f2-examples/opengenless.kompile.kore`;
  - `HwEmpty`: fixture hw-ex-unused-empty, `test/constructs/fixtures/hw-ex-unused-empty/hw-ex-unused-empty.kore`
    (the kompiled text of c3-unbound-req-nokey with the `[owise]` rule's right side put under a
    binder `\exists Z:Empty` that it does not hold; the reader drops the binder).
  On each:
  - Every value of S is `k()` (`valS`), at which `isMk` is `false`, so the rule 0 is not `Witnessed`
    (`not_witnessed0`).
  - `cP := EmptyInh.plus c 34` adds an element `e` to Empty. Its theory with the step's closure has
    a model, which is one of c's (`model`, from `EmptyInh.premises_sub` and `FnHyp cP`). There
    `mk(e)` is an element of S at which `isMk` is `true`, so the rule's condition
    `∃X. ⌈isMk(X) = true⌉` is satisfied and the rule 0 is not `Refuted` (`not_refuted0`).
  - Hence its `CondDecided` is false (`owed_false`), and so is `OpenDecided c` (`not_owed`): the
    hypothesis of the headline statements fails at this text, which therefore claims nothing of
    `Step` here.
  - The text determines no answer to whether `b()` follows `a()` (`succ_undetermined`): over all
    interpretations H of the parameters, the theory with the step's closure entails neither that
    the configuration `<k> b() </k>` is a successor of `<k> a() </k>` nor that it is not. In the
    model of `cP`, the rule 0 applies under X := `mk(e)` (`stepByP`) and soundness at `cP`
    (`sound_hyp`) makes `<k> b() </k>` a successor; in the value model of c at its own step
    (`vmModelCl`), the rule 0 applies at no value and the `[owise]` rule gives `<k> c() </k>`, so
    `<k> b() </k>` is no successor (`not_stepV`).
  The hypotheses of `EmptyInh.premises_sub` hold at the interpretation the parsed data carries,
  `HookParams.none`, which is the H the statements' negations are witnessed at.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace OwedGenlessFalse

open KCore ML Faithful Faithful.Model KoreAML EmptyInh

def sS : Srt := 32
def sExp : Srt := 33
def sE : Srt := 34
def kCell : KCore.Sym := 385
def symA : KCore.Sym := 387
def symB : KCore.Sym := 388
def symC : KCore.Sym := 389
def symK : KCore.Sym := 390
def symMk : KCore.Sym := 391
def isMk : KCore.Sym := 392

/-- `isMk(k()) => false` -/
def clK : Clause := { vars := [], pats := [.app symK []], req := none, rhs := .dv Srt.bool (.bool false), ens := none }
/-- `isMk(mk(_)) => true` -/
def clMk : Clause := { vars := [sE], pats := [.app symMk [.var 0]], req := none, rhs := .dv Srt.bool (.bool true), ens := none }
def fIsMk : Fn := { label := isMk, args := [sS], result := Srt.bool, clauses := [clK, clMk], total := true }

/-- `<k> st ~> K </k>` with the counter cell C, K and C the variables 0 and 1. -/
def side (st : KCore.Sym) : Term :=
  .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app st []), .var 0]], .var 1]
/-- `<k> a() => b() ... </k> requires isMk(X:S)` -/
def r0 : Rule :=
  { vars := [Srt.k, 19, sS], lhs := side symA, req := some (.app isMk [.var 2]), rhs := side symB,
    ens := none, prio := 50 }
/-- `<k> a() => c() ... </k> [owise]` -/
def r1 : Rule := { vars := [Srt.k, 19], lhs := side symA, req := none, rhs := side symC, ens := none, prio := 200 }

/-- The configuration `<k> st ~> . </k>` with the counter 0. -/
def cfg (st : KCore.Sym) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor st []), .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

/-- `mk(e)`, the element of S over Empty's element in `plus c sE`. -/
def mkE (c : Semantics) : GroundTerm := .ctor symMk [eVal c]

namespace Genless

definition_of defn from "f2-examples/opengenless.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable abbrev cP : Semantics := plus c sE

theorem names : c.sortName sS = "S" ∧ c.sortName sE = "Empty" ∧ c.sortName sExp = "Exp" ∧
    c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" ∧
    c.symName symC = "Lblc" ∧ c.symName symK = "Lblk" ∧ c.symName symMk = "Lblmk" ∧
    c.symName isMk = "LblisMk" ∧ eSym c = 393 := by
  decide +kernel

/-- The parsed data's interpretation is `HookParams.none`. -/
theorem cH_none : cH HookParams.none = c := rfl

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The function and the rules are the reader's. -/
theorem text : c.fns = [fIsMk] := by rfl
theorem rules : c.rules = [r0, r1] := by rfl

theorem lookupIsMk : c.lookupFn isMk = some fIsMk := by rfl

/-! ## The values of S -/

theorem ctorSigs_E : c.ctorSigs.all (fun k => k.result != sE) = true := by decide +kernel
theorem ctorSigs_S : c.ctorSigs.all (fun k => k.result != sS ||
    (k.name == symK && k.args == []) || (k.name == symMk && k.args == [sE])) = true := by decide +kernel
theorem subsorts_SE : c.subsorts.all (fun p => p.2 != sS && p.2 != sE) = true := by decide +kernel
theorem lits_SE : c.lib.carrier sS = sS ∧ c.lib.carrier sE = sE ∧
    c.lib.tokenSorts.contains sS = false ∧ c.lib.tokenSorts.contains sE = false ∧
    c.lib.byteSorts.contains sS = false ∧ c.lib.byteSorts.contains sE = false := by decide +kernel
theorem colls_SE : c.collOf sS = none ∧ c.collOf sE = none := by decide +kernel

/-- What `premises_sub` and `sortOf_e` ask of c, decided. -/
theorem facts : c.ovls = [] ∧ c.params = [] ∧ c.ctorSigs.all (·.name != eSym c) = true ∧ c.gens sE = [] ∧
    (c.readsConfined = true → cP.readsConfined = true) ∧ (c.litSort Srt.bool = true → cP.litSort Srt.bool = true) := by
  decide +kernel

theorem hooksNone : ∀ f vs, c.hooks.app f vs = none := fun _ _ => rfl

theorem fresh : ∀ k ∈ c.ctorSigs, k.name ≠ eSym c := fun k hk => by
  simpa using List.all_eq_true.mp facts.2.2.1 k hk

theorem freshP : ∀ k ∈ c.params, k.sig.name ≠ eSym c := fun k hk => by
  rw [facts.2.1] at hk; cases hk

theorem noRaw : ∀ k ∈ c.params, k.raw = false := fun k hk => by rw [facts.2.1] at hk; cases hk

/-- A sort that is its own carrier, no literal sort, token sort or byte sort, has no literal. -/
theorem dvOK_false {l : Lib} {s : Srt} (hc : l.carrier s = s) (ht : l.tokenSorts.contains s = false)
    (hb : l.byteSorts.contains s = false) (h1 : s ≠ Srt.int) (h2 : s ≠ Srt.bool)
    (h3 : s ≠ Srt.kconfigVar) (h4 : s ≠ Srt.string) (h5 : s ≠ Srt.bytes) (h6 : s ≠ Srt.float)
    (lit : Lit) : dvOK l s lit = false := by
  have ht' : s ∉ l.tokenSorts := by simpa using ht
  have hb' : s ∉ l.byteSorts := by simpa using hb
  cases lit <;> simp [dvOK, hc, h1, h2, h3, h4, h5, h6, ht', hb']

theorem dvOK_S (lit : Lit) : dvOK c.lib sS lit = false :=
  dvOK_false lits_SE.1 lits_SE.2.2.1 lits_SE.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) lit
theorem dvOK_E (lit : Lit) : dvOK c.lib sE lit = false :=
  dvOK_false lits_SE.2.1 lits_SE.2.2.2.1 lits_SE.2.2.2.2.2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) lit

/-- A constructor application of sort s is an application of a constructor whose result is s. -/
theorem ctor_sig {f : KCore.Sym} {ts : List GroundTerm} {s : Srt} (h : c.sortOf (.ctor f ts) = some s) :
    ∃ k ∈ c.ctorSigs, k.name = f ∧ c.sortsOf ts = some k.args ∧ k.result = s := by
  rcases (Semantics.sortOf_ctor_iff c).mp h with ⟨k, hk, hts, hr⟩ | ⟨-, o, ho, -⟩ | ⟨-, -, kp, hko, -⟩
  · rw [lookupSig_eq] at hk
    exact ⟨k, List.mem_of_find?_eq_some hk, by simpa using List.find?_some hk, hts, hr.symm⟩
  · simp [Semantics.lookupOvl, facts.1] at ho
  · rw [c.lookupOpen_of_noRaw noRaw f] at hko
    cases hko

/-- A value of a sort that is no injection's target, has no literal and is no collection sort is a
constructor application. -/
theorem ctor_of_sort {d : Semantics} {v : GroundTerm} {s : Srt} (h : d.sortOf v = some s)
    (hsub : ∀ p ∈ d.subsorts, p.2 ≠ s) (hlit : ∀ lit, dvOK d.lib s lit = false) (hcoll : d.collOf s = none) :
    ∃ f ts, v = .ctor f ts := by
  cases v with
  | ctor f ts => exact ⟨f, ts, rfl⟩
  | inj a b t =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i hcond
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hcond
      exact absurd rfl (hsub _ hcond.1.1)
    · cases h
  | dv s' lit =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i hok
      cases h
      rw [hlit] at hok
      cases hok
    · cases h
  | map s' es =>
    obtain ⟨rfl, hco⟩ := sortOf_map_sort h
    rw [hcoll] at hco; cases hco
  | set s' es =>
    obtain ⟨rfl, k, hco, -⟩ := Faithful.Model.sortOf_set_some h
    rw [hcoll] at hco; cases hco
  | list s' es =>
    obtain ⟨rfl, k, hco, -⟩ := Faithful.Model.sortOf_list_some h
    rw [hcoll] at hco; cases hco

theorem subsorts_S : ∀ p ∈ c.subsorts, p.2 ≠ sS := fun p hp => by
  have := List.all_eq_true.mp subsorts_SE p hp
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact this.1
theorem subsorts_E : ∀ p ∈ c.subsorts, p.2 ≠ sE := fun p hp => by
  have := List.all_eq_true.mp subsorts_SE p hp
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact this.2

/-- No value has sort Empty: no constructor, injection, literal or collection has it. -/
theorem noEmpty (v : GroundTerm) : c.sortOf v ≠ some sE := by
  intro h
  obtain ⟨f, ts, rfl⟩ := ctor_of_sort h subsorts_E dvOK_E colls_SE.2
  obtain ⟨k, hk, -, -, hr⟩ := ctor_sig h
  have := List.all_eq_true.mp ctorSigs_E k hk
  simp [hr] at this

/-- **Every value of S is `k()`**: S's constructors are `k()` and `mk(Empty)`, and Empty has no
value. -/
theorem valS {v : GroundTerm} (h : c.sortOf v = some sS) : v = .ctor symK [] := by
  obtain ⟨f, ts, rfl⟩ := ctor_of_sort h subsorts_S dvOK_S colls_SE.1
  obtain ⟨k, hk, hname, hts, hr⟩ := ctor_sig h
  have := List.all_eq_true.mp ctorSigs_S k hk
  simp only [hr, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  rcases this with ⟨hn, ha⟩ | ⟨hn, ha⟩
  · rw [ha] at hts
    cases ts with
    | nil => rw [← hname, hn]
    | cons t ts =>
      simp only [Semantics.sortsOf] at hts
      split at hts <;> cases hts
  · rw [ha] at hts
    cases ts with
    | nil => simp [Semantics.sortsOf] at hts
    | cons t ts =>
      simp only [Semantics.sortsOf] at hts
      split at hts
      · rename_i s ss hs _
        cases hts
        exact absurd hs (noEmpty t)
      · cases hts

/-! ## The functions of c -/

/-- The generated `Obl` at the call order `[isMk]`: no fact about a function is named. -/
theorem obl_nil : FnFacts c [isMk] [] :=
  FnFacts.of_nil (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem rightHeld : c.RightHeld := Semantics.rightHeld_of_valued (by decide +kernel)

theorem fnModel : FnDet c ∧ FnSolves c := fnModel_of_fnFacts coreOK rightHeld obl_nil

theorem fnDet : FnDet c := fnModel.1

/-- `isMk(k())` is `false`, by its clause `isMk(k()) => false`. -/
theorem eval_isMk_k : Eval c isMk [.ctor symK []] (some (bool false)) :=
  .clause (cl := clK) (σ := []) lookupIsMk (by simp [fIsMk])
    (fun i s hs => by cases (show (none : Option Srt) = some s from hs))
    (.cons (.ctor (by decide +kernel) .nil) .nil) (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fIsMk, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- Where X is `k()`, the `requires` `isMk(X)` evaluates to `false`. -/
theorem req_false {σ : Subst} (hl : σ.lookup 2 = some (.ctor symK [])) :
    EvalTerm c σ (.app isMk [.var 2]) (some (bool false)) :=
  .call (vs := [.ctor symK []]) (by decide +kernel) (by decide +kernel) (.cons .var .nil) (by rw [hl]; rfl)
    eval_isMk_k (by decide +kernel)

/-- **The rule 0 is not `Witnessed`**: X is `k()` at every value, where `isMk(X)` is `false` only. -/
theorem not_witnessed0 : ¬ r0.Witnessed c := by
  rintro ⟨σ, hσ, hreq, -⟩
  obtain ⟨v, hl, hv⟩ := hσ 2 (by decide) sS rfl
  rw [valS hv] at hl
  have := EvalTerm.functional_of_fnDet fnDet (hreq _ rfl) (req_false hl)
  simp [KCore.bool] at this

/-! ## The second model: Empty holds `e` -/

/-- `isMk` does not fail at a value of S: there it is `k()`, which `isMk(k()) => false` matches. -/
theorem noFail : ∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ cl ∈ fn.clauses, ¬ Fails c vs cl := by
  intro fn hfn vs hvs
  rw [text, List.mem_singleton] at hfn
  subst hfn
  obtain ⟨v, rfl, hv⟩ := EmptyInh.sortsOf_single hvs
  rw [valS hv]
  exact ⟨clK, by simp [fIsMk], not_fails_of (σ := []) rfl rfl
    (fun i hi => by rw [show clK.leftVars = [] from rfl] at hi; cases hi)
    (.cons (.ctor (by decide +kernel) .nil) .nil)⟩

theorem sub : ∀ φ, φ ∈ Γc c ∪ Γstep c → φ ∈ Γc cP ∪ Γstep cP :=
  premises_sub facts.1 fresh facts.2.2.2.1
    (fun k hk => by rw [facts.2.1] at hk; cases hk)
    (fun k _ vs _ _ _ => fallback_plus_of_none hooksNone k.name vs)
    (hfails_of_noFail noFail) facts.2.2.2.2.1 facts.2.2.2.2.2

theorem openLawsP : OpenLaws cP := by
  intro k hk _
  have hk' : k ∈ c.params ++ [eParam c sE] := hk
  rw [facts.2.1, List.nil_append, List.mem_singleton] at hk'
  subst hk'
  exact ⟨fun h => by simp [eParam] at h, fun h => by simp [eParam] at h⟩


/-! ## In `cP`, the rule 0 applies at `mk(e)` -/

theorem sortOf_e : cP.sortOf (eVal c) = some sE :=
  EmptyInh.sortOf_e facts.1 fresh freshP (keepsRaw_of_none hooksNone)

theorem mkE_sort : cP.sortOf (mkE c) = some sS :=
  sortOf_ctor_intro ⟨⟨symMk, [sE], sS⟩, by decide +kernel, sortsOf_cons.mpr ⟨_, _, sortOf_e, sortsOf_nil, rfl⟩, rfl⟩

theorem lookupIsMkP : cP.lookupFn isMk = some fIsMk := by rfl

/-- **`isMk(mk(e))` is `true` in `cP`**, by `isMk(mk(_)) => true`. -/
theorem isMk_mkE : Eval cP isMk [mkE c] (some (bool true)) :=
  .clause (cl := clMk) (σ := [(0, eVal c)]) lookupIsMkP (by simp [fIsMk])
    (fun i s hs => by
      cases i with
      | zero => cases (show some sE = some s from hs); exact ⟨_, rfl, sortOf_e⟩
      | succ i => cases (show (none : Option Srt) = some s from hs))
    (.cons (.ctor (by decide +kernel) (.cons (.var rfl) .nil)) .nil) (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fIsMk, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

theorem empty : c.subsorts.all (fun p => p.2 != sE) = true ∧ c.collOf sE = none ∧
    c.lib.carriers.all (·.1 != sE) = true ∧
    (sE != Srt.int && sE != Srt.bool && sE != Srt.kconfigVar && sE != Srt.string &&
      sE != Srt.bytes && sE != Srt.float && !c.lib.tokenSorts.contains sE &&
      !c.lib.byteSorts.contains sE) = true := by
  decide +kernel

/-- **`e` is the one value of Empty in `cP`.** -/
theorem value_eq {v : GroundTerm} (h : cP.sortOf v = some sE) : v = eVal c :=
  value_E_eq ctorSigs_E facts.1 noRaw empty.1 empty.2.1 empty.2.2.1 empty.2.2.2 h

/-- A constructor application of `cP` of a sort other than Empty is one of c's constructors: the
added open generator is of sort Empty. -/
theorem ctor_sigP {f : KCore.Sym} {ts : List GroundTerm} {s : Srt} (h : cP.sortOf (.ctor f ts) = some s)
    (hs : s ≠ sE) : ∃ k ∈ c.ctorSigs, k.name = f ∧ cP.sortsOf ts = some k.args ∧ k.result = s := by
  rcases (Semantics.sortOf_ctor_iff cP).mp h with ⟨k, hk, hts, hr⟩ | ⟨-, o, ho, -⟩ | ⟨-, -, kp, hko, -, -, hr⟩
  · rw [lookupSig_eq] at hk
    exact ⟨k, List.mem_of_find?_eq_some hk, by simpa using List.find?_some hk, hts, hr.symm⟩
  · simp [Semantics.lookupOvl, plus_ovls, facts.1] at ho
  · obtain ⟨hm, -, -, -⟩ := Semantics.lookupOpen_spec _ hko
    have hm' : kp ∈ c.params ++ [eParam c sE] := hm
    rw [facts.2.1, List.nil_append, List.mem_singleton] at hm'
    subst hm'
    exact absurd hr hs

/-- **The values of S in `cP`**: `k()` and `mk(e)`. -/
theorem valSP {v : GroundTerm} (h : cP.sortOf v = some sS) : v = .ctor symK [] ∨ v = mkE c := by
  obtain ⟨f, ts, rfl⟩ := ctor_of_sort h subsorts_S dvOK_S colls_SE.1
  obtain ⟨k, hk, hname, hts, hr⟩ := ctor_sigP h (by decide)
  have := List.all_eq_true.mp ctorSigs_S k hk
  simp only [hr, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  rcases this with ⟨hn, ha⟩ | ⟨hn, ha⟩
  · left
    rw [ha] at hts
    cases ts with
    | nil => rw [← hname, hn]
    | cons t ts =>
      simp only [Semantics.sortsOf] at hts
      split at hts <;> cases hts
  · right
    rw [ha] at hts
    cases ts with
    | nil => simp [Semantics.sortsOf] at hts
    | cons t ts =>
      simp only [Semantics.sortsOf] at hts
      split at hts
      · rename_i s ss hs hss
        cases hts
        rw [← hname, hn, value_eq hs, sortsOf_nil_of hss]
        rfl
      · cases hts

/-- `isMk(k())` is `false` in `cP`. -/
theorem eval_isMk_kP : Eval cP isMk [.ctor symK []] (some (bool false)) :=
  .clause (cl := clK) (σ := []) lookupIsMkP (by simp [fIsMk])
    (fun i s hs => by cases (show (none : Option Srt) = some s from hs))
    (.cons (.ctor (by decide +kernel) .nil) .nil) (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fIsMk, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- **`isMk` is total in `cP`**: it has a value at `k()` and at `mk(e)`. -/
theorem totalP : Total cP isMk := by
  intro fn hfn vs hvs
  rw [lookupIsMkP] at hfn
  cases hfn
  obtain ⟨v, rfl, hv⟩ := EmptyInh.sortsOf_single hvs
  rcases valSP hv with rfl | rfl
  · exact ⟨_, eval_isMk_kP⟩
  · exact ⟨_, isMk_mkE⟩

/-- In `cP` the totality of `isMk` is named, and nothing is owed: with `e`, S is confined. -/
theorem namedP : cP.coreOK = true ∧ cP.heldObligations = [] ∧
    cP.rankObligations [isMk] ++ cP.decObligationsL = [] ∧ cP.totalObligationsRP [isMk] [] = [isMk] ∧
    cP.agreeObligationsI = [] ∧ cP.matchObligationsL = [] ∧ cP.owedRules = [] ∧ cP.owedClauses = [] := by
  decide_cheap

theorem coreP : cP.coreOK = true := namedP.1

theorem openDecidedP : OpenDecided cP :=
  ⟨openRules_of_owed (by rw [namedP.2.2.2.2.2.2.1]; intro i hi; cases hi),
   openClauses_of_owed (by rw [namedP.2.2.2.2.2.2.2]; intro p hp; cases hp)⟩

theorem oblP : FnObligations cP [isMk] [] := by
  obtain ⟨-, -, hterm, htot, hagr, hmat, -, -⟩ := namedP
  refine ⟨fun f hf => (by rw [hterm] at hf; cases hf), fun f hf => ?_, fun f hf => (by rw [hagr] at hf; cases hf),
    fun p hp => (by rw [hmat] at hp; cases hp), openDecidedP, openLawsP⟩
  rw [htot, List.mem_singleton] at hf
  subst hf
  exact totalP

theorem fnHypP : FnHyp cP :=
  fnHyp_of_fnObligationsN coreP (by rw [namedP.2.1]; intro f hf; cases hf) ParamsTotal.nil oblP

/-- **A model of `cP`'s theory with the step's closure, which is one of c's.** -/
theorem model : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc cP ∪ Γstep cP)) ∧ (I ⊧ᴵP (Γc c ∪ Γstep c)) :=
  model_exists sub coreP fnHypP

/-- K := `.`, the counter 0, X := `mk(e)`. -/
noncomputable def σw : Subst := [(0, .ctor dotk []), (1, .ctor counterLabel [.dv Srt.int (.int 0)]), (2, mkE c)]

theorem ws_w : cP.WellSorted r0.vars σw := fun i s hs => by
  match i, hs with
  | 0, hs => cases (show some Srt.k = some s from hs); exact ⟨_, rfl, sortOf_plus (by decide +kernel)⟩
  | 1, hs => cases (show some (19 : Srt) = some s from hs); exact ⟨_, rfl, sortOf_plus (by decide +kernel)⟩
  | 2, hs => cases (show some sS = some s from hs); exact ⟨_, rfl, mkE_sort⟩
  | _ + 3, hs => cases (show (none : Option Srt) = some s from hs)

theorem req_w : EvalTerm cP σw (.app isMk [.var 2]) (some (bool true)) :=
  .call (vs := [mkE c]) (by decide +kernel) (by decide +kernel) (.cons .var .nil) rfl isMk_mkE (by decide +kernel)

def A : Config c := ⟨cfg symA, by decide +kernel⟩
def B : Config c := ⟨cfg symB, by decide +kernel⟩
noncomputable def AP : Config cP := ⟨A.val, sortOf_plus A.property⟩
noncomputable def BP : Config cP := ⟨B.val, sortOf_plus B.property⟩

theorem symsP : cP.isCtor topLabel = true ∧ cP.isCtor kCell = true ∧ cP.isCtor kseq = true ∧
    cP.isCtor symA = true ∧ cP.isCtor symB = true := by
  decide +kernel

/-- **In `cP` the rule 0 steps `<k> a() </k>` to `<k> b() </k>`**, under X := `mk(e)`. -/
theorem stepByP : StepBy cP r0 σw AP BP where
  mem := by rw [show cP.rules = [r0, r1] from rules]; simp
  hσ := ws_w
  hmatch := .ctor symsP.1 (.cons (.ctor symsP.2.1 (.cons (.ctor symsP.2.2.1
      (.cons (.inj (.ctor symsP.2.2.2.1 .nil)) (.cons (.var rfl) .nil))) .nil)) (.cons (.var rfl) .nil))
  hreq := fun t ht => by cases ht; exact req_w
  hpre := .top
  heval := .ctor symsP.1 (.cons (.ctor symsP.2.1 (.cons (.ctor symsP.2.2.1
      (.cons (.inj (.ctor symsP.2.2.2.2 .nil)) (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by cases ht
  hpost := .top
  hprio := fun r' hr' hlt => by
    rw [show cP.rules = [r0, r1] from rules] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)

/-! ## The rule 0 is not refuted -/

/-- **The rule 0 is not `Refuted`**: in the model of `cP`, which is one of c's, the valuation
X ↦ `mk(e)` satisfies `⌈isMk(X) = true⌉`. -/
theorem not_refuted0 : ¬ r0.Refuted c := by
  obtain ⟨M, hM, I, hP, hc⟩ := model
  have hIc : I ⊧ᴵP Γc c := fun φ hφ => hc φ (Or.inl hφ)
  have hΓ : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have hΓcP : I ⊧ᴵP Γc cP := fun φ hφ => hP φ (Or.inl hφ)
  have hΓP : I ⊧ᴵP Γ cP := fun φ hφ => hΓcP φ (Or.inl hφ)
  obtain ⟨-, -, -, -, -, -, -, -, hno⟩ := hypSound_of_core coreOK
  haveI : OvlOK c := hno
  obtain ⟨-, -, -, -, -, -, -, -, hnoP⟩ := hypSound_of_core coreP
  haveI : OvlOK cP := hnoP
  let tbl : VarTable := (List.range 3).map (canonKey cP r0.vars)
  have hkeys : ∀ i < r0.vars.length, canonKey cP r0.vars i ∈ tbl := fun i hi =>
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  let e := overV cP I tbl r0.vars σw KoreAML.val0
  have hag := overV_agrees (e := KoreAML.val0) hΓP hkeys ws_w
  have hts : HoldsShape.TermSound cP I := HoldsShape.termSoundEx (Semantics.coreOK_iff_ex.mp coreP) hΓcP openDecidedP.2
  have hq : ∀ t, r0.req = some t → ∀ b, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r0.vars) t)).interpret I e b ↔
      (den c (bool true)).interpret I e b := by
    intro t ht b
    cases ht
    have h := hts req_w ws_w (canonVars_length _ _) hag
      (show sortOfTerm _ r0.vars (.app isMk [.var 2]) = some Srt.bool by decide +kernel) b
    rw [← termKore_plus_fun (E := sE), ← den_plus (E := sE)]
    exact h
  have hm := reqPat_holds hΓ hq (elemOf_top hΓ A tbl e)
  refine cond_not_refuted_at coreOK hIc (by decide +kernel) rfl (fun i hi hci => ?_) rfl hm
  have h2 : i = 2 := by
    have : r0.condVars = [2] := by decide +kernel
    rw [this, List.mem_singleton] at hci
    exact hci
  subst h2
  show InS I (cP.sortName sS) ((overV cP I tbl r0.vars σw KoreAML.val0).evalEvar (tbl.ev (canonKey cP r0.vars 2)))
  rw [overV_at hkeys (by decide)]
  exact (inS_iff KoreAML.val0).mp (elemOf_spec hΓP mkE_sort KoreAML.val0).2

/-- **The owed `CondDecided` of the rule 0 is false**: it is neither `Witnessed` nor `Refuted`. -/
theorem owed_false : ¬ r0.CondDecided c := fun h => h.elim not_witnessed0 not_refuted0

/-- **`OpenDecided` is false at this text**: the rule 0 needs a witness and its condition is not
decided. -/
theorem not_owed : ¬ OpenDecided c := fun h =>
  owed_false (h.1 r0 (by rw [rules]; simp) (by decide +kernel))

/-! ## Whether `<k> b() </k>` follows `<k> a() </k>` -/

/-- What `vmModelCl` asks of c beside the functions' facts, decided. -/
theorem decided : c.sortedOKCl = true ∧ c.srReady = true ∧ c.faithCoreOK = true ∧
    patHooksApart c = true ∧ c.idsOK = true ∧ c.ovls = [] ∧ c.subsorts.all (fun p => p.1 != p.2) = true := by
  decide_cheap

instance ovl : OvlOK c := OvlOK.of_nil decided.2.2.2.2.2.1 decided.2.2.2.2.2.2

theorem syms : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symC = true := by
  decide +kernel

/-- **`<k> b() </k>` is no successor of `<k> a() </k>` in the value model's step**: the rule 0
applies at no value (X is `k()`, where `isMk` is `false`), and the `[owise]` rule gives `c()`. -/
theorem not_stepV : ¬ StepV c A.val B.val := by
  rintro ⟨r, σ, hr, hσ, -, hreq, -, heval, -⟩
  rw [rules] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · obtain ⟨v, hl, hv⟩ := hσ 2 sS rfl
    rw [valS hv] at hl
    have := EvalTerm.functional_of_fnDet fnDet (hreq _ rfl) (req_false hl)
    simp [KCore.bool] at this
  · obtain ⟨v0, h0, -⟩ := hσ 0 Srt.k rfl
    obtain ⟨v1, h1, -⟩ := hσ 1 19 rfl
    have e0 : EvalTerm c σ (.var 0) (some v0) := by rw [← h0]; exact .var
    have e1 : EvalTerm c σ (.var 1) (some v1) := by rw [← h1]; exact .var
    have hc : EvalTerm c σ r1.rhs
        (some (.ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symC []), v0]], v1])) :=
      .ctor syms.1 (.cons (.ctor syms.2.1 (.cons (.ctor syms.2.2.1
        (.cons (.inj (.ctor syms.2.2.2 .nil)) (.cons e0 .nil))) .nil)) (.cons e1 .nil))
    have := EvalTerm.functional_of_fnDet fnDet heval hc
    simp [B, cfg, symB, symC] at this

/-- **The text determines no answer to whether `<k> b() </k>` follows `<k> a() </k>`**: over all
H, the reading's theory with the step's closure entails neither that `<k> b() </k>` is a successor
of `<k> a() </k>` nor that it is not. At `HookParams.none`, the model of `cP` makes it one (the
rule 0 under X := `mk(e)`, by soundness at `cP`), and the value model of c makes it none. -/
theorem succ_undetermined :
    ¬ (∀ H : HookParams, (Γc (cH H) ∪ Γstep (cH H)) ⊧
        (den (cH H) A.val ⇒ ∼ KoreAML.sNext (den (cH H) B.val))) ∧
    ¬ (∀ H : HookParams, (Γc (cH H) ∪ Γstep (cH H)) ⊧
        (den (cH H) A.val ⇒ KoreAML.sNext (den (cH H) B.val))) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨M, hM, I, hP, hc⟩ := model
    have hΓcP : I ⊧ᴵP Γc cP := fun φ hφ => hP φ (Or.inl hφ)
    have hΓP : I ⊧ᴵP Γ cP := fun φ hφ => hΓcP φ (Or.inl hφ)
    have hD := defOK hΓP
    have hcP : ∀ fn ∈ cP.fns, ∀ cl ∈ fn.clauses, cl.needsWitness cP = true → cl.CondDecided cP := openDecidedP.2
    have h1 := ((sound_hyp cP coreP fnHypP).2 AP BP r0 σw stepByP).1 hΓcP KoreAML.val0 (elemOf cP I A.val)
    have hcl := famEx_closed cP coreP stepByP rfl hcP hΓcP KoreAML.val0 (elemOf cP I A.val)
    rw [KoreAML.interp_equal hD] at hcl
    have hx := ((elemOf_spec hΓP AP.property KoreAML.val0).1 (elemOf cP I A.val)).mpr rfl
    rw [interpret_impl] at h1
    have hn := sNext_congr hcl (h1 hx)
    have h2 := h HookParams.none hc KoreAML.val0 (elemOf cP I A.val)
    rw [cH_none, interpret_impl, interpret_neg] at h2
    rw [show den cP AP.val = den c A.val from den_plus _] at hx
    rw [show den cP BP.val = den c B.val from den_plus _] at hn
    exact h2 hx hn
  · have hm := hypModel_ofCl decided.1 decided.2.1 ovl decided.2.2.1 decided.2.2.2.1 decided.2.2.2.2.1
      fnModel.1 fnModel.2
    have hmod := vmModelCl c decided.1 decided.2.1 decided.2.2.1 decided.2.2.2.1 decided.2.2.2.2.1
      fnModel.1 fnModel.2 (clausePreDecided_of_fnFactsN coreOK (fun f _ => rightHeld.heldOwed f) obl_nil)
      obl_nil.2.2.2.2
    have hsat : stdI_T c (StepV c) ⊧ᴵ (den c A.val ⇒ ∼ KoreAML.sNext (den c B.val)) :=
      Classical.not_not.mp (mt (step_iff_stdI_T c hm (StepV c) A B).mpr not_stepV)
    have h1 := h HookParams.none hmod KoreAML.val0 (.val A.val)
    have h2 := hsat KoreAML.val0 (.val A.val)
    rw [interpret_impl] at h1 h2
    have hx := (den_val_T hm (StepV c) A.val A.property KoreAML.val0 _).mpr rfl
    exact (interpret_neg.mp (h2 hx)) (h1 hx)

end Genless

namespace HwEmpty

definition_of defn from "test/constructs/fixtures/hw-ex-unused-empty/hw-ex-unused-empty.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable abbrev cP : Semantics := plus c sE

theorem names : c.sortName sS = "S" ∧ c.sortName sE = "Empty" ∧ c.sortName sExp = "Exp" ∧
    c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" ∧
    c.symName symC = "Lblc" ∧ c.symName symK = "Lblk" ∧ c.symName symMk = "Lblmk" ∧
    c.symName isMk = "LblisMk" ∧ eSym c = 393 := by
  decide +kernel

/-- The parsed data's interpretation is `HookParams.none`. -/
theorem cH_none : cH HookParams.none = c := rfl

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The function and the rules are the reader's. -/
theorem text : c.fns = [fIsMk] := by rfl
theorem rules : c.rules = [r0, r1] := by rfl

theorem lookupIsMk : c.lookupFn isMk = some fIsMk := by rfl

/-! ## The values of S -/

theorem ctorSigs_E : c.ctorSigs.all (fun k => k.result != sE) = true := by decide +kernel
theorem ctorSigs_S : c.ctorSigs.all (fun k => k.result != sS ||
    (k.name == symK && k.args == []) || (k.name == symMk && k.args == [sE])) = true := by decide +kernel
theorem subsorts_SE : c.subsorts.all (fun p => p.2 != sS && p.2 != sE) = true := by decide +kernel
theorem lits_SE : c.lib.carrier sS = sS ∧ c.lib.carrier sE = sE ∧
    c.lib.tokenSorts.contains sS = false ∧ c.lib.tokenSorts.contains sE = false ∧
    c.lib.byteSorts.contains sS = false ∧ c.lib.byteSorts.contains sE = false := by decide +kernel
theorem colls_SE : c.collOf sS = none ∧ c.collOf sE = none := by decide +kernel

/-- What `premises_sub` and `sortOf_e` ask of c, decided. -/
theorem facts : c.ovls = [] ∧ c.params = [] ∧ c.ctorSigs.all (·.name != eSym c) = true ∧ c.gens sE = [] ∧
    (c.readsConfined = true → cP.readsConfined = true) ∧ (c.litSort Srt.bool = true → cP.litSort Srt.bool = true) := by
  decide +kernel

theorem hooksNone : ∀ f vs, c.hooks.app f vs = none := fun _ _ => rfl

theorem fresh : ∀ k ∈ c.ctorSigs, k.name ≠ eSym c := fun k hk => by
  simpa using List.all_eq_true.mp facts.2.2.1 k hk

theorem freshP : ∀ k ∈ c.params, k.sig.name ≠ eSym c := fun k hk => by
  rw [facts.2.1] at hk; cases hk

theorem noRaw : ∀ k ∈ c.params, k.raw = false := fun k hk => by rw [facts.2.1] at hk; cases hk

/-- A sort that is its own carrier, no literal sort, token sort or byte sort, has no literal. -/
theorem dvOK_false {l : Lib} {s : Srt} (hc : l.carrier s = s) (ht : l.tokenSorts.contains s = false)
    (hb : l.byteSorts.contains s = false) (h1 : s ≠ Srt.int) (h2 : s ≠ Srt.bool)
    (h3 : s ≠ Srt.kconfigVar) (h4 : s ≠ Srt.string) (h5 : s ≠ Srt.bytes) (h6 : s ≠ Srt.float)
    (lit : Lit) : dvOK l s lit = false := by
  have ht' : s ∉ l.tokenSorts := by simpa using ht
  have hb' : s ∉ l.byteSorts := by simpa using hb
  cases lit <;> simp [dvOK, hc, h1, h2, h3, h4, h5, h6, ht', hb']

theorem dvOK_S (lit : Lit) : dvOK c.lib sS lit = false :=
  dvOK_false lits_SE.1 lits_SE.2.2.1 lits_SE.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) lit
theorem dvOK_E (lit : Lit) : dvOK c.lib sE lit = false :=
  dvOK_false lits_SE.2.1 lits_SE.2.2.2.1 lits_SE.2.2.2.2.2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) lit

/-- A constructor application of sort s is an application of a constructor whose result is s. -/
theorem ctor_sig {f : KCore.Sym} {ts : List GroundTerm} {s : Srt} (h : c.sortOf (.ctor f ts) = some s) :
    ∃ k ∈ c.ctorSigs, k.name = f ∧ c.sortsOf ts = some k.args ∧ k.result = s := by
  rcases (Semantics.sortOf_ctor_iff c).mp h with ⟨k, hk, hts, hr⟩ | ⟨-, o, ho, -⟩ | ⟨-, -, kp, hko, -⟩
  · rw [lookupSig_eq] at hk
    exact ⟨k, List.mem_of_find?_eq_some hk, by simpa using List.find?_some hk, hts, hr.symm⟩
  · simp [Semantics.lookupOvl, facts.1] at ho
  · rw [c.lookupOpen_of_noRaw noRaw f] at hko
    cases hko

/-- A value of a sort that is no injection's target, has no literal and is no collection sort is a
constructor application. -/
theorem ctor_of_sort {d : Semantics} {v : GroundTerm} {s : Srt} (h : d.sortOf v = some s)
    (hsub : ∀ p ∈ d.subsorts, p.2 ≠ s) (hlit : ∀ lit, dvOK d.lib s lit = false) (hcoll : d.collOf s = none) :
    ∃ f ts, v = .ctor f ts := by
  cases v with
  | ctor f ts => exact ⟨f, ts, rfl⟩
  | inj a b t =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i hcond
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hcond
      exact absurd rfl (hsub _ hcond.1.1)
    · cases h
  | dv s' lit =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i hok
      cases h
      rw [hlit] at hok
      cases hok
    · cases h
  | map s' es =>
    obtain ⟨rfl, hco⟩ := sortOf_map_sort h
    rw [hcoll] at hco; cases hco
  | set s' es =>
    obtain ⟨rfl, k, hco, -⟩ := Faithful.Model.sortOf_set_some h
    rw [hcoll] at hco; cases hco
  | list s' es =>
    obtain ⟨rfl, k, hco, -⟩ := Faithful.Model.sortOf_list_some h
    rw [hcoll] at hco; cases hco

theorem subsorts_S : ∀ p ∈ c.subsorts, p.2 ≠ sS := fun p hp => by
  have := List.all_eq_true.mp subsorts_SE p hp
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact this.1
theorem subsorts_E : ∀ p ∈ c.subsorts, p.2 ≠ sE := fun p hp => by
  have := List.all_eq_true.mp subsorts_SE p hp
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact this.2

/-- No value has sort Empty: no constructor, injection, literal or collection has it. -/
theorem noEmpty (v : GroundTerm) : c.sortOf v ≠ some sE := by
  intro h
  obtain ⟨f, ts, rfl⟩ := ctor_of_sort h subsorts_E dvOK_E colls_SE.2
  obtain ⟨k, hk, -, -, hr⟩ := ctor_sig h
  have := List.all_eq_true.mp ctorSigs_E k hk
  simp [hr] at this

/-- **Every value of S is `k()`**: S's constructors are `k()` and `mk(Empty)`, and Empty has no
value. -/
theorem valS {v : GroundTerm} (h : c.sortOf v = some sS) : v = .ctor symK [] := by
  obtain ⟨f, ts, rfl⟩ := ctor_of_sort h subsorts_S dvOK_S colls_SE.1
  obtain ⟨k, hk, hname, hts, hr⟩ := ctor_sig h
  have := List.all_eq_true.mp ctorSigs_S k hk
  simp only [hr, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  rcases this with ⟨hn, ha⟩ | ⟨hn, ha⟩
  · rw [ha] at hts
    cases ts with
    | nil => rw [← hname, hn]
    | cons t ts =>
      simp only [Semantics.sortsOf] at hts
      split at hts <;> cases hts
  · rw [ha] at hts
    cases ts with
    | nil => simp [Semantics.sortsOf] at hts
    | cons t ts =>
      simp only [Semantics.sortsOf] at hts
      split at hts
      · rename_i s ss hs _
        cases hts
        exact absurd hs (noEmpty t)
      · cases hts

/-! ## The functions of c -/

/-- The generated `Obl` at the call order `[isMk]`: no fact about a function is named. -/
theorem obl_nil : FnFacts c [isMk] [] :=
  FnFacts.of_nil (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem rightHeld : c.RightHeld := Semantics.rightHeld_of_valued (by decide +kernel)

theorem fnModel : FnDet c ∧ FnSolves c := fnModel_of_fnFacts coreOK rightHeld obl_nil

theorem fnDet : FnDet c := fnModel.1

/-- `isMk(k())` is `false`, by its clause `isMk(k()) => false`. -/
theorem eval_isMk_k : Eval c isMk [.ctor symK []] (some (bool false)) :=
  .clause (cl := clK) (σ := []) lookupIsMk (by simp [fIsMk])
    (fun i s hs => by cases (show (none : Option Srt) = some s from hs))
    (.cons (.ctor (by decide +kernel) .nil) .nil) (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fIsMk, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- Where X is `k()`, the `requires` `isMk(X)` evaluates to `false`. -/
theorem req_false {σ : Subst} (hl : σ.lookup 2 = some (.ctor symK [])) :
    EvalTerm c σ (.app isMk [.var 2]) (some (bool false)) :=
  .call (vs := [.ctor symK []]) (by decide +kernel) (by decide +kernel) (.cons .var .nil) (by rw [hl]; rfl)
    eval_isMk_k (by decide +kernel)

/-- **The rule 0 is not `Witnessed`**: X is `k()` at every value, where `isMk(X)` is `false` only. -/
theorem not_witnessed0 : ¬ r0.Witnessed c := by
  rintro ⟨σ, hσ, hreq, -⟩
  obtain ⟨v, hl, hv⟩ := hσ 2 (by decide) sS rfl
  rw [valS hv] at hl
  have := EvalTerm.functional_of_fnDet fnDet (hreq _ rfl) (req_false hl)
  simp [KCore.bool] at this

/-! ## The second model: Empty holds `e` -/

/-- `isMk` does not fail at a value of S: there it is `k()`, which `isMk(k()) => false` matches. -/
theorem noFail : ∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ cl ∈ fn.clauses, ¬ Fails c vs cl := by
  intro fn hfn vs hvs
  rw [text, List.mem_singleton] at hfn
  subst hfn
  obtain ⟨v, rfl, hv⟩ := EmptyInh.sortsOf_single hvs
  rw [valS hv]
  exact ⟨clK, by simp [fIsMk], not_fails_of (σ := []) rfl rfl
    (fun i hi => by rw [show clK.leftVars = [] from rfl] at hi; cases hi)
    (.cons (.ctor (by decide +kernel) .nil) .nil)⟩

theorem sub : ∀ φ, φ ∈ Γc c ∪ Γstep c → φ ∈ Γc cP ∪ Γstep cP :=
  premises_sub facts.1 fresh facts.2.2.2.1
    (fun k hk => by rw [facts.2.1] at hk; cases hk)
    (fun k _ vs _ _ _ => fallback_plus_of_none hooksNone k.name vs)
    (hfails_of_noFail noFail) facts.2.2.2.2.1 facts.2.2.2.2.2

theorem openLawsP : OpenLaws cP := by
  intro k hk _
  have hk' : k ∈ c.params ++ [eParam c sE] := hk
  rw [facts.2.1, List.nil_append, List.mem_singleton] at hk'
  subst hk'
  exact ⟨fun h => by simp [eParam] at h, fun h => by simp [eParam] at h⟩


/-! ## In `cP`, the rule 0 applies at `mk(e)` -/

theorem sortOf_e : cP.sortOf (eVal c) = some sE :=
  EmptyInh.sortOf_e facts.1 fresh freshP (keepsRaw_of_none hooksNone)

theorem mkE_sort : cP.sortOf (mkE c) = some sS :=
  sortOf_ctor_intro ⟨⟨symMk, [sE], sS⟩, by decide +kernel, sortsOf_cons.mpr ⟨_, _, sortOf_e, sortsOf_nil, rfl⟩, rfl⟩

theorem lookupIsMkP : cP.lookupFn isMk = some fIsMk := by rfl

/-- **`isMk(mk(e))` is `true` in `cP`**, by `isMk(mk(_)) => true`. -/
theorem isMk_mkE : Eval cP isMk [mkE c] (some (bool true)) :=
  .clause (cl := clMk) (σ := [(0, eVal c)]) lookupIsMkP (by simp [fIsMk])
    (fun i s hs => by
      cases i with
      | zero => cases (show some sE = some s from hs); exact ⟨_, rfl, sortOf_e⟩
      | succ i => cases (show (none : Option Srt) = some s from hs))
    (.cons (.ctor (by decide +kernel) (.cons (.var rfl) .nil)) .nil) (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fIsMk, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

theorem empty : c.subsorts.all (fun p => p.2 != sE) = true ∧ c.collOf sE = none ∧
    c.lib.carriers.all (·.1 != sE) = true ∧
    (sE != Srt.int && sE != Srt.bool && sE != Srt.kconfigVar && sE != Srt.string &&
      sE != Srt.bytes && sE != Srt.float && !c.lib.tokenSorts.contains sE &&
      !c.lib.byteSorts.contains sE) = true := by
  decide +kernel

/-- **`e` is the one value of Empty in `cP`.** -/
theorem value_eq {v : GroundTerm} (h : cP.sortOf v = some sE) : v = eVal c :=
  value_E_eq ctorSigs_E facts.1 noRaw empty.1 empty.2.1 empty.2.2.1 empty.2.2.2 h

/-- A constructor application of `cP` of a sort other than Empty is one of c's constructors: the
added open generator is of sort Empty. -/
theorem ctor_sigP {f : KCore.Sym} {ts : List GroundTerm} {s : Srt} (h : cP.sortOf (.ctor f ts) = some s)
    (hs : s ≠ sE) : ∃ k ∈ c.ctorSigs, k.name = f ∧ cP.sortsOf ts = some k.args ∧ k.result = s := by
  rcases (Semantics.sortOf_ctor_iff cP).mp h with ⟨k, hk, hts, hr⟩ | ⟨-, o, ho, -⟩ | ⟨-, -, kp, hko, -, -, hr⟩
  · rw [lookupSig_eq] at hk
    exact ⟨k, List.mem_of_find?_eq_some hk, by simpa using List.find?_some hk, hts, hr.symm⟩
  · simp [Semantics.lookupOvl, plus_ovls, facts.1] at ho
  · obtain ⟨hm, -, -, -⟩ := Semantics.lookupOpen_spec _ hko
    have hm' : kp ∈ c.params ++ [eParam c sE] := hm
    rw [facts.2.1, List.nil_append, List.mem_singleton] at hm'
    subst hm'
    exact absurd hr hs

/-- **The values of S in `cP`**: `k()` and `mk(e)`. -/
theorem valSP {v : GroundTerm} (h : cP.sortOf v = some sS) : v = .ctor symK [] ∨ v = mkE c := by
  obtain ⟨f, ts, rfl⟩ := ctor_of_sort h subsorts_S dvOK_S colls_SE.1
  obtain ⟨k, hk, hname, hts, hr⟩ := ctor_sigP h (by decide)
  have := List.all_eq_true.mp ctorSigs_S k hk
  simp only [hr, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  rcases this with ⟨hn, ha⟩ | ⟨hn, ha⟩
  · left
    rw [ha] at hts
    cases ts with
    | nil => rw [← hname, hn]
    | cons t ts =>
      simp only [Semantics.sortsOf] at hts
      split at hts <;> cases hts
  · right
    rw [ha] at hts
    cases ts with
    | nil => simp [Semantics.sortsOf] at hts
    | cons t ts =>
      simp only [Semantics.sortsOf] at hts
      split at hts
      · rename_i s ss hs hss
        cases hts
        rw [← hname, hn, value_eq hs, sortsOf_nil_of hss]
        rfl
      · cases hts

/-- `isMk(k())` is `false` in `cP`. -/
theorem eval_isMk_kP : Eval cP isMk [.ctor symK []] (some (bool false)) :=
  .clause (cl := clK) (σ := []) lookupIsMkP (by simp [fIsMk])
    (fun i s hs => by cases (show (none : Option Srt) = some s from hs))
    (.cons (.ctor (by decide +kernel) .nil) .nil) (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fIsMk, List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- **`isMk` is total in `cP`**: it has a value at `k()` and at `mk(e)`. -/
theorem totalP : Total cP isMk := by
  intro fn hfn vs hvs
  rw [lookupIsMkP] at hfn
  cases hfn
  obtain ⟨v, rfl, hv⟩ := EmptyInh.sortsOf_single hvs
  rcases valSP hv with rfl | rfl
  · exact ⟨_, eval_isMk_kP⟩
  · exact ⟨_, isMk_mkE⟩

/-- In `cP` the totality of `isMk` is named, and nothing is owed: with `e`, S is confined. -/
theorem namedP : cP.coreOK = true ∧ cP.heldObligations = [] ∧
    cP.rankObligations [isMk] ++ cP.decObligationsL = [] ∧ cP.totalObligationsRP [isMk] [] = [isMk] ∧
    cP.agreeObligationsI = [] ∧ cP.matchObligationsL = [] ∧ cP.owedRules = [] ∧ cP.owedClauses = [] := by
  decide_cheap

theorem coreP : cP.coreOK = true := namedP.1

theorem openDecidedP : OpenDecided cP :=
  ⟨openRules_of_owed (by rw [namedP.2.2.2.2.2.2.1]; intro i hi; cases hi),
   openClauses_of_owed (by rw [namedP.2.2.2.2.2.2.2]; intro p hp; cases hp)⟩

theorem oblP : FnObligations cP [isMk] [] := by
  obtain ⟨-, -, hterm, htot, hagr, hmat, -, -⟩ := namedP
  refine ⟨fun f hf => (by rw [hterm] at hf; cases hf), fun f hf => ?_, fun f hf => (by rw [hagr] at hf; cases hf),
    fun p hp => (by rw [hmat] at hp; cases hp), openDecidedP, openLawsP⟩
  rw [htot, List.mem_singleton] at hf
  subst hf
  exact totalP

theorem fnHypP : FnHyp cP :=
  fnHyp_of_fnObligationsN coreP (by rw [namedP.2.1]; intro f hf; cases hf) ParamsTotal.nil oblP

/-- **A model of `cP`'s theory with the step's closure, which is one of c's.** -/
theorem model : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc cP ∪ Γstep cP)) ∧ (I ⊧ᴵP (Γc c ∪ Γstep c)) :=
  model_exists sub coreP fnHypP

/-- K := `.`, the counter 0, X := `mk(e)`. -/
noncomputable def σw : Subst := [(0, .ctor dotk []), (1, .ctor counterLabel [.dv Srt.int (.int 0)]), (2, mkE c)]

theorem ws_w : cP.WellSorted r0.vars σw := fun i s hs => by
  match i, hs with
  | 0, hs => cases (show some Srt.k = some s from hs); exact ⟨_, rfl, sortOf_plus (by decide +kernel)⟩
  | 1, hs => cases (show some (19 : Srt) = some s from hs); exact ⟨_, rfl, sortOf_plus (by decide +kernel)⟩
  | 2, hs => cases (show some sS = some s from hs); exact ⟨_, rfl, mkE_sort⟩
  | _ + 3, hs => cases (show (none : Option Srt) = some s from hs)

theorem req_w : EvalTerm cP σw (.app isMk [.var 2]) (some (bool true)) :=
  .call (vs := [mkE c]) (by decide +kernel) (by decide +kernel) (.cons .var .nil) rfl isMk_mkE (by decide +kernel)

def A : Config c := ⟨cfg symA, by decide +kernel⟩
def B : Config c := ⟨cfg symB, by decide +kernel⟩
noncomputable def AP : Config cP := ⟨A.val, sortOf_plus A.property⟩
noncomputable def BP : Config cP := ⟨B.val, sortOf_plus B.property⟩

theorem symsP : cP.isCtor topLabel = true ∧ cP.isCtor kCell = true ∧ cP.isCtor kseq = true ∧
    cP.isCtor symA = true ∧ cP.isCtor symB = true := by
  decide +kernel

/-- **In `cP` the rule 0 steps `<k> a() </k>` to `<k> b() </k>`**, under X := `mk(e)`. -/
theorem stepByP : StepBy cP r0 σw AP BP where
  mem := by rw [show cP.rules = [r0, r1] from rules]; simp
  hσ := ws_w
  hmatch := .ctor symsP.1 (.cons (.ctor symsP.2.1 (.cons (.ctor symsP.2.2.1
      (.cons (.inj (.ctor symsP.2.2.2.1 .nil)) (.cons (.var rfl) .nil))) .nil)) (.cons (.var rfl) .nil))
  hreq := fun t ht => by cases ht; exact req_w
  hpre := .top
  heval := .ctor symsP.1 (.cons (.ctor symsP.2.1 (.cons (.ctor symsP.2.2.1
      (.cons (.inj (.ctor symsP.2.2.2.2 .nil)) (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by cases ht
  hpost := .top
  hprio := fun r' hr' hlt => by
    rw [show cP.rules = [r0, r1] from rules] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)

/-! ## The rule 0 is not refuted -/

/-- **The rule 0 is not `Refuted`**: in the model of `cP`, which is one of c's, the valuation
X ↦ `mk(e)` satisfies `⌈isMk(X) = true⌉`. -/
theorem not_refuted0 : ¬ r0.Refuted c := by
  obtain ⟨M, hM, I, hP, hc⟩ := model
  have hIc : I ⊧ᴵP Γc c := fun φ hφ => hc φ (Or.inl hφ)
  have hΓ : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have hΓcP : I ⊧ᴵP Γc cP := fun φ hφ => hP φ (Or.inl hφ)
  have hΓP : I ⊧ᴵP Γ cP := fun φ hφ => hΓcP φ (Or.inl hφ)
  obtain ⟨-, -, -, -, -, -, -, -, hno⟩ := hypSound_of_core coreOK
  haveI : OvlOK c := hno
  obtain ⟨-, -, -, -, -, -, -, -, hnoP⟩ := hypSound_of_core coreP
  haveI : OvlOK cP := hnoP
  let tbl : VarTable := (List.range 3).map (canonKey cP r0.vars)
  have hkeys : ∀ i < r0.vars.length, canonKey cP r0.vars i ∈ tbl := fun i hi =>
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  let e := overV cP I tbl r0.vars σw KoreAML.val0
  have hag := overV_agrees (e := KoreAML.val0) hΓP hkeys ws_w
  have hts : HoldsShape.TermSound cP I := HoldsShape.termSoundEx (Semantics.coreOK_iff_ex.mp coreP) hΓcP openDecidedP.2
  have hq : ∀ t, r0.req = some t → ∀ b, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r0.vars) t)).interpret I e b ↔
      (den c (bool true)).interpret I e b := by
    intro t ht b
    cases ht
    have h := hts req_w ws_w (canonVars_length _ _) hag
      (show sortOfTerm _ r0.vars (.app isMk [.var 2]) = some Srt.bool by decide +kernel) b
    rw [← termKore_plus_fun (E := sE), ← den_plus (E := sE)]
    exact h
  have hm := reqPat_holds hΓ hq (elemOf_top hΓ A tbl e)
  refine cond_not_refuted_at coreOK hIc (by decide +kernel) rfl (fun i hi hci => ?_) rfl hm
  have h2 : i = 2 := by
    have : r0.condVars = [2] := by decide +kernel
    rw [this, List.mem_singleton] at hci
    exact hci
  subst h2
  show InS I (cP.sortName sS) ((overV cP I tbl r0.vars σw KoreAML.val0).evalEvar (tbl.ev (canonKey cP r0.vars 2)))
  rw [overV_at hkeys (by decide)]
  exact (inS_iff KoreAML.val0).mp (elemOf_spec hΓP mkE_sort KoreAML.val0).2

/-- **The owed `CondDecided` of the rule 0 is false**: it is neither `Witnessed` nor `Refuted`. -/
theorem owed_false : ¬ r0.CondDecided c := fun h => h.elim not_witnessed0 not_refuted0

/-- **`OpenDecided` is false at this text**: the rule 0 needs a witness and its condition is not
decided. -/
theorem not_owed : ¬ OpenDecided c := fun h =>
  owed_false (h.1 r0 (by rw [rules]; simp) (by decide +kernel))

/-! ## Whether `<k> b() </k>` follows `<k> a() </k>` -/

/-- What `vmModelCl` asks of c beside the functions' facts, decided. -/
theorem decided : c.sortedOKCl = true ∧ c.srReady = true ∧ c.faithCoreOK = true ∧
    patHooksApart c = true ∧ c.idsOK = true ∧ c.ovls = [] ∧ c.subsorts.all (fun p => p.1 != p.2) = true := by
  decide_cheap

instance ovl : OvlOK c := OvlOK.of_nil decided.2.2.2.2.2.1 decided.2.2.2.2.2.2

theorem syms : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symC = true := by
  decide +kernel

/-- **`<k> b() </k>` is no successor of `<k> a() </k>` in the value model's step**: the rule 0
applies at no value (X is `k()`, where `isMk` is `false`), and the `[owise]` rule gives `c()`. -/
theorem not_stepV : ¬ StepV c A.val B.val := by
  rintro ⟨r, σ, hr, hσ, -, hreq, -, heval, -⟩
  rw [rules] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · obtain ⟨v, hl, hv⟩ := hσ 2 sS rfl
    rw [valS hv] at hl
    have := EvalTerm.functional_of_fnDet fnDet (hreq _ rfl) (req_false hl)
    simp [KCore.bool] at this
  · obtain ⟨v0, h0, -⟩ := hσ 0 Srt.k rfl
    obtain ⟨v1, h1, -⟩ := hσ 1 19 rfl
    have e0 : EvalTerm c σ (.var 0) (some v0) := by rw [← h0]; exact .var
    have e1 : EvalTerm c σ (.var 1) (some v1) := by rw [← h1]; exact .var
    have hc : EvalTerm c σ r1.rhs
        (some (.ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symC []), v0]], v1])) :=
      .ctor syms.1 (.cons (.ctor syms.2.1 (.cons (.ctor syms.2.2.1
        (.cons (.inj (.ctor syms.2.2.2 .nil)) (.cons e0 .nil))) .nil)) (.cons e1 .nil))
    have := EvalTerm.functional_of_fnDet fnDet heval hc
    simp [B, cfg, symB, symC] at this

/-- **The text determines no answer to whether `<k> b() </k>` follows `<k> a() </k>`**: over all
H, the reading's theory with the step's closure entails neither that `<k> b() </k>` is a successor
of `<k> a() </k>` nor that it is not. At `HookParams.none`, the model of `cP` makes it one (the
rule 0 under X := `mk(e)`, by soundness at `cP`), and the value model of c makes it none. -/
theorem succ_undetermined :
    ¬ (∀ H : HookParams, (Γc (cH H) ∪ Γstep (cH H)) ⊧
        (den (cH H) A.val ⇒ ∼ KoreAML.sNext (den (cH H) B.val))) ∧
    ¬ (∀ H : HookParams, (Γc (cH H) ∪ Γstep (cH H)) ⊧
        (den (cH H) A.val ⇒ KoreAML.sNext (den (cH H) B.val))) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨M, hM, I, hP, hc⟩ := model
    have hΓcP : I ⊧ᴵP Γc cP := fun φ hφ => hP φ (Or.inl hφ)
    have hΓP : I ⊧ᴵP Γ cP := fun φ hφ => hΓcP φ (Or.inl hφ)
    have hD := defOK hΓP
    have hcP : ∀ fn ∈ cP.fns, ∀ cl ∈ fn.clauses, cl.needsWitness cP = true → cl.CondDecided cP := openDecidedP.2
    have h1 := ((sound_hyp cP coreP fnHypP).2 AP BP r0 σw stepByP).1 hΓcP KoreAML.val0 (elemOf cP I A.val)
    have hcl := famEx_closed cP coreP stepByP rfl hcP hΓcP KoreAML.val0 (elemOf cP I A.val)
    rw [KoreAML.interp_equal hD] at hcl
    have hx := ((elemOf_spec hΓP AP.property KoreAML.val0).1 (elemOf cP I A.val)).mpr rfl
    rw [interpret_impl] at h1
    have hn := sNext_congr hcl (h1 hx)
    have h2 := h HookParams.none hc KoreAML.val0 (elemOf cP I A.val)
    rw [cH_none, interpret_impl, interpret_neg] at h2
    rw [show den cP AP.val = den c A.val from den_plus _] at hx
    rw [show den cP BP.val = den c B.val from den_plus _] at hn
    exact h2 hx hn
  · have hm := hypModel_ofCl decided.1 decided.2.1 ovl decided.2.2.1 decided.2.2.2.1 decided.2.2.2.2.1
      fnModel.1 fnModel.2
    have hmod := vmModelCl c decided.1 decided.2.1 decided.2.2.1 decided.2.2.2.1 decided.2.2.2.2.1
      fnModel.1 fnModel.2 (clausePreDecided_of_fnFactsN coreOK (fun f _ => rightHeld.heldOwed f) obl_nil)
      obl_nil.2.2.2.2
    have hsat : stdI_T c (StepV c) ⊧ᴵ (den c A.val ⇒ ∼ KoreAML.sNext (den c B.val)) :=
      Classical.not_not.mp (mt (step_iff_stdI_T c hm (StepV c) A B).mpr not_stepV)
    have h1 := h HookParams.none hmod KoreAML.val0 (.val A.val)
    have h2 := hsat KoreAML.val0 (.val A.val)
    rw [interpret_impl] at h1 h2
    have hx := (den_val_T hm (StepV c) A.val A.property KoreAML.val0 _).mpr rfl
    exact (interpret_neg.mp (h2 hx)) (h1 hx)

end HwEmpty

end OwedGenlessFalse

/-- info: 'OwedGenlessFalse.Genless.owed_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OwedGenlessFalse.Genless.owed_false
/-- info: 'OwedGenlessFalse.Genless.not_owed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OwedGenlessFalse.Genless.not_owed
/--
info: 'OwedGenlessFalse.Genless.succ_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms OwedGenlessFalse.Genless.succ_undetermined
/-- info: 'OwedGenlessFalse.HwEmpty.owed_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OwedGenlessFalse.HwEmpty.owed_false
/-- info: 'OwedGenlessFalse.HwEmpty.not_owed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OwedGenlessFalse.HwEmpty.not_owed
/--
info: 'OwedGenlessFalse.HwEmpty.succ_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms OwedGenlessFalse.HwEmpty.succ_undetermined
