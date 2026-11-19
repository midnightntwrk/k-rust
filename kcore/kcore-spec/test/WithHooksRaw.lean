/-
  The `…_withHooks` statements and a raw parameter (an open generator). `Semantics.rightHeld_withHooks`
  and `ParamsTotal.withHooks` carry a fact of the data to every interpretation of the parameters
  under `hr` (no parameter is raw); each is false without it (`rightHeld_withHooks_needs_hr`,
  `paramsTotal_withHooks_needs_hr`). `Semantics.rightHeld_withHooks_of_valued` has no such hypothesis:
  its instance at a semantics with a raw parameter (`rightHeld_cA`). The statements that take `hr`
  last, filled by `decide +kernel` (`fnHyp_withHooks`, `sound_withHooks`, …), have the binder shape of
  `formA`: a call that leaves the argument out elaborates at a semantics without a raw parameter,
  with H free, and does not at one with a raw parameter.
  Run from the package root: `lake env lean test/WithHooksRaw.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.WithHooksRaw

open KCore

/-! ## The semantics: e2-open-mixed's (test/OpenGenSems.lean, OpenMixed) with one function

`A ::= x | y`, `B ::= A & A` (`and`, raw: B has no constructor), `c : B → KItem`, `d : A → KItem`,
and the function `fM() = c(V:B)`, whose variable V only the right side holds. -/

def ogCellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def ogCellCtors (b : Sym) : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨b, [Srt.k], nRegSorts⟩, ⟨b + 1, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def ogCellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def sA : Srt := nRegSorts + 2
def sB : Srt := nRegSorts + 3
def kS : Sym := nRegSyms + 4
def xS : Sym := nRegSyms + 6
def yS : Sym := nRegSyms + 7
def cS : Sym := nRegSyms + 8
def dS : Sym := nRegSyms + 9
def fS : Sym := nRegSyms + 10
def andS : Sym := nRegSyms + 11

def andP : ParamSig := { sig := ⟨andS, [sA, sA], sB⟩, raw := true }

/-- `fM() = c(V:B)` -/
def clM : Clause := { vars := [sB], pats := [], req := none, rhs := .app cS [.var 0], ens := none }
def fnM : Fn := ⟨fS, [], Srt.kitem, [clM], false⟩

/-- `fA() = d(V:A)`: a right-only variable of a sort with a nullary constructor. -/
def clA : Clause := { vars := [sA], pats := [], req := none, rhs := .app dS [.var 0], ens := none }
def fnA : Fn := ⟨fS, [], Srt.kitem, [clA], false⟩

def base (fn : Fn) : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt", "A", "B"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisA", "LblisB", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblx",
      "Lbly", "Lblc", "Lbld", "LblfM", "Lbland"]
    userSorts := ogCellSorts ++ [sA, sB]
    ctors := ogCellCtors kS ++ [⟨xS, [], sA⟩, ⟨yS, [], sA⟩, ⟨cS, [sB], Srt.kitem⟩, ⟨dS, [sA], Srt.kitem⟩]
    fns := [fn]
    userSubsorts := ogCellSubsorts
    pgmSort := Srt.k
    rules := []
    params := [andP] }

def cM : Semantics := base fnM
def cA : Semantics := base fnA

/-- The interpretation answering `x` (of sort A, not B) at every application of `and`. -/
def Hm : HookParams := ⟨fun f _ => if f == andS then some (.ctor xS []) else none⟩

/-! ## What `coreOK` reads of `cM`, apart from `paramsPlain`'s parameter conjunct -/

/-- Every conjunct of `coreOK` other than `paramsPlain`'s test of the parameters. -/
theorem cM_rest :
    (cM.subsortsOK && cM.fns.all (fun f => f.clauses.all (cM.clauseSorted f (cM.fns.map Fn.sig))) &&
      cM.rules.all cM.ruleSorted && cM.rulesPlain && cM.clausesPlain &&
      cM.faithCoreOK && cM.predsApart && cM.idsOK && cM.overloadsOK) = true := by
  decide_cheap

/-- `paramsPlain`'s test of the parameters (V2.d1-flip), restated: a raw parameter has no
implementation, two arguments of its result sort where it has a law, a number
outside the registry and no name the decoder reads as an instance (`instDecode?`), with `shapesOK`. -/
def paramsRuled (c : Semantics) : Bool :=
  c.params.all (fun k =>
    if k.raw then k.impl.isNone &&
      (!(k.assoc || k.idem) || k.sig.args == [k.sig.result, k.sig.result]) &&
      decide (nRegSyms ≤ k.sig.name) && (instDecode? (c.symName k.sig.name)).isNone &&
      c.shapesOK
    else !k.assoc && !k.idem)

theorem cM_params : paramsRuled cM = true ∧ (cM.params.any (·.raw)) = true := by decide +kernel

/-- `paramsPlain` is `paramsRuled`. -/
example (c : Semantics) : c.paramsPlain = paramsRuled c := rfl

/-- `coreOK` admits it (V2.d1-flip): a semantics with an open generator at which the two transport
lemmas fail without `hr`. -/
theorem cM_coreOK : cM.coreOK = true := by decide_cheap

/-- What `coreOK` gives of `cM`'s open generator: the parameter and the open generator its name
finds, with no hook, no constructor and no overloading symbol of its name (`raw_open_core`), so a
value at every argument list under `HookParams.none` (`openTotal_none`). -/
theorem cM_raw_open : ∀ k ∈ cM.params, k.raw = true → ∃ kp, cM.lookupParam k.sig.name = some kp ∧
    cM.lookupOpen k.sig.name = some kp ∧ kp.sig = k.sig ∧ kp.impl = none ∧
    lookupSig cM.ctorSigs k.sig.name = none ∧ cM.lookupOvl k.sig.name = none :=
  Semantics.raw_open_core cM_coreOK
theorem cM_openTotal_none : OpenTotal (cM.withHooks HookParams.none) := openTotal_none _ cM_coreOK

/-- `cM`'s raw parameter is the open generator `lookupOpen` answers for, and `and(x, x)` is a value
of B at `HookParams.none`. -/
theorem cM_value : (cM.withHooks HookParams.none).sortOf (.ctor andS [.ctor xS [], .ctor xS []]) = some sB ∧
    cM.lookupOpen andS = some andP ∧ cM.isOpenGen (.ctor andP.sig) = true := by decide +kernel

/-! ## `RightHeld` of the data does not give `RightHeld` at `Hm` -/

theorem and_value : cM.sortOf (.ctor andS [.ctor xS [], .ctor xS []]) = some sB := by decide +kernel

theorem rightHeld_cM : cM.RightHeld := by
  intro f hf cl hcl i s hs
  have hf' : f = fnM := by simpa [cM, base] using hf
  subst hf'
  have hcl' : cl = clM := by simpa [fnM] using hcl
  subst hcl'
  have hs' : s = sB := by
    cases i with
    | zero => simpa [clM] using hs.symm
    | succ n => simp [clM] at hs
  subst hs'
  exact Or.inr ⟨_, and_value⟩

theorem genWf_Hm : Faithful.genWf (cM.withHooks Hm) = true := by
  show Faithful.genWf cM = true
  decide +kernel

/-- **No value has sort B at `Hm`.** -/
theorem no_B (v : GroundTerm) : (cM.withHooks Hm).sortOf v ≠ some sB := by
  intro h
  have hctor : ∀ k ∈ cM.ctorSigs, k.result ≠ sB := by decide +kernel
  have hsub : ∀ p ∈ cM.subsorts, p.2 ≠ sB := by decide +kernel
  have hovl : cM.ovls.length = 0 := by decide +kernel
  have hpar : ∀ k ∈ cM.params, k.sig.name = andS := by decide +kernel
  have hcons : sB ∈ Faithful.consSorts (cM.withHooks Hm) := by
    show sB ∈ Faithful.consSorts cM
    decide +kernel
  rcases Faithful.consSort_shape genWf_Hm hcons h with ⟨f, ws, rfl⟩ | ⟨a, b, w0, rfl⟩
  · rcases (Semantics.sortOf_ctor_iff _).mp h with ⟨k, hk, -, hs⟩ | ⟨-, o, ho, -⟩ | ⟨-, -, k, hk, -, hkr, -⟩
    · exact hctor k (lookupSig_spec hk).1 hs.symm
    · obtain ⟨-, i, hi, -⟩ := OvlLaws.lookupOvl_spec ho
      have hi' : i < cM.ovls.length := hi
      omega
    · obtain ⟨hkm, -, hn, -⟩ := Semantics.lookupOpen_spec _ hk
      have hf : f = andS := hn.symm.trans (hpar k hkm)
      subst hf
      have hkr' : (GroundTerm.cmp (.ctor xS []) (.ctor andS ws) == .eq) = true := by
        simpa [Semantics.keepsRaw, Semantics.withHooks, Hm] using hkr
      have := GroundTerm.cmp_eq _ _ (beq_iff_eq.mp hkr')
      injection this with h1 _
      exact absurd h1 (by decide)
  · have hw : (cM.withHooks Hm).subsorts.contains (a, b) = true ∧ b = sB := by
      simp only [Semantics.sortOf] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        exact ⟨hc.1.1, (Option.some.inj h)⟩
      · cases h
    have hm : (a, b) ∈ cM.subsorts := List.contains_iff_mem.mp hw.1
    exact hsub _ hm hw.2

/-- **`RightHeld` fails at `Hm`**: `clM`'s variable is of B, which has no value there, and the
clause's patterns and conditions do not hold it. -/
theorem not_rightHeld_Hm : ¬ (cM.withHooks Hm).RightHeld := by
  intro h
  have hf : fnM ∈ (cM.withHooks Hm).fns := by
    show fnM ∈ cM.fns
    simp [cM, base]
  rcases h fnM hf clM (by simp [fnM]) 0 sB rfl with hl | ⟨v, hv⟩
  · exact absurd hl (by decide +kernel)
  · exact no_B v hv

/-- So `Semantics.rightHeld_withHooks` does not hold without its `hr`. -/
theorem rightHeld_withHooks_needs_hr :
    ¬ ∀ (c : Semantics) (_ : c.RightHeld) (H : HookParams), (c.withHooks H).RightHeld :=
  fun h => not_rightHeld_Hm (h cM rightHeld_cM Hm)

/-! ## The lemma that holds at every interpretation -/

/-- `Semantics.rightHeld_withHooks_of_valued` (RightHeldHooks.lean) is not vacuous: `cA` has a raw
parameter and a right-only variable. -/
theorem rightHeld_cA (H : HookParams) : (cA.withHooks H).RightHeld :=
  Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H

example : (cA.params.any (·.raw)) = true ∧ clA.leftVars = [] := by decide +kernel

/-! ## Form A: a trailing `hr` filled by `decide +kernel` -/

theorem formA {c : Semantics} (hrh : c.RightHeld) (H : HookParams) (_n : Nat)
    (hr : ∀ k ∈ c.params, k.raw = false := by decide +kernel) : (c.withHooks H).RightHeld :=
  Semantics.rightHeld_withHooks hrh H hr

/-- A semantics without a raw parameter, with the same right-only variable. -/
def cP : Semantics := { cA with params := [{ sig := ⟨andS, [sA, sA], sB⟩ }] }

/-- The generated text's shape (`Semantics.rightHeld_of_valued (by decide +kernel)` as the explicit
`RightHeld` argument, H free, the new argument left out) elaborates. -/
example (H : HookParams) : (cP.withHooks H).RightHeld :=
  formA (Semantics.rightHeld_of_valued (by decide +kernel)) H 0

/-! ## Form B: `RightHeld` asked at the interpretation -/

theorem formB {c : Semantics} (H : HookParams) (hrh : (c.withHooks H).RightHeld) (_n : Nat) :
    (c.withHooks H).RightHeld := hrh

-- The same generated text against form B fails: the decided goal names H.
/--
error: Expected type must not contain free variables
  (cP.withHooks H).rightValued = true

Hint: Use the `+revert` option to automatically clean up and revert free variables
-/
#guard_msgs in
example (H : HookParams) : (cP.withHooks H).RightHeld :=
  formB (c := cP) H (Semantics.rightHeld_of_valued (by decide +kernel)) 0

/-- Form A at a semantics with a raw parameter: the default does not close (as it must not). -/
example (H : HookParams) : (cA.withHooks H).RightHeld := by
  fail_if_success exact formA (Semantics.rightHeld_of_valued (by decide +kernel)) H 0
  exact rightHeld_cA H

#print axioms not_rightHeld_Hm
#print axioms rightHeld_cM
#print axioms cM_rest
#print axioms cM_params

/-! ## `ParamsTotal` of the data does not give `ParamsTotal` at the interpretation -/

def pS : Sym := nRegSyms + 12
/-- A parameter `P : → B` that is not raw and that no registry hook implements. -/
def pP : ParamSig := { sig := ⟨pS, [], sB⟩ }
def cQ : Semantics := { cM with params := [andP, pP] }

/-- `P()` is `x & x`, and `x & x` is `x`. -/
def Hq : HookParams := ⟨fun f _ => if f == andS then some (.ctor xS []) else
  if f == pS then some (.ctor andS [.ctor xS [], .ctor xS []]) else none⟩

theorem and_value_Q : cQ.sortOf (.ctor andS [.ctor xS [], .ctor xS []]) = some sB := by decide +kernel
theorem and_value_Hq : (cQ.withHooks Hq).sortOf (.ctor andS [.ctor xS [], .ctor xS []]) = none := by
  decide +kernel

theorem paramsTotal_cQ : ParamsTotal cQ [pS] Hq := by
  intro k hk _ hn vs hvs
  have hk' : k = andP ∨ k = pP := by simpa [cQ] using hk
  rcases hk' with rfl | rfl
  · exact absurd hn (by decide)
  · cases vs with
    | nil => exact ⟨_, rfl, and_value_Q⟩
    | cons v vs =>
      exfalso
      simp only [Semantics.sortsOf] at hvs
      split at hvs <;> cases hvs

theorem not_paramsTotal_Hq : ¬ ParamsTotal (cQ.withHooks Hq) [pS] (cQ.withHooks Hq).hooks := by
  intro h
  have hk : pP ∈ (cQ.withHooks Hq).params := by
    show pP ∈ cQ.params
    simp [cQ]
  obtain ⟨v, hv, hs⟩ := h pP hk rfl (by simp [pP]) [] rfl
  have hv' : v = .ctor andS [.ctor xS [], .ctor xS []] := by
    have : (cQ.withHooks Hq).hooks.app pS [] = some (.ctor andS [.ctor xS [], .ctor xS []]) := by decide +kernel
    exact (Option.some.inj (hv.symm.trans this))
  rw [hv', and_value_Hq] at hs
  cases hs

/-- So `ParamsTotal.withHooks` does not hold without its `hr`. -/
theorem paramsTotal_withHooks_needs_hr :
    ¬ ∀ (c : Semantics) (tp : List Sym) (H : HookParams), ParamsTotal c tp H →
      ParamsTotal (c.withHooks H) tp (c.withHooks H).hooks :=
  fun h => not_paramsTotal_Hq (h cQ [pS] Hq paramsTotal_cQ)

#print axioms paramsTotal_withHooks_needs_hr
#print axioms rightHeld_withHooks_needs_hr

/-- `Semantics.hasValue` counts no raw parameter as a generator: B, whose one generator is the raw
`and`, is outside at every interpretation (`hasValue_withHooks`), and has no value at `Hm`
(`no_B`); A is inside. -/
theorem cM_hasValue : (cM.withHooks Hm).hasValue sB = false ∧ cM.hasValue sB = false ∧
    cM.hasValue sA = true ∧ (cM.withHooks Hm).valueSorts.contains sB = true := by decide +kernel

end KCore.WithHooksRaw
