/-
  `Parse.exRead`'s clauses (`Parse.exClauses`): the clauses of the two instances, and a last
  clause whose premise keeps the binder, `¬∃B:Bool. ⋁ₖ (⌈aₖ[B]⌉ ∧ Pₖ[B])`. Run from the package
  root: `lake env lean -j1 test/ExLastBinder.lean`. Kernel-checked.

  - `eqB`: the equation of fixture `e3-eq-exists-bool-ml` (sentence 246,
    `f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})`, f `total`; a copy of
    test/RhsReader.lean's `HandEx.eqB`, which its `tie` checks against the text). `exRead_eqB`: its clauses are `pre ⌈b⌉ ∧ b = notBool(X)`,
    `rhs b` for b = true, false, and the last with `pre ¬∃B:Bool. (⌈B⌉ ∧ B = notBool(X))`, B the
    index 1, after X. `eqT`: `f() => #Exists B:Bool. (B #And #Not {B #Equals false})`, f `total`;
    the last clause's `pre` is `¬∃B:Bool. (⌈B⌉ ∧ ¬(B = false))`, B the index 0.
  - Each, as the only function of a definition (`cX`, `cT`), is `coreOK` and `coreOKEx`, reads a
    confined sort (`readsConfined`: the last clause's `pre` has a binder) and has `litSort Srt.bool`,
    so `Γcl` holds `boolClosed` (`cX_closed`, `cT_closed`).
  - The results at the fixture (`evalX_mk`, `evalX_inv`): `f(true)` is `false` and `f(false)` is
    `true`, and nothing else. The last clause's `pre` is false at both arguments (`lastX_inv`):
    some element of Bool, `notBool(x)`, gives the right side an element.
  - `FnHyp` holds of `cX` (`fnHypX`, `eval_fixture_fnHyp`): f has a value at each Bool argument (a
    value of Bool is a literal, `boolValues`); two clauses that apply at one argument list are the
    clause of one literal (`appliesX`), so they are coherent (`coherentX`); no clause needs a
    witness, and there is no parameter.
  - The fixtures through the reader (`runFx`, the kompiled texts from the cache `kfix.py` keeps):
    on `e3-eq-exists-bool-ml` the reader's clauses of f (`Parse.clauses?`) are `clsX`, and the
    text is read (`coreOK`, `readsConfined`, `litSort Srt.bool`). The spelling of EX-KPROV F4,
    `f(X) => ?B ensures ?B ==Bool notBool X`, is refused by kompile (fixture `e3-eq-exists-bool`,
    kompile.txt `exit: 113`); `e3-eq-exists-bool-ml` is its `#Exists` spelling. The binder of Int
    (`e3-eq-exists-int-ml`, h not `total`) and f not `total` (`e3-eq-exists-partial-ml`) are not
    EX's: the reader refuses both `manyValuedRightSide (\exists)`; their refusal
    `existentialEquation` and their reading by `Parse.ceRead` are the CE wiring's.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace ExLastBinderTest

open KCore KCore.Parse
open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

/-! ## The reader -/

section Reader
open KoreAML (ev ap srt evar)

/-- f, with its `functional` sentence, of result sort Bool. -/
def N1 : Names := { sorts := [], syms := ["Lblf"], keyFns := [(nRegSyms, "Bool")], fnlSyms := [("Lblf", false)] }

def bS : Kore.KSort := srt "Bool"
def Xp : Kore.Pattern := ev "VarX" bS
def Bp : Kore.Pattern := ev "VarB" bS
def exB (body : Kore.Pattern) : Kore.Pattern := .exist bS (evar "VarB" bS) body

/-- `f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})`. -/
def eqB : RawEqn :=
  ⟨"Lblf", [Xp], none, none, exB (.and bS [Bp, .equals bS bS Bp (ap "LblnotBool'Unds'" [Xp])]), [], none, false⟩

/-- `f() => #Exists B:Bool. (B #And #Not {B #Equals false})`. -/
def eqT : RawEqn :=
  ⟨"Lblf", [], none, none, exB (.and bS [Bp, .not bS (.equals bS bS Bp (.dv bS "false"))]), [], none, false⟩

end Reader

def litT (b : Bool) : Term := .dv Srt.bool (.bool b)
def notX : Term := .app boolNot [.var 0]

/-- The fixture's alternatives: at the literal b, the term b with `b = notBool(X)`; with B the
variable at index 1, the term B with `B = notBool(X)`. -/
def altsX : List (Term × List Cond) :=
  [(litT true, [.equals Srt.bool (litT true) notX]), (litT false, [.equals Srt.bool (litT false) notX])]
def bodyX : List (Term × List Cond) := [(.var 1, [.equals Srt.bool (.var 1) notX])]
def clsX : List Clause := exClauses Srt.bool [Srt.bool] [.var 0] none 50 false altsX bodyX

/-- `eqT`'s alternatives, B at index 0. -/
def altsT : List (Term × List Cond) :=
  [(litT true, [.not (.equals Srt.bool (litT true) (litT false))]),
   (litT false, [.not (.equals Srt.bool (litT false) (litT false))])]
def bodyT : List (Term × List Cond) := [(.var 0, [.not (.equals Srt.bool (.var 0) (litT false))])]
def clsT : List Clause := exClauses Srt.bool [] [] none 50 false altsT bodyT

/-- **`exRead` on the fixture's equation, in the kernel.** -/
theorem exRead_eqB : exRead N1 eqB = .ok (some (clsX, [⟨"X", "Bool"⟩])) := by kernel_rfl

theorem exRead_eqT : exRead N1 eqT = .ok (some (clsT, [])) := by kernel_rfl

/-- A clause of f over `[X:Bool]`. -/
def clX (rhs : Term) (ens : Option Term) (pre : Cond) : Clause :=
  { vars := [Srt.bool], pats := [.var 0], req := none, rhs, ens, prio := 50, aside := false, pre }

/-- `⌈b⌉ ∧ (b = notBool(X))`. -/
def preI (b : Bool) : Cond := .and (.ceil Srt.bool (litT b)) (.equals Srt.bool (litT b) notX)
/-- `⌈B⌉ ∧ (B = notBool(X))`, B the binder's variable. -/
def bodyC : Cond := .and (.ceil Srt.bool (.var 1)) (.equals Srt.bool (.var 1) notX)
def lastPre : Cond := .not (.ex Srt.bool bodyC)

/-- The clauses written out. -/
theorem clsX_eq : clsX = [clX (litT true) none (preI true), clX (litT false) none (preI false),
    clX (litT true) (some (litT false)) lastPre] := rfl

theorem clsT_last : clsT.getLast? = some
    { vars := [], pats := [], req := none, rhs := litT true, ens := some (litT false), prio := 50, aside := false,
      pre := .not (.ex Srt.bool (.and (.ceil Srt.bool (.var 0)) (.not (.equals Srt.bool (.var 0) (litT false))))) } := rfl

/-! ## The definitions -/

def Fs : Sym := nRegSyms + 4

def mk (f : Fn) : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [f]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

def fX : Fn := ⟨Fs, [Srt.bool], Srt.bool, clsX, true⟩
def cX : Semantics := mk fX
def cT : Semantics := mk ⟨Fs, [], Srt.bool, clsT, true⟩

theorem cX_coreOK : cX.coreOK = true := by decide +kernel
theorem cX_coreOKEx : cX.coreOKEx = true := by decide +kernel
theorem cX_reads : cX.readsConfined = true := by decide +kernel
theorem cX_lit : cX.litSort Srt.bool = true := by decide +kernel
theorem cX_closed : Faithful.Γcl cX (Faithful.boolClosed cX) := ⟨cX_reads, cX_lit, rfl⟩

theorem cT_coreOK : cT.coreOK = true := by decide +kernel
theorem cT_coreOKEx : cT.coreOKEx = true := by decide +kernel
theorem cT_reads : cT.readsConfined = true := by decide +kernel
theorem cT_lit : cT.litSort Srt.bool = true := by decide +kernel
theorem cT_closed : Faithful.Γcl cT (Faithful.boolClosed cT) := ⟨cT_reads, cT_lit, rfl⟩

/-! ## `Eval`'s results at the fixture -/

theorem lookupX : cX.lookupFn Fs = some fX := by rw [Semantics.lookupFn_eq]; rfl

theorem kindsX : cX.isCtor boolNot = false ∧ isHook boolNot = true ∧ cX.isOvl boolNot = false := by
  decide +kernel

theorem notRes (x : Bool) : cX.hookRes boolNot [bool x] = some (some (bool !x)) := by
  cases x <;> rfl

theorem allSome1 (a : GroundTerm) : allSome [some a] = some [a] := rfl

/-- `notBool(X)` is `!x` where X is x. -/
theorem notX_mk {σ : Subst} {x : Bool} (hl : σ.lookup 0 = some (bool x)) :
    EvalTerm cX σ notX (some (bool !x)) :=
  .hook kindsX.1 kindsX.2.1 (.cons .var .nil)
    (fun vs hvs => by
      rw [hl] at hvs
      have hv : vs = [bool x] := Option.some.inj (hvs.symm.trans (allSome1 _))
      subst hv; exact notRes x)
    (fun hn => by rw [hl] at hn; exact absurd (hn.symm.trans (allSome1 _)) (by simp))

/-- `notBool(X)` has no other result. -/
theorem notX_inv {σ : Subst} {x : Bool} (hl : σ.lookup 0 = some (bool x)) {w : Option GroundTerm}
    (h : EvalTerm cX σ notX w) : w = some (bool !x) := by
  cases h with
  | ctor hk _ => exact absurd (kindsX.1.symm.trans hk) (by simp)
  | hook _ _ hts hh _ =>
    cases hts with
    | cons h1 hs =>
      cases hs; cases h1
      rw [hl] at hh
      exact Option.some.inj ((hh _ (allSome1 _)).symm.trans (notRes x))
  | param _ hhk _ _ _ => exact absurd (kindsX.2.1.symm.trans hhk) (by simp)
  | call _ hhk _ _ _ _ => exact absurd (kindsX.2.1.symm.trans hhk) (by simp)
  | callUndef _ hhk _ _ _ => exact absurd (kindsX.2.1.symm.trans hhk) (by simp)
  | ovl _ ho _ _ => exact absurd (kindsX.2.2.symm.trans ho) (by simp)
  | ovlFn _ ho _ _ _ _ _ => exact absurd (kindsX.2.2.symm.trans ho) (by simp)

/-- The truth value of `b = !x`. -/
def bEq (b x : Bool) : Bool := sameResult (some (bool b)) (some (bool !x))

theorem bEq_iff (b x : Bool) : bEq b x = true ↔ b = !x := by cases b <;> cases x <;> decide

/-- The instance's premise at X := x has the truth value `b = !x`. -/
theorem preI_mk {σ : Subst} {x : Bool} (hl : σ.lookup 0 = some (bool x)) (b : Bool) :
    Holds cX 1 σ (preI b) (bEq b x) := by
  have h := Holds.and (n := 1) (Holds.ceil (s := Srt.bool) (EvalTerm.dv (c := cX) (σ := σ) (s := Srt.bool) (lit := .bool b)))
    (Holds.equals (s := Srt.bool) (EvalTerm.dv (c := cX) (σ := σ) (s := Srt.bool) (lit := .bool b)) (notX_mk hl))
  exact h

theorem preI_inv {σ : Subst} {x b r : Bool} (hl : σ.lookup 0 = some (bool x)) (h : Holds cX 1 σ (preI b) r) :
    r = bEq b x := by
  cases h with
  | and h1 h2 =>
    cases h1 with
    | ceil e1 =>
      cases h2 with
      | equals e2 e3 =>
        rw [EvalTerm.dv_inv e1, EvalTerm.dv_inv e2, notX_inv hl e3]
        rfl

/-- The binder's body under σ', B the index 1: `⌈B⌉ ∧ B = notBool(X)`. -/
def gB (x : Bool) (σ' : Subst) : Bool := (σ'.lookup 1).isSome && sameResult (σ'.lookup 1) (some (bool !x))

theorem bodyC_mk {σ' : Subst} {x : Bool} (hl : σ'.lookup 0 = some (bool x)) :
    Holds cX 2 σ' bodyC (gB x σ') :=
  Holds.and (Holds.ceil .var) (Holds.equals .var (notX_mk hl))

theorem bodyC_inv {σ' : Subst} {x r : Bool} (hl : σ'.lookup 0 = some (bool x)) (h : Holds cX 2 σ' bodyC r) :
    r = gB x σ' := by
  cases h with
  | and h1 h2 =>
    cases h1 with
    | ceil e1 =>
      cases h2 with
      | equals e2 e3 =>
        rw [EvalTerm.var_inv e1, EvalTerm.var_inv e2, notX_inv hl e3]; rfl

/-- The extension of σ by B := `!x`. -/
def ext (x : Bool) (σ : Subst) : Subst := (1, bool !x) :: σ

theorem sameBool (b : Bool) : sameResult (some (bool b)) (some (bool b)) = true := by cases b <;> decide

theorem gB_ext (x : Bool) (σ : Subst) : gB x (ext x σ) = true := by
  have hlk : (ext x σ).lookup 1 = some (bool !x) := rfl
  simp only [gB, hlk, Option.isSome_some, Bool.true_and, sameBool]

theorem ext_extends (x : Bool) (σ : Subst) : Extends cX 1 [Srt.bool] σ (ext x σ) := by
  refine ⟨fun i hi => ?_, fun j s hs => ?_⟩
  · have : i = 0 := by omega
    subst this; rfl
  · cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      exact ⟨bool !x, rfl, sortOf_bool _⟩
    | succ j => simp at hs

/-- **The last clause's premise is false where X is a literal**: B := `notBool(x)` gives the body. -/
theorem lastX_mk {σ : Subst} {x : Bool} (hl : σ.lookup 0 = some (bool x)) : Holds cX 1 σ lastPre false := by
  have hex : Holds cX 1 σ (.ex Srt.bool bodyC) true := by
    refine Holds.ex (gB x) (fun σ' he => bodyC_mk ((he.1 0 (by omega)).trans hl)) ?_
    exact ⟨fun _ => ⟨ext x σ, ext_extends x σ, gB_ext x σ⟩, fun _ => rfl⟩
  exact Holds.not hex

theorem lastX_inv {σ : Subst} {x r : Bool} (hl : σ.lookup 0 = some (bool x)) (h : Holds cX 1 σ lastPre r) :
    r = false := by
  cases h with
  | not h =>
    cases h with
    | ex g hb hr =>
      have hg := bodyC_inv (σ' := ext x σ) hl (hb (ext x σ) (ext_extends x σ))
      have h1 : g (ext x σ) = true := by rw [hg]; exact gB_ext x σ
      have := hr.mpr ⟨_, ext_extends x σ, h1⟩
      subst this; rfl

/-- The substitution that gives X the value v. -/
def sg (v : GroundTerm) : Subst := [(0, v)]

theorem sg_sortedAt (x : Bool) (is : List Nat) : cX.WellSortedAt [Srt.bool] is (sg (bool x)) := by
  intro i _ s hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨bool x, rfl, sortOf_bool _⟩
  | succ i => simp at hs

theorem sg_sorted (x : Bool) : cX.WellSorted [Srt.bool] (sg (bool x)) := by
  intro i s hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨bool x, rfl, sortOf_bool _⟩
  | succ i => simp at hs

theorem sg_match (v : GroundTerm) : PatVals cX (sg v) [.var 0] [v] := .cons (.var rfl) .nil

theorem match0 {σ : Subst} {vs : List GroundTerm} (h : PatVals cX σ [.var 0] vs) :
    ∃ v, vs = [v] ∧ σ.lookup 0 = some v := by
  obtain ⟨v, vs', rfl, hv, hs⟩ := PatVals.cons_inv h
  rw [PatVals.nil_inv hs]
  exact ⟨v, rfl, PatVal.var_inv hv⟩

theorem clX_of {cl : Clause} (h : cl ∈ fX.clauses) :
    cl = clX (litT true) none (preI true) ∨ cl = clX (litT false) none (preI false) ∨
      cl = clX (litT true) (some (litT false)) lastPre := by
  simpa [fX, clsX_eq] using h

theorem prio_none {d : Semantics} {vs : List GroundTerm} {cl : Clause} (hcl : cl ∈ fX.clauses) :
    ∀ cl' ∈ fX.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails d vs cl' := by
  intro cl' hcl' _ hlt
  rcases clX_of hcl with rfl | rfl | rfl <;> rcases clX_of hcl' with rfl | rfl | rfl <;>
    exact absurd hlt (by decide)

theorem litT_mem (b : Bool) : clX (litT b) none (preI b) ∈ fX.clauses := by
  cases b <;> simp [fX, clsX_eq]

/-- **`f(x)` is `notBool(x)`**, by the clause of the literal `!x`. -/
theorem evalX_mk (x : Bool) : Eval cX Fs [bool x] (some (bool !x)) := by
  have hp := preI_mk (σ := sg (bool x)) (x := x) rfl (!x)
  rw [(bEq_iff (!x) x).mpr rfl] at hp
  exact .clause (cl := clX (litT !x) none (preI !x)) lookupX (litT_mem _) (sg_sorted x) (sg_match _)
    (fun t ht => nomatch ht) hp (prio_none (litT_mem _)) rfl .dv (fun t ht => nomatch ht) .top

/-- **`f(x)` has no other result**: the other literal's clause and the last clause do not apply. -/
theorem evalX_inv {x : Bool} {r : Option GroundTerm} (h : Eval cX Fs [bool x] r) : r = some (bool !x) := by
  cases h with
  | clause hfn hcl _ hm _ hpre _ _ hrhs _ _ =>
    obtain rfl := Option.some.inj (lookupX.symm.trans hfn)
    rcases clX_of hcl with rfl | rfl | rfl <;> obtain ⟨w, hw, hl⟩ := match0 hm <;> cases hw
    · have hb := (bEq_iff true x).mp (preI_inv hl hpre).symm
      rw [EvalTerm.dv_inv hrhs, hb]; rfl
    · have hb := (bEq_iff false x).mp (preI_inv hl hpre).symm
      rw [EvalTerm.dv_inv hrhs, hb]; rfl
    · exact absurd (lastX_inv hl hpre) (by simp)
  | rest hfn hnone =>
    obtain rfl := Option.some.inj (lookupX.symm.trans hfn)
    cases hnone _ (litT_mem (!x)) with
    | intro hf =>
      cases hf (sg (bool x)) (sg_sortedAt x _) (sg_match _) with
      | intro ht _ _ => cases ht
      | pre hp =>
        have := (bEq_iff (!x) x).mpr rfl
        rw [← preI_inv (σ := sg (bool x)) rfl hp] at this
        exact absurd this (by simp)
  | ensFails hfn hcl _ hm _ hpre _ _ ht _ _ =>
    obtain rfl := Option.some.inj (lookupX.symm.trans hfn)
    rcases clX_of hcl with rfl | rfl | rfl <;> obtain ⟨w, hw, hl⟩ := match0 hm <;> cases hw
    · cases ht
    · cases ht
    · exact absurd (lastX_inv hl hpre) (by simp)
  | clauseEx hfn hcl _ _ _ _ _ hne _ _ _ _ =>
    obtain rfl := Option.some.inj (lookupX.symm.trans hfn)
    rcases clX_of hcl with rfl | rfl | rfl <;> exact absurd rfl hne
  | exNone hfn hcl hne _ _ _ _ _ _ _ =>
    obtain rfl := Option.some.inj (lookupX.symm.trans hfn)
    rcases clX_of hcl with rfl | rfl | rfl <;> exact absurd rfl hne

/-- **EX-KPROV D3's expectation**: `f(true)` is `false` and `f(false)` is `true`, nothing else. -/
theorem eval_fixture :
    (Eval cX Fs [bool true] (some (bool false)) ∧ ∀ r, Eval cX Fs [bool true] r → r = some (bool false)) ∧
    (Eval cX Fs [bool false] (some (bool true)) ∧ ∀ r, Eval cX Fs [bool false] r → r = some (bool true)) :=
  ⟨⟨evalX_mk true, fun _ h => evalX_inv h⟩, ⟨evalX_mk false, fun _ h => evalX_inv h⟩⟩

/-! ## `FnHyp` -/

/-- A value of Bool is a literal: `cX` gives Bool its literals only. -/
theorem boolX {v : GroundTerm} (hv : cX.sortOf v = some Srt.bool) : ∃ x, v = bool x :=
  boolValues cX_coreOK cX_lit hv

theorem mem_fns {fn : Fn} (h : fn ∈ cX.fns) : fn = fX := by simpa [cX, mk] using h

/-- **A clause of f that applies at an argument list**: the argument is a literal x, X is x, and the
clause is that of the literal `!x`; the other literal's clause and the last clause do not apply. -/
theorem appliesX {cl : Clause} (hcl : cl ∈ fX.clauses) {σ : Subst} {vs : List GroundTerm}
    (h : cl.AppliesAt cX σ vs) :
    ∃ x, vs = [bool x] ∧ σ.lookup 0 = some (bool x) ∧ cl = clX (litT !x) none (preI !x) := by
  obtain ⟨hs, hm, -, hpre⟩ := h
  have hp : cl.pats = [.var 0] := by rcases clX_of hcl with rfl | rfl | rfl <;> rfl
  rw [hp] at hm
  obtain ⟨v, rfl, hl⟩ := match0 hm
  have h0 : ∃ w, σ.lookup 0 = some w ∧ cX.sortOf w = some Srt.bool := by
    rcases clX_of hcl with rfl | rfl | rfl <;> exact hs 0 (by decide) Srt.bool rfl
  obtain ⟨w, hw, hws⟩ := h0
  rw [hl] at hw
  obtain rfl := Option.some.inj hw
  obtain ⟨x, rfl⟩ := boolX hws
  refine ⟨x, rfl, hl, ?_⟩
  rcases clX_of hcl with rfl | rfl | rfl
  · have := (bEq_iff true x).mp (preI_inv hl hpre).symm
    rw [← this]
  · have := (bEq_iff false x).mp (preI_inv hl hpre).symm
    rw [← this]
  · exact absurd (lastX_inv hl hpre) (by simp)

/-- **Any two clauses of f are coherent**: where both apply at one argument list they are one
clause, whose right side is a literal. -/
theorem coherentX {cl cl' : Clause} (hcl : cl ∈ fX.clauses) (hcl' : cl' ∈ fX.clauses) : Coherent cX cl cl' := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨x, hv, -, rfl⟩ := appliesX hcl ha
  obtain ⟨x', hv', -, rfl⟩ := appliesX hcl' ha'
  rw [hv] at hv'
  have : x' = x := by cases x <;> cases x' <;> first | rfl | exact absurd hv' (by decide)
  subst this
  left
  refine ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht => nomatch ht⟩
  cases x' <;> simp [clX, litT, varOccs] at hi

theorem noWitX : ∀ fn ∈ cX.fns, ∀ cl ∈ fn.clauses, cl.needsWitness cX = false := by decide +kernel

/-- **`FnHyp` holds of `cX`**: f has a result, a value, at each Bool argument (`evalX_mk`), its
clauses are coherent (`coherentX`), no clause needs a witness, and there is no parameter. -/
theorem fnHypX : FnHyp cX := by
  have hres : ∀ vs, cX.sortsOf vs = some fX.args → ∃ x, vs = [bool x] := fun vs hvs => by
    obtain ⟨v, rfl, hv⟩ := Faithful.Model.sortsOf_single hvs
    obtain ⟨x, rfl⟩ := boolX hv
    exact ⟨x, rfl⟩
  refine ⟨fun fn hfn vs hvs => ?_, fun fn hfn _ vs hvs => ?_, fun fn hfn => ?_, fun fn hfn cl hcl => ?_, ?_, ?_⟩
  · obtain rfl := mem_fns hfn
    obtain ⟨x, rfl⟩ := hres vs hvs
    exact ⟨_, evalX_mk x⟩
  · obtain rfl := mem_fns hfn
    obtain ⟨x, rfl⟩ := hres vs hvs
    exact ⟨_, evalX_mk x⟩
  · obtain rfl := mem_fns hfn
    intro cl cl' hp _
    obtain ⟨h1, h2⟩ := mem_of_mem_pairs hp
    exact ⟨coherentX h1 h2, coherentX h2 h1⟩
  · obtain rfl := mem_fns hfn
    have hx : cl.exs = [] := by rcases clX_of hcl with rfl | rfl | rfl <;> rfl
    exact (matchIndependent_iff_noExs hx).mpr (coherentX hcl hcl)
  · exact openDecided_of_coreCl cX_coreOK (fun r hr => by simp [cX, mk] at hr)
      (fun fn hfn cl hcl hw => absurd hw (by rw [noWitX fn hfn cl hcl]; decide))
  · exact openLaws_of_plain (fun k hk => by simp [cX, mk] at hk)

/-- **EX-KPROV D3's expectation, with `FnHyp`**: `f(true)` is `false` and `f(false)` is `true`,
nothing else, and the statements' hypothesis on the functions holds. -/
theorem eval_fixture_fnHyp :
    ((Eval cX Fs [bool true] (some (bool false)) ∧ ∀ r, Eval cX Fs [bool true] r → r = some (bool false)) ∧
    (Eval cX Fs [bool false] (some (bool true)) ∧ ∀ r, Eval cX Fs [bool false] r → r = some (bool true))) ∧
    FnHyp cX :=
  ⟨eval_fixture, fnHypX⟩

/-! ## The fixtures through the reader -/

/-- The cache of kompiled fixture texts, as test/constructs/kfix.py names it. -/
def cacheDir : IO String := do
  let get := fun (n : String) => do
    match ← IO.getEnv n with
    | some d => pure (if d.isEmpty then none else some d)
    | none => pure none
  if let some d ← get "KCORE_KFIX_CACHE" then return d
  if let some d ← get "XDG_CACHE_HOME" then return s!"{d}/kcore-kfix"
  let home := (← get "HOME").getD "."
  return s!"{home}/.cache/kcore-kfix"

/-- The kompiled text of fixture `n`, its `BUILTIN/` and `FIXTURE/` paths restored to made-up
directories (as `kfix.py accounts` restores them before reading). -/
def load (n : String) : IO Kore.Definition := do
  let t ← IO.FS.readFile s!"test/constructs/fixtures/{n}/kompile.txt"
  let some l := (t.splitOn "\n").find? (·.startsWith "definition.kore sha256: ")
    | throw (IO.userError s!"{n}: kompile.txt names no sha256")
  let sha := (l.splitOn ": ").getD 1 ""
  let raw ← IO.FS.readFile s!"{← cacheDir}/{sha}.kore"
  let raw := ((raw.replace "BUILTIN/" "/made-up-k/include/kframework/builtin/").replace "FIXTURE/" "/made-up-fx/").replace
    "FIXTURE" "/made-up-fx"
  match Kore.parseDefinition raw with
  | .ok k => pure k
  | .error e => throw (IO.userError s!"{n}: KORE read error {e}")

/-- The clauses the reader gives the equations of `fn` in fixture `n` (`Parse.clauses?`), whether
they are `clsX`, and `parse`'s verdict on the text. -/
def runFx (n fn : String) : IO Unit := do
  let k ← load n
  let some m := k.modules.getLast? | IO.println s!"{n}: no module"
  let S := scan m.sentences
  match envOf m S with
  | .error f => IO.println s!"{n}: envOf fails {f.reason.name}"
  | .ok E =>
    for e in S.eqs.filter (·.fn == fn) do
      match clauses? E.N E.src e none with
      | .ok xs => IO.println s!"{n} {fn}: {xs.length} clauses; clsX: {reprStr (xs.map (·.1)) == reprStr clsX}"
      | .error f => IO.println s!"{n} {fn}: refused {f.reason.name} ({f.detail})"
  match Parse.parse k with
  | .error r => IO.println s!"  parse: refused {r.reason.name} ({r.detail})"
  | .ok d => IO.println s!"  parse: read; coreOK {d.sem.coreOK}; readsConfined {d.sem.readsConfined}; litSort Bool {d.sem.litSort Srt.bool}"

/--
info: e3-eq-exists-bool-ml Lblf: 3 clauses; clsX: true
  parse: read; coreOK true; readsConfined true; litSort Bool true
e3-eq-exists-int-ml Lblh: refused manyValuedRightSide (\exists)
  parse: refused manyValuedRightSide (\exists)
e3-eq-exists-partial-ml Lblf: refused manyValuedRightSide (\exists)
  parse: refused manyValuedRightSide (\exists)
-/
#guard_msgs in
#eval show IO Unit from do
  runFx "e3-eq-exists-bool-ml" "Lblf"
  runFx "e3-eq-exists-int-ml" "Lblh"
  runFx "e3-eq-exists-partial-ml" "Lblf"

end ExLastBinderTest

/-- info: 'ExLastBinderTest.exRead_eqB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExLastBinderTest.exRead_eqB
/-- info: 'ExLastBinderTest.exRead_eqT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExLastBinderTest.exRead_eqT
/-- info: 'ExLastBinderTest.cX_closed' depends on axioms: [propext] -/
#guard_msgs in #print axioms ExLastBinderTest.cX_closed
/-- info: 'ExLastBinderTest.cX_coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExLastBinderTest.cX_coreOK
/-- info: 'ExLastBinderTest.cX_coreOKEx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExLastBinderTest.cX_coreOKEx
/-- info: 'ExLastBinderTest.cT_closed' depends on axioms: [propext] -/
#guard_msgs in #print axioms ExLastBinderTest.cT_closed
/-- info: 'ExLastBinderTest.cT_coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExLastBinderTest.cT_coreOK
/-- info: 'ExLastBinderTest.cT_coreOKEx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExLastBinderTest.cT_coreOKEx
/-- info: 'ExLastBinderTest.eval_fixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExLastBinderTest.eval_fixture
/-- info: 'ExLastBinderTest.fnHypX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExLastBinderTest.fnHypX
/-- info: 'ExLastBinderTest.eval_fixture_fnHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExLastBinderTest.eval_fixture_fnHyp
