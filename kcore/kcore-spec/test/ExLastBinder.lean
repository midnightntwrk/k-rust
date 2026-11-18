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
