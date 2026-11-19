/-
  Witness W1 of findings/work/decision-kk-cb-hyp.md section 1: C13 (`KK.collFormOK`, encodable's
  eleventh conjunct) is not implied by `execReady` and the ten older conditions of `encodable`, and
  at the definition below kore.k's collection construction has a value where KCore's has none.

  `sem key`: a map collection `M` with key sort `key` and value sort `C`, its unit `uM`, element `eM`
  and concatenation `cM` parameters implemented by the library's map symbols; the element declared
  `eM : B, C → M`; constructors `b : B`, `c : C`, `t1 : Tp`, `t2 : M → Tp`; one rule, in a k cell
  holding a `Tp`, `t1 => t2(eM(b, c))`. `d` is `sem A` (key sort `A`, unrelated to `B`); the control
  `dB` is `sem B`, the same text but for the key sort.

  At `d`:
  - `execReady` and the ten older conditions hold (`ready`, `older`); `collFormOK` is false, by its
    `collsOK` conjunct alone (`collForm`): `eM`'s declared arguments are not the collection's
    `[key, val]`.
  - KCore: the element's arguments have their declared sorts (`args_sorted`), and `paramVal` keeps
    no value there (`paramVal_none`): the map `MAP.element` builds has an entry whose key has sort
    `B`, not `A`, so it has no sort, and the filter by the declared result sort drops it. At the
    control the same call has a value (`paramVal_control`): the `none` is the key sort's.
    So at the configuration holding `t1` the rule's left side matches (`lhs_matches`) and its right
    side has no value (`rhs_none`), and there is no `Step` successor in `d₀ d` (`no_step`), while
    at the control there is one (`step_control`).
  - kore.k: the rule's right side is written with the construction `cb(map, M, ps)`
    (`encTerm_rhs`), and `colOf` at those parts is a collection, not `bot` (`colOf_parts`). The
    encoding reads no key sort: the rule is written the same at `d` and at `dB` (`encRl_same`).
  Without C13 `encDef d` would hold that rule, and kore.k's `succs` would list a successor of the
  configuration that is no `Step` of `d₀ d`; with C13 `encDef d = none` (`encDef_none`).

  Here rather than in test/: `colOfF`, kore.k's `colOf` as a Lean function, is User.HelpColl's.
  Run with gen/build.sh --only examples/ref-kk User.C13Witness.
-/
import User.HelpColl
import KcoreSpec.KKEncDef
import KcoreSpec.CollExecFinal

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.KK.C13Witness

open KCore

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
/-- The k cell, holding a `Tp`. -/
def kc : Sym := nRegSyms + 50
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def A : Srt := nRegSorts + 2
def B : Srt := nRegSorts + 3
def C : Srt := nRegSorts + 4
def M : Srt := nRegSorts + 5
def Tp : Srt := nRegSorts + 6

def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨kc, [Tp], nRegSorts⟩, ⟨nRegSyms + 51, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]

def b : Sym := nRegSyms + 100
def c : Sym := nRegSyms + 101
def t1 : Sym := nRegSyms + 102
def t2 : Sym := nRegSyms + 103
def uM : Sym := nRegSyms + 110
def eM : Sym := nRegSyms + 111
def cM : Sym := nRegSyms + 112

/-- `<k> t1 </k> => <k> t2(eM(b, c)) </k>`, the counter cell a variable. -/
def rule : Rule :=
  ⟨[Srt.counter], .app topLabel [.app kc [.app t1 []], .var 0], none,
    .app topLabel [.app kc [.app t2 [.app eM [.app b [], .app c []]]], .var 0], none, 50, [], .top, .top⟩

/-- The definition, with the map collection's key sort `key`. -/
def sem (key : Srt) : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts ++ [A, B, C, M, Tp]
  ctors := cellCtors ++ [⟨b, [], B⟩, ⟨c, [], C⟩, ⟨t1, [], Tp⟩, ⟨t2, [M], Tp⟩]
  fns := []
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := [rule]
  params := [{ sig := ⟨uM, [], M⟩, impl := some mapUnit }, { sig := ⟨eM, [B, C], M⟩, impl := some mapElem },
    { sig := ⟨cM, [M, M], M⟩, impl := some mapConcat }]
  colls := [⟨M, .map, key, some C, uM, eM, cM⟩]

/-- The witness: the collection's key sort `A`, the element declared at `B`. -/
def d : Semantics := sem A
/-- The control: the collection's key sort `B`. -/
def dB : Semantics := sem B

/-! ## The conditions -/

theorem ready : CExec.execReady d = true := by decide +kernel

/-- The ten conditions of `encodable` before C13. -/
theorem older : ovlsOK d = true ∧ paramsOK d = true ∧ appsOK d = true ∧ headsOK d = true ∧
    litsOK d = true ∧ subsortsOK d = true ∧ colPatsOK d = true ∧ asOK d = true ∧ ensOK d = true ∧
    shapesOK d = true := by
  decide +kernel

/-- C13 fails, by `collsOK` alone. -/
theorem collForm : collFormOK d = false ∧ Faithful.collsOK d = false ∧ Faithful.collSortsOK d = true ∧
    d.ctorSigs.all (fun k => (d.collOf k.result).isNone) = true ∧
    d.subsorts.all (fun p => (d.collOf p.2).isNone) = true := by
  decide +kernel

theorem encDef_none : encDef d = none := by
  have h : encodable d = false := by decide +kernel
  simp [encDef, h]

/-- The control passes every condition. -/
theorem control_ok : CExec.execReady dB = true ∧ encodable dB = true := by decide +kernel

/-! ## KCore: the element has no value, so the rule gives no step -/

def gb : GroundTerm := .ctor b []
def gc : GroundTerm := .ctor c []

theorem args_sorted : (d₀ d).sortsOf [gb, gc] = some [B, C] := by decide +kernel

theorem paramVal_none : (d₀ d).paramVal eM [gb, gc] = none := by decide +kernel

theorem paramVal_control : (d₀ dB).paramVal eM [gb, gc] = some (.map M [(gb, gc)]) := by decide +kernel

/-- The configuration with `t1` in the k cell. -/
def cfg : GroundTerm := .ctor topLabel [.ctor kc [.ctor t1 []], .ctor counterLabel [KCore.int 0]]

def cfgD : Config (d₀ d) := ⟨cfg, by decide +kernel⟩

/-- The left side matches the configuration, the counter bound, and the rule applies (`some true`:
no `requires`). -/
theorem lhs_matches : CExec.ruleMatches (d₀ d) 20 rule cfg =
    [([(0, .ctor counterLabel [KCore.int 0])], some true)] := by
  decide +kernel

/-- At that match the right side has no value (`some none`: evaluated, undefined, not out of fuel). -/
theorem rhs_none : CExec.evalT (d₀ d) 20 [(0, .ctor counterLabel [KCore.int 0])] rule.rhs = some none := by
  decide +kernel

/-- No `Step` from the configuration holding `t1`: the rule applies and its right side has no
value (`lhs_matches`, `rhs_none`). -/
theorem no_step (y : Config (d₀ d)) : ¬ Step (d₀ d) cfgD y :=
  CExec.noStep_at (n := 20) ((CExec.execReady_withHooks d _).trans ready)
    (Faithful.fnDet_of_agree (fun _ h => by cases h) (fun _ h => by cases h))
    (by decide +kernel) (by decide +kernel) y

def cfgB : Config (d₀ dB) := ⟨cfg, by decide +kernel⟩

/-- The control's successor: `t2` of the one-entry map. -/
def nextB : Config (d₀ dB) :=
  ⟨.ctor topLabel [.ctor kc [.ctor t2 [.map M [(gb, gc)]]], .ctor counterLabel [KCore.int 0]], by decide +kernel⟩

/-- At the control the rule steps, to `t2` of the one-entry map. -/
theorem step_control : Step (d₀ dB) cfgB nextB :=
  (CExec.step_iff_at (n := 20) ((CExec.execReady_withHooks dB _).trans control_ok.1)
    (Faithful.fnDet_of_agree (fun _ h => by cases h) (fun _ h => by cases h))
    (by decide +kernel)).mpr (by decide +kernel)

/-! ## kore.k: the construction has a value -/

/-- The parts `encCollWith` writes for `eM(b, c)`: one entry. -/
def ps : List T := [.kv (.ap (b : Int) []) (.ap (c : Int) [])]

theorem encTerm_rhs : encTerm d rule.rhs =
    some (.ap (topLabel : Int) [.ap (kc : Int) [.ap (t2 : Int) [.cb .map (M : Int) ps]], .vr 0]) := by
  decide +kernel

/-- `colOf(map, M, ps)` is the one-entry map, not `bot`. -/
theorem colOf_parts : colOfF .map (M : Int) ps = some (.co .map (M : Int) ps) := by
  decide +kernel

/-- The encoding reads no key sort: the rule is written the same at `d` and at the control. -/
theorem encRl_same : encRl d rule = encRl dB rule := rfl

end KCore.KK.C13Witness

#print axioms KCore.KK.C13Witness.ready
#print axioms KCore.KK.C13Witness.older
#print axioms KCore.KK.C13Witness.collForm
#print axioms KCore.KK.C13Witness.encDef_none
#print axioms KCore.KK.C13Witness.control_ok
#print axioms KCore.KK.C13Witness.args_sorted
#print axioms KCore.KK.C13Witness.paramVal_none
#print axioms KCore.KK.C13Witness.paramVal_control
#print axioms KCore.KK.C13Witness.lhs_matches
#print axioms KCore.KK.C13Witness.rhs_none
#print axioms KCore.KK.C13Witness.no_step
#print axioms KCore.KK.C13Witness.step_control
#print axioms KCore.KK.C13Witness.encTerm_rhs
#print axioms KCore.KK.C13Witness.colOf_parts
#print axioms KCore.KK.C13Witness.encRl_same
