/-
  The expectations of CN-4 §4.7 and CN-4b §7 on the kompiled texts with an open generator, read by
  the reader (their kompiled texts in f2-examples, the fixtures' under test/constructs/fixtures).
  The generated packages of the same texts, which state each statement of a model or of the
  semantics for every H with `OpenLaws` and `OpenTotal` and its instance at `lawHooks`, are
  generated and built by test/open-gen.sh, with the statements that read the text's `FnHyp` (the
  package's `fnHyp_defn`) in user modules built against them (test/open-gen/NS/User.lean):
  e2-comm-ctor's `ExactC` and e2-open-rule's one successor of `<k> go </k>`, for every H with the
  obligations, and their instances at `lawHooks`. Run from the package root:
  `lake env lean -j1 test/OpenKompiled.lean`. Kernel-checked.

  - `Comm` (e2-comm-ctor, `f2-examples/commctor.kompile.kore`): `and` raw without a law, `or` raw
    with `assoc`; `coreOK`; the associativity sentence of `or` is the one law item of `Γ`
    (`Faithful.lawItemsK`), and the reader reads exactly that sentence of the text
    (`Parse.openLawRead`); at `HookParams.none` `OpenTotal` holds and `OpenLaws` fails
    (`or(or(x,x),x)` and `or(x,or(x,x))` are two raw values).
  - `Rule` (e2-open-rule, `f2-examples/openrule.kompile.kore`): `and` raw without a law, so
    `OpenLaws` holds under every interpretation; `<k> go </k>` applies no open generator; for every
    H with `OpenTotal` the value of `x & y` exists and is a value of Exp; `same(x & y, y & x)` is
    `false` at `HookParams.none` and `true` at `Hswap`, which answers `and(x, y)` at `and [y, x]`;
    at `Hbad` `and [x, y]` has no value and `OpenTotal` fails.
  - `Idem` (e2-idem-ctor, `f2-examples/idemctor.kompile.kore`): `or` raw with `idem` (CN-4 V7 case
    2); for every H with `OpenLaws` `x | x` is `x`; at `lawHooks c HookParams.none` `(x | y) | y`
    is a value distinct from `x | y`; at `HookParams.none` `OpenIdem` fails at `x`.
  - `Band` (e2-band-ctor, `f2-examples/bandctor.kompile.kore`): `or` raw with `assoc` and `idem`
    (CN-4b §7); for every H with `OpenLaws` `x | x` is `x`, and with `OpenTotal` too `x | y` has a
    value v of Exp with `v | v` = v; at `lawHooks c HookParams.none` `x | y` and `y | x` are two
    values and `(x | y) | x` is `x | y`; at `HookParams.none` `OpenLaws` fails.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace OpenKompiled

/-! ## e2-comm-ctor -/
namespace Comm

definition_of defn from "f2-examples/commctor.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def exp : Srt := 32
def xS : Sym := 385
def andS : Sym := 386
def orS : Sym := 387

def andP : ParamSig := { sig := ⟨andS, [exp, exp], exp⟩, raw := true }
def orP : ParamSig := { sig := ⟨orS, [exp, exp], exp⟩, raw := true, assoc := true }

theorem names_ok : c.sortName exp = "Exp" ∧ c.symName xS = "Lblx" ∧ c.symName andS = "Lbland" ∧
    c.symName orS = "Lblor" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The text's two open generators, as the reader reads them. -/
theorem params_raw : c.params.filter (·.raw) = [andP, orP] := by decide +kernel

/-- `Γ`'s one law item is the associativity sentence of `or`, the sentence the text states
(`kore.txt:22`) and the reader reads. -/
theorem lawItems : (Faithful.lawItemsK c).map (·.pat) =
    [(KoreAML.trAxiom [] [] ⟨0, "kernel", Faithful.assocAxK c orP⟩).pat] := by
  decide +kernel

def xV : GroundTerm := .ctor xS []

theorem or_mem (H : HookParams) : orP ∈ (c.withHooks H).params := by
  show orP ∈ c.params; decide +kernel

/-- At `HookParams.none` the two nestings of `x, x, x` under `or` are two raw values of Exp. -/
theorem none_values :
    ((c.withHooks HookParams.none).paramVal orS [xV, xV]).bind
        (fun ab => (c.withHooks HookParams.none).paramVal orS [ab, xV]) =
      some (.ctor orS [.ctor orS [xV, xV], xV]) ∧
    ((c.withHooks HookParams.none).paramVal orS [xV, xV]).bind
        (fun bd => (c.withHooks HookParams.none).paramVal orS [xV, bd]) =
      some (.ctor orS [xV, .ctor orS [xV, xV]]) ∧
    GroundTerm.ctor orS [.ctor orS [xV, xV], xV] ≠ .ctor orS [xV, .ctor orS [xV, xV]] := by
  decide +kernel

theorem not_openLaws_none : ¬ OpenLaws (c.withHooks HookParams.none) := fun h => by
  have ha := (h orP (or_mem _) rfl).1 rfl xV xV xV (by decide +kernel)
  exact absurd (Option.some.inj ((none_values.1.symm.trans ha).trans none_values.2.1)) none_values.2.2

theorem openTotal_none : OpenTotal (c.withHooks HookParams.none) := KCore.openTotal_none _ coreOK

end Comm

#print axioms Comm.coreOK
#print axioms Comm.lawItems
#print axioms Comm.not_openLaws_none
#print axioms Comm.openTotal_none

/-! ## e2-open-rule -/
namespace Rule

definition_of defn from "f2-examples/openrule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def exp : Srt := 32
def kS : Sym := 383
def goS : Sym := 385
def xS : Sym := 386
def yS : Sym := 387
def andS : Sym := 389

def andP : ParamSig := { sig := ⟨andS, [exp, exp], exp⟩, raw := true }

theorem names_ok : c.sortName exp = "Exp" ∧ c.symName goS = "Lblgo" ∧ c.symName xS = "Lblx" ∧
    c.symName yS = "Lbly" ∧ c.symName andS = "Lbland" ∧ c.symName kS = "Lbl'-LT-'k'-GT-'" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

theorem params_raw : c.params.filter (·.raw) = [andP] := by decide +kernel

def xV : GroundTerm := .ctor xS []
def yV : GroundTerm := .ctor yS []
/-- The counter cell at 0. -/
def cnt : GroundTerm := .ctor counterLabel [int 0]
/-- `<k> go </k>`. -/
def goV : GroundTerm := .ctor topLabel [.ctor kS [.ctor kseq [.ctor goS [], .ctor dotk []]], cnt]

/-- `<k> go </k>`, x and y apply no open generator: their sorts are theirs under every H. -/
theorem go_rawFree : c.rawFree goV = true ∧ c.sortOf goV = some topCellSort ∧
    c.rawFree xV = true ∧ c.sortOf xV = some exp ∧ c.rawFree yV = true ∧ c.sortOf yV = some exp := by
  decide +kernel

/-- `and` has no law: `OpenLaws` holds under every interpretation. -/
theorem openLaws_any (H : HookParams) : OpenLaws (c.withHooks H) := fun k hk hr => by
  have hk' : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩
  rw [params_raw, List.mem_singleton] at hk'
  subst hk'
  exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

theorem and_mem (H : HookParams) : andP ∈ (c.withHooks H).params := by
  show andP ∈ c.params; decide +kernel

theorem sorts_xy (H : HookParams) : (c.withHooks H).sortsOf [xV, yV] = some [exp, exp] :=
  OvlLaws.sortsOf_cons_iff.mpr
    ⟨(Semantics.sortOf_withHooks_rawFree c H go_rawFree.2.2.1).trans go_rawFree.2.2.2.1,
     OvlLaws.sortsOf_cons_iff.mpr
      ⟨(Semantics.sortOf_withHooks_rawFree c H go_rawFree.2.2.2.2.1).trans go_rawFree.2.2.2.2.2, rfl⟩⟩

/-- For every H with `OpenTotal`, `x & y` has a value, a value of Exp. -/
theorem xy_value (H : HookParams) (ht : OpenTotal (c.withHooks H)) :
    ∃ v, (c.withHooks H).paramVal andS [xV, yV] = some v ∧ (c.withHooks H).sortOf v = some exp := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (ht andP (and_mem H) rfl [xV, yV] (sorts_xy H))
  have hlp : (c.withHooks H).lookupParam andS = some andP :=
    show c.lookupParam andS = some andP by decide +kernel
  exact ⟨v, hv, ((paramVal_raw_sorted hlp rfl rfl).mp hv).2⟩

/-- `same(x & y, y & x)`. -/
def sameS : Sym := 388
def sameT : Term := .app sameS [.app andS [.app xS [], .app yS []], .app andS [.app yS [], .app xS []]]

theorem same_name : c.symName sameS = "Lblsame" := by decide +kernel

/-- The interpretation answering `and(x, y)` at `and [y, x]`, and nothing elsewhere. -/
def Hswap : HookParams :=
  ⟨fun f vs => if f == andS && decide (vs = [yV, xV]) then some (.ctor andS [xV, yV]) else none⟩

/-- The interpretation answering `go`, of sort KItem, at every application of `and`. -/
def Hbad : HookParams := ⟨fun f _ => if f == andS then some (.ctor goS []) else none⟩

/-- A closed term's computed result is its result (`CExec.evalT_sound`). -/
theorem evalTerm_of_exec {c : Semantics} (hr : CExec.execReady c = true) {t : Term}
    {r : Option GroundTerm} {s : Srt} (n : Nat) (he : CExec.evalT c n [] t = some r)
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [] t = some s) : EvalTerm c [] t r := by
  obtain ⟨-, hsc, hcc, hcm, -⟩ := CExec.execReady_parts hr
  exact CExec.evalT_sound hsc hcc hcm n he (headsOK_fns _) (fun i s hs => by simp at hs) ht

/-- At `HookParams.none`, `x & y` and `y & x` are two raw values and `same` of them is `false`. -/
theorem same_none : EvalTerm (c.withHooks HookParams.none) [] sameT (some (bool false)) :=
  evalTerm_of_exec (by decide +kernel) 50 (by decide +kernel) (s := Srt.bool) (by decide +kernel)

/-- At `Hswap`, `y & x` is `and(x, y)`, the value of `x & y`, and `same` of them is `true`. -/
theorem same_swap : EvalTerm (c.withHooks Hswap) [] sameT (some (bool true)) :=
  evalTerm_of_exec (by decide +kernel) 50 (by decide +kernel) (s := Srt.bool) (by decide +kernel)

/-- At `Hbad` the answer at `and [x, y]` is no value of Exp: `and` has no value there, and
`OpenTotal` fails. -/
theorem bad_none : (c.withHooks Hbad).paramVal andS [xV, yV] = none := by decide +kernel
theorem not_openTotal_bad : ¬ OpenTotal (c.withHooks Hbad) := fun h => by
  have : ((c.withHooks Hbad).paramVal andS [xV, yV]).isSome = true :=
    h andP (and_mem Hbad) rfl [xV, yV] (sorts_xy Hbad)
  rw [bad_none] at this
  cases this

end Rule

#print axioms Rule.coreOK
#print axioms Rule.openLaws_any
#print axioms Rule.xy_value
#print axioms Rule.same_none
#print axioms Rule.same_swap
#print axioms Rule.not_openTotal_bad

/-! ## e2-idem-ctor -/
namespace Idem

definition_of defn from "f2-examples/idemctor.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def exp : Srt := 32
def xS : Sym := 385
def yS : Sym := 386
def orS : Sym := 387

def orP : ParamSig := { sig := ⟨orS, [exp, exp], exp⟩, raw := true, idem := true }

theorem names_ok : c.sortName exp = "Exp" ∧ c.symName xS = "Lblx" ∧ c.symName yS = "Lbly" ∧
    c.symName orS = "Lblor" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

theorem params_raw : c.params.filter (·.raw) = [orP] := by decide +kernel

/-- `Γ`'s one law item is the idempotence sentence of `or`. -/
theorem lawItems : (Faithful.lawItemsK c).map (·.pat) =
    [(KoreAML.trAxiom [] [] ⟨0, "kernel", Faithful.idemAxK c orP⟩).pat] := by
  decide +kernel

def xV : GroundTerm := .ctor xS []
def yV : GroundTerm := .ctor yS []

theorem sort_x (H : HookParams) : (c.withHooks H).sortOf xV = some exp :=
  (Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)).trans (by decide +kernel)

theorem or_mem (H : HookParams) : orP ∈ (c.withHooks H).params := by
  show orP ∈ c.params; decide +kernel

/-- For every H with `OpenLaws`: `x | x` is `x`. -/
theorem idem_x (H : HookParams) (hl : OpenLaws (c.withHooks H)) :
    (c.withHooks H).paramVal orS [xV, xV] = some xV :=
  (hl orP (or_mem H) rfl).2 rfl xV (sort_x H)

/-- At `lawHooks c HookParams.none`: `(x | y) | y` is a value of Exp distinct from `x | y`. -/
theorem lawHooks_values :
    (c.withHooks (lawHooks c HookParams.none)).paramVal orS [.ctor orS [xV, yV], yV] =
      some (.ctor orS [.ctor orS [xV, yV], yV]) ∧
    (c.withHooks (lawHooks c HookParams.none)).sortOf (.ctor orS [.ctor orS [xV, yV], yV]) = some exp ∧
    (c.withHooks (lawHooks c HookParams.none)).sortOf (.ctor orS [xV, yV]) = some exp ∧
    GroundTerm.ctor orS [.ctor orS [xV, yV], yV] ≠ .ctor orS [xV, yV] := by
  decide +kernel

theorem none_raw : (c.withHooks HookParams.none).paramVal orS [xV, xV] = some (.ctor orS [xV, xV]) := by
  decide +kernel
theorem not_openIdem_none : ¬ OpenIdem (c.withHooks HookParams.none) orS exp := fun h =>
  absurd ((h xV (sort_x _)).symm.trans none_raw) (by decide +kernel)
theorem not_openLaws_none : ¬ OpenLaws (c.withHooks HookParams.none) := fun h =>
  not_openIdem_none ((h orP (or_mem _) rfl).2 rfl)

end Idem

#print axioms Idem.coreOK
#print axioms Idem.lawItems
#print axioms Idem.idem_x
#print axioms Idem.lawHooks_values
#print axioms Idem.not_openLaws_none

/-! ## e2-band-ctor -/
namespace Band

definition_of defn from "f2-examples/bandctor.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def exp : Srt := 32
def xS : Sym := 385
def yS : Sym := 386
def orS : Sym := 387

def orP : ParamSig := { sig := ⟨orS, [exp, exp], exp⟩, raw := true, assoc := true, idem := true }

theorem names_ok : c.sortName exp = "Exp" ∧ c.symName xS = "Lblx" ∧ c.symName yS = "Lbly" ∧
    c.symName orS = "Lblor" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

theorem params_raw : c.params.filter (·.raw) = [orP] := by decide +kernel

/-- `Γ`'s law items are the associativity and the idempotence sentences of `or`. -/
theorem lawItems :
    (Faithful.lawItemsK c).map (·.pat) = [(KoreAML.trAxiom [] [] ⟨0, "kernel", Faithful.assocAxK c orP⟩).pat,
      (KoreAML.trAxiom [] [] ⟨0, "kernel", Faithful.idemAxK c orP⟩).pat] := by
  decide +kernel

def xV : GroundTerm := .ctor xS []
def yV : GroundTerm := .ctor yS []

theorem sort_x (H : HookParams) : (c.withHooks H).sortOf xV = some exp :=
  (Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)).trans (by decide +kernel)
theorem sort_y (H : HookParams) : (c.withHooks H).sortOf yV = some exp :=
  (Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)).trans (by decide +kernel)

theorem or_mem (H : HookParams) : orP ∈ (c.withHooks H).params := by
  show orP ∈ c.params; decide +kernel

/-- For every H with `OpenLaws`: `x | x` is `x`. -/
theorem idem_x (H : HookParams) (hl : OpenLaws (c.withHooks H)) :
    (c.withHooks H).paramVal orS [xV, xV] = some xV :=
  (hl orP (or_mem H) rfl).2 rfl xV (sort_x H)

/-- For every H with `OpenLaws` and `OpenTotal`: `x | y` has a value v, a value of Exp, and
`v | v` is v. -/
theorem idem_compound (H : HookParams) (hl : OpenLaws (c.withHooks H)) (ht : OpenTotal (c.withHooks H)) :
    ∃ v, (c.withHooks H).paramVal orS [xV, yV] = some v ∧ (c.withHooks H).sortOf v = some exp ∧
      (c.withHooks H).paramVal orS [v, v] = some v := by
  have hvs : (c.withHooks H).sortsOf [xV, yV] = some [exp, exp] :=
    OvlLaws.sortsOf_cons_iff.mpr ⟨sort_x H, OvlLaws.sortsOf_cons_iff.mpr ⟨sort_y H, rfl⟩⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (ht orP (or_mem H) rfl [xV, yV] hvs)
  have hlp : (c.withHooks H).lookupParam orS = some orP :=
    show c.lookupParam orS = some orP by decide +kernel
  have hs : (c.withHooks H).sortOf v = some exp := ((paramVal_raw_sorted hlp rfl rfl).mp hv).2
  exact ⟨v, hv, hs, (hl orP (or_mem H) rfl).2 rfl v hs⟩

/-- At `lawHooks c HookParams.none`: `x | y` and `y | x` are two values of Exp; `(x | y) | x` is
`x | y` (true of this interpretation; the text does not state it). -/
theorem lawHooks_values :
    (c.withHooks (lawHooks c HookParams.none)).paramVal orS [xV, yV] = some (.ctor orS [xV, yV]) ∧
    (c.withHooks (lawHooks c HookParams.none)).paramVal orS [yV, xV] = some (.ctor orS [yV, xV]) ∧
    (c.withHooks (lawHooks c HookParams.none)).sortOf (.ctor orS [xV, yV]) = some exp ∧
    (c.withHooks (lawHooks c HookParams.none)).sortOf (.ctor orS [yV, xV]) = some exp ∧
    GroundTerm.ctor orS [xV, yV] ≠ .ctor orS [yV, xV] ∧
    (c.withHooks (lawHooks c HookParams.none)).paramVal orS [.ctor orS [xV, yV], xV] =
      some (.ctor orS [xV, yV]) := by
  decide +kernel

/-- At `HookParams.none`: `or(x, x)` is the raw application, not `x`; `OpenIdem` fails at `x`, and
with it `OpenLaws`. -/
theorem none_raw : (c.withHooks HookParams.none).paramVal orS [xV, xV] = some (.ctor orS [xV, xV]) := by
  decide +kernel
theorem not_openIdem_none : ¬ OpenIdem (c.withHooks HookParams.none) orS exp := fun h =>
  absurd ((h xV (sort_x _)).symm.trans none_raw) (by decide +kernel)
theorem not_openLaws_none : ¬ OpenLaws (c.withHooks HookParams.none) := fun h =>
  not_openIdem_none ((h orP (or_mem _) rfl).2 rfl)

end Band

#print axioms Band.coreOK
#print axioms Band.lawItems
#print axioms Band.idem_x
#print axioms Band.idem_compound
#print axioms Band.lawHooks_values
#print axioms Band.not_openLaws_none

end OpenKompiled
