/-
  The parameter hooks of FLOAT, STRING, MAP, BYTES, SET and INT on the construct fixtures
  e6-param-float, e6-param-string, e6-param-map, e6-param-bytes, e6-param-set and e6-param-int
  (`f2-examples/e6-param-*.kompile.kore`, each the text its fixture's kompile.txt hashes, BUILTIN/
  restored as K's builtin directory and FIXTURE/ as the fixture's directory relative to the tree).
  Each text applies every hooked function of its module that no registry hook interprets once, in a
  rule's right side (`go(N, …)`); the reader reads each as a parameter symbol no hook implements
  (`impl = none`, `raw = false`; the fixture's params.txt): its value at an argument list is the
  interpretation's (`paramVal`), and Γ holds its graph, ⊥ where the interpretation gives none.

  The `param_undetermined` shape at a point of each (DONE-0 C2, row `parameter`; C7 form (c)): over
  all interpretations H, Γ entails neither that the application has no value nor that it is a given
  value of its result sort (`param_undetermined_const`, KcoreSpec/ParamSchema.lean). The pair of
  models: under `HookParams.none` the application is ⊥ in every model of Γ, under `constH v` it is
  `v` in every model, and both theories have models (`sound_hyp`). An instance reads its facts of
  the text as one decided test (`paramOK`: the parameter named, looked up by its number, no hook
  implementing it, the point's arguments values of its argument sorts and the given value one of its
  result sort) and is closed by `undetermined_of_paramOK`.

  `FnHyp` under every H: the texts of FLOAT, STRING, MAP, BYTES and SET have no function
  (`fnHyp_of_fns_nil`). INT's has one, K's `append` (`srandInt` gives a K, so the rule's right
  side appends it to the rest of the cell), declared total, which the totality decider confirms
  (its clauses cover K × K, the cover check splitting K over `kseq` and `dotk`); the deciders name
  no fact (`fnHyp_decided`).

  The points are values of the argument sorts (`1`, `"a"`, `0.0`, `b"a"`, `1 |-> 7`,
  `SetItem(1)`, `ListItem(1)`, the Id `x`) and the given values one of the result sort. Whatever
  value the K prose would name there, none is entailed: the text states no sentence of these
  symbols' graphs.

  Run from the package root: `lake env lean -j1 test/ParamE6Lib.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.ParamE6Lib

open KCore ML Faithful ParamSchema

/-! ## The points -/

def strV : GroundTerm := .dv Srt.string (.tok "a")
/-- The Float `0.0` of double precision. -/
def floatV : GroundTerm := .dv Srt.float (.float 53 11 0)
def bytesV : GroundTerm := .dv Srt.bytes (.tok "a")
def idV : GroundTerm := .dv Srt.ident (.tok "x")
def mapV : GroundTerm := .map Srt.map [(kint 1, kint 7)]
def setV : GroundTerm := .set Srt.set [kint 1]
def listV : GroundTerm := .list Srt.list [kint 1]
/-- The empty K. -/
def kDot : GroundTerm := .ctor dotk []
def ioIntV : GroundTerm := .inj Srt.int Srt.ioInt (int 1)
def ioStrV : GroundTerm := .inj Srt.string Srt.ioString strV
/-- The symbol named `n`, by number. -/
def symPL (c : Semantics) (n : String) : Sym :=
  ((List.range (nRegSyms + c.symNames.length)).find? fun f => c.symName f == n).getD 0
/-- `#tempFile("a", 1)`. -/
def ioFileV (c : Semantics) : GroundTerm := .ctor (symPL c "Lbl'Hash'tempFile") [strV, int 1]
/-- `#ffi_sint`. -/
def ffiTypeV (c : Semantics) : GroundTerm := .ctor (symPL c "Lbl'Hash'ffi'Unds'sint") []
/-- JSON's `null`. -/
def jsonV (c : Semantics) : GroundTerm := .ctor (symPL c "LblJSONnull") []


/-! ## e6-param-float: FLOAT -/

namespace Float6

definition_of defn from "f2-examples/e6-param-float.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_of_fns_nil c noRaw (by decide +kernel) (by decide +kernel) H

/-- **`Lbl'UndsXor-'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0, 0.0) nor that it is 0.0. -/
theorem powFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lbl'UndsXor-'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lbl'UndsXor-'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblFloat2Int'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 1. -/
theorem float2Int_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblFloat2Int'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblFloat2Int'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblacosFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem acosFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblacosFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblacosFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblasinFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem asinFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblasinFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblasinFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lblatan2Float'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0, 0.0) nor that it is 0.0. -/
theorem atan2Float_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblatan2Float'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblatan2Float'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblatanFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem atanFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblatanFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblatanFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblcosFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem cosFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblcosFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblcosFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblexpFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem expFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblexpFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblexpFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblexponentFloat'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 1. -/
theorem exponentFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblexponentFloat'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblexponentFloat'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LbllogFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem logFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LbllogFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LbllogFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblmaxFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0, 0.0) nor that it is 0.0. -/
theorem maxFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblmaxFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblmaxFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblminFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0, 0.0) nor that it is 0.0. -/
theorem minFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblminFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblminFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblrootFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0, 1) nor that it is 0.0. -/
theorem rootFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblrootFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Int").sig.name [floatV, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblrootFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Int").sig.name [floatV, int 1] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblsignFloat'LParUndsRParUnds'FLOAT'Unds'Bool'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is true. -/
theorem signFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblsignFloat'LParUndsRParUnds'FLOAT'Unds'Bool'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblsignFloat'LParUndsRParUnds'FLOAT'Unds'Bool'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (bool true))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblsinFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem sinFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblsinFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblsinFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LbltanFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem tanFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LbltanFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LbltanFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

end Float6

/-! ## e6-param-string: STRING -/

namespace String6

definition_of defn from "f2-examples/e6-param-string.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_of_fns_nil c noRaw (by decide +kernel) (by decide +kernel) H

/-- **`LblBase2String'LParUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is "a". -/
theorem base2String_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblBase2String'LParUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblBase2String'LParUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblFloat2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is "a". -/
theorem float2String_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblFloat2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblFloat2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblFloatFormat` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0, "a") nor that it is "a". -/
theorem floatFormat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblFloatFormat").sig.name [floatV, strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblFloatFormat").sig.name [floatV, strV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblId2String'LParUndsRParUnds'ID-COMMON'Unds'String'Unds'Id` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the Id `x`) nor that it is "a". -/
theorem id2String_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblId2String'LParUndsRParUnds'ID-COMMON'Unds'String'Unds'Id").sig.name [idV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblId2String'LParUndsRParUnds'ID-COMMON'Unds'String'Unds'Id").sig.name [idV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblString2Float'LParUndsRParUnds'STRING-COMMON'Unds'Float'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is 0.0. -/
theorem string2Float_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblString2Float'LParUndsRParUnds'STRING-COMMON'Unds'Float'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblString2Float'LParUndsRParUnds'STRING-COMMON'Unds'Float'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblString2Id'LParUndsRParUnds'ID-COMMON'Unds'Id'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is the Id `x`. -/
theorem string2Id_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblString2Id'LParUndsRParUnds'ID-COMMON'Unds'Id'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblString2Id'LParUndsRParUnds'ID-COMMON'Unds'Id'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (idV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblcategoryChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is "a". -/
theorem categoryChar_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblcategoryChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblcategoryChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LbldirectionalityChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is "a". -/
theorem directionalityChar_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LbldirectionalityChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LbldirectionalityChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblnewUUID'Unds'STRING-COMMON'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value (no argument) nor that it is "a". -/
theorem newUUID_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblnewUUID'Unds'STRING-COMMON'Unds'String").sig.name [] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblnewUUID'Unds'STRING-COMMON'Unds'String").sig.name [] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

end String6

/-! ## e6-param-map: MAP -/

namespace Map6

definition_of defn from "f2-examples/e6-param-map.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_of_fns_nil c noRaw (by decide +kernel) (by decide +kernel) H

/-- **`Lbl'Unds'-Map'UndsUnds'MAP'Unds'Map'Unds'Map'Unds'Map` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 |-> 7, 1 |-> 7) nor that it is 1 |-> 7. -/
theorem differenceMap_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lbl'Unds'-Map'UndsUnds'MAP'Unds'Map'Unds'Map'Unds'Map").sig.name [mapV, mapV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lbl'Unds'-Map'UndsUnds'MAP'Unds'Map'Unds'Map'Unds'Map").sig.name [mapV, mapV] ≡ den (c.withHooks H) (mapV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Unds-LT-Eqls'Map'UndsUnds'MAP'Unds'Bool'Unds'Map'Unds'Map` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 |-> 7, 1 |-> 7) nor that it is true. -/
theorem inclusionMap_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lbl'Unds-LT-Eqls'Map'UndsUnds'MAP'Unds'Bool'Unds'Map'Unds'Map").sig.name [mapV, mapV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lbl'Unds-LT-Eqls'Map'UndsUnds'MAP'Unds'Bool'Unds'Map'Unds'Map").sig.name [mapV, mapV] ≡ den (c.withHooks H) (bool true))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblMap'Coln'choice` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 |-> 7) nor that it is 1 (a KItem). -/
theorem choiceMap_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblMap'Coln'choice").sig.name [mapV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblMap'Coln'choice").sig.name [mapV] ≡ den (c.withHooks H) (kint 1))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lblkeys'Unds'list'LParUndsRParUnds'MAP'Unds'List'Unds'Map` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 |-> 7) nor that it is ListItem(1). -/
theorem keysListMap_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblkeys'Unds'list'LParUndsRParUnds'MAP'Unds'List'Unds'Map").sig.name [mapV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblkeys'Unds'list'LParUndsRParUnds'MAP'Unds'List'Unds'Map").sig.name [mapV] ≡ den (c.withHooks H) (listV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblupdateMap'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Map` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 |-> 7, 1 |-> 7) nor that it is 1 |-> 7. -/
theorem updateMap_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblupdateMap'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Map").sig.name [mapV, mapV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblupdateMap'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Map").sig.name [mapV, mapV] ≡ den (c.withHooks H) (mapV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lblvalues'LParUndsRParUnds'MAP'Unds'List'Unds'Map` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 |-> 7) nor that it is ListItem(1). -/
theorem valuesMap_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblvalues'LParUndsRParUnds'MAP'Unds'List'Unds'Map").sig.name [mapV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblvalues'LParUndsRParUnds'MAP'Unds'List'Unds'Map").sig.name [mapV] ≡ den (c.withHooks H) (listV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

end Map6

/-! ## e6-param-bytes: BYTES -/

namespace Bytes6

definition_of defn from "f2-examples/e6-param-bytes.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_of_fns_nil c noRaw (by decide +kernel) (by decide +kernel) H

/-- **`LblBytes2Hex'LParUndsRParUnds'BYTES-HOOKED'Unds'String'Unds'Bytes` is not determined by the text**: over all H, Γ entails neither that it has
no value at (b"a") nor that it is "a". -/
theorem bytes2Hex_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblBytes2Hex'LParUndsRParUnds'BYTES-HOOKED'Unds'String'Unds'Bytes").sig.name [bytesV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblBytes2Hex'LParUndsRParUnds'BYTES-HOOKED'Unds'String'Unds'Bytes").sig.name [bytesV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblBytes2String'LParUndsRParUnds'BYTES-HOOKED'Unds'String'Unds'Bytes` is not determined by the text**: over all H, Γ entails neither that it has
no value at (b"a") nor that it is "a". -/
theorem bytes2String_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblBytes2String'LParUndsRParUnds'BYTES-HOOKED'Unds'String'Unds'Bytes").sig.name [bytesV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblBytes2String'LParUndsRParUnds'BYTES-HOOKED'Unds'String'Unds'Bytes").sig.name [bytesV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblString2Bytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is b"a". -/
theorem string2Bytes_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblString2Bytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblString2Bytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (bytesV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LbldecodeBytes'LParUndsCommUndsRParUnds'BYTES-STRING-ENCODE'Unds'String'Unds'String'Unds'Bytes` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a", b"a") nor that it is "a". -/
theorem decodeBytes_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LbldecodeBytes'LParUndsCommUndsRParUnds'BYTES-STRING-ENCODE'Unds'String'Unds'String'Unds'Bytes").sig.name [strV, bytesV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LbldecodeBytes'LParUndsCommUndsRParUnds'BYTES-STRING-ENCODE'Unds'String'Unds'String'Unds'Bytes").sig.name [strV, bytesV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblencodeBytes'LParUndsCommUndsRParUnds'BYTES-STRING-ENCODE'Unds'Bytes'Unds'String'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a", "a") nor that it is b"a". -/
theorem encodeBytes_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblencodeBytes'LParUndsCommUndsRParUnds'BYTES-STRING-ENCODE'Unds'Bytes'Unds'String'Unds'String").sig.name [strV, strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblencodeBytes'LParUndsCommUndsRParUnds'BYTES-STRING-ENCODE'Unds'Bytes'Unds'String'Unds'String").sig.name [strV, strV] ≡ den (c.withHooks H) (bytesV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

end Bytes6

/-! ## e6-param-set: SET -/

namespace Set6

definition_of defn from "f2-examples/e6-param-set.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_of_fns_nil c noRaw (by decide +kernel) (by decide +kernel) H

/-- **`LblList2Set'LParUndsRParUnds'COLLECTIONS'Unds'Set'Unds'List` is not determined by the text**: over all H, Γ entails neither that it has
no value at (ListItem(1)) nor that it is SetItem(1). -/
theorem list2Set_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblList2Set'LParUndsRParUnds'COLLECTIONS'Unds'Set'Unds'List").sig.name [listV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblList2Set'LParUndsRParUnds'COLLECTIONS'Unds'Set'Unds'List").sig.name [listV] ≡ den (c.withHooks H) (setV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblSet'Coln'choice` is not determined by the text**: over all H, Γ entails neither that it has
no value at (SetItem(1)) nor that it is 1 (a KItem). -/
theorem choiceSet_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblSet'Coln'choice").sig.name [setV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblSet'Coln'choice").sig.name [setV] ≡ den (c.withHooks H) (kint 1))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblSet2List'LParUndsRParUnds'COLLECTIONS'Unds'List'Unds'Set` is not determined by the text**: over all H, Γ entails neither that it has
no value at (SetItem(1)) nor that it is ListItem(1). -/
theorem set2List_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblSet2List'LParUndsRParUnds'COLLECTIONS'Unds'List'Unds'Set").sig.name [setV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblSet2List'LParUndsRParUnds'COLLECTIONS'Unds'List'Unds'Set").sig.name [setV] ≡ den (c.withHooks H) (listV))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

end Set6

/-! ## e6-param-int: INT -/

namespace Int6

definition_of defn from "f2-examples/e6-param-int.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- K's `append` (number 385) is total by the decider, and the deciders name no fact: `FnHyp`
under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_decided c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

/-- **`Lbl'Tild'Int'Unds'` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is 1. -/
theorem notInt_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lbl'Tild'Int'Unds'").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lbl'Tild'Int'Unds'").sig.name [int 1] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Unds'xorInt'Unds'` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is 1. -/
theorem xorInt_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lbl'Unds'xorInt'Unds'").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lbl'Unds'xorInt'Unds'").sig.name [int 1, int 1] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'UndsAnd-'Int'Unds'` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is 1. -/
theorem andInt_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lbl'UndsAnd-'Int'Unds'").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lbl'UndsAnd-'Int'Unds'").sig.name [int 1, int 1] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'UndsPipe'Int'Unds'` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is 1. -/
theorem orInt_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lbl'UndsPipe'Int'Unds'").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lbl'UndsPipe'Int'Unds'").sig.name [int 1, int 1] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblrandInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is 1. -/
theorem randInt_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblrandInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblrandInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int").sig.name [int 1] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblsrandInt'LParUndsRParUnds'INT-COMMON'Unds'K'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is the empty K. -/
theorem srandInt_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblsrandInt'LParUndsRParUnds'INT-COMMON'Unds'K'Unds'Int").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "LblsrandInt'LParUndsRParUnds'INT-COMMON'Unds'K'Unds'Int").sig.name [int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

end Int6

end KCore.ParamE6Lib

/-- info: 'KCore.ParamE6Lib.Float6.powFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.powFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.float2Int_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.float2Int_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.acosFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.acosFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.asinFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.asinFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.atan2Float_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.atan2Float_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.atanFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.atanFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.cosFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.cosFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.expFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.expFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.exponentFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.exponentFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.logFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.logFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.maxFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.maxFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.minFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.minFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.rootFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.rootFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.signFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.signFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.sinFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.sinFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.tanFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.tanFloat_undetermined
/-- info: 'KCore.ParamE6Lib.String6.base2String_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.base2String_undetermined
/-- info: 'KCore.ParamE6Lib.String6.float2String_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.float2String_undetermined
/-- info: 'KCore.ParamE6Lib.String6.floatFormat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.floatFormat_undetermined
/-- info: 'KCore.ParamE6Lib.String6.id2String_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.id2String_undetermined
/-- info: 'KCore.ParamE6Lib.String6.string2Float_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.string2Float_undetermined
/-- info: 'KCore.ParamE6Lib.String6.string2Id_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.string2Id_undetermined
/-- info: 'KCore.ParamE6Lib.String6.categoryChar_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.categoryChar_undetermined
/-- info: 'KCore.ParamE6Lib.String6.directionalityChar_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.directionalityChar_undetermined
/-- info: 'KCore.ParamE6Lib.String6.newUUID_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.newUUID_undetermined
/-- info: 'KCore.ParamE6Lib.Map6.differenceMap_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Map6.differenceMap_undetermined
/-- info: 'KCore.ParamE6Lib.Map6.inclusionMap_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Map6.inclusionMap_undetermined
/-- info: 'KCore.ParamE6Lib.Map6.choiceMap_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Map6.choiceMap_undetermined
/-- info: 'KCore.ParamE6Lib.Map6.keysListMap_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Map6.keysListMap_undetermined
/-- info: 'KCore.ParamE6Lib.Map6.updateMap_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Map6.updateMap_undetermined
/-- info: 'KCore.ParamE6Lib.Map6.valuesMap_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Map6.valuesMap_undetermined
/-- info: 'KCore.ParamE6Lib.Bytes6.bytes2Hex_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Bytes6.bytes2Hex_undetermined
/-- info: 'KCore.ParamE6Lib.Bytes6.bytes2String_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Bytes6.bytes2String_undetermined
/-- info: 'KCore.ParamE6Lib.Bytes6.string2Bytes_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Bytes6.string2Bytes_undetermined
/-- info: 'KCore.ParamE6Lib.Bytes6.decodeBytes_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Bytes6.decodeBytes_undetermined
/-- info: 'KCore.ParamE6Lib.Bytes6.encodeBytes_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Bytes6.encodeBytes_undetermined
/-- info: 'KCore.ParamE6Lib.Set6.list2Set_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Set6.list2Set_undetermined
/-- info: 'KCore.ParamE6Lib.Set6.choiceSet_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Set6.choiceSet_undetermined
/-- info: 'KCore.ParamE6Lib.Set6.set2List_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Set6.set2List_undetermined
/-- info: 'KCore.ParamE6Lib.Int6.notInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Int6.notInt_undetermined
/-- info: 'KCore.ParamE6Lib.Int6.xorInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Int6.xorInt_undetermined
/-- info: 'KCore.ParamE6Lib.Int6.andInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Int6.andInt_undetermined
/-- info: 'KCore.ParamE6Lib.Int6.orInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Int6.orInt_undetermined
/-- info: 'KCore.ParamE6Lib.Int6.randInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Int6.randInt_undetermined
/-- info: 'KCore.ParamE6Lib.Int6.srandInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Int6.srandInt_undetermined
