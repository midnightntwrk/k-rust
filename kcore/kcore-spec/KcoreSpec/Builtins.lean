/-
  KCore. The builtin library, by K module (KCORE-SPEC.md §7, KCORE-AUDIT.md). Reviewed layer.

  krust writes a definition's imported builtin modules into its one KORE module. Each builtin
  sentence carries `Source(krust-builtin://FILE)` and a `Location`, and the K module that declares
  it is the module of FILE whose lines hold that location. A definition imports a module when its
  KORE holds a sentence of it (`Parse.envOf`), and its builtin part is then:
  - **each imported module's text** (`moduleText`, from prelude/builtin.kore): the module's
    declarations and hand-written axioms as krust writes them, and the few sentences kompile
    generates from the module's own attributes that are not schematic in the signature (LIST's,
    SET's and MAP's assoc, unit and idem axioms, MAP's definedness lemma of a map's concatenation,
    K-IO's selectors). Every definition holds the `KERNEL` text: the predicates and projections of
    K and KItem, `#KConfigValue`, `#unboxKConfigValue`;
  - **the generated axioms**, which `emit` writes from the signature for the library's sorts and
    constructors as for the user's: each sort's declaration, `isX`, `project:X`, its subsort of
    KItem, its no-junk axiom; each constructor's no-confusion, injectivity and functional axioms;
    the subsorts; the functional axiom of each total symbol (Emit.lean, `libBlocks`).
  - **in the core**: the modules' sorts, subsorts, token and byte sorts and constructors
    (`Semantics.lib`, the union `libOf`), and, as parameter symbols (`Semantics.params`, first), every
    function or hooked symbol of a module that no hook of Hooks.lean interprets (`libParams`).
    The interpreted ones are the registry's (FixedSignature.lean), whose meaning Hooks.lean gives.

  The text has two forms: kompile writes an argument-less `simplification` attribute as
  `simplification{}("")` when some sentence of the definition gives it an argument (INT-KORE's
  `simplification(51)`), and as `simplification{}()` otherwise (`Presentation.simpArg`); the
  attribute has no meaning in Γ_D (KCORE-SPEC.md §9, decision D2).

  The data are generated from krust's KORE of probe definitions (prelude/extract_builtin.py,
  BuiltinData.lean). That they are right does not matter for soundness: a KORE is tied only if
  `emit` prints it back, and `wf` checks the core's library is the union of its modules'. Their
  axioms enter Γ_D, so each hand-written one has a verdict (KCORE-AUDIT.md).
-/
import KcoreSpec.BuiltinData
import KcoreSpec.Core
import KcoreSpec.Kore.Import
import KcoreSpec.Kore.Base

set_option autoImplicit false

namespace KCore

/-- A builtin K module's declarations, as numbers. -/
structure BModule where
  name : String
  /-- the file declaring it, as its sentences' `Source` reads (`krust-builtin://domains.md`) -/
  src : String
  /-- the lines of the file it spans -/
  first : Nat
  last : Nat
  /-- the sorts it declares -/
  sorts : List Srt
  /-- the sorts its text declares by a generated `sort SortX{} []` (no location), which `emit` writes -/
  plainSorts : List Srt
  /-- the sorts with domain values, whose no-junk axiom is `⊤ ∨ ⊥` -/
  dvSorts : List Srt
  belowKItem : List Srt
  tokenSorts : List Srt
  byteSorts : List Srt
  subsorts : List (Srt × Srt)
  /-- its constructors, in the text's order -/
  ctors : List CtorSig
  /-- its function and hooked symbols that no hook of Hooks.lean interprets -/
  params : List CtorSig
  /-- the symbols kompile writes a functional axiom for (constructors aside) -/
  totals : List CtorSig
  /-- the ids of each sort's generated `project:X` equation (`""`: no projection) and `isX` equations -/
  uids : List (Srt × KoreAML.SortUids)
  deriving Repr, Inhabited

/-- The configuration value `#KConfigValue : K → KItem`, which krust's text declares (with
`#unboxKConfigValue`, which unwraps it) and K 7.1.337's does not. -/
def kconfigCtor : CtorSig := ⟨kconfigValue, [Srt.k], Srt.kitem⟩

/-- The module of `#KConfigValue` and `#unboxKConfigValue`, which krust writes into every text
without a source: imported exactly when the text declares `#KConfigValue` (`Parse.envOf`). Its
sentences are the kernel text's that name either symbol (`kconfigText`); its constructor is
`kconfigCtor`, first among the library's (`libOf`). It has no line range: no sentence is placed
in it by its source. -/
def kconfigModule : BModule :=
  { name := "K-RUST-CONFIGURATION-VALUES", src := "", first := 1, last := 0, sorts := [], plainSorts := [],
    dvSorts := [], belowKItem := [], tokenSorts := [], byteSorts := [], subsorts := [], ctors := [],
    params := [], totals := [], uids := [] }

/-- The library's modules, in their files' order, then `kconfigModule`. -/
def library : List BModule :=
  BuiltinData.modules.map (fun (n, s, a, b, ss, pl, dvs, bl, tk, by_, sb, cs, ps, ts, us) =>
    { name := n, src := s, first := a, last := b, sorts := ss, plainSorts := pl, dvSorts := dvs,
      belowKItem := bl, tokenSorts := tk, byteSorts := by_, subsorts := sb, ctors := cs, params := ps,
      totals := ts, uids := us.map fun (x, p, t, f) => (x, ⟨p, t, f⟩) }) ++ [kconfigModule]

/-- The number of `kconfigModule` in `library`. -/
def kconfigIdx : Nat := BuiltinData.modules.length

set_option maxRecDepth 100000 in
kore_definition builtinPlain from "prelude/builtin.kore"
set_option maxRecDepth 100000 in
kore_definition builtinArg from "prelude/builtin-arg.kore"

-- the elaborator would unfold the texts whenever it compares two terms holding them; the kernel
-- unfolds them all the same
attribute [irreducible] builtinPlain builtinArg

/-- The library's text in the form `arg` selects (`Presentation.simpArg`): module 0 is `KERNEL`,
module i + 1 is `library`'s i-th. -/
def builtinText (arg : Bool) : Kore.Definition := if arg then builtinArg else builtinPlain

/-- The text's `KERNEL` module: the predicates and projections of K and KItem, and krust's
`#KConfigValue` and `#unboxKConfigValue` (`kconfigText`). -/
def kernelModule (arg : Bool) : List Kore.Sentence := ((builtinText arg).modules.getD 0 default).sentences

/-- `#KConfigValue`'s and `#unboxKConfigValue`'s names. -/
def isKconfigName (n : String) : Bool := n == "Lbl'Hash'KConfigValue" || n == "Lbl'Hash'unboxKConfigValue"

mutual
  /-- The pattern applies `#KConfigValue` or `#unboxKConfigValue`. -/
  def appliesKconfig : Kore.Pattern → Bool
    | .app h _ ps => isKconfigName h.ident.name || appliesKconfigList ps
    | .and _ ps | .or _ ps => appliesKconfigList ps
    | .not _ p | .exist _ _ p | .forall _ _ p | .ceil _ _ p | .floor _ _ p | .next _ p => appliesKconfig p
    | .implies _ p q | .iff _ p q | .equals _ _ p q | .in _ _ p q | .rewrites _ p q =>
      appliesKconfig p || appliesKconfig q
    | _ => false
    termination_by structural p => p
  def appliesKconfigList : List Kore.Pattern → Bool
    | [] => false
    | p :: ps => appliesKconfig p || appliesKconfigList ps
    termination_by structural ps => ps
end

/-- A sentence of the kernel text that declares or applies `#KConfigValue` or `#unboxKConfigValue`. -/
def namesKconfig : Kore.Sentence → Bool
  | .symbol x => isKconfigName x.symbol.ident.ident.name
  | .axiom a => appliesKconfig a.pattern
  | _ => false

/-- The sentences every definition holds, with those of `#KConfigValue` when it imports
`kconfigModule` (`kc`); in the kernel module's order. -/
def kernelText (arg : Bool) (kc : Bool := true) : List Kore.Sentence :=
  (kernelModule arg).filter fun s => kc || !namesKconfig s

/-- The text of the library's i-th module. -/
def moduleText (arg : Bool) (i : Nat) : List Kore.Sentence := ((builtinText arg).modules.getD (i + 1) default).sentences

/-- The text's modules are the library's, in its order (`kconfigModule`, whose sentences are the
kernel module's, aside). -/
theorem builtinText_names (arg : Bool) :
    ((builtinText arg).modules.map (·.name.ident.name)) = "KERNEL" :: (library.dropLast).map (·.name) := by
  cases arg <;> unfold builtinText <;> decide +kernel

/-- The imported modules. -/
def importsOf (imports : List Nat) : List BModule := imports.filterMap (library[·]?)

/-- The builtin library of a definition importing `imports`: the union of the modules'. -/
def libOf (imports : List Nat) : Lib :=
  let ms := importsOf imports
  { sortsBelowKItem := ms.flatMap (·.belowKItem), subsorts := ms.flatMap (·.subsorts),
    tokenSorts := ms.flatMap (·.tokenSorts), byteSorts := ms.flatMap (·.byteSorts),
    ctors := (if imports.contains kconfigIdx then [kconfigCtor] else []) ++ ms.flatMap (·.ctors) }

/-- The imported modules' parameter symbols: their functions and hooked symbols that no hook
of Hooks.lean interprets (`hookSigs`). -/
def libParams (imports : List Nat) : List ParamSig :=
  (importsOf imports).flatMap fun m =>
    (m.params.filter fun k => !hookSigs.any (·.name == k.name)).map fun k => { sig := k }

/-- The module of a builtin sentence, by its source and line. -/
def moduleAt (src : String) (line : Nat) : Option Nat :=
  (List.range library.length).find? fun i =>
    let m := library.getD i default
    m.first ≤ line && line ≤ m.last && m.src == src

end KCore
