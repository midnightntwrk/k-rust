/-
  A user's hooked symbol named `Lblite`, read from K 7.1.337 kompile's KORE of the construct
  fixture rdr-ite-own-hook (`f2-examples/rdr-ite-own-hook.kompile.kore`: `syntax {S} S ::=
  pick(Bool, S, S) [function, symbol(ite), hook(KEQUAL.ite)]`, K-EQUAL not imported), and of that
  text with the declaration's shape or hook changed. Run from the package root:
  `lake env lean test/IteOwnHookShape.lean`.
  - The declaration `hooked-symbol Lblite{SortS}(SortBool{}, SortS, SortS) : SortS
    [hook{}("KEQUAL.ite")]` has the registry `ite`'s name, shape and hook (`regIteDeclIoh`): the
    text is read, every sentence accounted for.
  - The same name with another shape (arguments `S, Bool, S`; result `Bool`; two sort variables)
    or another hook (`BOOL.and`, a registry hook of another symbol; `FOO.bar`, none) is a
    declaration of the text's own under a registry symbol's name: refused `registrySymbolName`.
    (kompile writes no definition for a sort-parametric hooked symbol whose hook is not
    `KEQUAL.ite`, fixture rdr-ite-own-hookand; these texts are the reader's test only.)
-/
import KcoreSpec

set_option autoImplicit false

open KCore

namespace IteOwnHookShapeTest

def path : String := "f2-examples/rdr-ite-own-hook.kompile.kore"

/-- The declaration as kompile writes it, up to its attributes. -/
def decl : String := "hooked-symbol Lblite{SortS}(SortBool{}, SortS, SortS) : SortS [function{}(), hook{}(\"KEQUAL.ite\")"

/-- The reader's verdict on the text with `decl` replaced by `by`: the refusal, or the sentences
unaccounted. -/
def verdict (by_ : String) : IO String := do
  let t ← IO.FS.readFile path
  unless (t.splitOn decl).length == 2 do throw (IO.userError "the declaration is not in the text once")
  match Kore.parseDefinition (t.replace decl by_) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.parse k with
    | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).map fun r => s!"{r.head}: {r.detail}"}"
    | .error r => s!"{r.reason.name} {r.detail}"

/--
info: read; unaccounted []
read; unaccounted []
registrySymbolName Lblite
registrySymbolName Lblite
registrySymbolName Lblite
registrySymbolName Lblite
registrySymbolName Lblite
-/
#guard_msgs in
#eval show IO Unit from do
  -- as kompile writes it, and without the `function` attribute
  IO.println (← verdict decl)
  IO.println (← verdict "hooked-symbol Lblite{SortS}(SortBool{}, SortS, SortS) : SortS [hook{}(\"KEQUAL.ite\")")
  -- another shape
  IO.println (← verdict "hooked-symbol Lblite{SortS}(SortS, SortBool{}, SortS) : SortS [function{}(), hook{}(\"KEQUAL.ite\")")
  IO.println (← verdict "hooked-symbol Lblite{SortS}(SortBool{}, SortS, SortS) : SortBool{} [function{}(), hook{}(\"KEQUAL.ite\")")
  IO.println (← verdict "hooked-symbol Lblite{SortS, SortT}(SortBool{}, SortS, SortS) : SortS [function{}(), hook{}(\"KEQUAL.ite\")")
  -- another hook
  IO.println (← verdict "hooked-symbol Lblite{SortS}(SortBool{}, SortS, SortS) : SortS [function{}(), hook{}(\"BOOL.and\")")
  IO.println (← verdict "hooked-symbol Lblite{SortS}(SortBool{}, SortS, SortS) : SortS [function{}(), hook{}(\"FOO.bar\")")

end IteOwnHookShapeTest
