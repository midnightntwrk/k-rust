/-
  Rules the reader refuses with a reason that names the construct, and the account of two kompile
  runs of one K text, read from K 7.1.337 kompile's own KORE (the construct triage's fixtures, their
  kompiled texts copied). Run from the package root: `lake env lean test/RuleRefusals.lean`.
  - `rulecool` (e2-rule): `rule <k> c(1) => b(1) ... </k> [cool]`, which kompile writes with the
    `requires` `isKResult(HOLE)`, HOLE bound by no side: `unboundVariable`.
  - `unbound` (e2-unbound): `a() => b(X)` with `[unboundVariables(X)]`: X in the right side only:
    `unboundVariable`.
  - `cooleq` (e2-cool-eq): `f(X) => X [cool]` on a function: the equation's `requires` holds HOLE,
    which the arguments do not bind and which is the condition's only variable (a closed condition):
    read.
  - `exrhs` (e3-vars): `c(_, _Y) => d(?Z:Int)`, a right side under `\exists`: `existentialRhs`.
  - `antileft` (e8-enable-kore-antileft): a left side that is an alias application (`rule29LHS`):
    `aliasApplication`.
  - `mlag` (e3-ml-ag): `#AG(b())`, the prelude alias `allPathGlobally` at a sort: `aliasApplication`,
    not `parametricSymbol`.
  - `symrule` (e2-symbolic-rule): a rule declared `[symbolic]`: read, the attribute ignored (which
    terms a prover applies the rule to is no statement of the theory; the text states the rewrite
    axiom), as the construct table decides.
  - `kvref`, `kvtimeout` (e8-ref, e8-timeout): one K text kompiled twice, the second with `--timeout
    10m`, which changes no sentence but the numbers of the generated variables: the account's
    `kernelText` comparison (`Parse.kernelAbsent`) gives both texts the same absent sentences.
-/
import KcoreSpec

set_option autoImplicit false

open KCore

/-- The first refusal of the text at `path` (`Parse.refusals`) but an alias's declaration, which
`classify` refuses before the rule applying the alias, or "read". -/
def verdict (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match (Parse.refusals k).find? (·.reason != .aliasDeclaration) with
    | none => "read"
    | some r => s!"{r.reason.name} {r.detail}"

/-- The number of sentences of `kernelText` the text at `path` does not hold. -/
def absent (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k => return match Parse.parse k with
    | .ok d => s!"{(Parse.kernelAbsent k d).length}"
    | .error r => s!"refused {r.toText}"

/--
info: rulecool: unboundVariable VarHOLE: in the requires, not bound by the left side
unbound: unboundVariable VarX: in the right side, not bound by the left side
cooleq: read
exrhs: existentialRhs Var'Ques'Z
antileft: aliasApplication rule29LHS
mlag: aliasApplication allPathGlobally
symrule: read
kernelText absent: kvref 4, kvtimeout 4
-/
#guard_msgs in
#eval show IO Unit from do
  for n in ["rulecool", "unbound", "cooleq", "exrhs", "antileft", "mlag", "symrule"] do
    IO.println s!"{n}: {← verdict s!"f2-examples/{n}.kompile.kore"}"
  IO.println s!"kernelText absent: kvref {← absent "f2-examples/kvref.kompile.kore"}, kvtimeout {← absent "f2-examples/kvtimeout.kompile.kore"}"
