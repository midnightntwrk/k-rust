/-
  The KORE text's metadata and declarations, as the core's presentation and Γ_D's generation read
  them: source locations, a sentence's id and location, a constructor's declaration, the
  generators of a sort, the ids of a sort's generated equations. Reviewed layer (kept from F0's
  Definition, DefinitionWf, FixedSignature and Prelude when F0 was removed, P1.4).
-/

set_option autoImplicit false

namespace KoreAML

/-- A constructor: KORE symbol, argument sorts, result sort. -/
structure CtorSig where
  name : String
  args : List String
  result : String
  deriving Repr, DecidableEq

/-- A source location `Location(l1,c1,l2,c2)`, copied by kompile into attributes. -/
structure Loc where
  l1 : Nat
  c1 : Nat
  l2 : Nat
  c2 : Nat
  deriving Repr, DecidableEq, Inhabited

/-- What kompile attaches to a sentence from the source: its unique id (a hash) and its
location. The translation reads no attribute but `[simplification]` (TRANSLATION.md
D-attributes), so neither matters to Γ_D. -/
structure Meta where
  uid : String
  loc : Loc
  deriving Repr, Inhabited

/-- Each item paired with its partner at the same position, `default` where `bs` is short. -/
def withPres {α β : Type} [Inhabited β] : List α → List β → List (α × β)
  | [], _ => []
  | a :: as, bs => (a, bs.headD default) :: withPres as bs.tail

/-- A generator of a constructor sort N: a constructor with result N, or the injection from a
subsort of N. -/
inductive Gen where
  | ctor (c : CtorSig)
  | inj (src : String)
  deriving Repr, DecidableEq

def nodup : List String → Bool
  | [] => true
  | a :: as => !as.contains a && nodup as

def Gen.argSorts : Gen → List String
  | .ctor c => c.args
  | .inj a => [a]

/-- The ids of a sort's generated equations: `projectX`, `isX = true`, `isX = false`. -/
structure SortUids where
  proj : String
  isTrue : String
  isFalse : String
  deriving Repr, DecidableEq, Inhabited

end KoreAML
