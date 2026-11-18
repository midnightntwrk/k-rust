/-
  KCore, checked layer (P1.3; ARCHITECTURE.md §3.2): the features a definition uses, computed from its
  core (and its configuration's shape, from the presentation's cell tree) and decided by the kernel. A feature set describes a definition ("the IMP fragment" is the
  value of `uses` on kink's IMP), it is not a library: one core interprets every definition, and a
  generic meta-theorem whose proof does not yet cover a feature takes `c.uses p ≤ S` as a hypothesis
  until it does (soundness and completeness, staged: ARCHITECTURE.md §3.9). No theorem of the
  library takes one today.
-/
import KcoreSpec.DefinitionWf

set_option autoImplicit false

namespace KCore

/-- What a definition uses, each a Boolean. -/
structure Features where
  /-- functions defined by equations -/
  functions : Bool
  /-- a function that is not `[total]` (where no clause applies, its value is the interpretation's,
  `Semantics.fnRest`) -/
  partialFns : Bool
  /-- a clause of a function of a priority other than 50 (`[owise]`, `priority`) -/
  owiseFns : Bool
  /-- rules of more than one priority (`priority`, `[owise]` rules) -/
  priorities : Bool
  /-- a rule with a `requires` -/
  requires : Bool
  /-- Int's interpreted hooks -/
  ints : Bool
  /-- Bool's interpreted hooks (beyond `true` and `false`) -/
  bools : Bool
  /-- `==K`, `=/=K` -/
  kequal : Bool
  /-- Map's interpreted hooks -/
  maps : Bool
  /-- a map pattern `K |-> V M` in a left-hand side -/
  mapPatterns : Bool
  /-- Set's interpreted hooks -/
  sets : Bool
  /-- the library's token sorts (Id, String) -/
  tokens : Bool
  /-- several cells beside `<k>` (a configuration of more than one leaf) -/
  cells : Bool
  /-- a declared subsort (besides the cells' `XCell < XCellOpt`) -/
  subsorts : Bool
  /-- parameter symbols with no registry meaning (P1.3) -/
  params : Bool
  /-- own hooked symbols with a registry meaning -/
  hooked : Bool
  deriving Repr, DecidableEq

namespace Features

/-- Every feature f uses, g uses. -/
def le (f g : Features) : Bool :=
  (!f.functions || g.functions) && (!f.partialFns || g.partialFns) && (!f.owiseFns || g.owiseFns) &&
  (!f.priorities || g.priorities) && (!f.requires || g.requires) && (!f.ints || g.ints) &&
  (!f.bools || g.bools) && (!f.kequal || g.kequal) && (!f.maps || g.maps) &&
  (!f.mapPatterns || g.mapPatterns) && (!f.sets || g.sets) && (!f.tokens || g.tokens) &&
  (!f.cells || g.cells) && (!f.subsorts || g.subsorts) && (!f.params || g.params) && (!f.hooked || g.hooked)

instance : LE Features := ⟨fun f g => f.le g = true⟩
instance (f g : Features) : Decidable (f ≤ g) := inferInstanceAs (Decidable (f.le g = true))

/-- The union of two feature sets. -/
def union (f g : Features) : Features :=
  ⟨f.functions || g.functions, f.partialFns || g.partialFns, f.owiseFns || g.owiseFns,
   f.priorities || g.priorities, f.requires || g.requires, f.ints || g.ints, f.bools || g.bools,
   f.kequal || g.kequal, f.maps || g.maps, f.mapPatterns || g.mapPatterns, f.sets || g.sets,
   f.tokens || g.tokens, f.cells || g.cells, f.subsorts || g.subsorts, f.params || g.params,
   f.hooked || g.hooked⟩

end Features

mutual
  /-- The symbols a term applies. -/
  def Term.syms : Term → List Sym
    | .var _ => []
    | .dv _ _ => []
    | .inj _ _ t => Term.syms t
    | .as t _ => Term.syms t
    | .app f ts => f :: Term.symsList ts
    termination_by structural t => t
  def Term.symsList : List Term → List Sym
    | [] => []
    | t :: ts => Term.syms t ++ Term.symsList ts
    termination_by structural ts => ts
end

namespace Semantics
variable (c : Semantics)

/-- Every term of the core: rules' sides, `requires` and `ensures`, clauses' patterns, `requires`,
right-hand sides and `ensures`. -/
def terms : List Term :=
  c.rules.flatMap (fun r => [r.lhs, r.rhs] ++ r.req.toList ++ r.ens.toList) ++
  c.fns.flatMap fun f => f.clauses.flatMap fun cl => cl.pats ++ [cl.rhs] ++ cl.req.toList ++ cl.ens.toList

/-- The symbols the core's terms apply. -/
def usedSyms : List Sym := Term.symsList c.terms

/-- Some symbol of `fs` is applied. -/
def usesAny (fs : List Sym) : Bool := c.usedSyms.any fs.contains

/-- The features `c` uses, the configuration's shape read off its cell tree `p`. -/
def uses (p : Presentation) : Features :=
  { functions := !c.fns.isEmpty
    partialFns := c.fns.any (!·.total)
    owiseFns := c.fns.any fun f => f.clauses.any (·.prio != 50)
    priorities := match c.rules with
      | [] => false
      | r :: rs => rs.any (·.prio != r.prio)
    requires := c.rules.any (·.req.isSome)
    ints := c.usesAny [intAdd, intSub, intMul, intTDiv, intTMod, intEDiv, intEMod, intMin, intMax,
      intLt, intLe, intGt, intGe, intEq, intNe, intAbs, freshInt, intShr, intShl, intLog2, intPowMod, intBitRange,
      intSignExtBitRange]
    bools := c.usesAny [boolNot, boolAnd, boolAndThen, boolOr, boolOrElse, boolXor, boolImplies, boolEq, boolNe]
    kequal := c.usesAny [kEq, kNe]
    maps := c.usesAny [mapUnit, mapElem, mapConcat, mapUpdate, mapRemove, mapLookup, mapLookupOrDefault,
      mapInKeys, mapSize, mapRemoveAll, mapKeys]
    mapPatterns := Term.symsList (c.rules.map (·.lhs)) |>.any patternHooks.contains
    sets := c.usesAny [setUnit, setElem, setConcat, setUnion, setIntersect, setDifference, setIn,
      setInclusion, setSize]
    tokens := !c.lib.tokenSorts.isEmpty
    cells := decide ((cellLeavesList p.config).length > 1)
    subsorts := decide (c.userSubsorts.length > p.cellSubsorts.length)
    params := c.params.any (·.impl.isNone)
    hooked := c.params.any (·.impl.isSome) }

end Semantics

end KCore
