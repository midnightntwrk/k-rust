/-
  `lawHooks` (KcoreSpec/LawHooks.lean) at hand-built open generators, and its list lemmas at
  instances. Run from the package root: `lake env lean test/LawHooks.lean`. Kernel-checked.

  A semantics with five parameters of sort Int: `or` (raw, assoc), `bar` (raw, idem), `wrap` (raw,
  unary, no law), `plus` (not raw) and `band` (raw, assoc and idem). Under `lawHooks c H`:
  - `or` gives the right nesting of the flattened arguments: `or(or(x, y), z)` and `or(x, or(y, z))`
    are one value, `or(x, or(y, z))`;
  - `bar` merges equal arguments: `bar(x, x)` is x, `bar(x, y)` the application itself;
  - `wrap` gives the application itself (no law: no merge, even with one argument);
  - `plus` is H's;
  - `band` gives the right nesting of the flattened arguments, each at its first occurrence:
    `band(x, x)` is x; `band(band(x, y), band(x, y))` is `band(x, y)` (idempotence at a compound
    value, where no two adjacent leaves are equal); both groupings of three arguments are one value;
    `band(band(x, y), x)` is `band(x, y)` (true of this interpretation, not stated by the laws);
    `band(x, y)` and `band(y, x)` are two values.
-/
import KcoreSpec

set_option autoImplicit false

namespace KCore.LawHooksTest

open KCore

def orS : Sym := nRegSyms + 1
def barS : Sym := nRegSyms + 2
def wrapS : Sym := nRegSyms + 3
def plusS : Sym := nRegSyms + 4
def bandS : Sym := nRegSyms + 5

def lc : Semantics where
  lib := { sortsBelowKItem := [Srt.int] }
  sortNames := []
  symNames := []
  userSorts := []
  ctors := []
  fns := []
  userSubsorts := []
  pgmSort := Srt.k
  rules := []
  params := [{ sig := ⟨orS, [Srt.int, Srt.int], Srt.int⟩, raw := true, assoc := true },
    { sig := ⟨barS, [Srt.int, Srt.int], Srt.int⟩, raw := true, idem := true },
    { sig := ⟨wrapS, [Srt.int], Srt.int⟩, raw := true },
    { sig := ⟨plusS, [Srt.int, Srt.int], Srt.int⟩ },
    { sig := ⟨bandS, [Srt.int, Srt.int], Srt.int⟩, raw := true, assoc := true, idem := true }]

def H7 : HookParams := ⟨fun _ _ => some (int 7)⟩

def x : GroundTerm := int 1
def y : GroundTerm := int 2
def z : GroundTerm := int 3
def orT (a b : GroundTerm) : GroundTerm := .ctor orS [a, b]

def same' : Option GroundTerm → Option GroundTerm → Bool
  | some v, some w => Exec.same v w
  | none, none => true
  | _, _ => false

example :
    -- `or`: both groupings flatten to [x, y, z] and nest to the right
    same' ((lawHooks lc H7).app orS [orT x y, z]) (some (orT x (orT y z))) = true ∧
    same' ((lawHooks lc H7).app orS [x, orT y z]) (some (orT x (orT y z))) = true ∧
    -- `bar`: equal arguments merged, distinct ones kept
    same' ((lawHooks lc H7).app barS [x, x]) (some x) = true ∧
    same' ((lawHooks lc H7).app barS [x, y]) (some (.ctor barS [x, y])) = true ∧
    -- `wrap`: the application itself
    same' ((lawHooks lc H7).app wrapS [x]) (some (.ctor wrapS [x])) = true ∧
    -- `plus`: H's answer
    same' ((lawHooks lc H7).app plusS [x, y]) (some (int 7)) = true ∧
    same' ((lawHooks lc HookParams.none).app plusS [x, y]) none = true := by
  decide +kernel

def bandT (a b : GroundTerm) : GroundTerm := .ctor bandS [a, b]

example :
    -- `band`: idempotence at a value and at a compound value
    same' ((lawHooks lc H7).app bandS [x, x]) (some x) = true ∧
    same' ((lawHooks lc H7).app bandS [bandT x y, bandT x y]) (some (bandT x y)) = true ∧
    -- both groupings of three arguments one value
    same' ((lawHooks lc H7).app bandS [bandT x y, z]) (some (bandT x (bandT y z))) = true ∧
    same' ((lawHooks lc H7).app bandS [x, bandT y z]) (some (bandT x (bandT y z))) = true ∧
    -- a later occurrence dropped; no commutativity
    same' ((lawHooks lc H7).app bandS [bandT x y, x]) (some (bandT x y)) = true ∧
    same' ((lawHooks lc H7).app bandS [x, y]) (some (bandT x y)) = true ∧
    same' ((lawHooks lc H7).app bandS [y, x]) (some (bandT y x)) = true ∧
    Exec.same (bandT x y) (bandT y x) = false := by
  decide +kernel

/-! The list lemmas at instances. -/

example : lawFlat orS (lawNest orS [x, y, z]) = [x, y, z].flatMap (lawFlat orS) :=
  lawFlat_lawNest orS [x, y, z] (by decide)

example : lawFlat orS (lawNest orS (lawFlat orS (orT (orT x y) z))) = lawFlat orS (orT (orT x y) z) :=
  lawFlat_lawNest_lawFlat orS _

example : lawNest orS (lawFlat orS (lawNest orS [x, y, z])) = lawNest orS [x, y, z] :=
  lawNest_lawFlat orS [x, y, z] (by decide) (by decide +kernel)

example : lawMerge (lawMerge [x, x, y, y, x]) = lawMerge [x, x, y, y, x] := lawMerge_idem _

example : (lawMerge [x, x, y, y, x]).length = 3 := by decide +kernel

end KCore.LawHooksTest

#print axioms KCore.lawFlat_lawNest
#print axioms KCore.lawFlat_lawNest_lawFlat
#print axioms KCore.lawNest_lawFlat
#print axioms KCore.lawMerge_idem
