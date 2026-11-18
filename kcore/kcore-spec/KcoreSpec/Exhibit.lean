/-
  KCore. A value of a sort, exhibited by a search over the definition's data.

  A rule read without a variable of the axiom it comes from (`Parse.splitRule`, `Parse.unheldBinders`)
  needs an element of the variable's sort, and a clause variable that neither the patterns nor the
  conditions hold is read without an owed fact where its sort has a value (`Semantics.valued`,
  RightHeld.lean). The search exhibits a value: a ground term built from literals, empty
  collections, constructors and injections, checked to apply no open generator
  (`rawFree_of_exhibit`), of which the semantics gives the sort (`sortOf_of_exhibit`).

  Every sort test of the search is `sortOfT` read from the definition's tables (`tables`), which hold
  no interpretation of the parameters; at a value that applies no open generator it is
  `Semantics.sortOf` (`sortOfT_tables`). So the search is the same at every interpretation of the
  parameters by its definition (`exhibit_withHooks`), and its value is a value of the sort at every
  interpretation (`Faithful.sortOf_withHooks_of_exhibit`), where `Γ` entails an element of the sort
  in every model (`Faithful.inhabited_of_exhibit_withHooks`). At a sort whose only values apply an
  open generator no value is exhibited: at an interpretation that answers the generator outside the
  sort, the sort has no value. The search may miss a value; it states nothing where it finds none.
-/
import KcoreSpec.Tables
import KcoreSpec.Kore.KernelRfl

set_option autoImplicit false

namespace KCore.Parse

/-- The value of each sort first in `l`. -/
def firstPerSort (l : List (Srt × GroundTerm)) : List (Srt × GroundTerm) :=
  l.foldl (fun acc (s, v) => if acc.any (·.1 == s) then acc else acc ++ [(s, v)]) []

/-- Literals (`0`, `false`, the empty token) of Int, Bool, String, KConfigVar, Bytes and the
library's token, byte and carrier sorts, and the empty collections of the collection sorts, each
with the sort the tables `T` give it. -/
def exhibitSeeds (c : Semantics) (T : Tables) : List (Srt × GroundTerm) :=
  let litSorts := [Srt.int, Srt.bool, Srt.string, Srt.kconfigVar, Srt.bytes] ++ c.lib.tokenSorts ++
    c.lib.byteSorts ++ c.lib.carriers.map (·.1)
  let lits := litSorts.flatMap fun s =>
    [(s, GroundTerm.dv s (.int 0)), (s, .dv s (.bool false)), (s, .dv s (.tok ""))]
  let colls := c.colls.flatMap fun k =>
    [(k.sort, GroundTerm.map k.sort []), (k.sort, .set k.sort []), (k.sort, .list k.sort [])]
  firstPerSort ((lits ++ colls).filter fun (s, v) => sortOfT T c.lib v == some s)

/-- One round: a constructor applied to the values `acc` holds of its argument sorts, and an
injection of a value `acc` holds, at each sort `acc` has no value of, each with the sort the tables
`T` give it. -/
def exhibitRound (c : Semantics) (T : Tables) (acc : List (Srt × GroundTerm)) : List (Srt × GroundTerm) :=
  let has := fun (s : Srt) => acc.any (·.1 == s)
  let ctors := c.ctorSigs.filterMap fun k => if has k.result then none else do
    let args ← k.args.mapM fun a => acc.lookup a
    let v := GroundTerm.ctor k.name args
    if sortOfT T c.lib v == some k.result then some (k.result, v) else none
  let injs := c.subsorts.filterMap fun (a, b) => if has b then none else do
    let w ← acc.lookup a
    let v := match w with
      | .inj a' _ w' => GroundTerm.inj a' b w'
      | _ => GroundTerm.inj a b w
    if sortOfT T c.lib v == some b then some (b, v) else none
  firstPerSort (ctors ++ injs)

/-- `n` rounds from `acc`, or fewer where a round adds nothing. -/
def exhibitN (c : Semantics) (T : Tables) : Nat → List (Srt × GroundTerm) → List (Srt × GroundTerm)
  | 0, acc => acc
  | n + 1, acc => match exhibitRound c T acc with
    | [] => acc
    | new => exhibitN c T n (acc ++ new)

/-- A value of the sort `s` the search exhibits (`exhibitSeeds`, then rounds of `exhibitRound`, each
adding a sort, as many as there are constructors and subsort pairs), over the tables of `c`, checked:
one the tables give the sort `s` and that applies no open generator (`Semantics.rawFree`), so that
it is a value of `s` (`sortOf_of_exhibit`) at every interpretation of the parameters
(`Faithful.sortOf_withHooks_of_exhibit`). -/
def exhibit? (c : Semantics) (s : Srt) : Option GroundTerm :=
  let T := tables c
  ((exhibitN c T (c.ctorSigs.length + c.subsorts.length) (exhibitSeeds c T)).lookup s).filter
    fun v => sortOfT T c.lib v == some s && c.rawFree v

/-- `exhibit_withHooks`, as one closed equation of functions, checked by the kernel alone. -/
private theorem exhibit_withHooks_fun :
    (fun (c : Semantics) (H : HookParams) => exhibit? (c.withHooks H)) = fun c _ => exhibit? c := by
  kernel_rfl

/-- The search reads no interpretation of the parameters. -/
theorem exhibit_withHooks (c : Semantics) (H : HookParams) : exhibit? (c.withHooks H) = exhibit? c :=
  congrFun (congrFun exhibit_withHooks_fun c) H

theorem exhibit_parts {c : Semantics} {s : Srt} {v : GroundTerm} (h : exhibit? c s = some v) :
    c.sortOf v = some s ∧ c.rawFree v = true := by
  unfold exhibit? at h
  simp only [Option.filter_eq_some_iff, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨(sortOfT_tables c v h.2.2).symm.trans h.2.1, h.2.2⟩

theorem sortOf_of_exhibit {c : Semantics} {s : Srt} {v : GroundTerm} (h : exhibit? c s = some v) :
    c.sortOf v = some s :=
  (exhibit_parts h).1

/-- An exhibited value applies no open generator. -/
theorem rawFree_of_exhibit {c : Semantics} {s : Srt} {v : GroundTerm} (h : exhibit? c s = some v) :
    c.rawFree v = true :=
  (exhibit_parts h).2

end KCore.Parse
