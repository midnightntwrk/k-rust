/-
  The statement of K's claim `sum-spec` (imp-semantics, `examples/specs/imp-sum-spec.k`) about the
  package's step under every interpretation of the hooks, written from the claim's text:

      claim [sum-spec]:
        <k> while (!($n <= 0)) { $s = $s + $n; $n = $n + -1; } => .K ... </k>
        <env> $n |-> (N:Int => 0)  $s |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2)) </env>
        requires N >=Int 0

  `Expected.«sum-spec»` is the proposition: for every interpretation `H`, integers `N ≥ 0`, `S`,
  rest `K` of the k cell and counter `C`, every complete path of `Step (defn.sem.withHooks H)` from
  the left side's configuration holds the right side's. Its hypotheses are `N ≥ 0` alone: no
  hypothesis on the functions (`FnHyp`) is among them. It is a definition, not a theorem: this
  module shows that the statement can be written over the package's `Step`, not that it holds.

  - The claim has neither `one-path` nor `all-path`, and the K text leaves the modality of such a
    claim open (`kk:t230-claim-reading` (d)). The statement takes the reading
    `kk:t230-claim-reading#claim-all-path` (`Reachability.AllPath`: a run that never ends is not
    constrained; a path ending elsewhere without meeting the target falsifies it).
  - The variables of the claim and the rest of the k cell are bound outside `AllPath`: each has one
    value on both sides (the frame `...` of the k cell is one variable of sort K on both sides,
    `kk:t230-claim-reading` (c)). The K text leaves open what the claim states of the cell it does
    not mention, the generated counter (`kk:t230-claim-reading` (e)). The statement takes the
    reading `kk:t230-claim-reading#counter-unchanged`: the counter is bound outside `AllPath` too,
    one value on both sides.
  - `requires N >=Int 0` is the fact `N ≥ 0` (`>=Int` is total and is `≥` on the integers).
  - `S +Int ((N +Int 1) *Int N /Int 2)`: `*Int` and `/Int` associate to the left and `/Int`
    truncates, so the term's one value is `S + ((N + 1) * N).tdiv 2`.
  - `-1` is the integer token (the lexer prefers the longer token, `kk:t230-claim-reading` (b)).

  `ExpectedKore.«sum-spec»` is the statement of the claim's KORE sentence
  (examples/ref-kimp/claims/imp-sum-spec/spec.kore, the frontend's command in kprove.txt beside it):
  there the modality is all-path's alias `weakAlwaysFinally` and the counter of the right side is
  bound by `\exists` (`kk:t230-claim-reading`, the ruling on the KORE sentence). It is
  `Expected.«sum-spec»` with the target's counter existential, inside the target predicate, and
  nothing else changed; `Expected.«sum-spec»` implies it (the target's counter taken to be `C`).

  `used` is the list of the constants each of the two propositions mentions, as elaborated (the
  coercions written out), checked against the list below. `instSorted` shows the left side
  inhabited: at `N = 3`, `S = 0`, the rest `.K` and the counter `0` it is a configuration under
  every `H`.
-/
import RefKimp.Core
import RefKimp.Syntax
import KcoreSpec.Reachability
import KcoreSpec.Params

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace RefKimp.Claims

open KCore KCore.Reachability RefKimp.Syntax

def Expected.«sum-spec» : Prop :=
  ∀ (H : HookParams) (N S : Int) (K : Tm Srt.k) (C : Int) (_hreq : N ≥ 0),
    AllPath (Step (RefKimp.defn.sem.withHooks H))
      (fun x => x.val =
        («<generatedTop>»
          («<k>» (Tm.kseq
            («while(_)_» («!_» («_<=_» (Tm.ident "$n") (Tm.int 0)))
              («{_}» («__»
                («_=_;» (Tm.ident "$s") («_+_» (Tm.ident "$s") (Tm.ident "$n")))
                («_=_;» (Tm.ident "$n") («_+_» (Tm.ident "$n") (Tm.int (-1)))))))
            K))
          («<env>» (Tm.map [(Tm.ident "$n", Tm.int N), (Tm.ident "$s", Tm.int S)]))
          («<generatedCounter>» (Tm.int C))).val)
      (fun z => z.val =
        («<generatedTop>»
          («<k>» K)
          («<env>» (Tm.map [(Tm.ident "$n", Tm.int 0),
            (Tm.ident "$s", Tm.int (S + ((N + 1) * N).tdiv 2))]))
          («<generatedCounter>» (Tm.int C))).val)

def ExpectedKore.«sum-spec» : Prop :=
  ∀ (H : HookParams) (N S : Int) (K : Tm Srt.k) (C : Int) (_hreq : N ≥ 0),
    AllPath (Step (RefKimp.defn.sem.withHooks H))
      (fun x => x.val =
        («<generatedTop>»
          («<k>» (Tm.kseq
            («while(_)_» («!_» («_<=_» (Tm.ident "$n") (Tm.int 0)))
              («{_}» («__»
                («_=_;» (Tm.ident "$s") («_+_» (Tm.ident "$s") (Tm.ident "$n")))
                («_=_;» (Tm.ident "$n") («_+_» (Tm.ident "$n") (Tm.int (-1)))))))
            K))
          («<env>» (Tm.map [(Tm.ident "$n", Tm.int N), (Tm.ident "$s", Tm.int S)]))
          («<generatedCounter>» (Tm.int C))).val)
      (fun z => ∃ C' : Int, z.val =
        («<generatedTop>»
          («<k>» K)
          («<env>» (Tm.map [(Tm.ident "$n", Tm.int 0),
            (Tm.ident "$s", Tm.int (S + ((N + 1) * N).tdiv 2))]))
          («<generatedCounter>» (Tm.int C'))).val)

/-- The left side at `N = 3`, `S = 0`, the rest `.K`, the counter `0`. -/
def inst : Tm Srt.top :=
  «<generatedTop>»
    («<k>» (Tm.kseq
      («while(_)_» («!_» («_<=_» (Tm.ident "$n") (Tm.int 0)))
        («{_}» («__»
          («_=_;» (Tm.ident "$s") («_+_» (Tm.ident "$s") (Tm.ident "$n")))
          («_=_;» (Tm.ident "$n") («_+_» (Tm.ident "$n") (Tm.int (-1)))))))
      Tm.dotk))
    («<env>» (Tm.map [(Tm.ident "$n", Tm.int 3), (Tm.ident "$s", Tm.int 0)]))
    («<generatedCounter>» (Tm.int 0))

/-- The instance is a configuration under every interpretation: the claim's left side is
inhabited (its hypothesis `3 ≥ 0` holds). -/
theorem instSorted (H : HookParams) :
    (RefKimp.defn.sem.withHooks H).sortOf inst.val = some topCellSort :=
  (Semantics.sortOf_withHooks_rawFree _ H (by decide +kernel)).trans (by decide +kernel)

/-- The constants of the library and of the package that each proposition mentions; the others
are Lean's own (`Int` with `+`, `*`, `-`, `≥` and `Int.tdiv`, lists, pairs, `Option`, `Eq`,
`Exists`, `Subtype.val`). -/
def used : List String := [
  "KCore.Config", "KCore.Definition.sem", "KCore.GroundTerm", "KCore.HookParams",
  "KCore.Reachability.AllPath", "KCore.Semantics.sortOf", "KCore.Semantics.withHooks", "KCore.Srt",
  "KCore.Srt.ident", "KCore.Srt.int", "KCore.Srt.k", "KCore.Srt.kitem", "KCore.Srt.top",
  "KCore.Step", "KCore.Tm", "KCore.Tm.ident", "KCore.Tm.inj", "KCore.Tm.int", "KCore.Tm.kseq",
  "KCore.Tm.map", "KCore.Tm.val", "KCore.topCellSort",
  "RefKimp.Srt.Expr", "RefKimp.Srt.Stmt", "RefKimp.Syntax.__", "RefKimp.Syntax.«!_»",
  "RefKimp.Syntax.«<env>»", "RefKimp.Syntax.«<generatedCounter>»", "RefKimp.Syntax.«<generatedTop>»",
  "RefKimp.Syntax.«<k>»", "RefKimp.Syntax.«_+_»", "RefKimp.Syntax.«_<=_»", "RefKimp.Syntax.«_=_;»",
  "RefKimp.Syntax.«while(_)_»", "RefKimp.Syntax.«{_}»", "RefKimp.defn"]

open Lean in
#eval show CoreM Unit from do
  for d in [``Expected.«sum-spec», ``ExpectedKore.«sum-spec»] do
    let some v := (← getEnv).find? d | throwError "no statement {d}"
    let cs := (v.value!.getUsedConstants.toList.map (·.toString)).filter fun n =>
      n.startsWith "KCore." || n.startsWith "RefKimp."
    let cs := cs.mergeSort (· ≤ ·)
    unless cs == used do throwError "{d} mentions {cs}"
    if cs.any (· == "KCore.FnHyp") then throwError "{d} mentions FnHyp"
  let axs ← collectAxioms ``instSorted
  unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "instSorted: axioms {axs}"

end RefKimp.Claims
