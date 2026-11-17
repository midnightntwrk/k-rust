/-
  The generator of the places the kimp tie files name (`examples/ref-kimp/RefKimp/definition.kore`,
  user module `IMP`), by evaluation (`#eval`) of the library's definitions on KCore's parse of the
  text. Nothing printed here is trusted: each place is a hint that the kernel checks in the file
  that states it, where a wrong one makes the decision false. Run from the package root:
  `lake env lean test/TieKimpHints.lean`; it prints Lean text to paste.

  - `consPairs` (test/TieKimpCons.lean): for each user sentence, the reading `ConsHint` of it as a
    constructor sentence. The sort is the place in `consSorts c` of the sort the sentence states;
    the generators are found by the library's `tieFunB`, `tieInjB`, `tieDistB` (kind 0, 1, 2 by the
    sentence's shape: `\exists`, `\implies`, `\not`), the first such generator, or pair, in the
    sort's order; the item places are the first places in `consItemsK c` (computed once) of the
    generators' Cons-Fun, Cons-Inj and Cons-Dist items, in the order `consDistAt` reads them.
  - `declPos` (test/TieKimpDecls.lean): for each item of `declItems`, its first place in
    `sigItems c`, pattern for pattern.
  - The signature (test/TieKimpSig.lean): the lengths of `sigItems c` and of the text's signature,
    and the places of the surplus items (`surplusItem`), which are the costly ones of `sig_origin`.

  A reorder of `consItemsK` or `sigItems` in the library is then a regeneration: run this file and
  replace the lists.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore ML Faithful KoreAML

namespace KCore.TieKimpHints

/-- The reading of a constructor sentence as `ConsHint`'s seven fields. -/
abbrev HintGen := Nat × Nat × Nat × Nat × Nat × Nat × Nat

/-- The first place of the pattern `φ` among `its`. -/
def placeOf (its : Array Item) (φ : KoreAML.P) : Option Nat := its.findIdx? (·.pat == φ)

/-- The reading of the axiom `a`, by the sentence's shape, the sort it states, and the first
generator (or pair) of that sort the library's checks accept. -/
def hintOf (c : Semantics) (its : Array Item) (a : Kore.Axiom) : Option HintGen := Id.run do
  let sorts := consSorts c
  let sortOf : Option Kore.KSort := match a.pattern with
    | .exist _ _ (.equals s _ _ _) => some s
    | .implies s _ _ => some s
    | .not s _ => some s
    | _ => none
  let some s := sortOf | return none
  for h : si in [0:sorts.length] do
    let N := sorts[si]
    unless KoreAML.srt (c.sortName N) == s do continue
    let gs := (c.gens N).map (Gen.toK c)
    let n := c.sortName N
    match a.pattern with
    | .exist .. =>
      for h : i in [0:gs.length] do
        let g := gs[i]
        if tieFunB c N g a then
          if let some k1 := placeOf its (KoreAML.Cons.funItem n g).pat then
            return some (0, si, i, 0, k1, 0, 0)
    | .implies .. =>
      for h : i in [0:gs.length] do
        let g := gs[i]
        if tieInjB c N g a then
          if let (some k1, some k2) :=
              (placeOf its (KoreAML.Cons.funItem n g).pat, placeOf its (KoreAML.Cons.injItem n g).pat) then
            return some (1, si, i, 0, k1, k2, 0)
    | .not _ (.and _ [p1, _]) =>
      let t := KoreAML.tableOf a.sortVars a.pattern
      let vs := tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups
      for h : i in [0:gs.length] do
        let g := gs[i]
        let xs := vs.take g.argSorts.length
        let ix := xs.map fun k => t.ev (KoreAML.evarKey k)
        unless KoreAML.tr ⟨t, []⟩ p1 == KoreAML.Cons.genPat n g (ix.map .evar) do continue
        for h : j in [0:gs.length] do
          let g' := gs[j]
          if tieDistB c N g g' a then
            if let (some k1, some k2, some k3) :=
                (placeOf its (KoreAML.Cons.funItem n g).pat, placeOf its (KoreAML.Cons.funItem n g').pat,
                  placeOf its (KoreAML.Cons.distItem n g g').pat) then
              return some (2, si, i, j, k1, k2, k3)
    | _ => pure ()
  return none

/-- Lean text of a list of entries, `perLine` to a line. -/
def listText (xs : List String) (perLine : Nat) : String := Id.run do
  let mut out := "["
  for h : i in [0:xs.length] do
    if i > 0 then out := out ++ (if i % perLine == 0 then ",\n   " else ", ")
    out := out ++ xs[i]
  return out ++ "]"

/-- The text, read and parsed as `kore_term` and `definition_of` read it. -/
def load (path : String) : IO (Kore.Definition × Definition) := do
  let k ← match Kore.parseDefinition (← IO.FS.readFile path) with
    | .error e => throw (IO.userError s!"KORE read error {e}")
    | .ok k => pure k
  match Parse.parse k with
  | .ok d => return (k, d)
  | .error r => throw (IO.userError s!"refused {r.toText}")

def main (path : String) : IO Unit := do
  let (kore, defn) ← load path
  let c := defn.sem
  -- consPairs
  let its := (consItemsK c).toArray
  let user := kore.axiomDecls.filter (·.module == "IMP")
  let mut pairs : Array String := #[]
  let mut idx : Array Nat := #[]
  for ad in user do
    if let some (k, s, g, g', k1, k2, k3) := hintOf c its ad.ax then
      pairs := pairs.push s!"(U.ax{ad.index}, ⟨{k}, {s}, {g}, {g'}, {k1}, {k2}, {k3}⟩)"
      idx := idx.push ad.index
  IO.println s!"-- consItemsK c: {its.size} items; {pairs.size} constructor sentences read"
  IO.println s!"-- their indices: {idx.toList}"
  IO.println ("noncomputable def consPairs : List (AxiomDecl × ConsHint) :=\n  " ++ listText pairs.toList 3)
  -- declPos
  let sig := (sigItems c).toArray
  let hasSym := fun (n : String) => (kernelSyms c).any fun k => c.symName k.name == n
  let plainSorts := kore.sortDecls.filter (·.params.isEmpty)
  let plainSyms := kore.symbolDecls.filter fun sd => sd.params.isEmpty && hasSym sd.name
  let declItems := plainSorts.map sortConstantItem ++ plainSyms.map arityItem
  let pos := declItems.map fun it => placeOf sig it.pat
  if pos.any (·.isNone) then
    IO.println s!"-- declItems without a place in sigItems c: {((List.range pos.length).zip pos).filter (·.2.isNone) |>.map (·.1)}"
  IO.println s!"-- declItems: {declItems.length}"
  IO.println ("def declPos : List Nat :=\n  " ++ listText (pos.map fun p => toString (p.getD 0)) 28)
  -- the signature
  let text := (Theory.ofDefinition kore).signature
  let declared := sig.toList.map fun it => text.any (·.pat == it.pat)
  let surplus := sig.toList.map fun it => surplusItem kore it
  let places := fun (l : List Bool) => ((List.range l.length).zip l).filterMap fun (i, b) => if b then some i else none
  IO.println s!"-- sigItems c: {sig.size} items; the text's signature: {text.length}"
  IO.println s!"-- surplus (and not declared): {places ((declared.zip surplus).map fun (d, s) => !d && s)}"
  IO.println s!"-- declared: {(places declared).length}; neither: {places ((declared.zip surplus).map fun (d, s) => !d && !s)}"

end KCore.TieKimpHints

#eval KCore.TieKimpHints.main "examples/ref-kimp/RefKimp/definition.kore"
