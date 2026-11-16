/-
  `lake exe gammad [file.kore] [--axioms i,j,…]`: reads a KORE definition at run time,
  translates it, and prints Γ_D in the papers' notation, with timings on stderr.
  With `--axioms i,j,…`, prints only those translated axioms, each after its KORE text;
  with `--raw i,j,…`, the same with AML primitives only (no notation recognized);
  (F0's `--spec` mode, which printed F0's verdict and its Γ_cons, was removed with F0 in P1.4;
  GAMMA_CONS.txt is its last output.)
  Default file: ../milestone-1/kore/definition.kore.
-/
import KcoreSpec.Kore.Translate
import KcoreSpec.Kore.Print

open KoreAML

def printItem (it : Item) : IO Unit := do
  IO.println s!"[{it.rule}] {it.label}"
  IO.println s!"  {Print.item it}"

def main (args : List String) : IO UInt32 := do
  let (file, sel) := match args with
    | [f, "--axioms", is] => (f, some is)
    | ["--axioms", is] => ("../milestone-1/kore/definition.kore", some is)
    | ["--raw", is] => ("../milestone-1/kore/definition.kore", some ("raw:" ++ is))
    | [f] => (f, none)
    | _ => ("../milestone-1/kore/definition.kore", none)
  let t0 ← IO.monoMsNow
  let input ← IO.FS.readFile file
  let .ok d := Kore.parseDefinition input
    | IO.eprintln "parse failed"; return 1
  let t1 ← IO.monoMsNow
  let T := Theory.ofDefinition d
  -- force the translation before timing it
  let nodes := T.all.foldl (fun n it => n + it.pat.size) 0
  let t2 ← IO.monoMsNow
  match sel with
  | some is =>
    let rawMode := is.startsWith "raw:"
    let idx := ((if rawMode then is.drop 4 |>.toString else is).splitOn ",").filterMap String.toNat?
    let axs := d.axioms
    for i in idx do
      match axs[i - 1]?, T.axioms[i - 1]? with
      | some a, some it =>
        IO.println s!"── {it.label}"
        IO.println s!"KORE: axiom\{{", ".intercalate (a.sortVars.map toString)}} {Kore.Printer.pattern a.pattern}"
        IO.println s!"AML:  {if rawMode then Print.raw it.names it.pat else Print.item it}"
        IO.println ""
      | _, _ => IO.eprintln s!"no axiom {i}"
  | none =>
    IO.println s!"# Γ_D of {file}"
    IO.println s!"# Γ^AML: {T.signature.length} axioms; AML(Γ): {T.axioms.length} axioms; {nodes} AML pattern nodes"
    IO.println ""
    IO.println "## Γ^AML (the encoding: TRANSLATION.md G-rules)"
    for it in T.signature do printItem it
    IO.println ""
    IO.println "## AML(Γ) (the KORE axioms, translated by T-axiom)"
    for it in T.axioms do printItem it
  let t3 ← IO.monoMsNow
  IO.eprintln s!"parse {t1 - t0} ms, translate {t2 - t1} ms, print {t3 - t2} ms; {T.all.length} axioms, {nodes} pattern nodes"
  return 0
