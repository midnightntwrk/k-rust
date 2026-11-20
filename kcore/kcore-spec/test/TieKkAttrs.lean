/-
  Attribute agreement (C14, layer 1) on kore.k's text as kompile wrote it
  (`examples/ref-kk/RefKk/definition.kore`), on the literals `kore` and `defn`. Nothing here reads
  `Parse.parse` or `emit`. Run from the package root: `lake env lean test/TieKkAttrs.lean`.

  - `attrs_agree`: `attrsAgree kore defn = true`, joined from its five conjuncts (constructors,
    functions, hooks, collection symbols, priorities).
  - `instDecls_nil`: no symbol name of the semantics ends with a closing brace (`namesR_all`, by
    ranges of 50 names), so the semantics has no instance of a sort-parametric declaration and the
    rows `symDeclsAt` compares are the text's symbol declarations (`symDeclsAt_eq`).
  - `attrs_ctors`, `attrs_fns`, `attrs_hooks`: each conjunct is `List.all` of its row predicate
    (`ctorP`, `fnsP`, `hooksP`, the bodies of `AttrsAgree.ctors`, `fns`, `hooks`) over the 311
    declarations, decided by ranges (`ctorsR_a`, `fnsR_a`, `hooksR_a`) joined by `tieAll_range`;
    `attrs_colls` and `attrs_prios` are one kernel decision each.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKk

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kk/RefKk/definition.kore"
definition_of defn from "examples/ref-kk/RefKk/definition.kore"

/-! ## No instance of a sort-parametric declaration -/

theorem namesR_0 : (((defn.sem.symNames).drop 0).take 50).all (fun m => (AttrsAgree.instBase m).isNone) = true := by decide +kernel
theorem namesR_50 : (((defn.sem.symNames).drop 50).take 50).all (fun m => (AttrsAgree.instBase m).isNone) = true := by decide +kernel
theorem namesR_100 : (((defn.sem.symNames).drop 100).take 50).all (fun m => (AttrsAgree.instBase m).isNone) = true := by decide +kernel
theorem namesR_150 : (((defn.sem.symNames).drop 150).take 50).all (fun m => (AttrsAgree.instBase m).isNone) = true := by decide +kernel
theorem namesR_200 : (((defn.sem.symNames).drop 200).take 50).all (fun m => (AttrsAgree.instBase m).isNone) = true := by decide +kernel
theorem namesR_250 : (((defn.sem.symNames).drop 250).take 50).all (fun m => (AttrsAgree.instBase m).isNone) = true := by decide +kernel
theorem namesR_300 : (((defn.sem.symNames).drop 300).take 50).all (fun m => (AttrsAgree.instBase m).isNone) = true := by decide +kernel
theorem namesR_350 : ((defn.sem.symNames).drop 350).all (fun m => (AttrsAgree.instBase m).isNone) = true := by decide +kernel

theorem namesR_all : (defn.sem.symNames).all (fun m => (AttrsAgree.instBase m).isNone) = true :=
  tieAll_whole (p := fun m => (AttrsAgree.instBase m).isNone) <|
    tieAll_range (a := 0) (n := 50) namesR_0 <|
    tieAll_range (a := 50) (n := 50) namesR_50 <|
    tieAll_range (a := 100) (n := 50) namesR_100 <|
    tieAll_range (a := 150) (n := 50) namesR_150 <|
    tieAll_range (a := 200) (n := 50) namesR_200 <|
    tieAll_range (a := 250) (n := 50) namesR_250 <|
    tieAll_range (a := 300) (n := 50) namesR_300 <|
    namesR_350

/-- The semantics has no instance of a sort-parametric declaration of the text. -/
theorem instDecls_nil : AttrsAgree.instDecls kore defn.sem = [] := by
  unfold AttrsAgree.instDecls
  split
  · rfl
  · refine List.filterMap_eq_nil_iff.mpr fun m hm => ?_
    have h := List.all_eq_true.mp namesR_all m hm
    rw [Option.isNone_iff_eq_none] at h
    rw [h]; rfl

theorem symDeclsAt_eq : AttrsAgree.symDeclsAt kore defn.sem = AttrsAgree.symDecls kore := by
  unfold AttrsAgree.symDeclsAt; rw [instDecls_nil, List.append_nil]

/-! ## The row predicates of `ctors`, `fns` and `hooks` -/

/-- `AttrsAgree.ctors`' row: `constructor{}` exactly where the semantics has a constructor. -/
def ctorP (c : Semantics) : String × List Kore.AppPattern → Bool := fun (n, as) =>
  AttrsAgree.has as "constructor" == c.ctorSigs.any (c.symName ·.name == n)

/-- `AttrsAgree.fns`' row. -/
def fnsP (k : Kore.Definition) (c : Semantics) : String × List Kore.AppPattern → Bool := fun (n, as) =>
  let fn := AttrsAgree.has as "function" && !AttrsAgree.has as "hook"
  let isFn := c.allFns.any (c.symName ·.label == n)
  let own := (c.ctorSigs ++ c.params.map (·.sig) ++ c.ovlSigs).any (c.symName ·.name == n)
  let par := !(c.ctorSigs ++ c.ovlSigs).any (c.symName ·.name == n) &&
    (c.params.all fun p => c.symName p.sig.name != n || (p.impl.isNone && !p.raw)) && (AttrsAgree.eqnsOf k n).isEmpty
  (!isFn || (AttrsAgree.has as "function" && (!AttrsAgree.has as "hook" ||
    (AttrsAgree.strArg as "hook").any (regHookOf · == none)))) &&
    (!(fn && own) || isFn || par)

/-- `AttrsAgree.hooks`' row. -/
def hooksP (k : Kore.Definition) (c : Semantics) : String × List Kore.AppPattern → Bool := fun (n, as) =>
  let plain := k.symbolDecls.any fun sd => sd.name == n && sd.params.isEmpty
  match AttrsAgree.strArg as "hook" with
  | some h =>
    (hookSigs.all fun g => c.symName g.name != n || regHookOf h == some g.name || !plain) &&
    (c.params.all fun p => c.symName p.sig.name != n || p.impl == regHookOf h)
  | none =>
    (hookSigs.all fun g => c.symName g.name != n || (AttrsAgree.libFn g && AttrsAgree.has as "function") || !plain) &&
    c.params.all fun p => c.symName p.sig.name != n ||
      (p.impl.isNone && (p.raw != AttrsAgree.has as "function") && (AttrsAgree.eqnsOf k n).isEmpty)

theorem ctors_eq : AttrsAgree.ctors kore defn.sem = (AttrsAgree.symDecls kore).all (ctorP defn.sem) := by
  unfold AttrsAgree.ctors; rw [symDeclsAt_eq]; try rfl
theorem fns_eq : AttrsAgree.fns kore defn.sem = (AttrsAgree.symDecls kore).all (fnsP kore defn.sem) := by
  unfold AttrsAgree.fns; rw [symDeclsAt_eq]; try rfl
theorem hooks_eq : AttrsAgree.hooks kore defn.sem = (AttrsAgree.symDecls kore).all (hooksP kore defn.sem) := by
  unfold AttrsAgree.hooks; rw [symDeclsAt_eq]; try rfl

/-! ## Constructors, by ranges of 50 declarations -/

theorem ctorsR_0 : (((AttrsAgree.symDecls kore).drop 0).take 50).all (ctorP defn.sem) = true := by decide +kernel
theorem ctorsR_50 : (((AttrsAgree.symDecls kore).drop 50).take 50).all (ctorP defn.sem) = true := by decide +kernel
theorem ctorsR_100 : (((AttrsAgree.symDecls kore).drop 100).take 50).all (ctorP defn.sem) = true := by decide +kernel
theorem ctorsR_150 : (((AttrsAgree.symDecls kore).drop 150).take 50).all (ctorP defn.sem) = true := by decide +kernel
theorem ctorsR_200 : (((AttrsAgree.symDecls kore).drop 200).take 50).all (ctorP defn.sem) = true := by decide +kernel
theorem ctorsR_250 : (((AttrsAgree.symDecls kore).drop 250).take 50).all (ctorP defn.sem) = true := by decide +kernel
theorem ctorsR_300 : ((AttrsAgree.symDecls kore).drop 300).all (ctorP defn.sem) = true := by decide +kernel

theorem ctorsR_all : (AttrsAgree.symDecls kore).all (ctorP defn.sem) = true :=
  tieAll_whole (p := ctorP defn.sem) <|
    tieAll_range (a := 0) (n := 50) ctorsR_0 <|
    tieAll_range (a := 50) (n := 50) ctorsR_50 <|
    tieAll_range (a := 100) (n := 50) ctorsR_100 <|
    tieAll_range (a := 150) (n := 50) ctorsR_150 <|
    tieAll_range (a := 200) (n := 50) ctorsR_200 <|
    tieAll_range (a := 250) (n := 50) ctorsR_250 <|
    ctorsR_300

/-! ## Functions, by ranges of 25 declarations -/

theorem fnsR_0 : (((AttrsAgree.symDecls kore).drop 0).take 25).all (fnsP kore defn.sem) = true := by decide +kernel
theorem fnsR_25 : (((AttrsAgree.symDecls kore).drop 25).take 25).all (fnsP kore defn.sem) = true := by decide +kernel
theorem fnsR_50 : (((AttrsAgree.symDecls kore).drop 50).take 25).all (fnsP kore defn.sem) = true := by decide +kernel
theorem fnsR_75 : (((AttrsAgree.symDecls kore).drop 75).take 25).all (fnsP kore defn.sem) = true := by decide +kernel
theorem fnsR_100 : (((AttrsAgree.symDecls kore).drop 100).take 25).all (fnsP kore defn.sem) = true := by decide +kernel
theorem fnsR_125 : (((AttrsAgree.symDecls kore).drop 125).take 25).all (fnsP kore defn.sem) = true := by decide +kernel
theorem fnsR_150 : (((AttrsAgree.symDecls kore).drop 150).take 25).all (fnsP kore defn.sem) = true := by decide +kernel
theorem fnsR_175 : (((AttrsAgree.symDecls kore).drop 175).take 25).all (fnsP kore defn.sem) = true := by decide +kernel
theorem fnsR_200 : (((AttrsAgree.symDecls kore).drop 200).take 25).all (fnsP kore defn.sem) = true := by decide +kernel
theorem fnsR_225 : (((AttrsAgree.symDecls kore).drop 225).take 25).all (fnsP kore defn.sem) = true := by decide +kernel
theorem fnsR_250 : (((AttrsAgree.symDecls kore).drop 250).take 25).all (fnsP kore defn.sem) = true := by decide +kernel
theorem fnsR_275 : (((AttrsAgree.symDecls kore).drop 275).take 25).all (fnsP kore defn.sem) = true := by decide +kernel
theorem fnsR_300 : ((AttrsAgree.symDecls kore).drop 300).all (fnsP kore defn.sem) = true := by decide +kernel

theorem fnsR_all : (AttrsAgree.symDecls kore).all (fnsP kore defn.sem) = true :=
  tieAll_whole (p := fnsP kore defn.sem) <|
    tieAll_range (a := 0) (n := 25) fnsR_0 <|
    tieAll_range (a := 25) (n := 25) fnsR_25 <|
    tieAll_range (a := 50) (n := 25) fnsR_50 <|
    tieAll_range (a := 75) (n := 25) fnsR_75 <|
    tieAll_range (a := 100) (n := 25) fnsR_100 <|
    tieAll_range (a := 125) (n := 25) fnsR_125 <|
    tieAll_range (a := 150) (n := 25) fnsR_150 <|
    tieAll_range (a := 175) (n := 25) fnsR_175 <|
    tieAll_range (a := 200) (n := 25) fnsR_200 <|
    tieAll_range (a := 225) (n := 25) fnsR_225 <|
    tieAll_range (a := 250) (n := 25) fnsR_250 <|
    tieAll_range (a := 275) (n := 25) fnsR_275 <|
    fnsR_300

/-! ## Hooks, by ranges of 50 declarations -/

theorem hooksR_0 : (((AttrsAgree.symDecls kore).drop 0).take 50).all (hooksP kore defn.sem) = true := by decide +kernel
theorem hooksR_50 : (((AttrsAgree.symDecls kore).drop 50).take 50).all (hooksP kore defn.sem) = true := by decide +kernel
theorem hooksR_100 : (((AttrsAgree.symDecls kore).drop 100).take 50).all (hooksP kore defn.sem) = true := by decide +kernel
theorem hooksR_150 : (((AttrsAgree.symDecls kore).drop 150).take 50).all (hooksP kore defn.sem) = true := by decide +kernel
theorem hooksR_200 : (((AttrsAgree.symDecls kore).drop 200).take 50).all (hooksP kore defn.sem) = true := by decide +kernel
theorem hooksR_250 : (((AttrsAgree.symDecls kore).drop 250).take 50).all (hooksP kore defn.sem) = true := by decide +kernel
theorem hooksR_300 : ((AttrsAgree.symDecls kore).drop 300).all (hooksP kore defn.sem) = true := by decide +kernel

theorem hooksR_all : (AttrsAgree.symDecls kore).all (hooksP kore defn.sem) = true :=
  tieAll_whole (p := hooksP kore defn.sem) <|
    tieAll_range (a := 0) (n := 50) hooksR_0 <|
    tieAll_range (a := 50) (n := 50) hooksR_50 <|
    tieAll_range (a := 100) (n := 50) hooksR_100 <|
    tieAll_range (a := 150) (n := 50) hooksR_150 <|
    tieAll_range (a := 200) (n := 50) hooksR_200 <|
    tieAll_range (a := 250) (n := 50) hooksR_250 <|
    hooksR_300

/-! ## The five conjuncts -/

theorem attrs_ctors : AttrsAgree.ctors kore defn.sem = true := ctors_eq.trans ctorsR_all
theorem attrs_fns : AttrsAgree.fns kore defn.sem = true := fns_eq.trans fnsR_all
theorem attrs_hooks : AttrsAgree.hooks kore defn.sem = true := hooks_eq.trans hooksR_all
theorem attrs_colls : AttrsAgree.colls kore defn.sem = true := by decide +kernel
theorem attrs_prios : AttrsAgree.prios kore defn = true := by decide +kernel

/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,
hooks, collection symbols, priorities. -/
theorem attrs_agree : attrsAgree kore defn = true := by
  unfold attrsAgree
  rw [attrs_ctors, attrs_fns, attrs_hooks, attrs_colls, attrs_prios]
  rfl

end KCore.TieKk

#check @KCore.TieKk.attrs_agree
#print axioms KCore.TieKk.attrs_agree
