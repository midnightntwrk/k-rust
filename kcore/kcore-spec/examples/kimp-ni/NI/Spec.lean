/-
  Noninterference for kimp over KCore: the statement, a proposition (`KimpNI`). Nothing here
  proves it; KcoreSpec/Noninterference.lean's theorem kind reduces it to an unwinding relation
  (Kind.lean).

  Termination-insensitive noninterference, as k2lean states it for kimp (k2lean docs/design.md
  §3.7): take a labelling G of identifiers by the two levels lo and hi, and a program P that kimp's
  security checker accepts at G. Take two stores that agree on every identifier G labels lo, and
  whose identifiers hold values. Then two runs of kimp's step from P with the two stores that
  both finish (`<k>` empty) end with stores that agree on every identifier G labels lo.

  The two definitions are KCore cores, each the generated package of its KORE text: kimp's (`Kimp.c`,
  f2-examples/kimp.kore) and its checker's (`ImpSec.c`, f2-examples/imp-sec.kore, k2lean's
  demos/k/imp-sec.k with `conf` and `sec` not declared total). The checker's core has kimp's
  constructors and subsorts, under the same names, and adds the sort Level with `lo` and `hi`.
  Each core numbers its own sorts and symbols, so the same name may have different
  numbers in the two: the checker reads kimp's program through the renaming `toSec` (by name,
  Names.lean; Incl.lean decides that it keeps names and maps kimp's signature into the
  checker's).

  What each part reads:
  - `Secure G P`: the checker's `sec(P, G)` evaluates to `true` (`Eval`, KCore's frozen evaluation);
  - `Low G X`: the checker's `lev(X, G)` evaluates to `lo` (an identifier with no label, or with
    hi, is not low);
  - `Good E`: E is a map of kimp's, and every identifier it binds holds a value of kimp's sort
    Value, by kimp's own sort predicate `isValue` (the test of k2lean's `imp-ni.k`, `storeOk`,
    stated here so that no function needs a map pattern with a free key). Without it a
    store could bind a low identifier to an expression, which a lookup puts on `<k>`: `l = x;` with
    `x |-> h` would read the high `h`;
  - `LowEq G E₁ E₂`: at every low identifier both stores bind the same value, or neither binds it;
  - `Run x y`: a sequence of kimp's `Step`s from x to y.

  The statement is `NIFor chk` for a checker core `chk`, and `KimpNI` is `NIFor ImpSec.c`: stated
  for any checker so that a wrong one can be refuted (Leak.lean refutes `NIFor ImpSecLeaky.c`).
-/
import NI.Names

set_option autoImplicit false

namespace NI

open KCore

/-! ## Values the statement names -/

/-- An identifier `\dv{SortId{}}(x)`. -/
def ident (x : String) : GroundTerm := .dv Srt.ident (.tok x)

/-- The two levels, constructors of the checker's sort Level. -/
def lo : GroundTerm := .ctor S.lo []
def hi : GroundTerm := .ctor S.hi []

/-- The empty K sequence and the one-item sequence of a value of sort s. -/
def dotK : GroundTerm := .ctor dotk []
def item (s : Srt) (v : GroundTerm) : GroundTerm := .ctor kseq [.inj s Srt.kitem v, dotK]

/-- An identifier as a map key (`inj{Id,KItem}`). -/
def key (X : GroundTerm) : GroundTerm := .inj Srt.ident Srt.kitem X

/-- The value a map binds to a key (`Map:lookup`'s meaning, Hooks.lean). -/
def lookup (m k : GroundTerm) : Option GroundTerm :=
  match m with
  | .map _ es => findK k es
  | _ => none

/-! ## kimp's configurations -/

mutual
  /-- The configuration of a cell tree whose leaf named n holds `v n`. A cell collection child is
  no cell and its name is empty (`Cell.name`): it holds `v ""`. kimp's cell tree has none. -/
  def fill (v : String → GroundTerm) : Cell → GroundTerm
    | .leaf n _ i => .ctor i.label [v n]
    | .node _ cs i => .ctor i.label (fillList v cs)
    | .coll _ => v ""
    termination_by structural x => x
  def fillList (v : String → GroundTerm) : List Cell → List GroundTerm
    | [] => []
    | x :: xs => fill v x :: fillList v xs
    termination_by structural xs => xs
end

/-- kimp's configuration `<generatedTop> <k> K </k> <env> E </env> <generatedCounter> n
</generatedCounter> </generatedTop>`. -/
noncomputable def cfg (K E n : GroundTerm) : GroundTerm :=
  fill (fun x => if x == "k" then K else if x == "env" then E else n) Kimp.defn.pres.topCell

/-- The initial configuration of the program P with the store E (`$PGM`, `$ENV`; counter 0). -/
noncomputable def init (P E : GroundTerm) : GroundTerm := cfg (item K.stmt P) E (.dv Srt.int (.int 0))

/-! ## kimp's values in the checker's numbering -/

/-- A number renamed by a table (unchanged if absent: the registry's). -/
def rn (m : List (Nat × Nat)) (x : Nat) : Nat := (m.lookup x).getD x

mutual
  /-- A kimp value renamed into the checker's numbering. Maps are renamed entry by entry and not
  re-sorted; kimp's programs hold none. -/
  def toSec : GroundTerm → GroundTerm
    | .ctor f ts => .ctor (rn symMap f) (toSecList ts)
    | .inj a b t => .inj (rn sortMap a) (rn sortMap b) (toSec t)
    | .dv s l => .dv (rn sortMap s) l
    | .map s es => .map (rn sortMap s) (toSecEntries es)
    | .set s es => .set (rn sortMap s) (toSecList es)
    | .list s es => .list (rn sortMap s) (toSecList es)
    termination_by structural t => t
  def toSecList : List GroundTerm → List GroundTerm
    | [] => []
    | t :: ts => toSec t :: toSecList ts
    termination_by structural ts => ts
  def toSecEntries : List (GroundTerm × GroundTerm) → List (GroundTerm × GroundTerm)
    | [] => []
    | (k, v) :: es => (toSec k, toSec v) :: toSecEntries es
    termination_by structural es => es
end

/-! ## The checker's verdicts -/

def levLabel : Sym := S.lev
def secLabel : Sym := S.sec

/-- The checker `chk` labels the identifier X low at G: its level `lev(X, G)` is `lo`. -/
def LowIn (chk : Semantics) (G X : GroundTerm) : Prop :=
  Eval chk levLabel [.inj Srt.ident S.expr X, G] (some lo)

/-- The checker `chk` accepts the program P at G: `sec(P, G)` is `true`. -/
def SecureIn (chk : Semantics) (G P : GroundTerm) : Prop :=
  Eval chk secLabel [toSec P, G] (some (bool true))

/-- kimp's checker labels X low at G. -/
def Low (G X : GroundTerm) : Prop := LowIn ImpSec.c G X

/-- kimp's checker accepts P at G. -/
def Secure (G P : GroundTerm) : Prop := SecureIn ImpSec.c G P

/-! ## Stores -/

/-- E is a store: a map of kimp's whose every identifier holds a value of sort Value. -/
def Good (E : GroundTerm) : Prop :=
  Kimp.c.sortOf E = some Srt.map ∧
    ∀ X v, lookup E (key X) = some v → Eval Kimp.c K.isValue [.ctor kseq [v, dotK]] (some (bool true))

/-- E₁ and E₂ agree at every identifier the checker `chk` labels low at G. -/
def LowEqIn (chk : Semantics) (G E₁ E₂ : GroundTerm) : Prop :=
  ∀ X, LowIn chk G X → lookup E₁ (key X) = lookup E₂ (key X)

/-- E₁ and E₂ agree at every identifier kimp's checker labels low at G. -/
def LowEq (G E₁ E₂ : GroundTerm) : Prop := LowEqIn ImpSec.c G E₁ E₂

/-! ## Runs -/

/-- Zero or more steps of r. -/
inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Star r a a
  | step {a b d : α} : r a b → Star r b d → Star r a d

/-- A run of kimp's step from the configuration x to the configuration y. -/
def Run (x y : GroundTerm) : Prop :=
  ∃ (hx : Kimp.c.sortOf x = some topCellSort) (hy : Kimp.c.sortOf y = some topCellSort),
    Star (Step Kimp.c) ⟨x, hx⟩ ⟨y, hy⟩

/-! ## The statement -/

/-- **Noninterference for kimp under the checker `chk`** (termination-insensitive): for a
labelling G, a program P that `chk` accepts at G, and two stores that agree on G's low identifiers,
two runs from P that both end with `<k>` empty end with stores that agree on G's low identifiers.
`chk` is a core with the checker's symbols (`lev`, `sec`, `lo`, `hi`) under the checker's numbers. -/
def NIFor (chk : Semantics) : Prop :=
  ∀ {G P E₁ E₂ E₁' E₂' n₁ n₂ : GroundTerm},
    chk.sortOf G = some Srt.map → Kimp.c.sortOf P = some K.stmt → SecureIn chk G P →
    Good E₁ → Good E₂ → LowEqIn chk G E₁ E₂ →
    Run (init P E₁) (cfg dotK E₁' n₁) → Run (init P E₂) (cfg dotK E₂' n₂) →
    LowEqIn chk G E₁' E₂'

/-- **Noninterference for kimp**: under kimp's checker (`ImpSec.c`, f2-examples/imp-sec.kore). -/
def KimpNI : Prop := NIFor ImpSec.c

end NI
