import KImp.Rules
import KPrelude.InvColl

/-!
# No pending statement assigns `x` (a kind 2 invariant of kimp that walks `<k>`)

`Invariant x c`: no statement in the `<k>` cell of `c` assigns the identifier `x` (statements in
the frozen contexts of the heating rules included), and no value of the store `<env>` does.
The second part is needed for the first to be inductive: the rule `CALC.var` moves a value of the
store into `<k>`, and `$ENV` may bind a statement.

`writesK`, `writesI` and `writesS` are `writesT` at the sorts `K`, `KItem` and `Stmt`: one
function over the term family, matching on the generated constructors, by structural recursion on
the term. Each recursive call is at another sort of the family, so separate functions per sort would
recurse on a family at fixed indices, which Lean compiles by well-founded recursion only; those do
not unfold by `decide` or `rfl`, which `k2l_preserve`'s closers need. The heating rules put
`inj_Expr_KItem HOLE` (an injection, defined by cases on `HOLE`) into `<k>`, on which `writesI`
does not reduce; `k2l_preserve`'s injection closer cases on `HOLE` there.
-/

namespace ImpWrites

open KPrelude KImp

/-- The term `t` assigns `x`: a statement that does (`SortStmt`), an item of the computation that
does (`SortKItem`: such a statement, a frozen `x = □;`, or a frozen `if (□) S₁ else S₂` whose
branches do), or a computation with such an item (`SortK`); any other term does not.
One function over the family, by structural recursion on the term, so that it reduces by
definitional unfolding (`decide`, `rfl`) on constructors. -/
def writesT (x : SortId) : {s : Tag} → Term s → Bool
  | .«SortStmt», SortStmt.«{}» => false
  | .«SortStmt», SortStmt.«{_}» s => writesT x s
  | .«SortStmt», SortStmt.«_=_;» y _ => decide (y = x)
  | .«SortStmt», SortStmt.__ s₁ s₂ => writesT x s₁ || writesT x s₂
  | .«SortStmt», SortStmt.«if(_)_else_» _ s₁ s₂ => writesT x s₁ || writesT x s₂
  | .«SortStmt», SortStmt.«if(_)_» _ s => writesT x s
  | .«SortStmt», SortStmt.«while(_)_» _ s => writesT x s
  | .«SortKItem», SortKItem.inj_Stmt s => writesT x s
  | .«SortKItem», SortKItem.inj_KItem (.«#freezer_=_;_CALC-SYNTAX_Stmt_Id_Expr1_» k) =>
      decide (k = .kseq (.inj_Id x) .dotk)
  | .«SortKItem», SortKItem.inj_KItem (.«#freezerif(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt0_» k₁ k₂) =>
      writesT x k₁ || writesT x k₂
  | .«SortK», SortK.kseq i k => writesT x i || writesT x k
  | _, _ => false
termination_by structural _ t => t

/-- The statement `s` assigns `x`. -/
def writesS (x : SortId) (s : SortStmt) : Bool := writesT x s

/-- The computation item `i` assigns `x`. -/
def writesI (x : SortId) (i : SortKItem) : Bool := writesT x i

/-- Some item of the computation `k` assigns `x`. -/
def writesK (x : SortId) (k : SortK) : Bool := writesT x k

/-- The `<k>` cell's computation. -/
def kOf : SortGeneratedTopCell → SortKCell
  | .«<generatedTop>» k _ _ => k

def kContent : SortKCell → SortK
  | .«<k>» k => k

/-- The store. -/
def envOf : SortGeneratedTopCell → SortEnvCell
  | .«<generatedTop>» _ e _ => e

def envContent : SortEnvCell → SortMap
  | .«<env>» m => m

/-- No pending statement and no value of the store assigns `x`. -/
def Invariant (x : SortId) (c : SortGeneratedTopCell) : Prop :=
  writesK x (kContent (kOf c)) = false ∧
    MapHook.EntriesOn (fun p => writesI x p.2 = false) (envContent (envOf c))

end ImpWrites
