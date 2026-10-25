import KImp.Rules
import KPrelude.InvColl

/-!
# No pending statement assigns `x` (a kind 2 invariant of kimp that walks `<k>`)

`Invariant x c`: no statement in the `<k>` cell of `c` assigns the identifier `x` (statements in
the frozen contexts of the heating rules included), and no value of the store `<env>` does.
The second part is needed for the first to be inductive: the rule `CALC.var` moves a value of the
store into `<k>`, and `$ENV` may bind a statement.

`writesK`, `writesI` and `writesS` match on the generated constructors. The heating rules put
`inj_Expr_KItem HOLE` (an injection, defined by cases on `HOLE`) into `<k>`, on which `writesI`
does not reduce; `k2l_preserve`'s injection closer cases on `HOLE` there.
-/

namespace ImpWrites

open KPrelude KImp

/-- The statement `s` assigns `x`. -/
def writesS (x : SortId) : SortStmt → Bool
  | .«{}» => false
  | .«{_}» s => writesS x s
  | .«_=_;» y _ => decide (y = x)
  | .__ s₁ s₂ => writesS x s₁ || writesS x s₂
  | .«if(_)_else_» _ s₁ s₂ => writesS x s₁ || writesS x s₂
  | .«if(_)_» _ s => writesS x s
  | .«while(_)_» _ s => writesS x s

mutual
/-- The computation item `i` assigns `x`: a statement that does, a frozen `x = □;`, or a frozen
`if (□) S₁ else S₂` whose branches do. -/
def writesI (x : SortId) : SortKItem → Bool
  | .inj_Stmt s => writesS x s
  | .inj_KItem (.«#freezer_=_;_CALC-SYNTAX_Stmt_Id_Expr1_» k) => decide (k = .kseq (.inj_Id x) .dotk)
  | .inj_KItem (.«#freezerif(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt0_» k₁ k₂) => writesK x k₁ || writesK x k₂
  | _ => false

/-- Some item of the computation `k` assigns `x`. -/
def writesK (x : SortId) : SortK → Bool
  | .dotk => false
  | .kseq i k => writesI x i || writesK x k
end

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
