/-
  `KK.enc` at configurations of kimp: the configuration of K's claim `sum-spec` at `N = 3`,
  `S = 0` (`Claims.inst`), and the one after the rule `while` (the loop unfolded into an `if`).
  Each is printed, and the kernel checks of each encoding that no `bot` is inside it and that
  every map's and set's elements are strictly ordered by `ckeyF`.
-/
import User.SumSpecStmt
import KcoreSpec.KKEnc

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace RefKimp.KKEncSamples

open KCore KCore.KK RefKimp.Syntax

def body : Tm Srt.«Stmt» :=
  «{_}» («__»
    («_=_;» (Tm.ident "$s") («_+_» (Tm.ident "$s") (Tm.ident "$n")))
    («_=_;» (Tm.ident "$n") («_+_» (Tm.ident "$n") (Tm.int (-1)))))

def cond : Tm Srt.«Expr» := «!_» («_<=_» (Tm.ident "$n") (Tm.int 0))

/-- `Claims.inst` after the rule `while`. -/
def unfolded : Tm Srt.top :=
  «<generatedTop>»
    («<k>» (Tm.kseq
      («if(_)_» cond («{_}» («__» body («while(_)_» cond body))))
      Tm.dotk))
    («<env>» (Tm.map [(Tm.ident "$n", Tm.int 3), (Tm.ident "$s", Tm.int 0)]))
    («<generatedCounter>» (Tm.int 0))

/-- Each element strictly below the next by `ckeyF`. -/
def ascB : List T → Bool
  | e :: f :: fs => (ckeyF e f).any (· < 0) && ascB (f :: fs)
  | _ => true

mutual
/-- No `bot` inside, and every map's and set's elements strictly increasing by `ckeyF`. -/
def canonB : T → Bool
  | .ap _ as => canonTsB as
  | .ij _ _ t => canonB t
  | .iv _ | .bv _ | .tk _ _ => true
  | .co .list _ es => canonTsB es
  | .co _ _ es => canonTsB es && ascB es
  | .kv a v => canonB a && canonB v
  | .el x => canonB x
  | _ => false
def canonTsB : List T → Bool
  | [] => true
  | t :: ts => canonB t && canonTsB ts
end

#eval enc Claims.inst.val
#eval enc unfolded.val

example : canonB (enc Claims.inst.val) = true := by decide +kernel
example : canonB (enc unfolded.val) = true := by decide +kernel

end RefKimp.KKEncSamples
