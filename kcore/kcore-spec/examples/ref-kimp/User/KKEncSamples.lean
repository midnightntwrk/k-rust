/-
  `KK.enc` at configurations of kimp: the configuration of K's claim `sum-spec` at `N = 3`,
  `S = 0` (`Claims.inst`), and the one after the rule `while` (the loop unfolded into an `if`).
  Each is printed, and the kernel checks of each encoding that no `bot` is inside it and that
  every map's and set's elements are strictly ordered by `ckeyF`.

  `KK.encDef` at kimp's text: each condition of `KK.encodable` holds, and `encDef` is `some`.
  `defn` is a term the compiler does not evaluate, so the text is parsed again here
  (`semanticsOfFile`, the parse `definition_of` adds as `defn`).
-/
import User.SumSpecStmt
import KcoreSpec.KKEnc
import KcoreSpec.KKEncDef

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

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let c ← semanticsOfFile "RefKimp/definition.kore"
  let conds := [("C1", ovlsOK c), ("C2", paramsOK c), ("C3", appsOK c), ("C4", headsOK c),
    ("C5", litsOK c), ("C7", subsortsOK c), ("C8", colPatsOK c), ("C10", asOK c), ("C11", ensOK c),
    ("C12", shapesOK c), ("C13", collFormOK c)]
  for (n, b) in conds do
    unless b do throwError "kimp: condition {n} of KK.encodable fails"
  let unread := (lhsTerms c ++ rhsTerms c ++ ensTerms c).filter fun t => (encTerm c t).isNone
  unless unread.isEmpty do throwError "kimp: {unread.length} terms have no kore.k form"
  match encDef c with
  | some E =>
    IO.println s!"encDef: some ({E.subs.length} subsorts, {E.fns.length} functions, {E.rules.length} rules)"
  | none => throwError "kimp: encDef is none"

end RefKimp.KKEncSamples
