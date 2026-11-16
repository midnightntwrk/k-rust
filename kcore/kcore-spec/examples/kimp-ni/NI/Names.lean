/- The symbols and sorts the statement names, by the generated packages' readable names (`Kimp`,
   `ImpSec`), and kimp's own sorts and symbols in the checker's numbering (same names; printed data,
   which Incl.lean checks by name). -/
import Kimp
import ImpSec
set_option autoImplicit false
namespace NI
open KCore
namespace K
/-- `Lbl'UndsEqlsUndsSClnUnds'CALC-SYNTAX'Unds'Stmt'Unds'Id'Unds'Expr` -/
@[match_pattern, reducible] def assign : Sym := Kimp.Sym.«_=_;_CALC-SYNTAX_Stmt_Id_Expr»
/-- `Lbl'UndsUndsUnds'CALC-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt` -/
@[match_pattern, reducible] def seq : Sym := Kimp.Sym.«___CALC-SYNTAX_Stmt_Stmt_Stmt»
/-- `Lblif'LParUndsRParUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Expr'Unds'Stmt` -/
@[match_pattern, reducible] def ifThen : Sym := Kimp.Sym.«if(_)__IMP-SYNTAX_Stmt_Expr_Stmt»
/-- `Lblwhile'LParUndsRParUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Expr'Unds'Stmt` -/
@[match_pattern, reducible] def while_ : Sym := Kimp.Sym.«while(_)__IMP-SYNTAX_Stmt_Expr_Stmt»
/-- `Lbl'LBraUndsRBraUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt` -/
@[match_pattern, reducible] def block : Sym := Kimp.Sym.«{_}_IMP-SYNTAX_Stmt_Stmt»
/-- `Lbl'UndsPlusUndsUnds'EXPR-SYNTAX'Unds'Expr'Unds'Expr'Unds'Expr` -/
@[match_pattern, reducible] def plus : Sym := Kimp.Sym.«_+__EXPR-SYNTAX_Expr_Expr_Expr»
/-- `Lbl'Unds-GT-UndsUnds'EXPR-SYNTAX'Unds'Expr'Unds'Expr'Unds'Expr` -/
@[match_pattern, reducible] def gt : Sym := Kimp.Sym.«_>__EXPR-SYNTAX_Expr_Expr_Expr»
/-- `LblisValue` -/
@[match_pattern, reducible] def isValue : Sym := Kimp.Sym.«isValue»
/-- `Stmt` -/
@[match_pattern, reducible] def stmt : Srt := Kimp.Srt.«Stmt»
/-- `Expr` -/
@[match_pattern, reducible] def expr : Srt := Kimp.Srt.«Expr»
/-- `Value` -/
@[match_pattern, reducible] def value : Srt := Kimp.Srt.«Value»
end K
namespace S
/-- `Lbllo'Unds'IMP-SEC'Unds'Level` -/
@[match_pattern, reducible] def lo : Sym := ImpSec.Sym.«lo_IMP-SEC_Level»
/-- `Lblhi'Unds'IMP-SEC'Unds'Level` -/
@[match_pattern, reducible] def hi : Sym := ImpSec.Sym.«hi_IMP-SEC_Level»
/-- `Lbllev'LParUndsCommUndsRParUnds'IMP-SEC'Unds'Level'Unds'Expr'Unds'Map` -/
@[match_pattern, reducible] def lev : Sym := ImpSec.Sym.«lev(_,_)_IMP-SEC_Level_Expr_Map»
/-- `Lblsec'LParUndsCommUndsRParUnds'IMP-SEC'Unds'Bool'Unds'Stmt'Unds'Map` -/
@[match_pattern, reducible] def sec : Sym := ImpSec.Sym.«sec(_,_)_IMP-SEC_Bool_Stmt_Map»
/-- `Level` -/
@[match_pattern, reducible] def level : Srt := ImpSec.Srt.«Level»
/-- `Expr` -/
@[match_pattern, reducible] def expr : Srt := ImpSec.Srt.«Expr»
/-- `Stmt` -/
@[match_pattern, reducible] def stmt : Srt := ImpSec.Srt.«Stmt»
end S
/-- kimp's own symbols the checker has, with the checker's numbers. -/
def symMap : List (Sym × Sym) := [(376, 376), (377, 377), (380, 378), (381, 379), (382, 381), (383, 382), (384, 383), (385, 384), (388, 385), (389, 386), (390, 387), (391, 388), (392, 389), (393, 390), (394, 391), (395, 392), (396, 393), (397, 394), (398, 395), (399, 396), (400, 397), (401, 398), (402, 399), (403, 400), (404, 401), (405, 402), (406, 403), (407, 404), (408, 405), (409, 408), (410, 409), (411, 410), (412, 411), (413, 412), (414, 413), (415, 414), (416, 415), (417, 416), (418, 417), (419, 418), (420, 419), (421, 420), (422, 421), (423, 422), (424, 423), (425, 424), (426, 425), (427, 426), (428, 427), (429, 428), (430, 429), (431, 430), (432, 431), (433, 432), (434, 433)]
/-- kimp's own sorts the checker has, with the checker's numbers. -/
def sortMap : List (Srt × Srt) := [(30, 30), (31, 31), (34, 32), (35, 33), (36, 35), (37, 36)]
end NI
