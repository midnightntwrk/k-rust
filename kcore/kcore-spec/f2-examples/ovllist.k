// Overloaded list constructors as wasm writes them (wasm.md: EmptyStmt, Instr, Defn, Stmt and
// their lists, `overload(listStmt)`), with a constructor of Instr and one of Defn. kompile declares
// the conses and nils of Instrs, Defns and Stmts `anywhere` and states ten overload equations.
module OVLLIST-SYNTAX
  imports INT-SYNTAX
  syntax EmptyStmt
  syntax Instr ::= EmptyStmt
  syntax Defn  ::= EmptyStmt
  syntax Stmt  ::= Instr | Defn
  syntax Instr ::= "nop" [symbol(nop)]
  syntax Defn  ::= "fn" [symbol(fn)]
  syntax EmptyStmts ::= List{EmptyStmt , ""} [overload(listStmt), terminator-symbol(".List{\"listStmt\"}")]
  syntax Instrs     ::= List{Instr     , ""} [overload(listStmt)]
  syntax Defns      ::= List{Defn      , ""} [overload(listStmt)]
  syntax Stmts      ::= List{Stmt      , ""} [overload(listStmt)]
  syntax Instrs ::= EmptyStmts
  syntax Defns  ::= EmptyStmts
  syntax Stmts  ::= Instrs | Defns
  syntax Pgm ::= len(Stmts, Int) [symbol(len)]
  syntax Pgm ::= done(Int) [symbol(done)]
  syntax Int ::= count(Stmts) [function, total, symbol(count)]
endmodule

module OVLLIST
  imports OVLLIST-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k>
  rule <k> len(_S:Stmt SS:Stmts, N) => len(SS, N +Int 1) </k>
  rule <k> len(.Stmts, N) => done(N) </k>
  rule count(_S:Stmt SS:Stmts) => 1 +Int count(SS)
  rule count(.Stmts) => 0
endmodule
