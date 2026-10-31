// The coroutine language of the two-layer prototype (k2lean/docs/direction.md §8 step 4) on its
// own: the lower layer of the fixture twolayer, the semantics that the fixture twoparam leaves as a
// parameter. A configuration is the code left and the register. Nothing steps at `yield` or at the
// code's end: those are where a segment ends, and the upper layer takes over there. `loop(M, B)`
// runs B M times.
requires "domains.md"

module COROUT-SYNTAX
  imports INT-SYNTAX
  syntax Stmt ::= "add" "(" Int ")"           // add a constant to the register
                | "dbl"                       // double the register
                | "loop" "(" Int "," Code ")" // the body, that many times
                | "yield"                     // end the segment: its output is the register
  syntax Stmts ::= List{Stmt, ";"}
  syntax Code ::= "{" Stmts "}"
endmodule

module COROUT
  imports COROUT-SYNTAX
  imports INT
  imports BOOL

  syntax Stmts ::= app(Stmts, Stmts) [function, total]
  rule app(.Stmts, T) => T
  rule app(S ; R, T) => S ; app(R, T)

  configuration <T> <k> $PGM:Stmts </k> <reg> 0 </reg> </T>

  rule <k> add(I) ; C => C </k> <reg> R => R +Int I </reg> [label(add)]
  rule <k> dbl ; C => C </k> <reg> R => R *Int 2 </reg> [label(dbl)]
  rule <k> loop(M, { B }) ; C => app(B, loop(M -Int 1, { B }) ; C) </k> requires M >Int 0 [label(loop)]
  rule <k> loop(M, _) ; C => C </k> requires M <=Int 0 [label(loop-done)]
endmodule
