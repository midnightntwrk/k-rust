// A cell sort below a sort of the definition (`syntax Pgm ::= KCell`, as K's regression test
// checks/checkCellSortDeclOK.k): the subsort `KCell < Pgm` is a subsort between two sorts of the
// definition, the configuration's cell sort and a user sort.
module CELLSUB-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)] | done(Int) [symbol(done)]
endmodule

module CELLSUB
  imports CELLSUB-SYNTAX
  imports INT
  configuration <T> <k> $PGM:Pgm </k> </T>
  syntax Pgm ::= KCell
  rule [go]: <k> go(N) => done(N) </k>
endmodule
