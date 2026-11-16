// A rule whose left side applies LIST's update `L [ I <- J ]` (`List:set`, a function), as K's
// regression test list-set does. A function's application in a pattern denotes the values the
// function takes at some arguments; matching it needs what the function's inverse says, which no
// part of the semantics gives. The account refuses it with a reason of its own
// (`functionInPattern`), the function named.
module LSET-SYNTAX
  imports INT-SYNTAX
  imports LIST
  syntax Cmd ::= l(Int, Int) [symbol(l)] | done() [symbol(done)]
endmodule

module LSET
  imports LSET-SYNTAX
  imports INT
  configuration <k> $PGM:Cmd </k> <list> ListItem(0) ListItem(1) ListItem(2) </list>
  rule [set]: <k> l(I, J) => done() </k> <list> _ [ I <- J ] </list>
endmodule
