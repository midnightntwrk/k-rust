// state-observations SO-09, attack SO-AT3: a Conditional event between two Certain events on
// one path. `go(B)` steps to `mid(B)` unconditionally; `mid(B)` steps to `fin` only where B
// holds (the remainder under not B is stuck); `fin` steps to `halt`. A whole-transition event
// `mid(true) -> fin` on the symbolic run is Conditional{B = true}, so a NextEvent plan that
// must skip it cannot use the adjacency of the events around it.
module NEXTGAP-SYNTAX
  imports BOOL-SYNTAX
  syntax Prog ::= go(Bool) [symbol(go)]
                | mid(Bool) [symbol(mid)]
                | "fin" [symbol(fin)]
                | "halt" [symbol(halt)]
endmodule

module NEXTGAP
  imports NEXTGAP-SYNTAX
  imports BASIC-K
  imports BOOL
  configuration <k> .K </k>

  rule [go]:  go(B) => mid(B)
  rule [mid]: mid(B) => fin requires B
  rule [fin]: fin => halt
endmodule
