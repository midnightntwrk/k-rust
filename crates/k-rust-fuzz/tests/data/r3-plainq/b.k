// FZ-DATAEND review R3-S1: two total-function equations q(_) => a and q(_) => bb equate a with bb
// (no axiom keeps injections from different source sorts apart). The load's check does not pair
// them (they withdraw no value claim); the full check does. This side stores a.

module PQ-SYNTAX
  imports INT-SYNTAX
  syntax A  ::= "a"
  syntax B  ::= "bb"
  syntax AB ::= A | B
  syntax Pgm ::= go(Int)
endmodule
module PQ
  imports PQ-SYNTAX
  imports INT
  syntax AB ::= q(Int) [function, total]
  rule q(_) => a
  rule q(_) => bb
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => a </s>
endmodule
