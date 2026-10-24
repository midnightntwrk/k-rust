module PQ
  imports INT
  syntax A  ::= "a"
  syntax B  ::= "bb"
  syntax AB ::= A | B
  syntax AB ::= q(Int) [function, total]
  rule q(_) => a
  rule q(_) => bb
  syntax Pgm ::= go(Int)
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => a </s>
endmodule
