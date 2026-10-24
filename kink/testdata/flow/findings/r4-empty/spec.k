module R4
  imports INT
  imports BOOL
  syntax A  ::= "a"
  syntax B  ::= "bb"
  syntax AB ::= A | B
  syntax S
  syntax AB ::= f(S) [function, total]
  rule f(_) => a
  rule f(_) => bb
  syntax Pgm ::= go(Int)
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => a </s>
endmodule
