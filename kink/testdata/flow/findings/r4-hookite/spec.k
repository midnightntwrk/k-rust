module R4
  imports INT
  imports BOOL
  syntax A  ::= "a"
  syntax B  ::= "bb"
  syntax AB ::= A | B
  syntax AB ::= sel(Bool, AB, AB) [function, total, hook(KEQUAL.ite)]
  rule sel(_, _, Y) => Y
  syntax Pgm ::= go(Int)
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => a </s>
endmodule
