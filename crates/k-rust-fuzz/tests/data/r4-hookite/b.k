// FZ-DATAEND review R4 (r4-hookite): `sel` is hooked to KEQUAL.ite, whose builtin the evaluator
// applies before any equation, and the equation `sel(_, _, Y) => Y` disagrees with it: the
// builtin gives sel(true, a, bb) = a, the equation bb, so the theory equates a with bb. The full
// check pairs the equation with the hook's written meaning. This side stores a.

module HI-SYNTAX
  imports INT-SYNTAX
  syntax A  ::= "a"
  syntax B  ::= "bb"
  syntax AB ::= A | B
  syntax Pgm ::= go(Int)
endmodule
module HI
  imports HI-SYNTAX
  imports INT
  imports BOOL
  syntax AB ::= sel(Bool, AB, AB) [function, total, hook(KEQUAL.ite)]
  rule sel(_, _, Y) => Y
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => a </s>
endmodule
