// FZ-DATAEND review round 4 (r4-partnorule): S's only production is the partial function g, which
// no rule rewrites, so S has no normal form; f(_:S) => a and f(_:S) => bb overlap only over it.
// Matching-logic carriers are nonempty, so every model has an element s of S, and the two
// equations give a = f(s) = bb there; the full check reports the pair (FZ-EMPTYSORT), so no end
// of this definition is data. This side stores bb.

module RP-SYNTAX
  imports INT-SYNTAX
  syntax A  ::= "a"
  syntax B  ::= "bb"
  syntax AB ::= A | B
  syntax Pgm ::= go(Int)
endmodule
module RP
  imports RP-SYNTAX
  imports INT
  syntax S ::= g(Int) [function]
  syntax AB ::= f(S) [function, total]
  rule f(_) => a
  rule f(_) => bb
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => bb </s>
endmodule
