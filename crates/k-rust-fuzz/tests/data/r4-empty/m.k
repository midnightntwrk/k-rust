// FZ-DATAEND review round 4 (r4-empty): `syntax S` has no production, so S has no normal form, and
// f(_:S) => a, f(_:S) => bb overlap only over it.
// Matching-logic carriers are nonempty, so every model has an element s of S, and the two
// equations give a = f(s) = bb there; the full check reports the pair (FZ-EMPTYSORT), so no end
// of this definition is data. This side stores bb.

module RE-SYNTAX
  imports INT-SYNTAX
  syntax A  ::= "a"
  syntax B  ::= "bb"
  syntax AB ::= A | B
  syntax Pgm ::= go(Int)
endmodule
module RE
  imports RE-SYNTAX
  imports INT
  syntax S
  syntax AB ::= f(S) [function, total]
  rule f(_) => a
  rule f(_) => bb
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => bb </s>
endmodule
