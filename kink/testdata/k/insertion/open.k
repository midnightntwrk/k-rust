// A function into a grown sort that no equation decides (kink-patch tests/insertion.rs
// `a_sentence_over_an_open_value_is_withdrawn`, PJ-34 U34f review fix). p's `total` makes p(0) a
// value of Val, which no equation fixes: a or b in the baseline, possibly c once c is a
// constructor of Val. q's equation and the lemma ab rest on p(0) being a or b, so both go when c
// is inserted; p keeps its own `total`, and r, which names no open value, keeps its claim. t's
// condition names the sort predicate isVal, which compilation generates, and goes too.
module OPEN
  imports BASIC-K
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> .K </k>

  syntax Val ::= "a" [symbol(a)] | "b" [symbol(b)]
  syntax Val ::= p(Int) [function, total, symbol(p)]
  syntax Int ::= q(Int) [function, total, symbol(q)]
  rule [q]: q(N) => 1 requires (p(N) ==K a) orBool (p(N) ==K b)
  rule [ab]: (p(N) ==K a) orBool (p(N) ==K b) => true [simplification]
  syntax Int ::= r(Int) [function, total, symbol(r)]
  rule [r]: r(N) => N +Int 1
  syntax Int ::= t(Int) [function, total, symbol(t)]
  rule [t]: t(N) => 1 requires notBool isVal(N)
endmodule
