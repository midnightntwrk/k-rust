// List concatenation is associative and not commutative: A B and B A differ, so p(L, L) does not
// match them; (A B) A and A (B A) are one list, which q(L, L) matches; a list may hold an element
// twice; size counts every element.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports LIST
  syntax S ::= go(List, List) | p(List, List) | q(List, List) | same(List) | assoc(List) | n(Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports LIST
  configuration <k> $PGM:S </k>
  rule <k> go(A, B) => p(A B, B A) </k>
  rule <k> go(A, B) => q((A B) A, A (B A)) </k>
  rule <k> go(A, B) => n(size(A B A)) </k>
  rule <k> p(L, L) => same(L) </k>
  rule <k> q(L, L) => assoc(L) </k>
endmodule
