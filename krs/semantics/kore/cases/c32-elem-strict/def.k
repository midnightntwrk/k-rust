// Sets and lists are strict in their elements: an element that is undefined (1 /Int 0) makes the
// collection, and so the rule's result, undefined; the rule of the same priority without one
// gives the one final configuration.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports SET
  imports LIST
  syntax S ::= go(Set, List, Int) | a(Set) | b(List) | c(Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports SET
  imports LIST
  configuration <k> $PGM:S </k>
  rule <k> go(S, _, Z) => a(S SetItem(1 /Int Z)) </k>
  rule <k> go(_, L, Z) => b(L ListItem(1 /Int Z)) </k>
  rule <k> go(S, L, _) => c(size(S) +Int size(L)) </k>
endmodule
