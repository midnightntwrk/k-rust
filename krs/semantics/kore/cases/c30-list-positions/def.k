// List patterns match by position: ListItem(X) L takes the first element and L ListItem(X) the
// last; a pattern without a frame matches only a list of exactly its length.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports LIST
  syntax S ::= go(List) | a(List) | b(List) | d(List) | r(Int, List)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports LIST
  configuration <k> $PGM:S </k>
  rule <k> go(L) => a(L) </k>
  rule <k> go(L) => b(L) </k>
  rule <k> go(L) => d(L) </k>
  rule <k> a(ListItem(X:Int) L:List) => r(X, L) </k>
  rule <k> b(L:List ListItem(X:Int)) => r(X, ListItem(X) L) </k>
  rule <k> d(ListItem(X:Int) ListItem(_:Int)) => r(X, .List) </k>
endmodule
