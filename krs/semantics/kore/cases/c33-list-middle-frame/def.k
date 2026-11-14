// A List pattern with elements on both sides of its frame: ListItem(X) L ListItem(Y) takes the
// first and the last element and binds the middle to L.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports LIST
  syntax S ::= c(List) | r(Int, Int, List)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports LIST
  configuration <k> $PGM:S </k>
  rule <k> c(ListItem(X:Int) L:List ListItem(Y:Int)) => r(X, Y, L) </k>
endmodule
