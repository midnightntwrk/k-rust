// A token sort with literals, and sort predicates: a token literal in a left side matches only
// that token; tokens of two sorts with one text are two values; isS holds of a value of S and of
// a sort below S, and not of a value of another sort.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Id ::= r"[a-z][a-z0-9]*" [token]
  syntax Key ::= r"[$][a-z]+" [token]
  syntax Val ::= Int | Id
  syntax S ::= Val | go(Val, Val) | r(Bool, Bool, Bool, Bool, Bool, Bool)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:S </k>
  rule <k> go(V, W) => r(isId(V), isInt(V), isVal(V), isId(W), V ==K #token("x", "Key"), V ==K W) </k>
  rule <k> go(#token("x", "Id"), _) => #token("z", "Id") </k>
  rule <k> go(#token("y", "Id"), _) => 0 </k>
endmodule
