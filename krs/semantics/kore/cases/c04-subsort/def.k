// Subsorts Int < Num < Val < Exp and Bool < Val: a variable of sort Val matches an Int injected
// into Exp only through the closure of the stated subsorts; injections built by functions'
// results compose.
module CASE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Num ::= Int
  syntax Val ::= Num | Bool | pair(Val, Val)
  syntax Exp ::= Val | neg(Exp) | wrap(Exp) | kind(Exp)
  syntax Exp ::= id(Exp) [function]
  syntax Val ::= v(Int) [function]
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Exp </k>
  rule id(E) => E
  rule v(I) => I
  rule <k> wrap(E) => kind(id(E)) </k>
  rule <k> kind(V:Val) => pair(V, v(1)) </k>
  rule <k> kind(neg(I:Int)) => wrap(0 -Int I) </k>
endmodule
