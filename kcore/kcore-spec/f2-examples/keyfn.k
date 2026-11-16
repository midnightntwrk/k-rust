// A total function of the definition's own applied as a map key in a rule's left side, its
// arguments bound by the rest of the left side.
module KEYFN-SYNTAX
  imports INT-SYNTAX
endmodule

module KEYFN
  imports KEYFN-SYNTAX
  imports INT
  imports MAP
  imports BOOL
  syntax Int ::= idx(Int, Int) [function, total, symbol(idx)]
  rule idx(B, I) => B +Int I
  syntax KItem ::= get(Int) [symbol(get)]
  configuration <k> $PGM:KItem </k> <base> 0 </base> <mem> .Map </mem>
  rule <k> get(I) => V ... </k> <base> B </base> <mem> idx(B, I) |-> V ... </mem>
endmodule
