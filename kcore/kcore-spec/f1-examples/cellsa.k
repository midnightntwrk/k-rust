module CELLSA
  imports INT
  syntax Foo ::= foo(Int) [symbol(foo)]
  configuration <t> <k> $PGM:Foo </k> <c> 0 </c> </t>
  rule <k> foo(I) => foo(I) </k> <c> N => N +Int I </c>
endmodule
