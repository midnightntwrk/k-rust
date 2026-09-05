module TEST
  imports INT
  configuration <k> $PGM:KItem </k>
  syntax Foo ::= test(Int, foo: Int, bar: Int)
  syntax Int ::= getFoo(Foo) [function]
  rule getFoo(F) => foo(F)
endmodule
