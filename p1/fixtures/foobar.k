module P1-FOOBAR-SYNTAX
  syntax Foo ::= "foo" [symbol(foo)]
               | "bar" [symbol(bar)]
               | "pick" "(" Foo ")" [symbol(pick), function]
endmodule

module P1-FOOBAR
  imports P1-FOOBAR-SYNTAX

  configuration <k> $PGM:Foo </k>

  rule pick(foo) => bar
endmodule
