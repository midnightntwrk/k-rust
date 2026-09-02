module TEST-SYNTAX
  imports BASIC-K
  syntax Aa ::= r"%[a-z]+" [token, prefer]
  syntax Bb ::= r"%[a-z]+" [token]
  syntax Foo ::= "foo" "(" KItem ")" [symbol(foo)]
endmodule
