// A constructor of the text whose symbol is named inj.
module RDR-INJ-OWN
  imports INT
  syntax Foo ::= "a" [symbol(a)] | inj(Int) [symbol(inj)]
  syntax Foo ::= f(Int) [function, symbol(f)]
  rule f(X) => inj(X)
endmodule
