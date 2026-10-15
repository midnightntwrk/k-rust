module PRIV
  imports PRIV-B
endmodule

module PRIV-B
  imports private PRIV-C
  imports BOOL
  imports INT
  syntax KItem ::= h(K) | g(Int)
  rule [pred]: h(X) => .K requires isFoo(X)
  rule [field]: h(X) => g(fst({X}:>Pair))
endmodule

module PRIV-C
  imports INT-SYNTAX
  syntax Foo ::= foo()
  syntax Pair ::= pair(fst: Int, snd: Int) [symbol(pair)]
endmodule
