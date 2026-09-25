module COUNTER-SYNTAX
  imports SORT-BOOL
  syntax Nat ::= "z" [symbol(z)]
               | s(Nat) [symbol(s)]
  syntax Counter ::= counter(Nat, Nat) [symbol(counter)]
  syntax Control ::= choose(Bool) [symbol(choose)]
                   | selected(Bool) [symbol(selected)]
endmodule

module COUNTER
  imports COUNTER-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule [increment]: counter(N, s(L)) => counter(s(N), L)
  rule [branch]: choose(B) => selected(B) requires B
  rule [fallback]: choose(B) => selected(B) [priority(200)]
endmodule
