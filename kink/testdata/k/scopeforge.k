module SCOPEFORGE-SYNTAX
  syntax Ab ::= "a" [symbol(a)] | "b" [symbol(b)]
  syntax Pair ::= pair(Ab, Ab) [symbol(pair)]
  syntax Prog ::= start(Ab) [symbol(start)] | Pair
endmodule

module SCOPEFORGE
  imports SCOPEFORGE-SYNTAX
  imports BASIC-K
  imports K-EQUAL
  imports BOOL
  configuration <k> .K </k>
  rule [startA]: start(a) => pair(a, b)
  rule [startB]: start(b) => pair(b, a)
endmodule
