module WEAKF-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Val ::= v(Int) [symbol(v)]
  syntax Prog ::= runh(Int) [symbol(runh)] | out(Int) [symbol(out)]
  syntax Val ::= h(Int) [function, total, symbol(h)]
               | k(Int) [function, total, symbol(k)]
endmodule

module WEAKF
  imports WEAKF-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [runh]: <k> runh(I) => h(I) </k>
  rule [out]: <k> v(I) => out(I) </k>
  // k(1) is v(1) by k-one and v(2) by k-two: a critical pair that does not join, a finding of
  // the baseline that no [spec] assume_joined names.
  rule [k-one]: k(_) => v(1)
  rule [k-two]: k(I) => v(2) requires I >Int 0
  rule [h-big]: h(I) => v(I) requires I >Int 10
  rule [h-small]: h(I) => v(I +Int 1) requires I <=Int 10
endmodule
