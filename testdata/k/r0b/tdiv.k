// Re-pin R0b (decision 2, finding A-13): k-rust's tdiv/td shape (k-rust
// tests/undefined_step_coverage.rs). `td` is declared total and `pd` preserves-definedness, but
// both divide by their argument plus one, so at -1 the claim is false: the definition is
// inconsistent there. `half` divides by its argument and makes no claim.
module TDIV-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= tdiv(Int) [symbol(tdiv)]
                | pd(Int) [symbol(pd)]
                | half(Int) [symbol(half)]
                | val(Int) [symbol(val)]
  syntax Int ::= td(Int) [function, total, symbol(td)]
endmodule
module TDIV
  imports TDIV-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [tdeq]: td(I) => 10 /Int (I +Int 1)
  rule [tdiv]: <k> tdiv(I) => val(td(I)) </k>
  rule [pd]: <k> pd(I) => val(10 /Int (I +Int 1)) </k> [preserves-definedness]
  rule [half]: <k> half(I) => val(10 /Int I) </k>
endmodule
