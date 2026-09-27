module SYMPARTIAL-SYNTAX
  imports INT-SYNTAX
  syntax Address ::= addr(Int) [symbol(addr)]
  syntax Op ::= write(Address, Int) [symbol(write)]
              | load(Address, Int) [symbol(load)]
              | half(Int) [symbol(half)]
  syntax Prog ::= "halt" [symbol(halt)]
                | seq(Op, Prog) [symbol(seq)]
endmodule

module SYMPARTIAL
  imports SYMPARTIAL-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  configuration <k> .K </k>

  syntax Int ::= f(Int) [function, symbol(f)]
  rule [f]: f(I) => 1 ensures I ==Int I

  rule [write]: seq(write(addr(A), V), P) => P
  rule [load]:  seq(load(addr(A), V), P) => P
  rule [half]:  seq(half(A), P) => seq(load(addr(1), f(A)), P)
endmodule
