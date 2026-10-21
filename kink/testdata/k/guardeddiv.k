module GUARDEDDIV-SYNTAX
  imports INT-SYNTAX
  syntax Address ::= addr(Int) [symbol(addr)]
  syntax Op ::= write(Address, Int) [symbol(write)]
              | load(Address, Int) [symbol(load)]
  syntax Prog ::= "halt" [symbol(halt)]
                | seq(Op, Prog) [symbol(seq)]
                | divide(Int, Int) [symbol(divide)]
                | done(Int) [symbol(done)]
endmodule

module GUARDEDDIV
  imports GUARDEDDIV-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> .K </k>

  rule [write]:  seq(write(addr(A), V), P) => P
  rule [load]:   seq(load(addr(A), V), P) => P
  rule [divide]: divide(I1, I2) => done(I1 /Int I2) requires I2 =/=Int 0
  rule [done]:   done(_) => halt
endmodule
