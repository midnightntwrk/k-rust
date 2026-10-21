module GUARDEDMEM-SYNTAX
  imports INT-SYNTAX
  syntax Address ::= addr(Int) [symbol(addr)]
  syntax Op ::= write(Address, Int) [symbol(write)]
              | load(Address, Int) [symbol(load)]
              | loadNeg(Address, Int) [symbol(loadNeg)]
  syntax Prog ::= "halt" [symbol(halt)] | "fault" [symbol(fault)]
                | seq(Op, Prog) [symbol(seq)]
endmodule

module GUARDEDMEM
  imports GUARDEDMEM-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> .K </k>

  rule [write]:      seq(write(addr(A), V), P) => P requires A >=Int 0
  rule [writeFault]: seq(write(addr(A), _), _) => fault requires A <Int 0
  rule [load]:       seq(load(addr(A), V), P) => P requires A >=Int 0
  rule [loadFault]:  seq(load(addr(A), _), _) => fault requires A <Int 0
  rule [loadNeg]:    seq(loadNeg(addr(A), V), P) => P requires A <Int 0
endmodule
