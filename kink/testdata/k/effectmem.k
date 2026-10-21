// Execution-identity audit fixture (EI-05, attack AT7). guardedmem's write and load, plus
// `writeLogged`: the same step as `write` that also logs a line (`IO.logString`). At
// priority 200 it never fires, because `write` handles every state it could.
module EFFECTMEM-SYNTAX
  imports INT-SYNTAX
  syntax Address ::= addr(Int) [symbol(addr)]
  syntax Op ::= write(Address, Int) [symbol(write)]
              | load(Address, Int) [symbol(load)]
  syntax Prog ::= "halt" [symbol(halt)] | "fault" [symbol(fault)]
                | seq(Op, Prog) [symbol(seq)]
endmodule

module EFFECTMEM
  imports EFFECTMEM-SYNTAX
  imports BASIC-K
  imports INT
  imports STRING
  imports K-IO
  configuration <k> .K </k>

  rule [write]:       seq(write(addr(A), _), P) => P requires A >=Int 0
  rule [writeFault]:  seq(write(addr(A), _), _) => fault requires A <Int 0
  rule [writeLogged]: seq(write(addr(A), _), P) => #log("write") ~> P requires A >=Int 0 [priority(200)]
  rule [load]:        seq(load(addr(A), _), P) => P requires A >=Int 0
  rule [loadFault]:   seq(load(addr(A), _), _) => fault requires A <Int 0
endmodule
