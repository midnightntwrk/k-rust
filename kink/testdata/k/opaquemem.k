module OPAQUEMEM-SYNTAX
  syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
  syntax Address ::= addr(Nat) [symbol(addr)]
                   | opaque(Nat) [function, total, symbol(opaque)]
  syntax Op ::= write(Address, Nat) [symbol(write)]
              | load(Address, Nat) [symbol(load)]
  syntax Prog ::= "halt" [symbol(halt)]
                | seq(Op, Prog) [symbol(seq)]
endmodule

module OPAQUEMEM
  imports OPAQUEMEM-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule [write]: seq(write(A, V), P) => P
  rule [load]:  seq(load(A, V), P) => P
endmodule
