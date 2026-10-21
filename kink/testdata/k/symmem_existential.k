// VI-03F construction fixture: symmem with an existential rewrite variable.
module SYMMEM_EXISTENTIAL-SYNTAX
  syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
  syntax Address ::= addr(Nat) [symbol(addr)]
  syntax Op ::= write(Address, Nat) [symbol(write)]
              | load(Address, Nat) [symbol(load)]
              | free(Address) [symbol(free)]
  syntax Prog ::= "halt" [symbol(halt)]
                | seq(Op, Prog) [symbol(seq)]
                | fork(Prog, Prog) [symbol(fork)]
endmodule

module SYMMEM_EXISTENTIAL
  imports SYMMEM_EXISTENTIAL-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule [write]: seq(write(A, V), P) => seq(write(A, ?W:Nat), P)
  rule [load]:  seq(load(A, V), P) => P
  rule [free]:  seq(free(A), P) => P
  rule [left]:  fork(P, _) => P
  rule [right]: fork(_, Q) => Q
endmodule
