module SYMOWISE-SYNTAX
  syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
  syntax Address ::= addr(Nat) [symbol(addr)]
  syntax Op ::= write(Address, Nat) [symbol(write)]
              | load(Address, Nat) [symbol(load)]
  syntax Prog ::= "halt" [symbol(halt)]
                | seq(Op, Prog) [symbol(seq)]
                | pick(Nat, Prog) [symbol(pick)]
endmodule

module SYMOWISE
  imports SYMOWISE-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  // Every Nat is z or s(_), so `other` never applies to a value.
  rule [zero]:  pick(z, _) => halt
  rule [succ]:  pick(s(_), _) => halt
  rule [other]: pick(_, P) => P [owise]
  rule [write]: seq(write(A, V), P) => P
  rule [load]:  seq(load(A, V), P) => P
endmodule
