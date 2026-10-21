module SYMENSURES-SYNTAX
  syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
  syntax Address ::= addr(Nat) [symbol(addr)]
  syntax Op ::= write(Address, Nat) [symbol(write)]
              | load(Address, Nat) [symbol(load)]
  syntax Prog ::= "halt" [symbol(halt)]
                | seq(Op, Prog) [symbol(seq)]
                | pin(Nat, Nat, Prog) [symbol(pin)]
endmodule

module SYMENSURES
  imports SYMENSURES-SYNTAX
  imports BASIC-K
  imports K-EQUAL
  imports BOOL
  configuration <k> .K </k>

  // `pin` constrains its symbolic arguments after the events that carry them.
  rule [pin]:   pin(A, B, P) => P ensures A ==K z andBool B ==K s(z)
  rule [write]: seq(write(A, V), P) => P
  rule [load]:  seq(load(A, V), P) => P
endmodule
