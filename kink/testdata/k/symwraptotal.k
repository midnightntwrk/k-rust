module SYMWRAPTOTAL-SYNTAX
  syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
  syntax Address ::= addr(Nat) [symbol(addr)] | wrap(Nat) [symbol(wrap), function, total]
  syntax Op ::= write(Address, Nat) [symbol(write)]
              | load(Address, Nat) [symbol(load)]
  syntax Prog ::= "halt" [symbol(halt)]
                | seq(Op, Prog) [symbol(seq)]
endmodule

module SYMWRAPTOTAL
  imports SYMWRAPTOTAL-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  // `wrap` is constructor-like syntax, but this equation makes it non-injective:
  // wrap(s(z)) and wrap(z) denote the same Address.
  rule [collapse]: wrap(s(z)) => wrap(z) [anywhere]
  rule [write]: seq(write(A, V), P) => P
  rule [load]:  seq(load(A, V), P) => P
endmodule
