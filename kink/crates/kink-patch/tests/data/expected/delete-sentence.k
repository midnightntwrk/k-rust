module MEMORY-SYNTAX
  syntax Nat ::= "z" [symbol(z)]
               | s(Nat) [symbol(s)]
  syntax Address ::= addr(Nat) [symbol(addr)]
  syntax State ::= write(Address, Nat) [symbol(write)]
                 | stored(Address, Nat) [symbol(stored)]
                 | load(Address, Nat) [symbol(load)]
                 | loaded(Address, Nat) [symbol(loaded)]
                 | free(Address) [symbol(free)]
                 | freed(Address) [symbol(freed)]
endmodule

module MEMORY
  imports MEMORY-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule [write]: write(A, V) => stored(A, V)
  rule [free]: free(A) => freed(A)
endmodule
