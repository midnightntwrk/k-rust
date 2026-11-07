// Flow fixture (KINK-guard-coverage): complementary boundary rules over a halted flag and an
// interrupt flag, one of which never holds on the corpus (no program halts), and a function
// whose two equations split an address range, one of which no program refutes.
module GUARDS-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Pgm ::= step(Bool, Bool) [symbol(step)]
               | write(Int)       [symbol(write)]
endmodule

module GUARDS
  imports GUARDS-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>

  syntax KItem ::= "dispatched" | "ran" | "woke" | "slept" | stored(Int)
  rule [dispatch]: <k> step(H, I) => dispatched </k> requires notBool H andThenBool I
  rule [run]:      <k> step(H, I) => ran </k>        requires notBool H andThenBool notBool I
  rule [wake]:     <k> step(H, I) => woke </k>       requires H andThenBool I
  rule [halted]:   <k> step(H, I) => slept </k>      requires H andThenBool notBool I

  syntax Int ::= store(Int) [function, symbol(store)]
  rule [low]:  store(A) => A requires A <Int 32768
  rule [high]: store(A) => 0 requires A >=Int 32768
  rule [writing]: <k> write(A) => stored(store(A)) </k>
endmodule
