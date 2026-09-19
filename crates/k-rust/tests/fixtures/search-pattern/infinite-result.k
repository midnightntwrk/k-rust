module INFINITE-RESULT-SYNTAX
  syntax Nat ::= "z" [symbol(z)]
               | "s" "(" Nat ")" [symbol(s)]
  syntax State ::= "loop" "(" Nat ")" [symbol(loop)]
                 | "done" "(" Nat ")" [symbol(done)]
endmodule

module INFINITE-RESULT
  imports INFINITE-RESULT-SYNTAX

  configuration <k> $PGM:State </k>

  rule loop(N:Nat) => done(N)
  rule loop(N:Nat) => loop(s(N))
endmodule
