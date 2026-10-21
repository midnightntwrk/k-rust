module CS13-CLEAN
  imports BOOL
  syntax Program ::= "a" [symbol(a)]
                   | "b" [symbol(b)]
                   | "c" [symbol(c)]
                   | "done" [symbol(done)]
  configuration <k> $PGM:K </k>
  rule a => b
  rule b => c
  rule c => done
endmodule
