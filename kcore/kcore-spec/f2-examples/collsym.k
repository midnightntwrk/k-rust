// MAP-SYMBOLIC and SET-SYMBOLIC imported, so that the text holds the lemmas of
// MAP-KORE-SYMBOLIC and SET-KORE-SYMBOLIC (domains.md, K 7.1.337), with one rule over a map.
module COLLSYM-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= run(Int) [symbol(run)] | done(Int) [symbol(done)]
endmodule

module COLLSYM
  imports COLLSYM-SYNTAX
  imports INT
  imports BOOL
  imports MAP-SYMBOLIC
  imports SET-SYMBOLIC
  imports LIST
  configuration <k> $PGM:Cmd </k> <m> .Map </m>
  rule [go]: <k> run(N) => done(N) </k> <m> M => M [ N <- N ] </m>
endmodule
