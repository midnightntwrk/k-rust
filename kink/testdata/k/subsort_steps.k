module SUBSORT_STEPS-SYNTAX
  syntax Small ::= "a" [symbol(a)]
  syntax Other ::= "b" [symbol(b)]
  syntax Large ::= Small | Other | "c" [symbol(c)]
  syntax Tiny ::= "t" [symbol(t)]
  syntax Left ::= Tiny | "l" [symbol(l)]
  syntax Right ::= Tiny | "r" [symbol(r)]
  syntax Wide ::= Left | Right
  syntax Prog ::= "halt" [symbol(halt)]
                | step(Large) [symbol(step)]
                | done(Large) [symbol(done)]
                | probe(Wide) [symbol(probe)]
endmodule

module SUBSORT_STEPS
  imports SUBSORT_STEPS-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule [step]: step(X) => done(X)
endmodule
