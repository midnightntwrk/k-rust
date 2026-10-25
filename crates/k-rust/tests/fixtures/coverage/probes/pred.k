// Predicate equations of `#Equals`, selected by the predicate simplifier, each with a
// higher-priority equation that decides and a lower-priority one that would decide otherwise
// (`offered_mutation.rs`, `run_coverage.rs`).
module PRED-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)] | done(Int) [symbol(done)] | eq(Int) [symbol(eq)]
endmodule

module PRED
  imports PRED-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  syntax Int ::= h(Int) [function, total, no-evaluators, symbol(h)]
               | hs(Int) [function, total, no-evaluators, symbol(hs)]
  rule [hTop]:     {h(_X) #Equals 0} => #Top [simplification]
  rule [hBottom]:  {h(_X) #Equals 0} => #Bottom [simplification(60)]
  rule [hsFive]:   {hs(X) #Equals 0} => {X #Equals 5} [simplification]
  rule [hsBottom]: {hs(_X) #Equals 0} => #Bottom [simplification(60)]
  rule [go]:       go(X) => done(X) requires h(X) ==Int 0
  rule [eq]:       eq(X) => done(X) requires hs(X) ==Int 0
endmodule
