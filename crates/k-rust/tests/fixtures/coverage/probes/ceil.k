// Ceil equations, selected by the predicate simplifier's ceil scan and by the definedness
// analysis, each with a higher-priority equation that decides and a lower-priority one that would
// decide otherwise (`offered_mutation.rs`, `run_coverage.rs`).
module CEIL-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)] | done(Int) [symbol(done)]
               | rhs(Int) [symbol(rhs)] | req(Int) [symbol(req)]
endmodule

module CEIL
  imports CEIL-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  syntax Int ::= g(Int) [function, symbol(g)]
               | k(Int) [function, symbol(k)]
  rule [gEq]:     g(X) => X +Int 1 requires X >Int 100
  rule [gTop]:    #Ceil(g(_X:Int)) => #Top [simplification]
  rule [gBottom]: #Ceil(g(_X:Int)) => #Bottom [simplification(60)]
  rule [kEq]:     k(X) => X +Int 1 requires X >Int 100
  rule [kCeil]:   #Ceil(k(X:Int)) => {(X >Int 100) #Equals true} [simplification]
  rule [kBottom]: #Ceil(k(_X:Int)) => #Bottom [simplification(60)]
  rule [go]:      go(X) => done(X) requires #Ceil(g(X))
  rule [rhs]:     rhs(X) => done(k(X))
  rule [req]:     req(X) => done(X) requires #Ceil(k(X))
endmodule
