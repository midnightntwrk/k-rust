// The equation selection sites outside the function and simplification term scans, each with a
// higher-priority equation that decides and a lower-priority one that would decide otherwise
// (`offered_mutation.rs`, `run_coverage.rs`).
module PROBE-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)] | done(Int) [symbol(done)]
               | rhs(Int) [symbol(rhs)] | req(Int) [symbol(req)]
               | eq(Int) [symbol(eq)] | def(Int) [symbol(def)]
endmodule

// Ceil equations, selected by the predicate simplifier's ceil scan and by the definedness
// analysis.
module CEIL
  imports PROBE-SYNTAX
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

// Predicate equations of `#Equals`, selected by the predicate simplifier.
module PRED
  imports PROBE-SYNTAX
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

// `#Top` lemmas on an operand of a term-level conjunction, and the ceil equations of the
// definedness of a right-hand side. The compiler reads `X #And tp(X)` in a rule as a predicate
// on `X`, so the term-level conjunction is in the initial state, written in KORE.
module TOPDEF
  imports PROBE-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  syntax Int ::= tp(Int) [function, total, no-evaluators, symbol(tp)]
               | t(Int) [function, symbol(t)]
  rule [tpHigh]:   tp(_X) => #Top [simplification]
  rule [tpLow]:    tp(_X) => #Top [simplification(60)]
  rule [tEq]:      t(X) => X requires X >Int 0
  rule [tCeil]:    #Ceil(t(X:Int)) => {(X >Int 0) #Equals true} [simplification]
  rule [tBottom]:  #Ceil(t(_X:Int)) => #Bottom [simplification(60)]
  rule [go]:       go(X) => done(X)
  rule [def]:      def(X) => done(t(X))
endmodule
