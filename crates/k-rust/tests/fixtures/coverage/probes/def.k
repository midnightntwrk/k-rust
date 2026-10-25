// The ceil equations of the definedness of a right-hand side: the higher-priority one decides
// and the lower-priority one would decide otherwise (`offered_mutation.rs`, `run_coverage.rs`).
module DEF-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= done(Int) [symbol(done)] | def(Int) [symbol(def)]
endmodule

module DEF
  imports DEF-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  syntax Int ::= t(Int) [function, symbol(t)]
  rule [tEq]:      t(X) => X requires X >Int 0
  rule [tCeil]:    #Ceil(t(X:Int)) => {(X >Int 0) #Equals true} [simplification]
  rule [tBottom]:  #Ceil(t(_X:Int)) => #Bottom [simplification(60)]
  rule [def]:      def(X) => done(t(X))
endmodule
