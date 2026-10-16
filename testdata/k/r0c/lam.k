// Re-pin R0c-fix-1 deliverable 2 (R0c review 1 major 3, the reviewer's probe): beta reduction through
// SUBSTITUTION.substOne, whose renamed-variable suffix substitution.md leaves to the backend.
requires "substitution.md"
module LAM-SYNTAX
  imports KVAR-SYNTAX
  syntax Exp ::= KVar
               | lam(KVar, Exp) [binder, symbol(lam)]
               | app(Exp, Exp) [symbol(app)]
  syntax Prog ::= run(Exp) [symbol(run)] | out(Exp) [symbol(out)]
endmodule
module LAM
  imports LAM-SYNTAX
  imports SUBSTITUTION
  configuration <k> $PGM:Prog </k>
  rule [beta]: <k> run(app(lam(X, E), V)) => out(E[V / X]) </k>
endmodule
