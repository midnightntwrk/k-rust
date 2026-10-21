// Re-pin R0c-fix-1 deliverable 2 (R0c review 1 major 3): lam.k with the substitution routed through
// a fixed name y0 first, so the result is alpha-equivalent to lam.k's and differs in k-rust's suffix.
requires "substitution.md"
module LAMM-SYNTAX
  imports KVAR-SYNTAX
  syntax Exp ::= KVar
               | lam(KVar, Exp) [binder, symbol(lam)]
               | app(Exp, Exp) [symbol(app)]
  syntax Prog ::= run(Exp) [symbol(run)] | out(Exp) [symbol(out)]
endmodule
module LAMM
  imports LAMM-SYNTAX
  imports SUBSTITUTION
  imports STRING
  imports KVAR
  configuration <k> $PGM:Prog </k>
  rule [beta]: <k> run(app(lam(X, E), V)) => out(E[String2KVar("y0") / X][V / String2KVar("y0")]) </k>
endmodule
