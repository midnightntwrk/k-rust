requires "substitution.md"
module E2-BINDER
  imports KVAR
  imports INT
  syntax Exp ::= KVar | Int | lam(KVar, Exp)         [binder, symbol(lam)]
endmodule
