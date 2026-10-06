module EXPS-SYNTAX
  imports SORT-BOOL
  syntax Nat ::= "z" [symbol(z)]
               | s(Nat) [symbol(s)]
  syntax Exp ::= Nat
               | plus(Exp, Exp) [symbol(plus)]
               | f(Exp) [function, symbol(f)]
endmodule

module EXPS
  imports EXPS-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule f(X) => X
  rule [cast]: plus((E => z):Nat, z)
endmodule
