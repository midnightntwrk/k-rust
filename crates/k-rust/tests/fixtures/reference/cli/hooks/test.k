module HOOKS
  imports INT
  syntax Int ::= f(Int) [function, hook(A.f)]
               | g(Int) [function, hook(B.g)]
endmodule
