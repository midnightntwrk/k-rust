// INT-COMMON's unhooked function `dividesInt`, applied in a rule's right side to variables, so the
// reading holds it as a parameter symbol (a bare import gives Γ no symbol of that name).
module E6-DIVIDES-INT
  imports INT
  syntax KItem ::= go(Int, Int) [symbol(go)]
  rule <k> go(X1:Int, X2:Int) => X1 dividesInt X2 ... </k>
endmodule
