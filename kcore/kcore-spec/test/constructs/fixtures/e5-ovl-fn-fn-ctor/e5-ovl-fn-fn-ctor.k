module E5-OVL-FN-FN-CTOR
  imports INT
  syntax N ::= "z" [symbol(z)]
  syntax Exp ::= N | "e" [symbol(e)]
  syntax Exp ::= s(Exp) [function, symbol(sExp), overload(s)]
  syntax N ::= s(N) [symbol(sN), overload(s)]
  rule s(e) => e
endmodule
