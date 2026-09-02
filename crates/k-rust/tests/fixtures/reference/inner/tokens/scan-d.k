// reference: k/result/bin/kompile --backend kore --main-module MAIN scan-d.k
module MAIN
  syntax #UpperId ::= r"[A-Z][a-zA-Z0-9]*" [prec(2), token]
  syntax Id ::= r"[A-Za-z_][A-Za-z_0-9]*" [prec(1), token]
              | #UpperId [token]
  syntax Int ::= r"[0-9]+" [token]
  syntax Exp ::= Id | Int | Exp "+" Exp [symbol(plus), left]
  rule X + 0 => X
endmodule
