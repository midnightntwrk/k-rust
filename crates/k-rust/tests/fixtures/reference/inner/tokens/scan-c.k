// reference: k/result/bin/kompile --backend kore --main-module MAIN --syntax-module MAIN scan-c.k
module MAIN
  syntax Id ::= r"[A-Za-z_][A-Za-z_0-9]*" [prec(1), token]
  syntax Int ::= r"[0-9]+" [token]
  syntax Exp ::= Id | Int | Exp "+" Exp [symbol(plus), left]
  rule X + 0 => X
endmodule
