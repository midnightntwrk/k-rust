// reference: k/result/bin/kompile --backend kore --main-module MAIN scan-b.k
module MAIN
  syntax Id ::= r"[a-zA-Z][a-zA-Z0-9_]*" [token]
  syntax Int ::= r"[0-9]+" [token]
  syntax Exp ::= Id | Int | Exp "+" Exp [symbol(plus), left]
  rule bar => 1
endmodule
