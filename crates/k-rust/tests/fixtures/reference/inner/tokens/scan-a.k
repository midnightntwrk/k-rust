// reference: k/result/bin/kompile --backend kore --main-module MAIN scan-a.k
module MAIN
  syntax Id ::= r"[a-zA-Z][a-zA-Z0-9_]*" [token]
  syntax Int ::= r"[0-9]+" [token]
  syntax Exp ::= Id | Int | Exp "+" Exp [symbol(plus), left]
  rule plus(X:Int, Y:Int) => X + Y
endmodule
