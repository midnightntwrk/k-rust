module E5-HOOKED-INT
  imports INT
  syntax MyInt [hook(INT.Int)]
  syntax MyInt ::= r"[0-9]+" [token, prec(2)]
  syntax MyInt ::= MyInt "+My" MyInt [function, total, hook(INT.add), symbol(plusMy)]
  syntax MyInt ::= sum(MyInt, MyInt) [function, total, symbol(sum)]
  rule sum(X, Y) => X +My Y
  syntax KItem ::= "go" [symbol(go)] | "go2" [symbol(go2)]
  rule <k> go => 2 +My 3 </k>
  rule <k> go2 => sum(2, 3) </k>
endmodule
