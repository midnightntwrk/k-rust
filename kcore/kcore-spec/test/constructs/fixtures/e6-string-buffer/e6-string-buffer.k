module E6-STRING-BUFFER
  imports STRING-BUFFER
  syntax KItem ::= "go" [symbol(go)]
  syntax KItem ::= res(String) [symbol(res)]
  rule <k> go => res(StringBuffer2String(.StringBuffer +String "a")) </k>
endmodule
