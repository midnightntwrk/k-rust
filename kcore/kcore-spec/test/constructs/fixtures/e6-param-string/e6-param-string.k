// Each hooked function of STRING-COMMON and ID-COMMON that the library reads as a parameter symbol (no registry
// hook), applied once in a rule's right side to variables (literal arguments would be folded
// by kompile); fixture.toml params records `kcore sem-fields`'s parameter lines.
module E6-PARAM-STRING
  imports STRING
  imports ID
  imports INT
  imports FLOAT
  syntax KItem ::= go(Int, K, K) [symbol(go)]
  rule <k> go(1, X1:Int, X2:Int) => Base2String(X1, X2) ... </k>
  rule <k> go(2, X1:Float, _) => Float2String(X1) ... </k>
  rule <k> go(3, X1:Float, X2:String) => Float2String(X1, X2) ... </k>
  rule <k> go(4, X1:Id, _) => Id2String(X1) ... </k>
  rule <k> go(5, X1:String, _) => String2Float(X1) ... </k>
  rule <k> go(6, X1:String, _) => String2Id(X1) ... </k>
  rule <k> go(7, X1:String, _) => categoryChar(X1) ... </k>
  rule <k> go(8, X1:String, _) => directionalityChar(X1) ... </k>
  rule <k> go(9, _, _) => newUUID ... </k>
endmodule
