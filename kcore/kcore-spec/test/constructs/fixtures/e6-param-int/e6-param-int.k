// Each hooked function of INT-COMMON that the library reads as a parameter symbol (no registry
// hook), applied once in a rule's right side to variables (literal arguments would be folded
// by kompile); fixture.toml params records `kcore sem-fields`'s parameter lines.
module E6-PARAM-INT
  imports INT
  syntax KItem ::= go(Int, K, K) [symbol(go)]
  rule <k> go(1, X1:Int, X2:Int) => X1 &Int X2 ... </k>
  rule <k> go(2, X1:Int, X2:Int) => X1 xorInt X2 ... </k>
  rule <k> go(3, X1:Int, X2:Int) => X1 |Int X2 ... </k>
  rule <k> go(4, X1:Int, _) => ~Int X1 ... </k>
  rule <k> go(5, X1:Int, _) => randInt(X1) ... </k>
  rule <k> go(6, X1:Int, _) => srandInt(X1) ... </k>
endmodule
