// Each hooked function of FLOAT that the library reads as a parameter symbol (no registry
// hook), applied once in a rule's right side to variables (literal arguments would be folded
// by kompile); fixture.toml params records `kcore sem-fields`'s parameter lines.
module E6-PARAM-FLOAT
  imports FLOAT
  imports INT
  imports BOOL
  syntax KItem ::= go(Int, K, K) [symbol(go)]
  rule <k> go(1, X1:Float, _) => Float2Int(X1) ... </k>
  rule <k> go(2, X1:Float, X2:Float) => X1 ^Float X2 ... </k>
  rule <k> go(3, X1:Float, _) => acosFloat(X1) ... </k>
  rule <k> go(4, X1:Float, _) => asinFloat(X1) ... </k>
  rule <k> go(5, X1:Float, X2:Float) => atan2Float(X1, X2) ... </k>
  rule <k> go(6, X1:Float, _) => atanFloat(X1) ... </k>
  rule <k> go(7, X1:Float, _) => cosFloat(X1) ... </k>
  rule <k> go(8, X1:Float, _) => expFloat(X1) ... </k>
  rule <k> go(9, X1:Float, _) => exponentFloat(X1) ... </k>
  rule <k> go(10, X1:Float, _) => logFloat(X1) ... </k>
  rule <k> go(11, X1:Float, X2:Float) => maxFloat(X1, X2) ... </k>
  rule <k> go(12, X1:Float, X2:Float) => minFloat(X1, X2) ... </k>
  rule <k> go(13, X1:Float, X2:Int) => rootFloat(X1, X2) ... </k>
  rule <k> go(14, X1:Float, _) => signFloat(X1) ... </k>
  rule <k> go(15, X1:Float, _) => sinFloat(X1) ... </k>
  rule <k> go(16, X1:Float, _) => tanFloat(X1) ... </k>
endmodule
