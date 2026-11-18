// Each hooked function of MAP that the library reads as a parameter symbol (no registry
// hook), applied once in a rule's right side to variables (literal arguments would be folded
// by kompile); fixture.toml params records `kcore sem-fields`'s parameter lines.
module E6-PARAM-MAP
  imports MAP
  imports LIST
  imports BOOL
  imports INT
  syntax KItem ::= go(Int, K, K) [symbol(go)]
  rule <k> go(1, X1:Map, _) => choice(X1) ... </k>
  rule <k> go(2, X1:Map, X2:Map) => X1 -Map X2 ... </k>
  rule <k> go(3, X1:Map, X2:Map) => X1 <=Map X2 ... </k>
  rule <k> go(4, X1:Map, _) => keys_list(X1) ... </k>
  rule <k> go(5, X1:Map, X2:Map) => updateMap(X1, X2) ... </k>
  rule <k> go(6, X1:Map, _) => values(X1) ... </k>
endmodule
