// Each hooked function of RANGEMAP that the library reads as a parameter symbol (no registry
// hook), applied once in a rule's right side to variables (literal arguments would be folded
// by kompile); fixture.toml params records `kcore sem-fields`'s parameter lines.
module E6-PARAM-RANGEMAP
  imports RANGEMAP
  imports LIST
  imports INT
  syntax KItem ::= go(Int, K, K) [symbol(go)]
  rule <k> go(1, X1:RangeMap, _) => choice(X1) ... </k>
  rule <k> go(2, X1:RangeMap, _) => keys_list(X1) ... </k>
  rule <k> go(3, X1:RangeMap, _) => values(X1) ... </k>
endmodule
