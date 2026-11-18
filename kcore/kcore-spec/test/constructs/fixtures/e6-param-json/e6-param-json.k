// Each hooked function of JSON that the library reads as a parameter symbol (no registry
// hook), applied once in a rule's right side to variables (literal arguments would be folded
// by kompile); fixture.toml params records `kcore sem-fields`'s parameter lines.
requires "json.md"
module E6-PARAM-JSON
  imports JSON
  imports INT
  imports STRING
  syntax KItem ::= go(Int, K, K) [symbol(go)]
  rule <k> go(1, X1:JSON, _) => JSON2String(X1) ... </k>
  rule <k> go(2, X1:String, _) => String2JSON(X1) ... </k>
endmodule
