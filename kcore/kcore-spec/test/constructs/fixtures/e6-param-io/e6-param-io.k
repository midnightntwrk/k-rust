// Each hooked function of K-IO that the library reads as a parameter symbol (no registry
// hook), applied once in a rule's right side to variables (literal arguments would be folded
// by kompile); fixture.toml params records `kcore sem-fields`'s parameter lines.
module E6-PARAM-IO
  imports K-IO
  imports INT
  imports STRING
  syntax KItem ::= go(Int, K, K) [symbol(go)]
  rule <k> go(1, X1:Int, _) => #accept(X1) ... </k>
  rule <k> go(2, X1:Int, _) => #close(X1) ... </k>
  rule <k> go(3, X1:Int, _) => #getc(X1) ... </k>
  rule <k> go(4, X1:Int, X2:Int) => #lock(X1, X2) ... </k>
  rule <k> go(5, X1:String, _) => #log(X1) ... </k>
  rule <k> go(6, X1:String, X2:String) => #logToFile(X1, X2) ... </k>
  rule <k> go(7, X1:String, _) => #mkstemp(X1) ... </k>
  rule <k> go(8, X1:String, X2:String) => #open(X1, X2) ... </k>
  rule <k> go(9, X1:Int, X2:Int) => #putc(X1, X2) ... </k>
  rule <k> go(10, X1:Int, X2:Int) => #read(X1, X2) ... </k>
  rule <k> go(11, X1:String, _) => #remove(X1) ... </k>
  rule <k> go(12, X1:Int, X2:Int) => #seek(X1, X2) ... </k>
  rule <k> go(13, X1:Int, X2:Int) => #seekEnd(X1, X2) ... </k>
  rule <k> go(14, X1:Int, _) => #shutdownWrite(X1) ... </k>
  rule <k> go(15, X1:String, _) => #system(X1) ... </k>
  rule <k> go(16, X1:Int, _) => #tell(X1) ... </k>
  rule <k> go(17, _, _) => #time() ... </k>
  rule <k> go(18, X1:KItem, _) => #trace(X1) ... </k>
  rule <k> go(19, X1:K, _) => #traceK(X1) ... </k>
  rule <k> go(20, X1:Int, X2:Int) => #unlock(X1, X2) ... </k>
  rule <k> go(21, X1:Int, X2:String) => #write(X1, X2) ... </k>
endmodule
