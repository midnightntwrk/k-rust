// CS-15 spike: ground Map, Set and List values in the final configuration. The Bytes key is
// built with `encodeBytes("UTF-8", S)`, whose encoding domains.md names, not `String2Bytes`,
// whose value it leaves open (re-pin decision 1, R0c).
module COLLSTORE-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  syntax Prog ::= put(Int, Int) [symbol(put)]
                | putTwo(Int, Int, Int, Int) [symbol(putTwo)]
                | putTwoRev(Int, Int, Int, Int) [symbol(putTwoRev)]
                | dupKey(Int) [symbol(dupKey)]
                | dupElem(Int) [symbol(dupElem)]
                | addSet(Int) [symbol(addSet)]
                | logList(Int) [symbol(logList)]
                | fKey(Int) [symbol(fKey)]
                | fVal(Int) [symbol(fVal)]
                | bytesKey(String) [symbol(bytesKey)]
                | nest(Int) [symbol(nest)]
                | clear() [symbol(clear)]
                | seq(Prog, Prog) [symbol(seq)]
                | halt() [symbol(halt)]
  syntax Int ::= f(Int) [function, symbol(f)]
endmodule

module COLLSTORE
  imports COLLSTORE-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  imports SET
  imports LIST
  imports BYTES
  imports STRING
  configuration <k> $PGM:Prog </k> <store> .Map </store> <seen> .Set </seen> <log> .List </log> <deep> .Map </deep>

  rule [seq]: <k> seq(P, Q) => P ~> Q ... </k>
  rule [put]: <k> put(K, V) => .K ... </k> <store> M => M [ K <- V ] </store>
  rule [putTwo]: <k> putTwo(K1, V1, K2, V2) => .K ... </k> <store> M => M [ K1 <- V1 ] [ K2 <- V2 ] </store>
  rule [putTwoRev]: <k> putTwoRev(K1, V1, K2, V2) => .K ... </k> <store> M => M [ K2 <- V2 ] [ K1 <- V1 ] </store>
  rule [dupKey]: <k> dupKey(K) => .K ... </k> <store> M => M (K |-> 1) </store>
  rule [dupElem]: <k> dupElem(I) => .K ... </k> <seen> S => S SetItem(I) </seen>
  rule [addSet]: <k> addSet(I) => .K ... </k> <seen> S => S |Set SetItem(I) </seen>
  rule [logList]: <k> logList(I) => .K ... </k> <log> L => L ListItem(I) </log>
  rule [fKey]: <k> fKey(I) => .K ... </k> <store> M => M [ f(I) <- 1 ] </store>
  rule [fVal]: <k> fVal(I) => .K ... </k> <store> M => M [ 1 <- f(I) ] </store>
  rule [bytesKey]: <k> bytesKey(S) => .K ... </k> <store> M => M [ encodeBytes("UTF-8", S) <- 1 ] </store>
  rule [nest]: <k> nest(I) => .K ... </k> <deep> D => D [ SetItem(I) <- ListItem(I) ListItem(I) ] </deep>
  rule [clear]: <k> clear() => .K ... </k> <store> _ => .Map </store>
  rule [halt]: <k> halt() => .K ... </k>
  rule [f0]: f(0) => 0
endmodule
