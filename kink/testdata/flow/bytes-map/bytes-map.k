// A program that writes a value under a Bytes key into a Map cell and halts: a Bytes key is
// not a value kink compares (CS-T04), so the final configuration stays class unknown. The key is
// built with `encodeBytes("UTF-8", K)`, whose encoding domains.md names, not `String2Bytes`,
// whose value it leaves open (re-pin decision 1, R0c).
module BYTES-MAP-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  syntax Stmt ::= "store" "(" String "," Int ")" [symbol(store)]
endmodule

module BYTES-MAP
  imports BYTES-MAP-SYNTAX
  imports INT
  imports STRING
  imports BYTES
  imports MAP
  configuration <k> $PGM:Stmt </k> <mem> .Map </mem>

  rule [store]: <k> store(K, V) => .K ... </k> <mem> M => M[encodeBytes("UTF-8", K) <- V] </mem>
endmodule
