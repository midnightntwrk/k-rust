// A program that writes a value under a Bytes key into a Map cell and halts: a Bytes key is
// not a value kink compares (CS-T04), so the final configuration stays class unknown.
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

  rule [store]: <k> store(K, V) => .K ... </k> <mem> M => M[String2Bytes(K) <- V] </mem>
endmodule
