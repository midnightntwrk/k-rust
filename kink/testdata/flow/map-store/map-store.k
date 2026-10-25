// Flow fixture (F-03): a program that writes a value into a Map cell and halts.
// A final configuration holding a ground natural Map is comparable.
// Collections with entries kink cannot compare remain class unknown.
module MAP-STORE-SYNTAX
  imports INT-SYNTAX
  syntax Stmt ::= "store" "(" Int "," Int ")" [symbol(store)]
endmodule

module MAP-STORE
  imports MAP-STORE-SYNTAX
  imports INT
  imports MAP
  configuration <k> $PGM:Stmt </k> <mem> .Map </mem>

  rule [store]: <k> store(K, V) => .K ... </k> <mem> M => M[K <- V] </mem>
endmodule
