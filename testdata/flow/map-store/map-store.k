// Flow fixture (F-03): a program that writes a value into a Map cell and halts.
// Until ground collections are admitted (corpus-scale CS-15/CS-16) a final
// configuration holding a Map is not a comparable value: class unknown.
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
