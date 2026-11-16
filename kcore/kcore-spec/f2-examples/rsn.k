// A user sort named like a library sort whose module is not imported (as the corpus fixture
// wordstack-fn): `Bytes` declared with a constructor of its own, BYTES not imported. kompile writes
// `sort SortBytes{} []`, a plain sort. The reader refuses the declaration with a reason of its
// own (`registrySortName`).
module RSN-SYNTAX
  imports INT-SYNTAX
  syntax Bytes ::= ".Bytes" [symbol(.Bytes)]
  syntax Cmd ::= go(Bytes) [symbol(go)] | done() [symbol(done)]
endmodule

module RSN
  imports RSN-SYNTAX
  imports INT
  configuration <k> $PGM:Cmd </k>
  rule [go]: <k> go(.Bytes) => done() </k>
endmodule
