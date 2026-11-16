// A probe for the noninterference kind's decided condition (KcoreSpec/NICells.lean): a public
// counter `<pub>` and a secret `<sec>`, the secret a whole cell (`kcore gen … --high sec`). Every
// rule keeps what an observer of `<pub>` and `<k>` sees independent of `<sec>`: public data may
// flow into the secret (`save`), a constant may overwrite it (`store`, `wipe`), and nothing reads it.
// Compiled to vault.kore by findings/work/p31/vault-kore.sh.
module VAULT
  imports INT
  syntax Op ::= "inc" [symbol(inc)] | "save" [symbol(save)] | store(Int) [symbol(store)] | "wipe" [symbol(wipe)]
  syntax Ops ::= Op | Op ";" Ops [symbol(seq)]
  configuration <k> $PGM:Ops </k> <pub> 0 </pub> <sec> 0 </sec>
  rule <k> O:Op ; Os:Ops => O ~> Os ... </k>
  rule <k> inc => .K ... </k> <pub> P => P +Int 1 </pub>
  rule <k> save => .K ... </k> <pub> P </pub> <sec> _ => P </sec>
  rule <k> store(N) => .K ... </k> <sec> _ => N </sec>
  rule <k> wipe => .K ... </k> <sec> _ => 0 </sec>
endmodule
