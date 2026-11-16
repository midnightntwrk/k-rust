// vault.k with one rule added that copies the secret into the public cell (`leak`). Not
// noninterfering: the decided condition rejects `leak`, and examples/vault-leaky's User.Leak
// refutes its obligation by two runs. Compiled to vault-leaky.kore by findings/work/p31/vault-kore.sh.
module VAULT-LEAKY
  imports INT
  syntax Op ::= "inc" [symbol(inc)] | "save" [symbol(save)] | store(Int) [symbol(store)] | "wipe" [symbol(wipe)] | "leak" [symbol(leak)]
  syntax Ops ::= Op | Op ";" Ops [symbol(seq)]
  configuration <k> $PGM:Ops </k> <pub> 0 </pub> <sec> 0 </sec>
  rule <k> O:Op ; Os:Ops => O ~> Os ... </k>
  rule <k> inc => .K ... </k> <pub> P => P +Int 1 </pub>
  rule <k> save => .K ... </k> <pub> P </pub> <sec> _ => P </sec>
  rule <k> store(N) => .K ... </k> <sec> _ => N </sec>
  rule <k> wipe => .K ... </k> <sec> _ => 0 </sec>
  rule <k> leak => .K ... </k> <pub> _ => S </pub> <sec> S </sec>
endmodule
