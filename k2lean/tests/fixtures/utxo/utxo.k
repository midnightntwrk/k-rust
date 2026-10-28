// Coroutines over a UTXO ledger: processes in a cell map, each running its own `<k>`; outputs in a
// ledger map. Ids are derived from their content, not drawn from a counter: the process a process
// spawns is `child(P, N)` and the output it creates `oid(P, N)`, for its id `P` and its count `N`
// of spawns and creates so far (its `<nonce>`), so no schedule changes which id an action makes.
// A process creates an output owned by a process (a new binding: an id already bound would make
// the ledger undefined, not overwrite an output), spends an output it owns (once: a second spend
// has no rule), spawns a process, yields (its `<k>` is suspended), or resumes a suspended child of
// its own once (a second resume has no rule; only the parent resumes, so no two processes race for
// one).
requires "domains.md"

module UTXO-SYNTAX
  imports INT-SYNTAX
  syntax Pid ::= "root" | "child" "(" Pid "," Int ")"
  syntax Oid ::= "oid" "(" Pid "," Int ")"
  syntax Instr ::= "create" "(" Pid "," Int ")"
                 | "spend" "(" Oid ")"
                 | "spawn" "(" Pgm ")"
                 | "yield"
                 | "resume" "(" Pid ")"
  syntax Pgm ::= List{Instr, ";"}
endmodule

module UTXO
  imports UTXO-SYNTAX
  imports INT
  imports MAP
  syntax KItem ::= "#suspended" | out(Pid, Int)
  configuration <T>
      <procs> <proc multiplicity="*" type="Map" initial="">
        <pid> root </pid> <nonce> 0 </nonce> <k> $PGM:Pgm </k>
      </proc> </procs>
      <ledger> .Map </ledger>
    </T>

  rule <k> I:Instr ; P:Pgm => I ~> P ... </k> [label(seq)]
  rule <k> .Pgm => .K ... </k> [label(nil)]
  rule <procs> <proc> <pid> P </pid> <nonce> N => N +Int 1 </nonce> <k> create(Q, V) => .K ... </k> </proc> ... </procs>
       <ledger> ... .Map => oid(P, N) |-> out(Q, V) ... </ledger> [label(create)]
  rule <procs> <proc> <pid> P </pid> <k> spend(I) => .K ... </k> ... </proc> ... </procs>
       <ledger> ... I |-> out(P, _) => .Map ... </ledger> [label(spend)]
  rule <procs> <proc> <pid> P </pid> <nonce> N => N +Int 1 </nonce> <k> spawn(G) => .K ... </k> </proc>
         (.Bag => <proc> <pid> child(P, N) </pid> <nonce> 0 </nonce> <k> G </k> </proc>) ... </procs> [label(spawn)]
  rule <k> yield => #suspended ... </k> [label(yield)]
  rule <procs> <proc> <pid> P </pid> <k> resume(child(P, M)) => .K ... </k> ... </proc>
         <proc> <pid> child(P, M) </pid> <k> #suspended => .K ... </k> ... </proc> ... </procs> [label(resume)]
  rule <procs> (<proc> <pid> _ </pid> <k> .K </k> ... </proc> => .Bag) ... </procs> [label(done)]
endmodule
