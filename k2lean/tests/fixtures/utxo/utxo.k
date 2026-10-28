// Coroutines over a UTXO ledger: processes in a cell map, each running its own `<k>`; outputs in a
// ledger map keyed by fresh ids. A process creates an output (a new binding: an id already bound
// would make the ledger undefined, not overwrite an output), spends one (an output is spent at
// most once: a second spend has no rule), spawns a process, yields (its `<k>` is suspended), or
// resumes a suspended process once (a second resume has no rule).
// The first process is -1: fresh ids count from 0, and a spawned process keyed like an existing one
// would make the process map undefined.
requires "domains.md"

module UTXO-SYNTAX
  imports INT-SYNTAX
  syntax Instr ::= "create" "(" Int ")"
                 | "spend" "(" Int ")"
                 | "spawn" "(" Pgm ")"
                 | "yield"
                 | "resume" "(" Int ")"
  syntax Pgm ::= List{Instr, ";"}
endmodule

module UTXO
  imports UTXO-SYNTAX
  imports INT
  imports MAP
  syntax KItem ::= "#suspended"
  configuration <T>
      <procs> <proc multiplicity="*" type="Map" initial=""> <pid> -1 </pid> <k> $PGM:Pgm </k> </proc> </procs>
      <ledger> .Map </ledger>
    </T>

  rule <k> I:Instr ; P:Pgm => I ~> P ... </k> [label(seq)]
  rule <k> .Pgm => .K ... </k> [label(nil)]
  rule <k> create(V) => .K ... </k> <ledger> ... .Map => !N:Int |-> V ... </ledger> [label(create)]
  rule <k> spend(I) => .K ... </k> <ledger> I |-> _ => .Map ... </ledger> [label(spend)]
  rule <procs> <proc> <pid> _ </pid> <k> spawn(P) => .K ... </k> </proc>
         (.Bag => <proc> <pid> !N:Int </pid> <k> P </k> </proc>) ... </procs> [label(spawn)]
  rule <k> yield => #suspended ... </k> [label(yield)]
  rule <procs> <proc> <pid> _ </pid> <k> resume(Q) => .K ... </k> </proc>
         <proc> <pid> Q </pid> <k> #suspended => .K ... </k> </proc> ... </procs> [label(resume)]
  rule <procs> (<proc> <pid> _ </pid> <k> .K </k> </proc> => .Bag) ... </procs> [label(done)]
endmodule
