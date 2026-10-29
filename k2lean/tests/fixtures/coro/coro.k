// Coroutines in a cell map, each with its own `<k>` (`gen --progress` with `<k>` in a cell
// collection, SND-14). A process spawns a child (`child(P, N)` for its id `P` and its count `N` of
// spawns), yields (it is suspended until its parent resumes it), or resumes its `M`-th child, which
// waits until that child has yielded. Processes are never removed: a finished one has an empty
// `<k>`. Resuming a child that does not exist, has finished or has failed fails (`#fail`).
// The acceptable endings (`ended`): finished, suspended (waiting for its parent, or for the next
// transaction: the environment) or failed. A parent waits only on its children, whose ids contain
// its id, so no two processes wait on each other.
requires "domains.md"

module CORO-SYNTAX
  imports INT-SYNTAX
  syntax Pid ::= "root" | "child" "(" Pid "," Int ")"
  syntax Instr ::= "spawn" "(" Pgm ")" | "yield" | "resume" "(" Int ")"
  syntax Pgm ::= List{Instr, ";"}
endmodule

module CORO
  imports CORO-SYNTAX
  imports INT
  imports BOOL
  syntax KItem ::= "#suspended" | "#fail"
  configuration <T>
      <procs> <proc multiplicity="*" type="Map" initial="">
        <pid> root </pid> <nonce> 0 </nonce> <k> $PGM:Pgm </k>
      </proc> </procs>
    </T>

  rule <k> I:Instr ; P:Pgm => I ~> P ... </k> [label(seq)]
  rule <k> .Pgm => .K ... </k> [label(nil)]
  rule <procs> <proc> <pid> P </pid> <nonce> N => N +Int 1 </nonce> <k> spawn(G) => .K ... </k> </proc>
         (.Bag => <proc> <pid> child(P, N) </pid> <nonce> 0 </nonce> <k> G </k> </proc>) ... </procs> [label(spawn)]
  rule <k> yield => #suspended ... </k> [label(yield)]
  rule <procs> <proc> <pid> P </pid> <k> resume(M) => .K ... </k> ... </proc>
         <proc> <pid> child(P, M) </pid> <k> #suspended => .K ... </k> ... </proc> ... </procs> [label(resume)]
  rule <procs> <proc> <pid> P </pid> <k> resume(M) => #fail ... </k> ... </proc>
         <proc> <pid> child(P, M) </pid> <k> .K </k> ... </proc> ... </procs> [label(resume-finished)]
  rule <procs> <proc> <pid> P </pid> <k> resume(M) => #fail ... </k> ... </proc>
         <proc> <pid> child(P, M) </pid> <k> #fail ... </k> ... </proc> ... </procs> [label(resume-failed)]
  rule <procs> <proc> <pid> P </pid> <k> resume(M) => #fail ... </k> ... </proc> REST </procs>
    requires notBool (<pid> child(P, M) </pid> in_keys(REST)) [label(resume-none)]

  syntax Bool ::= kOk(K) [function, total]
                | itemOk(KItem) [function, total]
                | ended(K) [function, total]
  rule kOk(.K) => true
  rule kOk(I ~> K) => itemOk(I) andBool kOk(K)
  rule itemOk(_:Instr) => true
  rule itemOk(_:Pgm) => true
  rule itemOk(#suspended) => true
  rule itemOk(#fail) => true
  rule itemOk(_) => false [owise]
  rule ended(.K) => true
  rule ended(#suspended ~> _) => true
  rule ended(#fail ~> _) => true
  rule ended(_) => false [owise]
endmodule
