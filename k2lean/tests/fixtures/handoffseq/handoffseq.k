// The sequential definition of the fixture handoff: the coordination script's instructions run in
// the script's order, one after the other, over the same processes and values. Each instruction is
// the step its task takes in handoff, with the same readiness: a resume steps only when its process
// has taken N segments and its input exists, so a script that is out of order is stuck here where
// handoff may still run it. The lower layer is the same parameters `next` and `out`.
requires "domains.md"
module HANDOFFSEQ-SYNTAX
  imports INT-SYNTAX
  syntax Oid ::= "o" "(" Int "," Int ")"
  syntax Inp ::= Int | Oid
  syntax Instr ::= "new" "(" Int "," Int ")"
                 | "resume" "(" Int "," Int "," Inp ")"
  syntax Pgm ::= List{Instr, ";"}
endmodule
module HANDOFFSEQ
  imports HANDOFFSEQ-SYNTAX
  imports INT
  imports MAP
  syntax KItem ::= st(Int, Int)
  syntax Int ::= next(Int, Int) [function]
               | out(Int, Int) [function]
  configuration <T>
      <k> $PGM:Pgm </k>
      <procs> .Map </procs>
      <vals> .Map </vals>
    </T>
  rule <k> new(Q, S) ; P:Pgm => P </k> <procs> ... .Map => Q |-> st(0, S) ... </procs> [label(new)]
  rule <k> resume(Q, N, V:Int) ; P:Pgm => P </k> <procs> ... Q |-> (st(N, S) => st(N +Int 1, next(S, V))) ... </procs>
       <vals> ... .Map => o(Q, N) |-> out(S, V) ... </vals> [label(resume-lit)]
  rule <k> resume(Q, N, I:Oid) ; P:Pgm => P </k> <procs> ... Q |-> (st(N, S) => st(N +Int 1, next(S, V))) ... </procs>
       <vals> ... I |-> V:Int (.Map => o(Q, N) |-> out(S, V)) ... </vals> [label(resume-oid)]
  rule <k> .Pgm => .K </k> [label(nil)]
endmodule
