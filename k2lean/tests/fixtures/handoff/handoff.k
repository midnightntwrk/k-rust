// The coroutine handoff shape: a transaction's coordination script is a DAG of tasks, and a task
// runs as soon as its inputs are ready. A process (a coroutine) is resumed by one task at a time,
// and its whole segment, from the resume to its next yield, is one step: the resumer waits for it,
// so nothing interleaves inside a segment. The segment is the K functions `next` and `out` of the
// process's state and the resumed value: the lower layer, left as parameters.
// The root task forks one task per instruction of the script. Readiness is in the rules:
// `resume(Q, N, I)` is the N-th resume of the process Q, which steps only when Q has taken N
// segments and the input I exists (a literal, or the output `o(P, M)` of the M-th segment of P).
// Ids are derived from content: the M-th segment of P writes its output at `o(P, M)`, so no
// schedule changes which id a step writes. Two tasks naming the same N-th resume of one process,
// or creating one process, race; the script's well-formedness excludes them.
requires "domains.md"
module HANDOFF-SYNTAX
  imports INT-SYNTAX
  syntax Oid ::= "o" "(" Int "," Int ")"
  syntax Inp ::= Int | Oid
  syntax Instr ::= "new" "(" Int "," Int ")"
                 | "resume" "(" Int "," Int "," Inp ")"
  syntax Pgm ::= List{Instr, ";"}
endmodule
module HANDOFF
  imports HANDOFF-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports BOOL
  syntax KItem ::= st(Int, Int)
  // the lower layer: a segment's next state and output, parameters of the definition (no equations,
  // so fields of the generated `class Hooks`): what is proved holds for every coroutine language
  syntax Int ::= next(Int, Int) [function]
               | out(Int, Int) [function]
  configuration <T>
      <tasks> <task multiplicity="*" type="Map" initial="">
        <tid> 0 </tid> <n> 0 </n> <k> $PGM:Pgm </k>
      </task> </tasks>
      <procs> .Map </procs>
      <vals> .Map </vals>
    </T>
  // the root forks one task per instruction, at ids derived from its count of forks
  rule <tasks> <task> <tid> 0 </tid> <n> N => N +Int 1 </n> <k> I:Instr ; P:Pgm => P </k> </task>
         (.Bag => <task> <tid> N +Int 1 </tid> <n> 0 </n> <k> I </k> </task>) ... </tasks> [label(fork)]
  rule <k> .Pgm => .K </k> [label(nil)]
  rule <k> new(Q, S) => .K </k> <procs> ... .Map => Q |-> st(0, S) ... </procs> [label(new)]
  rule <k> resume(Q, N, V:Int) => .K </k> <procs> ... Q |-> (st(N, S) => st(N +Int 1, next(S, V))) ... </procs>
       <vals> ... .Map => o(Q, N) |-> out(S, V) ... </vals> [label(resume-lit)]
  rule <k> resume(Q, N, I:Oid) => .K </k> <procs> ... Q |-> (st(N, S) => st(N +Int 1, next(S, V))) ... </procs>
       <vals> ... I |-> V:Int (.Map => o(Q, N) |-> out(S, V)) ... </vals> [label(resume-oid)]
  rule <tasks> (<task> <tid> _ </tid> <k> .K </k> ... </task> => .Bag) ... </tasks> [label(done)]

  // The script's well-formedness, `wf` (`gen --invariant wf@T`, k2lean/docs/invariants.md): no
  // claim is named twice, within one task or across tasks. A task claims what its instruction or
  // program names: `new(Q, _)` the creation of `Q` (the claim `Q`), `resume(Q, N, _)` the `N`-th
  // resume of `Q` (the claim `o(Q, N)`, the id of its output). A task whose `<k>` is done claims
  // nothing. `mclaims` lists the claims of every task; the order K's map pattern takes the tasks
  // in is not fixed, and `noDup` does not depend on it.
  syntax List ::= iclaims(Instr) [function, total]
                | pclaims(Pgm) [function, total]
                | kclaims(K) [function, total]
                | mclaims(TasksCell) [function, total]
  syntax Bool ::= wf(TCell) [function, total]
                | noDup(List) [function, total]
  rule iclaims(new(Q, _)) => ListItem(Q)
  rule iclaims(resume(Q, N, _)) => ListItem(o(Q, N))
  rule pclaims(I ; P) => iclaims(I) pclaims(P)
  rule pclaims(.Pgm) => .List
  rule kclaims(I:Instr) => iclaims(I)
  rule kclaims(P:Pgm) => pclaims(P)
  rule kclaims(_) => .List [owise]
  rule mclaims(<tasks> .Bag </tasks>) => .List
  rule mclaims(<tasks> <task> <tid> _ </tid> <n> _ </n> <k> K </k> </task> Ts </tasks>)
    => kclaims(K) mclaims(<tasks> Ts </tasks>)
  rule noDup(.List) => true
  rule noDup(ListItem(X) L) => notBool (X in L) andBool noDup(L)
  rule wf(<T> TS:TasksCell <procs> _ </procs> <vals> _ </vals> </T>) => noDup(mclaims(TS))
endmodule
