// The two-layer prototype of k2lean/docs/direction.md §8 step 4, in its combined form (one K
// definition): a tiny coroutine language under a process-plus-ledger level, with the coroutine
// handoff shape of the fixture handoff (§4.3).
// - The upper layer: a transaction's coordination script, a DAG of tasks. The root task forks one
//   task per instruction; a task runs as soon as its inputs are ready. `new(Q, C)` creates the
//   process Q with code C. `resume(Q, N, I)` is the N-th resume of Q: it steps only when Q has
//   taken N segments and its input I exists, a literal or the output `o(P, M)` of the M-th segment
//   of P, which the resume spends (an output is spent once, as a UTXO is).
// - The lower layer: the coroutine language, run by the task that resumed the process. Between
//   segments a process is suspended in <procs> (`st(N, R, C)`: N segments taken, its register R,
//   its code C left); a resume moves its register and code into the task (`seg`), adding the input
//   to the register, and marks it `busy`; the task runs the code until `yield` (or its end), which
//   writes the register as the segment's output `o(Q, N)` and suspends the process again. So a
//   segment is atomic for the other tasks: they cannot reach a busy process, and its small steps
//   read and write only the running task's own cells. `loop(M, B)` runs B M times: the one
//   construct that repeats, so a segment's termination is a real obligation (a measure over the
//   code left, which the author writes in K).
// Ids are derived from content (the M-th segment of P writes `o(P, M)`), so no schedule changes
// which id a step writes. Two tasks naming one creation, one resume or one spend race; the
// script's well-formedness `wf` (below) excludes them.
requires "domains.md"

module TWOLAYER-SYNTAX
  imports INT-SYNTAX
  syntax Oid ::= "o" "(" Int "," Int ")"
  syntax Inp ::= Int | Oid
  // the coroutine language
  syntax Stmt ::= "add" "(" Int ")"           // add a constant to the register
                | "dbl"                       // double the register
                | "loop" "(" Int "," Code ")" // the body, that many times
                | "yield"                     // end the segment: its output is the register
  syntax Stmts ::= List{Stmt, ";"}
  syntax Code ::= "{" Stmts "}"
  // the coordination script
  syntax Instr ::= "new" "(" Int "," Code ")"
                 | "resume" "(" Int "," Int "," Inp ")"
  syntax Pgm ::= List{Instr, "&"}
endmodule

module TWOLAYER
  imports TWOLAYER-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports BOOL

  syntax KItem ::= st(Int, Int, Stmts)  // a suspended process: segments taken, register, code left
                 | busy(Int)            // a process in its N-th segment
                 | seg(Int, Int, Stmts) // a task running the N-th segment of a process: code left
  syntax Stmts ::= app(Stmts, Stmts) [function, total]
  rule app(.Stmts, T) => T
  rule app(S ; R, T) => S ; app(R, T)

  configuration <T>
      <tasks> <task multiplicity="*" type="Map" initial="">
        <tid> 0 </tid> <n> 0 </n> <reg> 0 </reg> <k> $PGM:Pgm </k>
      </task> </tasks>
      <procs> .Map </procs>
      <vals> .Map </vals>
    </T>

  // the upper layer
  rule <tasks> <task> <tid> 0 </tid> <n> N => N +Int 1 </n> <k> I:Instr & P:Pgm => P </k> ... </task>
         (.Bag => <task> <tid> N +Int 1 </tid> <n> 0 </n> <reg> 0 </reg> <k> I </k> </task>) ... </tasks> [label(fork)]
  rule <k> .Pgm => .K </k> [label(nil)]
  rule <k> new(Q, { C }) => .K </k> <procs> ... .Map => Q |-> st(0, 0, C) ... </procs> [label(new)]
  rule <k> resume(Q, N, V:Int) => seg(Q, N, C) </k> <reg> _ => R +Int V </reg>
       <procs> ... Q |-> (st(N, R, C) => busy(N)) ... </procs> [label(resume-lit)]
  rule <k> resume(Q, N, I:Oid) => seg(Q, N, C) </k> <reg> _ => R +Int V </reg>
       <procs> ... Q |-> (st(N, R, C) => busy(N)) ... </procs>
       <vals> ... I |-> V:Int => .Map ... </vals> [label(resume-oid)]
  rule <tasks> (<task> <tid> _ </tid> <k> .K </k> ... </task> => .Bag) ... </tasks> [label(done)]

  // the lower layer, inside the running task
  rule <k> seg(Q, N, add(I) ; C) => seg(Q, N, C) </k> <reg> R => R +Int I </reg> [label(add)]
  rule <k> seg(Q, N, dbl ; C) => seg(Q, N, C) </k> <reg> R => R *Int 2 </reg> [label(dbl)]
  rule <k> seg(Q, N, loop(M, { B }) ; C) => seg(Q, N, app(B, loop(M -Int 1, { B }) ; C)) </k>
    requires M >Int 0 [label(loop)]
  rule <k> seg(Q, N, loop(M, _) ; C) => seg(Q, N, C) </k> requires M <=Int 0 [label(loop-done)]
  rule <k> seg(Q, N, yield ; C) => .K </k> <reg> R </reg>
       <procs> ... Q |-> (busy(N) => st(N +Int 1, R, C)) ... </procs>
       <vals> ... .Map => o(Q, N) |-> R ... </vals> [label(yield)]
  rule <k> seg(Q, N, .Stmts) => .K </k> <reg> R </reg>
       <procs> ... Q |-> (busy(N) => st(N +Int 1, R, .Stmts)) ... </procs>
       <vals> ... .Map => o(Q, N) |-> R ... </vals> [label(end)]

  // The script's well-formedness, `wf` (`gen --invariant wf@T`): no claim is named twice, within
  // one task or across tasks. A task claims what its instruction or segment names: `new(Q, _)` the
  // creation of Q (the claim `Q`), `resume(Q, N, I)` the N-th resume of Q (the claim `o(Q, N)`, the
  // id of its output) and, for an output I, its spend (`sp(I)`); a running segment `seg(Q, N, _)`
  // its output `o(Q, N)`. A done task claims nothing. The order K's map pattern takes the tasks in
  // is not fixed, and `noDup` does not depend on it.
  syntax KItem ::= sp(Oid)
  syntax List ::= iclaims(Instr) [function, total]
                | pclaims(Pgm) [function, total]
                | kclaims(K) [function, total]
                | mclaims(TasksCell) [function, total]
  syntax Bool ::= wf(TCell) [function, total]
                | noDup(List) [function, total]
  rule iclaims(new(Q, _)) => ListItem(Q)
  rule iclaims(resume(Q, N, _:Int)) => ListItem(o(Q, N))
  rule iclaims(resume(Q, N, I:Oid)) => ListItem(o(Q, N)) ListItem(sp(I))
  rule pclaims(I & P) => iclaims(I) pclaims(P)
  rule pclaims(.Pgm) => .List
  rule kclaims(I:Instr) => iclaims(I)
  rule kclaims(P:Pgm) => pclaims(P)
  rule kclaims(seg(Q, N, _)) => ListItem(o(Q, N))
  rule kclaims(_) => .List [owise]
  rule mclaims(<tasks> .Bag </tasks>) => .List
  rule mclaims(<tasks> <task> <tid> _ </tid> <n> _ </n> <reg> _ </reg> <k> K </k> </task> Ts </tasks>)
    => kclaims(K) mclaims(<tasks> Ts </tasks>)
  rule noDup(.List) => true
  rule noDup(ListItem(X) L) => notBool (X in L) andBool noDup(L)
  rule wf(<T> TS:TasksCell <procs> _ </procs> <vals> _ </vals> </T>) => noDup(mclaims(TS))
endmodule
