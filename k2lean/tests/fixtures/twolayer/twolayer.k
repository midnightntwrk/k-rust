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
// script's well-formedness `wf` (below) excludes them, and the weaker `wfOut` all but the spends.
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
  // A weaker legality, `wfOut` (`gen --invariant wfOut@T`, the demonstration TwoOutConf): `wf`
  // without the spends' claims, so that two resumes may spend one output. Under it the race of two
  // spends remains, refuted by a program it admits (witnesses/two-spends.two); every other race is
  // excluded, as under `wf`.
  syntax List ::= iclaimsOut(Instr) [function, total]
                | pclaimsOut(Pgm) [function, total]
                | kclaimsOut(K) [function, total]
                | mclaimsOut(TasksCell) [function, total]
  syntax Bool ::= wfOut(TCell) [function, total]
  rule iclaimsOut(new(Q, _)) => ListItem(Q)
  rule iclaimsOut(resume(Q, N, _)) => ListItem(o(Q, N))
  rule pclaimsOut(I & P) => iclaimsOut(I) pclaimsOut(P)
  rule pclaimsOut(.Pgm) => .List
  rule kclaimsOut(I:Instr) => iclaimsOut(I)
  rule kclaimsOut(P:Pgm) => pclaimsOut(P)
  rule kclaimsOut(seg(Q, N, _)) => ListItem(o(Q, N))
  rule kclaimsOut(_) => .List [owise]
  rule mclaimsOut(<tasks> .Bag </tasks>) => .List
  rule mclaimsOut(<tasks> <task> <tid> _ </tid> <n> _ </n> <reg> _ </reg> <k> K </k> </task> Ts </tasks>)
    => kclaimsOut(K) mclaimsOut(<tasks> Ts </tasks>)
  rule wfOut(<T> TS:TasksCell <procs> _ </procs> <vals> _ </vals> </T>) => noDup(mclaimsOut(TS))
  // The work left, the measure of every run's length (`gen --measure measure@T`), in two maps: each
  // task weighs what its <k> still has to do, and each suspended process the steps its code left
  // takes when resumed (`mu`: one per statement, a loop's body as often as it runs, and one more for
  // the loop's own end). A resume moves a process's code from <procs> into the task and a yield
  // moves the rest back, so every rule lowers the total, by the cells it rewrites alone.
  syntax Int ::= measure(TCell) [function, total]
               | work(TasksCell) [function, total]
               | pwork(Map) [function, total]
               | sw(KItem) [function, total]
               | kw(K) [function, total]
               | iw(Instr) [function, total]
               | pw(Pgm) [function, total]
               | mu(Stmts) [function, total]
  rule measure(<T> TS:TasksCell <procs> PS </procs> _ </T>) => work(TS) +Int pwork(PS)
  rule work(<tasks> .Bag </tasks>) => 0
  rule work(<tasks> <task> <tid> _ </tid> <n> _ </n> <reg> _ </reg> <k> K </k> </task> Ts </tasks>)
    => kw(K) +Int work(<tasks> Ts </tasks>)
  rule pwork(.Map) => 0
  rule pwork((_ |-> V) PS) => sw(V) +Int pwork(PS)
  rule sw(st(_, _, C)) => mu(C)
  rule sw(_) => 0 [owise]
  rule kw(I:Instr) => iw(I)
  rule kw(P:Pgm) => pw(P)
  rule kw(seg(_, _, C)) => 2 +Int mu(C)
  rule kw(_) => 1 [owise]
  rule iw(new(_, { C })) => 2 +Int mu(C)
  rule iw(resume(_, _, _)) => 3
  rule pw(.Pgm) => 2
  rule pw(I & P) => iw(I) +Int 1 +Int pw(P)
  rule mu(.Stmts) => 0
  rule mu(add(_) ; C) => 1 +Int mu(C)
  rule mu(dbl ; C) => 1 +Int mu(C)
  rule mu(yield ; C) => 1 +Int mu(C)
  rule mu(loop(M, { B }) ; C) => 1 +Int maxInt(M, 0) *Int (mu(B) +Int 1) +Int mu(C)
  rule mu(app(A, B)) => mu(A) +Int mu(B) [simplification]
  rule mu(_C) >=Int 0 => true [simplification]
  rule pw(_P) >=Int 0 => true [simplification]
endmodule
