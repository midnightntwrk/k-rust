// The two-layer prototype of k2lean/docs/direction.md §8 step 4, in its parameterized form: the
// upper layer of the fixture twolayer (a transaction's coordination script, a DAG of tasks over
// processes and a ledger of outputs) with the lower layer, the coroutine language, left as a
// parameter. A resume is one step: the process's whole segment, from the resume to its next yield
// or the code's end, is the functions `segReg` and `segCode` of the register the segment starts
// with and the code left. They have no equations, so they are fields of the generated `class
// Hooks`: what is proved here holds for every semantics of the coroutine language's code, and a
// segment reads and writes nothing but the process it runs (a function reads only its arguments).
// The fixture corout is that language on its own; its runs to a segment's end are an instance
// (demos/TwoParamInst).
// Readiness, ids and races are twolayer's: `resume(Q, N, I)` steps only when Q has taken N
// segments and its input I exists (a literal, or the output `o(P, M)` of the M-th segment of P,
// which the resume spends); the M-th segment of P writes `o(P, M)`; two tasks naming one creation,
// one resume or one spend race, and the script's well-formedness `wf` excludes them.
requires "domains.md"

module TWOPARAM-SYNTAX
  imports INT-SYNTAX
  syntax Oid ::= "o" "(" Int "," Int ")"
  syntax Inp ::= Int | Oid
  // the coroutine language's code, shared with the lower layer; its semantics is the parameter
  syntax Stmt ::= "add" "(" Int ")"
                | "dbl"
                | "loop" "(" Int "," Code ")"
                | "yield"
  syntax Stmts ::= List{Stmt, ";"}
  syntax Code ::= "{" Stmts "}"
  // the coordination script
  syntax Instr ::= "new" "(" Int "," Code ")"
                 | "resume" "(" Int "," Int "," Inp ")"
  syntax Pgm ::= List{Instr, "&"}
endmodule

module TWOPARAM
  imports TWOPARAM-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports BOOL
  imports K-EQUAL

  syntax KItem ::= st(Int, Int, Stmts)  // a suspended process: segments taken, register, code left
  // the lower layer: a segment from a register and code, its register and code left at the next
  // yield or the code's end
  syntax Int ::= segReg(Int, Stmts) [function]
  syntax Stmts ::= segCode(Int, Stmts) [function]

  configuration <T>
      <tasks> <task multiplicity="*" type="Map" initial="">
        <tid> 0 </tid> <n> 0 </n> <k> $PGM:Pgm </k>
      </task> </tasks>
      <procs> .Map </procs>
      <vals> .Map </vals>
    </T>

  rule <tasks> <task> <tid> 0 </tid> <n> N => N +Int 1 </n> <k> I:Instr & P:Pgm => P </k> </task>
         (.Bag => <task> <tid> N +Int 1 </tid> <n> 0 </n> <k> I </k> </task>) ... </tasks> [label(fork)]
  rule <k> .Pgm => .K </k> [label(nil)]
  rule <k> new(Q, { C }) => .K </k> <procs> ... .Map => Q |-> st(0, 0, C) ... </procs> [label(new)]
  rule <k> resume(Q, N, V:Int) => .K </k>
       <procs> ... Q |-> (st(N, R, C) => st(N +Int 1, segReg(R +Int V, C), segCode(R +Int V, C))) ... </procs>
       <vals> ... .Map => o(Q, N) |-> segReg(R +Int V, C) ... </vals> [label(resume-lit)]
  // A resume with an output spends it and writes its own in one step: the step changes <vals> at
  // two keys. A segment never spends its own output (`o(Q, N)` exists only once this resume has
  // run), and the requirement says so: it tells the two keys apart for confluence's commutation.
  rule <k> resume(Q, N, I:Oid) => .K </k>
       <procs> ... Q |-> (st(N, R, C) => st(N +Int 1, segReg(R +Int V, C), segCode(R +Int V, C))) ... </procs>
       <vals> ... (I |-> V:Int => .Map) (.Map => o(Q, N) |-> segReg(R +Int V, C)) ... </vals>
    requires I =/=K o(Q, N) [label(resume-oid)]
  rule <tasks> (<task> <tid> _ </tid> <k> .K </k> ... </task> => .Bag) ... </tasks> [label(done)]

  // The script's well-formedness, `wf` (`gen --invariant wf@T`): twolayer's, with no running
  // segment to claim. `new(Q, _)` claims the creation of Q (`Q`), `resume(Q, N, I)` the N-th resume
  // of Q (`o(Q, N)`) and, for an output I, its spend (`sp(I)`); no claim is named twice.
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
  rule kclaims(_) => .List [owise]
  rule mclaims(<tasks> .Bag </tasks>) => .List
  rule mclaims(<tasks> <task> <tid> _ </tid> <n> _ </n> <k> K </k> </task> Ts </tasks>)
    => kclaims(K) mclaims(<tasks> Ts </tasks>)
  rule noDup(.List) => true
  rule noDup(ListItem(X) L) => notBool (X in L) andBool noDup(L)
  rule wf(<T> TS:TasksCell <procs> _ </procs> <vals> _ </vals> </T>) => noDup(mclaims(TS))
endmodule
