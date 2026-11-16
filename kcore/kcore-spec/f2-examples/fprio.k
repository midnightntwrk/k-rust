// The probe of function priorities (KcoreSpec/Evaluation.lean, `Eval.clause`): a clause applies
// where its patterns match and its `requires` is true, and decides where every clause of a smaller
// priority fails; `[owise]` is priority 200. `pr`'s clauses have priorities 40, 50 and 100: at 0
// all three match and `pr-low` decides (1), at 3 `pr-def` shadows `pr-mid` (2), at 9 only `pr-mid`
// applies (3). `ow`'s `[owise]` has a `requires`: at 5 `ow-pos` decides although the `[owise]`
// also applies (5), at -3 the `[owise]` does (3), at -200 nothing applies and `ow` is undefined.
// `op`'s `[owise]` is over a pattern, beside a clause of priority 30: `op(0, 0)` is 100, `op(0, 4)`
// is 4, `op(1, 4)` is 7 and `op(2, 4)` is undefined. `ag`'s two clauses of priority 50 overlap at 0,
// where both give 0.
module FPRIO-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= "t1" [symbol(t1)] | "t2" [symbol(t2)] | "t3" [symbol(t3)] | "t4" [symbol(t4)]
endmodule

module FPRIO
  imports FPRIO-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Cmd </k>

  syntax Int ::= pr(Int) [function, symbol(pr)]
  rule [pr-low]: pr(0) => 1 [priority(40)]
  rule [pr-def]: pr(N) => 2 requires N <=Int 5
  rule [pr-mid]: pr(_) => 3 [priority(100)]

  syntax Int ::= ow(Int) [function, symbol(ow)]
  rule [ow-pos]: ow(N) => N requires N >Int 0
  rule [ow-else]: ow(N) => 0 -Int N requires N >=Int -100 [owise]

  syntax Int ::= op(Int, Int) [function, symbol(op)]
  rule [op-zz]: op(0, 0) => 100 [priority(30)]
  rule [op-z]: op(0, N) => N
  rule [op-one]: op(1, _) => 7 [owise]

  syntax Int ::= ag(Int) [function, symbol(ag)]
  rule [ag-z]: ag(0) => 0
  rule [ag-sq]: ag(N) => N *Int N

  syntax KItem ::= res(Int) [symbol(res)]
  rule [t1]: <k> t1 => res(pr(0) +Int pr(3)) </k>
  rule [t2]: <k> t2 => res(ow(-3)) </k>
  rule [t3]: <k> t3 => res(op(1, 4) +Int ag(0)) </k>
  rule [t4]: <k> t4 => res(ow(-200)) </k>
endmodule
