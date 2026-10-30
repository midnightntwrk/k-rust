// kink27 R3-CENSUS-RUNLEVEL: one rule per class k-rust marks; the census reads none of them.
// Each probe's run lists the value it reads on `implementationChosenValues`, and each control
// reads a determined value (one binding, one format, no NaN, no signed zero pair, no letter digit).
// `lit` applies `Base2String` to a literal (the constant-fold route), `cond` in a condition,
// `eqn` through the equation `hex` and `req` in the condition of the equation `isff` (whose `owise`
// equation is selected when that condition is false); `rd` applies `#read`, which a request
// without a console leaves unevaluated.
module CLASSES-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  syntax Prog ::= keys(Int) [symbol(keys)] | keysOne(Int) [symbol(keysOne)] | s2l(Int) [symbol(s2l)]
                | choiceMap(Int) [symbol(choiceMap)] | choiceSet(Int) [symbol(choiceSet)] | choiceOne(Int) [symbol(choiceOne)]
                | mixed(Int) [symbol(mixed)] | same(Int) [symbol(same)] | nan(Int) [symbol(nan)] | mz(Int) [symbol(mz)]
                | b2s(Int) [symbol(b2s)] | lit(Int) [symbol(lit)] | cond(Int) [symbol(cond)] | eqn(Int) [symbol(eqn)]
                | vals(Int) [symbol(vals)] | mdiv(Int) [symbol(mdiv)] | mx(Int) [symbol(mx)] | req(Int) [symbol(req)]
                | rd(Int) [symbol(rd)] | done(KItem) [symbol(done)] | "yes" [symbol(yes)] | "no" [symbol(no)]
endmodule
module CLASSES
  imports CLASSES-SYNTAX
  imports INT
  imports FLOAT
  imports STRING
  imports MAP
  imports SET
  imports LIST
  imports COLLECTIONS
  imports K-IO
  configuration <k> $PGM:Prog </k>
  syntax String ::= hex(Int) [function, total, symbol(hex)]
  rule [hex]: hex(I) => Base2String(I, 16)
  syntax Int ::= isff(Int) [function, total, symbol(isff)]
  rule [isff]: isff(I) => 1 requires Base2String(I, 16) ==String "ff"
  rule [isffow]: isff(_) => 0 [owise]
  rule [keys]: <k> keys(N) => done(keys_list((N |-> 0) (N +Int 1 |-> 0))) </k>
  rule [keysOne]: <k> keysOne(N) => done(keys_list(N |-> 0)) </k>
  rule [vals]: <k> vals(N) => done(values((N |-> 0) (N +Int 1 |-> 1))) </k>
  rule [s2l]: <k> s2l(N) => done(Set2List(SetItem(N) SetItem(N +Int 1))) </k>
  rule [choiceMap]: <k> choiceMap(N) => done(choice((N |-> 0) (N +Int 1 |-> 0))) </k>
  rule [choiceSet]: <k> choiceSet(N) => done(choice(SetItem(N) SetItem(N +Int 1))) </k>
  rule [choiceOne]: <k> choiceOne(N) => done(choice(N |-> 0)) </k>
  rule [mixed]: <k> mixed(N) => done(Int2Float(N, 24, 8) +Float Int2Float(N, 53, 11)) </k>
  rule [mdiv]: <k> mdiv(N) => done(Int2Float(N, 24, 8) /Float Int2Float(N, 53, 11)) </k>
  rule [same]: <k> same(N) => done(Int2Float(N, 53, 11) +Float Int2Float(N, 53, 11)) </k>
  rule [nan]: <k> nan(N) => done(signFloat(Int2Float(N, 53, 11) /Float Int2Float(N, 53, 11))) </k>
  rule [mz]: <k> mz(N) => done(minFloat(Int2Float(N, 53, 11), --Float Int2Float(N, 53, 11))) </k>
  rule [mx]: <k> mx(N) => done(maxFloat(Int2Float(N, 53, 11), --Float Int2Float(N, 53, 11))) </k>
  rule [b2s]: <k> b2s(N) => done(Base2String(N, 16)) </k>
  rule [lit]: <k> lit(_) => done(Base2String(255, 16)) </k>
  rule [cond]: <k> cond(N) => yes </k> requires Base2String(N, 16) ==String "ff"
  rule [condo]: <k> cond(_) => no </k> [owise]
  rule [eqn]: <k> eqn(N) => done(hex(N)) </k>
  rule [req]: <k> req(N) => done(isff(N)) </k>
  rule [rd]: <k> rd(N) => done(#read(0, N)) </k>
endmodule
