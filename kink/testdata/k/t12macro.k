// TB-03M (TB-03 review 2): kompile emits macro and alias rules to macros_kore as bare
// sentences, outside definition_kore. T12MACRO and T12ALIAS are clean; T12MACROFLOAT holds a
// Float literal only in an unused macro body; T12MACROFOLD folds chrChar(233) in a macro body
// (review 2 probe R2MACRO).
module T12MACRO-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  syntax Prog ::= start(Int) [symbol(start)] | chk(Int) [symbol(chk)]
                | chks(String) [symbol(chks)] | done(Int) [symbol(done)]
endmodule
module T12MACRO-COMMON
  imports T12MACRO-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> .K </k>
endmodule
module T12ALIAS
  imports T12MACRO-COMMON
  syntax Int ::= seven() [alias]
  rule seven() => 7
  rule [start]: start(I) => chk(I)
  rule [p]: chk(I) => done(7) requires I ==Int seven()
  rule [o]: chk(_) => done(0) [owise]
endmodule
module T12MACROFLOAT
  imports T12MACRO-COMMON
  imports FLOAT
  syntax Float ::= half() [macro]
  rule half() => 0.5
  rule [start]: start(I) => chk(I)
  rule [p]: chk(I) => done(7) requires I ==Int 7
  rule [o]: chk(_) => done(0) [owise]
endmodule
module T12MACROFOLD
  imports T12MACRO-COMMON
  imports STRING
  syntax String ::= eacute() [macro]
  rule eacute() => chrChar(233)
  rule [start]: start(I) => chks(chrChar(I))
  rule [p]: chks(S) => done(7) requires S ==K eacute()
  rule [o]: chks(_) => done(0) [owise]
endmodule
module T12MACRO
  imports T12MACRO-COMMON
  syntax Int ::= seven() [macro]
  rule seven() => 7
  rule [start]: start(I) => chk(I)
  rule [p]: chk(I) => done(7) requires I ==Int seven()
  rule [o]: chk(_) => done(0) [owise]
endmodule
