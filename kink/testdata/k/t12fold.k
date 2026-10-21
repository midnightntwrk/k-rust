// TB-03 review 1 F1: kompile constant folding writes String values in U+0080..U+00FF as \xHH.
// One folded route per main module; T12FOLDCLEAN is fold-free (mutant-only insertion).
module T12FOLD-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  syntax Prog ::= start(Int) [symbol(start)] | pair(Int, Int) [symbol(pair)]
                | chk(String) [symbol(chk)] | done(Int) [symbol(done)]
endmodule
module T12FOLDCHR
  imports T12FOLD-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports STRING
  imports K-EQUAL
  configuration <k> .K </k>
  rule [start]: start(I) => chk(chrChar(I))
  rule [p]: chk(S) => done(7) requires S ==K chrChar(233)
  rule [o]: chk(_) => done(0) [owise]
endmodule
module T12FOLDCAT
  imports T12FOLD-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports STRING
  imports K-EQUAL
  configuration <k> .K </k>
  rule [start]: start(I) => chk(chrChar(I))
  rule [p]: chk(S) => done(7) requires S ==K "é" +String ""
  rule [o]: chk(_) => done(0) [owise]
endmodule
module T12FOLDPAIR
  imports T12FOLD-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports STRING
  imports K-EQUAL
  configuration <k> .K </k>
  rule [pair]: pair(I, J) => chk(chrChar(I) +String chrChar(J))
  rule [p]: chk(S) => done(7) requires S ==K chrChar(195) +String chrChar(169)
  rule [o]: chk(_) => done(0) [owise]
endmodule
module T12FOLDCLEAN
  imports T12FOLD-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports STRING
  imports K-EQUAL
  configuration <k> .K </k>
  rule [start]: start(I) => chk(chrChar(I))
  rule [p]: chk(S) => done(7) requires S ==K "é"
  rule [o]: chk(_) => done(0) [owise]
endmodule
