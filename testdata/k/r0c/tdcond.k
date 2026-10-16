// Re-pin R0c-fix-2: the R0c-fix-1 review's probe review-probe/tdcond.k, kept as written.
module TDCOND-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= chk(Int) [symbol(chk)] | cho(Int) [symbol(cho)] | kv(Int) [symbol(kv)]
                | sb(Int) [symbol(sb)] | pr(Int) [symbol(pr)] | iv(Int) [symbol(iv)]
                | yes() [symbol(yes)] | no() [symbol(no)] | val(Int) [symbol(val)]
  syntax Int ::= td(Int) [function, total, symbol(td)] | k(Int) [function, symbol(k)]
endmodule
module TDCOND
  imports TDCOND-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [tdeq]: td(I) => 10 /Int (I +Int 0)
  rule [chk]: <k> chk(I) => yes() </k> requires td(I) >Int 0
  rule [cho]: <k> cho(I) => yes() </k> requires td(I) >Int 0
  rule [chono]: <k> cho(_) => no() </k> [owise]
  rule k(I) => 1 requires td(I) >Int 0
  rule k(_) => 2 [owise]
  rule [kv]: <k> kv(I) => val(k(I)) </k>
  rule [sba]: <k> sb(I) => val(td(I)) </k>
  rule [sbb]: <k> sb(_) => no() </k>
  rule [prhi]: <k> pr(I) => val(td(I)) </k> [priority(10)]
  rule [prlo]: <k> pr(_) => no() </k> [priority(20)]
  rule [iv]: <k> iv(I) => val(I) </k>
endmodule
