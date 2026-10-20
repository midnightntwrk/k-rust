// A coverage fact that rests on work no leaf carries (FZ-05 review 2, decision D18). `sib(A, B)`
// has two rules of one priority. `sib-chosen`'s right-hand side divides 10 by 0 or 1, chosen by
// the first key of `keys_list((A |-> 0) [ B <- 1 ])`, an order the definition leaves open
// (MAP.keys_list, class `order`); k-rust lists A first for `sib(1, 2)`, so the division is by 0
// and the right-hand side is undefined. Under strategy `all` and without `max_work` the
// candidate then vanishes beside `sib-ok`, which ends cleanly with 1: the run lists the
// implementation-chosen value, no leaf carries it, and coverage holds `sib-chosen`.
//
// The read is in the right-hand side on purpose: a `requires` that reads the chosen value
// decides which candidates apply, so the backend puts the mark on the surviving leaf, which is
// then not clean.

module SIBLING-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= sib(Int, Int)  [symbol(sib)]
endmodule

module SIBLING
  imports SIBLING-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports K-EQUAL

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [sib-chosen]: <k> sib(A, B) => .K ... </k>
                     <out> _ => 10 /Int (#if keys_list((A |-> 0) [ B <- 1 ]) [ 0 ] ==K A #then 0 #else 1 #fi) </out>
  rule [sib-ok]:     <k> sib(_, _) => .K ... </k> <out> _ => 1 </out>
endmodule
