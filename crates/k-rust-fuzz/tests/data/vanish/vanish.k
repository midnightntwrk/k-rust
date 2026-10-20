// Baseline of the vanished-end fixture (FZ-08 review B1). `pick(A, B)` has two candidate rules
// of one priority. `split` divides 10 by 0 or 1, chosen by the first key of
// `keys_list((A |-> 0) [B <- 1])`, an order the definition leaves open (MAP.keys_list, class
// `order`). k-rust lists key A first for `pick(1, 2)`, so `split`'s right-hand side is undefined
// there and the candidate vanishes beside `plain`, which ends with 0. The run lists the
// implementation-chosen value, but without `max_work` no leaf carries it: in the model that lists
// B first, `split` ends with 10. So the baseline's leaves are not every end of every model.

module VANISH-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= pick(Int, Int)  [symbol(pick)]
endmodule

module VANISH
  imports VANISH-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports K-EQUAL

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [split]: <k> pick(A, B) => .K ... </k>
                <out> _ => 10 /Int (#if keys_list((A |-> 0) [ B <- 1 ]) [ 0 ] ==K A #then 0 #else 1 #fi) </out>
  rule [plain]: <k> pick(_, _) => .K ... </k> <out> _ => 0 </out>
endmodule
