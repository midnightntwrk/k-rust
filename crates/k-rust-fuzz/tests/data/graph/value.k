// A hole value at the head of `<k>` (FZ-G8 fix round, review B1).
//
// The configuration variable `$N` is the whole `<k>` cell. `zero` applies only when `$N` is 0,
// and `pos` otherwise; both empty `<k>`. The program `run` only fills `<prog>`. With `$N`
// bound to 5 the configuration keys `<k>` as the value 5, which `zero`'s key does not cover;
// with `$N` a variable of sort `Int` (the hole template) it keys nothing, so `zero` is an entry
// rule.

module VALUE-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= "run"  [symbol(run)]
endmodule

module VALUE
  imports VALUE-SYNTAX
  imports INT
  imports BOOL

  configuration <k> $N:Int </k>
                <prog> $PGM:Pgm </prog>
                <out> 0 </out>

  rule [zero]: <k> 0 => .K </k> <out> _ => 1 </out>
  rule [pos]:  <k> N:Int => .K </k> <out> _ => 2 </out> requires N =/=Int 0
endmodule
