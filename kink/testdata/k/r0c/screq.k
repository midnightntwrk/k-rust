// Re-pin R0c-fix-1 deliverable 4 (R0c review 1 minor, decision 1): conditions that depend on the
// short-circuit reading. rq's condition is true when orBool skips 10 /Int 0 and undefined in
// k-rust's reading, so rq(0) is a Stuck leaf that names no rule; vg applies g, whose first
// equation's condition does the same, so g(0) is 2 in k-rust's reading and 1 in the other. No
// leaf shows either, so the definition is excluded.
module SCREQ-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Prog ::= rq(Int) [symbol(rq)] | vg(Int) [symbol(vg)] | res(Bool) [symbol(res)]
                | num(Int) [symbol(num)]
  syntax Int ::= g(Int) [function, symbol(g)]
endmodule
module SCREQ
  imports SCREQ-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule g(I) => 1 requires true orBool 10 /Int I >Int 0
  rule g(_) => 2 [owise]
  rule [rq]: <k> rq(I) => res(true) </k> requires true orBool 10 /Int I >Int 0
  rule [vg]: <k> vg(I) => num(g(I)) </k>
endmodule
