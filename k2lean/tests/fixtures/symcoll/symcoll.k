// The simplifications of `MAP-KORE-SYMBOLIC` and `SET-KORE-SYMBOLIC` (domains.md), stated with the
// well-formedness premise on every variable of a Set or Map sort and proved from the collection
// laws (k2lean/lean/prelude/KPrelude/HookLaws.lean; k2lean/docs/design.md, section 3).
module SYMCOLL-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "go" "(" Int ")"
endmodule

module SYMCOLL
  imports SYMCOLL-SYNTAX
  imports INT
  imports BOOL
  imports MAP-SYMBOLIC
  imports SET-SYMBOLIC
  configuration <k> $PGM:Pgm </k> <m> .Map </m> <s> .Set </s>
  rule <k> go(I) => .K ... </k> <m> M => M[I <- I] </m> <s> S => S SetItem(I) </s>
    requires notBool (I in_keys(M))
endmodule
