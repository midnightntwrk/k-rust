// Rules whose left side is headed by a helper compilation declares before it wraps cell-free
// rules in the computation cell (a sort predicate, a sort projection): function rules there,
// which compilation emits as equations and does not wrap.
module GENERATED-HEADS-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
endmodule

module GENERATED-HEADS
  imports GENERATED-HEADS-SYNTAX
  imports INT
  imports BOOL
  syntax Foo ::= foo(Int) [symbol(foo)]
  configuration <k> $PGM:Pgm </k>
  rule [go]: go(X) => foo(X)
  rule [pred]: isFoo(foo(1)) => true
  rule [proj]: project:Foo(foo(1)) => foo(2)
endmodule
