// FZ-CRASH-CAUSE (haltcause): halts whose structured cause tells a defect of a hook declaration
// or of k-rust from an option bound or a query the solver could not answer.
// - `arity(N)`: `add3` is hooked to `INT.add` at three arguments, which that builtin does not
//   take: the step's result does not simplify (a builtin failure, `wrong-arity`).
// - `loop(N)`: `f` and `g` rewrite into each other by simplification rules, so simplifying
//   `f(N)` ends only at `max-simplification-iterations`. Execution keeps the partial term and
//   marks the leaf (`simplification-budget-exhausted`, the fuzz reason `iteration-exhaustion`);
//   no execution of a K definition was found to halt on the bound itself (`iteration-limit`).
// - `smt(N)`: `odd` is smt-hooked to an operator SMT-LIB lacks, so the solver rejects the script
//   of the rule's condition over it: text the definition supplied (`malformed-script`, not blamed
//   on k-rust's translation).

module HC-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= arity(Int) | loop(Int) | smt(Int)
endmodule

module HC
  imports HC-SYNTAX
  imports INT
  imports BOOL
  syntax Int ::= add3(Int, Int, Int) [function, total, hook(INT.add)]
  syntax Int ::= f(Int) [function, total]
               | g(Int) [function, total]
  rule f(X) => g(X) [simplification]
  rule g(X) => f(X) [simplification]
  syntax Bool ::= odd(Int) [function, total, smt-hook(no-such-operator)]
  configuration <k> $PGM:Pgm </k> <s> 0 </s>
  rule <k> arity(N) => .K </k> <s> _ => add3(N, 1, 2) </s>
  rule <k> loop(N) => .K </k> <s> _ => f(N) </s>
  rule <k> smt(N) => .K </k> <s> _ => 1 </s> requires odd(N)
endmodule
