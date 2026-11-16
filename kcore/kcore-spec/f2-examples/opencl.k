// The vocabulary of the clauses of test/OpenClauses.lean, which the reader does not read yet (a
// variable of the `requires` the arguments do not bind): Int, and a sort S that the text leaves
// unconfined (its generator `c(Empty)` takes a sort without a value) with a total predicate isC.
// `f()` and `g(Int)` are functions whose open clauses the test writes by hand, from
// f2-examples/openh.k (`f() => 0 requires 1 ==Int 2 *Int H`) and f2-examples/clgenless.k
// (`f(_) => 1 requires isC(H:S)`, here `g`, beside the `[owise]` clause kept below).
module OPENCL
  imports INT
  imports BOOL
  syntax Empty
  syntax S ::= "a" [symbol(a)] | c(Empty) [symbol(c)]
  syntax Bool ::= isC(S) [function, total, symbol(isC)]
  rule isC(c(_)) => true
  rule isC(_) => false [owise]
  syntax Int ::= f() [function, symbol(f)]
  syntax Int ::= g(Int) [function, symbol(g)]
  rule g(_) => 0 [owise]
  syntax KItem ::= "go" [symbol(go)]
  rule <k> go => g(f()) </k>
endmodule
