// Re-pin adoption A-1 (ADOPTION.md section 2.3): work a run passes over that leaves no diagnostic
// but is on k-rust's run-level lists (k-rust tests/contradicted_claims.rs, `REFUSALS`).
// - run(N): `fpad` pads to N bytes; at 2^40 the memory allowance refuses that on every host, the
//   condition stays undecided, and `fpos` gives 2: the leaf `val(2)` carries no diagnostic and
//   `allowanceRefusals` holds the refusal.
// - runh(N): `hcount` reads `countAllOccurrences("a", "")`, a value the definition does not
//   determine, left unevaluated as an unsupported hook; the equation is passed over and `hpos`
//   gives 2: `unsupportedHooks` holds it.
module REFUSALS-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= run(Int) [symbol(run)]
                | runh(Int) [symbol(runh)]
                | val(Int) [symbol(val)]
  syntax Int ::= f(Int) [function, total, symbol(f)]
               | h(Int) [function, total, symbol(h)]
endmodule
module REFUSALS
  imports REFUSALS-SYNTAX
  imports INT
  imports BYTES
  imports STRING
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [fpad]: f(N) => 1 requires lengthBytes(padRightBytes(.Bytes, N, 0)) >Int 0
  rule [fpos]: f(N) => 2 requires N >Int 0
  rule [hcount]: h(N) => 1 requires countAllOccurrences("a", "") >Int N
  rule [hpos]: h(N) => 2 requires N >Int 0
  rule [run]: <k> run(N) => val(f(N)) </k>
  rule [runh]: <k> runh(N) => val(h(N)) </k>
endmodule
