// An overloaded constructor over a subsort (as the corpus's gas3): `cap` at Gas overloads `cap` at
// N, N < Gas, and Gas has a value outside N (`inf`). kompile declares `capGas` `anywhere` (not a
// constructor) and states `capGas(inj{N,Gas}(K)) = inj{N,Gas}(capN(K))`.
module OVLSUB-SYNTAX
  imports INT-SYNTAX
  syntax N ::= "z" [symbol(z)]
  syntax N ::= s(N) [symbol(s)]
  syntax Gas ::= N
  syntax Gas ::= "inf" [symbol(inf)]
  syntax Gas ::= cap(Gas) [symbol(capGas), overload(cap)]
  syntax N ::= cap(N) [symbol(capN), overload(cap)]
  syntax Pgm ::= run(Gas) [symbol(run)]
  syntax Pgm ::= wrap(Gas) [symbol(wrap)]
  syntax Pgm ::= done(Gas) [symbol(done)]
endmodule

module OVLSUB
  imports OVLSUB-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k>
  rule <k> run(cap(G:Gas)) => done(G) </k>
  rule <k> wrap(G:Gas) => done(cap(G)) </k>
endmodule
