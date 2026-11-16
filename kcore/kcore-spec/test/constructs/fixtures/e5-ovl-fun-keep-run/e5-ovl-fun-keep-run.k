module E5-OVL-FUN-KEEP-RUN
  syntax N ::= "z" [symbol(z)]
  syntax Gas ::= N | "inf" [symbol(inf)]
  syntax Gas ::= cap(Gas) [symbol(capGas), overload(cap)]
  syntax Gas ::= cap(N)   [function, total, symbol(capN), overload(cap)]
  syntax Pgm ::= run(Gas) [symbol(run)] | done(Gas) [symbol(done)]
  configuration <k> $PGM:Pgm </k>
  rule cap(z) => inf
  rule <k> run(cap(G:Gas)) => done(G) </k>
endmodule
