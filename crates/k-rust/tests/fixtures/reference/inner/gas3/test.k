module TEST
  syntax N ::= "zero" [symbol(zero)]
  syntax Gas ::= N
  syntax Gas ::= cap(Gas) [symbol(capGas), overload(cap)]
  syntax N ::= cap(N) [symbol(capN), overload(cap)]
  syntax Bool ::= Gas "<Gas" Gas [function, symbol(ltGas)]
  rule cap(GCAP) => zero requires GCAP <Gas zero
endmodule
