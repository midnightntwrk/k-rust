module E5-OVL-FUN-PARTIAL
  syntax N ::= "z" [symbol(z)] | "y" [symbol(y)]
  syntax Gas ::= N
  syntax Gas ::= cap(Gas) [symbol(capGas), overload(cap)]
  syntax N ::= cap(N)     [function, symbol(capN), overload(cap)]
  rule cap(z) => z
endmodule
