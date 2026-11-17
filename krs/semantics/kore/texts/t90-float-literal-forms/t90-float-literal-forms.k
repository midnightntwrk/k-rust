module T90-FLOAT-LITERAL-FORMS
  imports FLOAT
  imports INT
  syntax Exp ::= go(Int) [symbol(go)] | l(Float) [symbol(l)]
  configuration <k> $PGM:Exp </k>
  // first alternative: digits, with and without fraction and exponent
  rule <k> go(1) => l(1.0) ... </k>
  rule <k> go(2) => l(1.) ... </k>
  rule <k> go(3) => l(1e3) ... </k>
  rule <k> go(4) => l(1.5e-3) ... </k>
  rule <k> go(5) => l(1.5E+3) ... </k>
  // first alternative: a sign before digits
  rule <k> go(6) => l(+1.5) ... </k>
  rule <k> go(7) => l(-1.5) ... </k>
  // second alternative: no digit before the point
  rule <k> go(8) => l(.5) ... </k>
  rule <k> go(9) => l(.5e2) ... </k>
  // the suffixes
  rule <k> go(10) => l(1.0f) ... </k>
  rule <k> go(11) => l(1.0F) ... </k>
  rule <k> go(12) => l(1.0d) ... </k>
  rule <k> go(13) => l(1.0D) ... </k>
  rule <k> go(14) => l(1.0p24x8) ... </k>
  rule <k> go(15) => l(1.0P24X8) ... </k>
  rule <k> go(16) => l(1.0p53x11) ... </k>
  rule <k> go(17) => l(.5f) ... </k>
  // Infinity, signed and suffixed
  rule <k> go(18) => l(Infinity) ... </k>
  rule <k> go(19) => l(+Infinity) ... </k>
  rule <k> go(20) => l(-Infinity) ... </k>
  rule <k> go(21) => l(Infinityf) ... </k>
  rule <k> go(22) => l(-InfinityD) ... </k>
  rule <k> go(23) => l(-Infinityp24x8) ... </k>
  // NaN, suffixed
  rule <k> go(24) => l(NaN) ... </k>
  rule <k> go(25) => l(NaNf) ... </k>
  rule <k> go(26) => l(NaNd) ... </k>
  rule <k> go(27) => l(NaNP24X8) ... </k>
endmodule
