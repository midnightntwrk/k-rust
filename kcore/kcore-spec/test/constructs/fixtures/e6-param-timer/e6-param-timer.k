// Each hooked function of TIMER (timer.md), read as a parameter symbol of the definition's own (a
// builtin file's sentence about names no library text declares, Parse.isOwnBuiltin; no registry
// hook), applied once in a rule's right side; fixture.toml params records `kcore sem-fields`'s
// parameter lines.
requires "timer.md"
module E6-PARAM-TIMER
  imports TIMER
  imports INT
  syntax KItem ::= go(Int) [symbol(go)]
  rule <k> go(1) => timerStart() ... </k>
  rule <k> go(2) => timerStop() ... </k>
endmodule
