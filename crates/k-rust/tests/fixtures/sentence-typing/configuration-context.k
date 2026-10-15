module TYPER-CFG
  imports DOMAINS
  configuration <k> $PGM:K </k> <n> 0 </n>
  syntax Int ::= cnt() [function]
  syntax KItem ::= go(Int)
  rule [withconfig]: [[ cnt() => N ]] <n> N </n>
  rule [cell-pred]: <k> go(X) => cnt() ... </k> <n> N => N +Int 1 </n> requires isInt(X)
endmodule
