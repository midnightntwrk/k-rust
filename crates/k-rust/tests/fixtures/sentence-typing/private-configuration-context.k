module PCFG
  imports DOMAINS
  syntax Exp ::= Int
  configuration <k> $PGM:K </k> <n> 0 </n> <e> 0:Exp </e>
endmodule
module PFUN
  imports private PCFG
  syntax Exp
  syntax Exp ::= cnt() [function]
  rule [r1]: [[ cnt() => N ]] <n> N </n>
  rule [r2]: [[ cnt() => E ]] <e> E </e> [owise]
endmodule
module PSUP
  imports DOMAINS
  syntax Sup ::= Int
endmodule
module P
  imports PFUN
  imports PCFG
  imports PSUP
  syntax Sup ::= Exp
  syntax Int ::= cnt2() [function]
  rule [r3]: [[ cnt2() => N ]] <n> N </n>
endmodule
