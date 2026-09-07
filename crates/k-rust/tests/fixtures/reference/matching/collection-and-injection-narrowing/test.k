module TEST2
  imports MAP
  imports SET
  imports LIST
  imports INT
  syntax Exp ::= Int | foo(Exp) [symbol(foo)] | bar(Int) [symbol(bar)]
  syntax Pgm ::= "goM" [symbol(goM)] | "goS" [symbol(goS)] | "goL" [symbol(goL)] | "goI" [symbol(goI)]
               | "doneM" [symbol(doneM)] | "doneS" [symbol(doneS)] | "doneL" [symbol(doneL)] | "doneI" [symbol(doneI)]
               | Exp
  configuration <k> $PGM:Pgm </k> <m> .Map </m> <s> .Set </s> <l> .List </l>
  rule <k> goM => doneM </k> <m> (_K |-> _V) REST => REST </m> [label(mapsel)]
  rule <k> goS => doneS </k> <s> SetItem(_X) REST => REST </s> [label(setsel)]
  rule <k> goL => doneL </k> <l> ListItem(1) => .List </l> [label(listclosed)]
  rule <k> foo(I:Int) => bar(I) </k> [label(injnarrow)]
endmodule
