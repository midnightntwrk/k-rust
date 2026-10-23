// A threaded language: the <k> cell lies under the multiplicity cell <thread>, as in SIMPLE or
// KOOL, so a configuration holds one <k> cell per live thread (ARCHITECTURE.md 5.2).
//
// - `go(N)` spawns a thread that adds N to <out>; the spawning thread then has nothing left.
// - `wait(N)` waits until <out> holds N: with no thread left to add, a wrong N deadlocks.
// - `C1 ; C2` runs C1 then C2 in the same thread.
// - A thread whose <k> is empty is removed (`reap`) while <reap> holds true; `noreap` turns
//   that off, so finished threads stay with an empty <k>.
// - `fail(N)` adds N for N =/= 0; `fail(0)` is an error, which removes its thread (`crash`) and
//   counts it in <errors>. Under the default normal end that run ends like a finished one; only
//   a pattern over <errors> tells them apart.

module THREADS-SYNTAX
  imports INT-SYNTAX

  syntax Cmd ::= go(Int)      [symbol(go)]
               | wait(Int)    [symbol(wait)]
               | fail(Int)    [symbol(fail)]
               | "noreap"     [symbol(noreap)]
               > Cmd ";" Cmd  [left, symbol(seq)]
  syntax Pgm ::= Cmd
endmodule

module THREADS
  imports THREADS-SYNTAX
  imports INT
  imports BOOL

  syntax KItem ::= add(Int)  [symbol(add)]

  configuration <threads>
                  <thread multiplicity="*" type="Map" initial="">
                    <id> 0 </id> <k> $PGM:Pgm </k>
                  </thread>
                </threads>
                <next> 1 </next>
                <out> 0 </out>
                <reap> true </reap>
                <errors> 0 </errors>

  rule [seq]:    <k> C1:Cmd ; C2:Cmd => C1 ~> C2 ... </k>
  rule [spawn]:  <thread>... <k> go(N) => .K ... </k> ...</thread>
                 (.Bag => <thread> <id> I </id> <k> add(N) </k> </thread>)
                 <next> I => I +Int 1 </next>
  rule [add]:    <k> add(N) => .K ... </k> <out> M => M +Int N </out>
  rule [wait]:   <k> wait(N) => .K ... </k> <out> N </out>
  rule [noreap]: <k> noreap => .K ... </k> <reap> _ => false </reap>
  rule [ok]:     <k> fail(N) => add(N) ... </k> requires N =/=Int 0
  rule [crash]:  (<thread>... <k> fail(0) ... </k> ...</thread> => .Bag) <errors> E => E +Int 1 </errors>
  rule [reap]:   (<thread>... <k> .K </k> ...</thread> => .Bag) <reap> true </reap>
endmodule
