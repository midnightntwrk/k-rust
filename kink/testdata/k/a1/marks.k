// Re-pin adoption A-1 (ADOPTION.md section 2.1): values the definition leaves open that show on
// k-rust's run-level `implementationChosenValues` list. Every rule here lists a map's keys, so
// decision 1's census flags the definition; the tests read the list beside it.
// - a(I): the diamond a -> b -> d, a -> c -> d (k-rust docs/compatibility.md, "Marks in
//   executions"): only `cd` lists two keys, and a state set absorbs one arrival at d.
// - v(I): `vk` lists two keys and its result is undefined (`10 /Int 0`); `vok` covers every
//   instance, so the candidate vanishes and its mark is on the list only.
// - e(nk2(I)) and e(nk1(I)): an initial state that applies a function whose equation lists two
//   keys, or one (a listing of one binding is determined: no mark).
module MARKS-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= a(Int) [symbol(a)]
                | b(Int) [symbol(b)]
                | c(Int) [symbol(c)]
                | v(Int) [symbol(v)]
                | e(Int) [symbol(e)]
                | val(Int) [symbol(val)]
                | "d" [symbol(d)]
                | "done" [symbol(done)]
  syntax Int ::= nk1(Int) [function, symbol(nk1)]
               | nk2(Int) [function, symbol(nk2)]
endmodule
module MARKS
  imports MARKS-SYNTAX
  imports INT
  imports MAP
  imports LIST
  configuration <k> $PGM:Prog </k>
  rule [ab]: <k> a(I) => b(I) </k>
  rule [ac]: <k> a(I) => c(I) </k>
  rule [bd]: <k> b(_) => d </k>
  rule [cd]: <k> c(I) => d </k> requires size(keys_list((0 |-> I) (1 |-> I))) >=Int 0
  rule [vk]: <k> v(I) => val(10 /Int (size(keys_list((0 |-> I) (1 |-> I))) -Int 2)) </k>
  rule [vok]: <k> v(_) => done </k>
  rule [nk1]: nk1(I) => size(keys_list(0 |-> I))
  rule [nk2]: nk2(I) => size(keys_list((0 |-> I) (1 |-> I)))
  rule [e]: <k> e(I) => val(I) </k>
endmodule
