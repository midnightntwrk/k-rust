// Recursive functions whose termination needs a measure that Lean's own search does not find:
// the gate's test of the generator's measure synthesis (`crates/k2lean/src/termination.rs`,
// `docs/design.md`), generated in the arity-indexed term universe (library kterm-ar).

requires "domains.md"

module TERM-SYNTAX
  imports INT-SYNTAX
  imports BYTES-SYNTAX
  imports LIST
  imports MAP
  syntax Ints ::= ".Ints" | Int ";" Ints
  syntax Ty ::= ty(Int)
  syntax Pgm ::= run(Bytes, Ints, List, Int) | runN(Int) | runT(Map, Ty) | runL(List)
endmodule

module TERM
  imports TERM-SYNTAX
  imports INT
  imports BOOL
  imports BYTES
  imports LIST
  imports MAP
  configuration <T> <k> $PGM:Pgm </k> </T>

  // Two functions calling each other: `scan` stops at the end of the bytes, `scanAt` steps past
  // one item, whose width is at least 1. The measure is the distance to the end, then a rank of
  // the two functions; the step needs a lower bound of `width`.
  syntax Int ::= width(Int) [function, total, symbol(width)]
  rule width(W) => W -Int 90 requires W >=Int 92 andBool W <=Int 99
  rule width(_) => 1 [owise]
  syntax Int ::= scan(Bytes, Int, Int) [function, symbol(scan)]
               | scanAt(Bytes, Int, Int) [function, symbol(scanAt)]
  rule scan(B, I, N) => N requires I >=Int lengthBytes(B)
  rule scan(B, I, N) => scanAt(B, I, N) requires I <Int lengthBytes(B)
  rule scanAt(B, I, N) => scan(B, I +Int width(B[I]), N +Int 1)

  // Quicksort: each recursive call is on a filtered tail, so it needs "a filter returns at most
  // its input".
  syntax Ints ::= isort(Ints) [function, symbol(isort)]
                | below(Int, Ints) [function, symbol(below)]
                | atLeast(Int, Ints) [function, symbol(atLeast)]
                | cat(Ints, Ints) [function, symbol(cat)]
  rule below(_, .Ints) => .Ints
  rule below(P, X ; L) => X ; below(P, L) requires X <Int P
  rule below(P, X ; L) => below(P, L) requires X >=Int P
  rule atLeast(_, .Ints) => .Ints
  rule atLeast(P, X ; L) => X ; atLeast(P, L) requires X >=Int P
  rule atLeast(P, X ; L) => atLeast(P, L) requires X <Int P
  rule cat(.Ints, L) => L
  rule cat(X ; L, M) => X ; cat(L, M)
  rule isort(.Ints) => .Ints
  rule isort(P ; L) => cat(isort(below(P, L)), P ; isort(atLeast(P, L)))

  // A fold over a list that grows: a group is replaced by its first value and its members,
  // doubled. Neither the list's length nor its `sizeOf` decreases (doubling grows an integer);
  // the number of constructors and values in the list does.
  syntax KItem ::= grp(Int, List) [symbol(grp)]
  syntax List ::= twice(List) [function, symbol(twice)]
  rule twice(.List) => .List
  rule twice(ListItem(X:Int) L) => ListItem(X *Int 2) twice(L)
  syntax Int ::= total(List, Int) [function, symbol(total)]
  rule total(.List, A) => A
  rule total(ListItem(grp(N, M)) L, A) => total(ListItem(N) twice(M) L, A)
  rule total(ListItem(X:Int) L, A) => total(L, A +Int X)

  // A series: the counter counts up, and once it exceeds the multiplier's absolute value the
  // accumulator shrinks. The measure is the counter's distance to that bound, then the
  // accumulator.
  syntax Int ::= series(Int, Int, Int, Int) [function, symbol(series)]
  rule series(I, S, A, N) => series(I +Int 1, S +Int A, (A *Int N) /Int I, N) requires A >Int 0
  rule series(_, S, _, _) => S [owise]

  // A decoder of nested length-prefixed items: a header gives the item's kind, the length of its
  // payload and where the payload starts; a node's payload is a sequence of items. An item can
  // span the whole input, so the measure is the distance of a position to the end, then a rank
  // of the four functions, and it needs what `hdr` returns: the position is in range, the item
  // ends after it, and a node's payload starts after it.
  syntax Kind ::= "#leaf" | "#node"
  syntax Hdr ::= Kind "(" Int "," Int ")"
  syntax Hdr ::= hdr(Bytes, Int) [function, symbol(hdr)]
               | hdrOf(Bytes, Int, Int) [function, symbol(hdrOf)]
               | longHdr(Bytes, Int, Int) [function, symbol(longHdr)]
  syntax Int ::= word(Bytes) [function, total, symbol(word)]
  rule word(W) => Bytes2Int(W, BE, Unsigned) modInt 65536
  rule hdr(B, S) => hdrOf(B, S, B[S])
  rule hdrOf(_, S, X) => #leaf(1, S) requires X <Int 128
  rule hdrOf(_, S, X) => #leaf(X -Int 128, S +Int 1) requires X >=Int 128 andBool X <Int 192
  rule hdrOf(_, S, X) => #node(X -Int 192, S +Int 1) requires X >=Int 192 andBool X <Int 248
  rule hdrOf(B, S, X) => longHdr(B, S, X -Int 247) [owise]
  rule longHdr(B, S, N) => #node(word(substrBytes(B, S +Int 1, S +Int 1 +Int N)), S +Int 1 +Int N)

  syntax Tree ::= leaf(Bytes) | node(Trees)
  syntax Trees ::= ".Trees" | Tree "::" Trees
  syntax Tree ::= dec(Bytes) [function, symbol(dec)]
                | decHdr(Bytes, Hdr) [function, symbol(decHdr)]
  syntax Trees ::= decSeq(Bytes, Int) [function, symbol(decSeq)]
                 | decSeqHdr(Bytes, Int, Hdr) [function, symbol(decSeqHdr)]
  rule dec(B) => decHdr(B, hdr(B, 0))
  rule decHdr(B, #leaf(L, P)) => leaf(substrBytes(B, P, P +Int L))
  rule decHdr(B, #node(_, P)) => node(decSeq(B, P))
  rule decSeq(B, S) => decSeqHdr(B, S, hdr(B, S)) requires S <Int lengthBytes(B)
  rule decSeq(_, _) => .Trees [owise]
  rule decSeqHdr(B, S, _:Kind(L, P)) => dec(substrBytes(B, S, L +Int P)) :: decSeq(B, L +Int P)

  // Shifting right towards zero, after a sign flip: the distance of the negation, then of the
  // value, which `>>Int 1` makes smaller while it is positive (`IntHook.shr_facts`).
  syntax Int ::= popcount(Int) [function, total, symbol(popcount)]
  rule popcount(0) => 0
  rule popcount(N) => (N &Int 1) +Int popcount(N >>Int 1) requires N >Int 0
  rule popcount(N) => popcount(N *Int -1) requires N <Int 0

  // Two partial calls in one right-hand side: the definition matches on the value of the first call
  // and then of the second, and the equation binds both (cased on by `k2l_case_call`).
  syntax Int ::= popcounts(Int, Int) [function, total, symbol(popcounts)]
  rule popcounts(M, N) => popcount(M) +Int popcount(N)

  // List patterns of recursive functions, whose definitions take the list apart with `uncons` and
  // `unsnoc` and test it against `.List`, which the left-hand side's pattern decides
  // (`k2l_case_list`): a group of two functions, one over a list and one over its items, whose
  // equation of `ListItem(I) L` binds two partial calls; and a pattern with an element at each end.
  syntax KItem ::= grpOf(List) [symbol(grpOf)]
  syntax Bool ::= allPos(List) [function, symbol(allPos)]
                | itemPos(KItem) [function, symbol(itemPos)]
  rule allPos(.List) => true
  rule allPos(ListItem(I) L) => itemPos(I) andBool allPos(L)
  rule itemPos(grpOf(L)) => allPos(L)
  rule itemPos(I:Int) => I >Int 0
  syntax Int ::= ends(List) [function, symbol(ends)]
  rule ends(ListItem(X:Int) L ListItem(Y:Int)) => X +Int Y +Int ends(L)
  rule ends(ListItem(X:Int)) => X
  rule ends(.List) => 0
  // `owise` rules after list patterns: the left-hand side is a variable, and the statement has a
  // no-match premise per other rule; the definition takes the variable apart (`k2l_case_lvar`),
  // and each other rule's arm is refuted by its premise (`k2l_owise_arm`), once both sides'
  // concatenations are normalized: `ListItem(X) ListItem(Y) L` is written left-nested, the arm
  // builds it right-nested. Front, back and both ends, and a function that is not recursive with
  // a second argument in its pattern.
  syntax Int ::= sumPairs(List) [function, total, symbol(sumPairs)]
  rule sumPairs(ListItem(X:Int) ListItem(Y:Int) L) => X +Int Y +Int sumPairs(L)
  rule sumPairs(_) => 0 [owise]
  syntax Int ::= lastSum(List) [function, total, symbol(lastSum)]
  rule lastSum(L ListItem(X:Int)) => X +Int lastSum(L)
  rule lastSum(_) => 0 [owise]
  syntax Int ::= edgeSum(List) [function, total, symbol(edgeSum)]
  rule edgeSum(ListItem(X:Int) L ListItem(Y:Int)) => X +Int Y +Int edgeSum(L)
  rule edgeSum(ListItem(X:Int)) => X
  rule edgeSum(_) => 0 [owise]
  syntax Int ::= headOr(List, Int) [function, total, symbol(headOr)]
  rule headOr(ListItem(X:Int) _, _) => X
  rule headOr(_, D) => D [owise]

  // Types read from a table: an array's alignment is its element's, its size the element's size
  // times its length, and the element's description is read from the table. The table is an
  // arbitrary map, so on a table whose entry for a type mentions that type (`ty(0) |-> arr(ty(0),
  // 2)`) the rewriting does not terminate, and no measure exists: `align` (one function that
  // matches its argument) and `size`/`sizeTy` (a group) are least fixed points
  // (term-termination.toml), and term-diverges.lean proves they have no value on that table.
  syntax Info ::= prim(Int) | arr(Ty, Int) | ptr(Ty)
  syntax Info ::= info(Map, Ty) [function, total, symbol(info)]
  rule info(M, T) => {M[T] orDefault prim(0)}:>Info
  syntax Int ::= align(Map, Info) [function, total, symbol(align)]
  rule align(_, prim(N)) => N
  rule align(M, arr(T, _)) => align(M, info(M, T))
  rule align(_, ptr(_)) => 8
  syntax Int ::= size(Map, Info) [function, total, symbol(size)]
               | sizeTy(Map, Ty) [function, total, symbol(sizeTy)]
  rule size(_, prim(N)) => N
  rule size(M, arr(T, N)) => N *Int sizeTy(M, T)
  rule size(_, ptr(_)) => 8
  rule sizeTy(M, T) => size(M, info(M, T))

  rule <k> run(B, L, Xs, N) => scan(B, 0, 0) ~> isort(L) ~> total(Xs, 0) ~> series(1, 0, N, N) ~> dec(B) </k>
  rule <k> runN(N) => popcount(N) ~> popcounts(N, 0 -Int N) </k>
  rule <k> runT(M, T) => sizeTy(M, T) ~> align(M, info(M, T)) </k>
  rule <k> runL(L) => allPos(L) ~> ends(L) ~> sumPairs(L) ~> lastSum(L) ~> edgeSum(L) ~> headOr(L, 0) </k>
endmodule
