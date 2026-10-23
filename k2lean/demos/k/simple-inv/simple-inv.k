// A kind 1 invariant of SIMPLE: every thread's lock counts are non-negative integers.
// `<holds>` maps each lock a thread has acquired to the number of times it re-acquired it; the
// invariant says that every value in every thread's `<holds>` is an `Int` that is at least 0.
// k2lean lifts `holdsOk@holds` over SIMPLE's `<thread>` cell map: for every thread, `holdsOk` of
// its `<holds>` is `true`.
requires "simple-untyped.md"

module SIMPLE-INV
  imports SIMPLE-UNTYPED

  syntax Bool ::= holdsOk(Map)    [function, total]
                | allCounts(List) [function, total]
                | isCount(KItem)  [function, total]

  rule holdsOk(H) => allCounts(values(H))

  rule allCounts(.List) => true
  rule allCounts(ListItem(V) L) => isCount(V) andBool allCounts(L)

  rule isCount(I:Int) => I >=Int 0
  rule isCount(_) => false [owise]
endmodule
