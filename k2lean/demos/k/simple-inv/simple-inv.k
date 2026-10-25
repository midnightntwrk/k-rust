// Kind 1 invariants of SIMPLE (k2lean/docs/invariants.md):
// - holdsOk@holds: every thread's lock counts are non-negative integers. `<holds>` maps each
//   lock a thread has acquired to the number of times it re-acquired it; the invariant says that
//   every value in every thread's `<holds>` is an `Int` that is at least 0. k2lean lifts
//   `holdsOk@holds` over SIMPLE's `<thread>` cell map: for every thread, `holdsOk` of its
//   `<holds>` is `true`.
// - storeOk@store and tStoreOk@T: every value of the store is a `Val` or `undefined` (the value
//   of a declared variable or array element before its first assignment), as a function of the
//   `<store>` cell's content and as a function of SIMPLE's top cell `<T>`, whose one equation
//   matches `<store>` among `<T>`'s cells.
requires "simple-untyped.md"

module SIMPLE-INV
  imports SIMPLE-UNTYPED
  syntax TCell

  syntax Bool ::= holdsOk(Map)    [function, total]
                | allCounts(List) [function, total]
                | isCount(KItem)  [function, total]

  rule holdsOk(H) => allCounts(values(H))

  rule allCounts(.List) => true
  rule allCounts(ListItem(V) L) => isCount(V) andBool allCounts(L)

  rule isCount(I:Int) => I >=Int 0
  rule isCount(_) => false [owise]

  syntax Bool ::= storeOk(Map)    [function, total]
                | tStoreOk(TCell) [function, total]
                | allVals(List)   [function, total]

  rule storeOk(S) => allVals(values(S))
  rule tStoreOk(<T> <store> S </store> ... </T>) => allVals(values(S))

  rule allVals(.List) => true
  rule allVals(ListItem(V) L) => (isVal(V) orBool V ==K undefined) andBool allVals(L)
endmodule
