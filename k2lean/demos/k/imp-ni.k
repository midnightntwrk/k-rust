requires "imp.k"

// kimp with the fact about its store that noninterference's statement reads (k2lean
// `noninterference --good storeOk`, demos/ImpNI): every identifier the store <env> binds holds a
// Value. A store whose low identifier held an expression would leak: `l = x;` with `x |-> h` reads
// the high `h`. `k2lean gen --invariant storeOk@env` states it as a walk over the store's
// bindings (`Invariant.storeOk_walk`), which the generated store lemmas read, and proves that
// every rule keeps it. No rule is added: the library's `Step` is kimp's.
module IMP-NI
  imports IMP
  imports MAP
  imports BOOL

  syntax Bool ::= storeOk(Map) [function, total]
  rule storeOk(.Map) => true
  rule storeOk((K |-> V) E) => (notBool isId(K) orBool isValue(V)) andBool storeOk(E)
endmodule
