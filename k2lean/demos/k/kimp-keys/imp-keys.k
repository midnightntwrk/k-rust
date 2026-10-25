requires "imp.k"

// A kind 1 invariant of kimp (k2lean/docs/invariants.md, §3): every key of the store <env> is
// an Id. `k2lean gen --invariant envKeysOk@env` states and proves that every rule keeps it.
module IMP-KEYS
  imports IMP
  imports MAP
  imports LIST
  imports BOOL

  syntax Bool ::= envKeysOk(Map) [function, total]
                | allIds(List) [function, total]
  rule envKeysOk(M) => allIds(keys_list(M))
  rule allIds(.List) => true
  rule allIds(ListItem(X) L) => isId(X) andBool allIds(L)
endmodule
