import KImp.Rules
import KPrelude.InvTactic
import KPrelude.InvColl

/-! Tests of the collection lemmas through `k2l_coll_close`, at kimp's `Map`, `Set` and `List`
carriers (the preservation proofs of the demonstrations use only the map `update` case). Each goal is a
shape a rule produces: an operation on a right-hand side, or a part of a matched pattern. -/

namespace CollTest

open KPrelude KImp MapHook

variable (Q : SortKItem × SortKItem → Prop) (P : SortKItem → Prop) (R : SortKItem → Prop)
  (m m' r : SortMap) (k v : SortKItem)

example (hm : EntriesOn Q m) (hq : Q (k, v)) : EntriesOn Q (update m k v) := by k2l_coll_close
example (hm : EntriesOn Q m) : EntriesOn Q (remove m k) := by k2l_coll_close
example (hm : EntriesOn Q m) (hc : concat (element k v) r = some m) : EntriesOn Q r := by
  k2l_coll_close
example (hm : EntriesOn Q m) (hc : concat (element k v) r = some m) : Q (k, v) :=
  entry_of_concat_element hc hm
example (hm : EntriesOn Q m) (hq : Q (k, v)) (m'' : SortMap) (hc : concat (element k v) m = some m'') :
    EntriesOn Q m'' := by k2l_coll_close
example (hm : EntriesOn Q m) (hm' : EntriesOn Q m') : EntriesOn Q (updateAll m m') := by
  k2l_coll_close
example (hm : KeysOn P m) (hk : P k) : KeysOn P (update m k v) := by k2l_coll_close
example (hm : ValuesOn R m) (hv : R v) : ValuesOn R (update (remove m k) k v) := by
  k2l_coll_close
example (hm : ValuesOn R m) (hv : R v) :
    ∀ p ∈ ListIso.toList (update m k v), R p.2 := by k2l_coll_close

variable (s t : SortSet) (l l' : SortList)

example (hs : SetHook.ElemsOn P s) (ht : SetHook.ElemsOn P t) : SetHook.ElemsOn P (SetHook.union s t) := by
  k2l_coll_close
example (hs : SetHook.ElemsOn P s) (hk : P k) (u : SortSet) (hc : SetHook.concat (SetHook.element k) s = some u) :
    SetHook.ElemsOn P u := by k2l_coll_close
example (hs : SetHook.ElemsOn P s) : SetHook.ElemsOn P (SetHook.difference s t) := by k2l_coll_close
example (hm : KeysOn P m) : SetHook.ElemsOn P (MapHook.keys m : SortSet) := by k2l_coll_close

example (hl : ListHook.ElemsOn P l) (hk : P k) : ListHook.ElemsOn P (ListHook.concat (ListHook.element k) l) := by
  k2l_coll_close
example (hl : ListHook.ElemsOn P l) (x : SortKItem) (h : ListHook.uncons l = some (x, l')) :
    ListHook.ElemsOn P l' := by k2l_coll_close
example (hl : ListHook.ElemsOn P l) (x : SortKItem) (h : ListHook.uncons l = some (x, l')) : P x :=
  ListHook.elem_of_uncons h hl
example (hl : ListHook.ElemsOn P l) (i : Int) (h : ListHook.update l i k = some l') (hk : P k) :
    ListHook.ElemsOn P l' := by k2l_coll_close
example (hm : ValuesOn R m) : ListHook.ElemsOn R (MapHook.values m : SortList) := by k2l_coll_close

end CollTest
