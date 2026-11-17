/-
  The registry family in the extension of a model of the theory without it
  (KcoreSpec/ConsRegistrySat.lean): the statements exist as stated and depend on no axiom but
  `propext`, `Classical.choice` and `Quot.sound`. Run from the package root:
  `lake env lean test/ConsRegistrySat.lean`.
-/
import KcoreSpec.ConsRegistrySat

open KCore KCore.Cons ML Faithful

example {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hm : Model.HypModelCore c) (hV : ValElems c D I)
    (hax : ∀ k ∈ builtinColls, D (.sort ("Sort" ++ c.sortName k.sort)) → collAxioms c k = [])
    (hnj : ∀ k ∈ builtinColls, k.sort < nRegSorts → D (.sort ("Sort" ++ c.sortName k.sort)) →
      extModel c D I ⊧ᴵ collNoJunk c k)
    {φ : KoreAML.P} (h : RegistryItem c D φ) : extModel c D I ⊧ᴵ φ :=
  sat_registry_of hm hV hax hnj h

example {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hm : Model.HypModelCore c) {s : Srt} {lit : Lit} (hv : c.sortOf (.dv s lit) = some s)
    (hs : DSort c D s) (e : Valuation (Ext M)) (x : Ext M) :
    (den c (.dv s lit)).interpret (extModel c D I) e x ↔ x = .inr (.val (.dv s lit)) :=
  ext_den_dvDet hm hv hs e x

#check @sat_registry_decided
#check @valElems_of_decided
#check @sat_registry_arity
#check @sat_registry_graph
#check @sat_registry_fallback
#check @sat_registry_value
#check @sat_registry_distinct

#print axioms sat_registry_of
#print axioms sat_registry_decided
#print axioms valElems_of_decided
#print axioms ext_den_dvDet
