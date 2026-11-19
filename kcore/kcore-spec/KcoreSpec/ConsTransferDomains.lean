/-
  The extension of a model of the theory without the detached names (`extModel`,
  ConsExtModel.lean) satisfies the premises of the domains (`sat_own_domains`), of the
  interpretation's values at silent points (`sat_own_fallback`) and the closure axiom of Bool
  (`sat_own_cl`) that name nothing of `D`, for names `D` that are sort constants and symbols of the
  definition.

  Each of these premises is built from the patterns of ground KORE terms, which are of the class
  `OwnSorted` (ConsTransfer.lean) at no name (`ownEx_kground_rs`), with equality, a sorted
  quantifier, negation, conjunction, disjunction and inclusion, or is a collection's no-junk item
  (`ownSorted_collNoJunk`); so `transfer` carries each of them (`transfer0_sg`).
-/
import KcoreSpec.ConsTransferCons

set_option autoImplicit false

namespace KCore.Cons

open ML Faithful
open KoreAML (DefOK Inh IsSort)

local notation "Own0" => OwnSorted (fun _ => False)

section
variable {V : List EVar} {W : List SVar}

/-- The pattern of a value is of the class at no name. -/
theorem own_den_dm (c : Semantics) (v : GroundTerm) : Own0 V W .ex (den c v) :=
  ownEx_kground_rs (kore_ground c v) fun _ _ h => h

theorem kground_symApp_dm (c : Semantics) (f : Sym) (vs : List GroundTerm) :
    KoreAML.KGround (symApp c f (GroundTerm.koreList c vs)) := by
  obtain ⟨h, xs, -, hw⟩ := symApp_head c f
  rw [hw]
  exact .app (fun s hs => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hs; exact ⟨_, rfl⟩) (koreList_ground c vs)

/-- A symbol applied to values is of the class at no name. -/
theorem own_symApp_dm (c : Semantics) (f : Sym) (vs : List GroundTerm) :
    Own0 V W .ex (KoreAML.den (symApp c f (GroundTerm.koreList c vs))) :=
  ownEx_kground_rs (kground_symApp_dm c f vs) fun _ _ h => h

/-- The graph of a symbol at values: its application is the pattern of the value, or nothing. -/
theorem own_graph_dm (c : Semantics) (f : Sym) (vs : List GroundTerm) (r : Option GroundTerm) :
    Own0 V W .pred (KoreAML.den (symApp c f (GroundTerm.koreList c vs)) ≡ (match r with
      | some v => den c v
      | none => ⊥)) := by
  cases r with
  | some v => exact .equal_ex (own_symApp_dm c f vs) (own_den_dm c v)
  | none => exact .equal_ex (own_symApp_dm c f vs) .bot

end

section
variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : ∀ σ, D σ → plainSym σ)
include hD

/-- **The extension satisfies every premise of `ΓDomains` that names nothing of `D`**, for a model
of `Γown c D` and names `D` that are sort constants and symbols of the definition. -/
theorem sat_own_domains (hI : I ⊧ᴵP Γown c D) {φ : KoreAML.P} (hφ : ΓDomains c φ)
    (hn : ∀ σ ∈ psyms φ, ¬ D σ) : extModel c D I ⊧ᴵ φ := by
  have hDI := defOK_own_sg hD hI
  have hI' : I ⊧ᴵ φ := hI _ ⟨.inl (.inl (.inl (.inl (.inl (.inl (.inr hφ)))))), hn⟩
  rcases hφ with ⟨k, vs, r, -, -, -, -, rfl⟩ | ⟨k, vs, -, -, rfl⟩ | ⟨v, s, -, rfl⟩ |
    ⟨v, w, s, -, -, -, -, rfl⟩ | ⟨k, -, rfl⟩
  · exact transfer0_sg hD hDI (own_graph_dm c k.name vs r) (.inl rfl) hn hI'
  · exact transfer0_sg hD hDI (own_graph_dm c k.sig.name vs _) (.inl rfl) hn hI'
  · exact transfer0_sg hD hDI (.sEx (V' := []) (.sortC id) nil_sub (.inr (.inl rfl))
      (.equal_ex (own_den_dm c v) (.evar (List.mem_cons_self ..)))) (.inl rfl) hn hI'
  · exact transfer0_sg hD hDI (.neg_ex (.conj_ex_old (own_den_dm c v) (own_den_dm c w).toOld)) (.inr rfl) hn hI'
  · exact transfer0_sg hD hDI (ownSorted_collNoJunk c k id id id id id id) (.inl rfl) hn hI'

/-- **The extension satisfies every premise of `ΓFallback` that names nothing of `D`.** -/
theorem sat_own_fallback (hI : I ⊧ᴵP Γown c D) {φ : KoreAML.P} (hφ : ΓFallback c φ)
    (hn : ∀ σ ∈ psyms φ, ¬ D σ) : extModel c D I ⊧ᴵ φ := by
  have hDI := defOK_own_sg hD hI
  have hI' : I ⊧ᴵ φ := hI _ ⟨.inl (.inl (.inr hφ)), hn⟩
  rcases hφ with ⟨k, vs, -, -, -, -, rfl⟩ | ⟨fn, vs, -, -, -, rfl⟩
  · exact transfer0_sg hD hDI (own_graph_dm c k.name vs _) (.inl rfl) hn hI'
  · exact transfer0_sg hD hDI (own_graph_dm c fn.label vs _) (.inl rfl) hn hI'

/-- **The extension satisfies the closure axiom of Bool where it names nothing of `D`.** -/
theorem sat_own_cl (hI : I ⊧ᴵP Γown c D) {φ : KoreAML.P} (hφ : Γcl c φ)
    (hn : ∀ σ ∈ psyms φ, ¬ D σ) : extModel c D I ⊧ᴵ φ := by
  have hDI := defOK_own_sg hD hI
  have hI' : I ⊧ᴵ φ := hI _ ⟨.inl (.inr hφ), hn⟩
  obtain ⟨-, -, rfl⟩ := hφ
  exact transfer0_sg hD hDI (.included (.inhOf (.sortC id))
    (.toOld (.disj_ex (own_den_dm c _) (own_den_dm c _)))) (.inl rfl) hn hI'

end

end KCore.Cons
