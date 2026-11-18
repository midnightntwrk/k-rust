/-
  KCore. A semantics that satisfies `Hyp` and whose `Γ` has no model because two of its symbols
  have one name.

  `Γ` writes every symbol under its name (`Semantics.symName`). `Hyp` asks nothing of the names
  but that none is `ite` at a sort and that the functions' sorts are numbered: two constructors of
  one sort may have one name. Their distinctness axiom (Cons-Dist) is then `¬(a = a)`, which no
  inhabited model satisfies. Here the user sort `Foo` has two constructors, numbered apart, both
  named `Lbla`; the numbering is the one `idsOK` checks, and the duplicate name is what
  `Definition.namesOK` (not part of `Hyp`) rejects in the emitted text. The decidable facts are
  kernel decisions.
-/
import KcoreSpec.FaithfulSound

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace NamesWitness

open ML

def kIds : CellIds := { sort := nRegSorts, opt := some (nRegSorts + 1), label := nRegSyms + 3, no := some (nRegSyms + 4) }

/-- The configuration `<k> K </k>` with the generated counter, as ordinary sorts, constructors
and subsorts: the top cell's, its fragment's, the `k` cell's and the counter's. -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 3, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 4, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- The user sort `Foo`. -/
def foo : Srt := nRegSorts + 2

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt", "Foo"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisFoo", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lbla", "Lbla"]
    userSorts := cellSorts ++ [foo]
    ctors := cellCtors ++ [⟨nRegSyms + 5, [], foo⟩, ⟨nRegSyms + 6, [], foo⟩]
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem okAll : c.okAll = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem idsOK : c.idsOK = true := by decide +kernel
theorem names_plain : c.ctorSigs.all (fun k => (iteSort? (c.symName k.name)).isNone) = true := by decide +kernel
theorem names_fns : c.allFns.all (fun fn => (iteSort? (c.symName fn.label)).isNone &&
    (fn.result :: fn.args).all (· < nRegSorts + c.sortNames.length)) = true := by decide +kernel

theorem namesNumbered : NamesNumbered c := by
  refine ⟨fun k hk => ?_, fun o ho g hg => ?_, fun fn hfn s hs => ?_⟩
  · exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp names_plain k hk)
  · have h : c.ovls.all (fun o => o.over.all fun g => (iteSort? (c.symName g)).isNone) = true := by
      decide +kernel
    exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp (List.all_eq_true.mp h o ho) g hg)
  · have := List.all_eq_true.mp names_fns fn hfn
    simp only [Bool.and_eq_true] at this
    exact of_decide_eq_true (List.all_eq_true.mp this.2 s hs)

theorem hyp : Hyp c :=
  ⟨okAll, srReady, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, namesNumbered⟩

/-- The generator `Lbla` of `Foo`, as both constructors are written. -/
def ga : KoreAML.Gen := .ctor ⟨"Lbla", [], "Foo"⟩

/-- Cons-Dist of the two constructors: `¬(Lbla = Lbla)`. -/
def distAx : KoreAML.P := (KoreAML.Cons.distItem "Foo" ga ga).pat

theorem distAx_mem_any : (consItemsK c).any (fun it => decide (it.pat = distAx)) = true := by decide +kernel

theorem distAx_mem : distAx ∈ ΓCons c := by
  obtain ⟨it, hit, h⟩ := List.any_eq_true.mp distAx_mem_any
  exact Or.inl ⟨it, hit, of_decide_eq_true h⟩

/-- `¬(φ = φ)` holds of no element. -/
theorem not_equal_self {M : Type} (I : Interpretation KoreAML.Sym M) (e : Valuation M) (φ : KoreAML.P) (m : M) :
    ¬ (KoreAML.notEqual φ φ).interpret I e m := by
  unfold KoreAML.notEqual ML.equal ML.total
  simp

/-- **`Γ c` has no model**, though `c` satisfies `Hyp`. -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have h := hI distAx (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr distAx_mem)))))) ⟨fun _ => default, fun _ _ => False⟩ default
  exact not_equal_self I _ _ _ h

theorem not_hasModel : ¬ HasModel c := fun h => by
  obtain ⟨M, hM, I, hI⟩ := h hyp
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl hφ))

end NamesWitness

end Faithful

end KCore
