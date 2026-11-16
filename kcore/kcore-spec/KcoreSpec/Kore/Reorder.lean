/-
  `Reordered e k`: two KORE definitions equal up to the order of each module's sentences, and
  its check from a permutation hint (`Tie.reorder`, `Tie.permsOK`, `Tie.reordered_of_permsOK`,
  M2.5b). Kept from F0's Fragment and F1's Tie when they were removed (P1.4). F1's account of the
  hint follows.
  F1, checked layer: `Reordered e k` from a permutation hint (M2.5b).

  Deciding `Reordered d.emit k` directly (`decide +kernel`, as test/F1Check.lean does for peano)
  decides `List.Perm` on each module's sentences, comparing sentences pairwise: on an INT-prelude
  definition (flow-diamonds) that was 270M heartbeats and 10 GB. Here the untrusted driver supplies,
  for each module of k, the order `π` in which `e` lists k's sentences, and the kernel checks two
  things: `e = reorder k πs` (definitional equality of closed terms, one pass), and that each `π`
  is a permutation of `range n` (`permsOK`, by `List.isPerm`, structural). `reordered_of_permsOK` turns these into
  `Reordered`. A wrong hint only makes one of the two checks fail.

  This is the smallest F1 counterpart of F0Route: the parse stays one `kernel_rfl` and `wf` one
  `decide +kernel`. Under a 12 GiB cap per process it ties 34 of M2.5's 36 definitions; SYNTH(30)
  (the emit check) and SYNTH(100) (the parse) need F0Route's finer split
  (findings/M2.5-certificates.md, M2.5b).
-/
import KoreParser

set_option autoImplicit false

namespace KoreAML

/-- `Reordered e k`: the KORE definitions e and k are equal except for the order of the sentences
inside each module. They have the same attributes and the same modules in the same order; each
module keeps its name and attributes; its sentences are a permutation of the other's, counting
repetitions. The order carries no meaning: a module's sentences declare a set of sorts and symbols
and state a set of axioms, and a sentence may use a sort or symbol declared after it. That
reordering leaves the theory's models unchanged is `sameModels_of_reordered` (ReorderTheory.lean). -/
def Reordered (e k : Kore.Definition) : Prop :=
  e.attributes = k.attributes ∧ e.modules.length = k.modules.length ∧
  ∀ mm ∈ e.modules.zip k.modules,
    mm.1.name = mm.2.name ∧ mm.1.attributes = mm.2.attributes ∧ mm.1.sentences.Perm mm.2.sentences

instance (e k : Kore.Definition) : Decidable (Reordered e k) := by
  unfold Reordered; exact inferInstance

namespace Tie

/-- The elements of `l` at the indices `π`, in that order (out-of-range indices dropped). -/
def pick {α : Type} (l : List α) (π : List Nat) : List α := π.filterMap fun i => l[i]?

/-- k with each module's sentences taken in the order its `π` gives. -/
def reorder (k : Kore.Definition) (πs : List (List Nat)) : Kore.Definition :=
  { k with modules := (k.modules.zip πs).map fun (m, π) => { m with sentences := pick m.sentences π } }

/-- One order per module, each a permutation of the module's sentence indices. -/
def permsOK (k : Kore.Definition) (πs : List (List Nat)) : Bool :=
  πs.length == k.modules.length &&
    (k.modules.zip πs).all fun (m, π) => π.isPerm (List.range m.sentences.length)

theorem pick_range {α : Type} : ∀ (l : List α), pick l (List.range l.length) = l
  | [] => rfl
  | a :: t => by
    unfold pick
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map]
    simp only [List.getElem?_cons_zero, Function.comp_def, List.getElem?_cons_succ]
    have := pick_range t
    unfold pick at this
    rw [this]

theorem pick_perm {α : Type} {l : List α} {π : List Nat}
    (h : π.isPerm (List.range l.length) = true) : (pick l π).Perm l := by
  have hp : π.Perm (List.range l.length) := List.isPerm_iff.mp h
  have := hp.filterMap (fun i => l[i]?)
  have hr := pick_range l
  unfold pick at hr ⊢
  rw [hr] at this
  exact this

theorem reordered_of_permsOK {k : Kore.Definition} {πs : List (List Nat)}
    (h : permsOK k πs = true) : Reordered (reorder k πs) k := by
  unfold permsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  unfold Reordered reorder
  refine ⟨rfl, by simp [hlen], ?_⟩
  intro mm hmm
  simp only [List.zip_map_left, List.mem_map] at hmm
  obtain ⟨⟨⟨m, π⟩, m'⟩, hmem, rfl⟩ := hmm
  have hmm' : m' = m := by
    -- the pair comes from zipping `k.modules.zip πs` with `k.modules`: same index, same module
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hmem
    simp only [List.getElem_zip] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨h1, _⟩, h2⟩ := he
    rw [← h1, ← h2]
  subst hmm'
  have hz := (List.of_mem_zip hmem).1
  exact ⟨rfl, rfl, pick_perm (hall _ hz)⟩

end Tie

end KoreAML
