/-
  KCore. A semantics with a sort that has no value below KItem and a function whose equations
  have no consistent result at an element of that sort: a regression test for `ΓSig` saying no
  sort is inhabited (`sigItems`).

  Its library puts IOError below KItem without K-IO's constructors, so IOError has no value: no
  literal is an IOError (`dvOK`), no constructor or subsort pair ends there, and it is no
  collection sort. `f : KItem → Bool` has two equations,
  `f(inj{IOError,KItem}(F)) = false requires f(inj{IOError,KItem}(F))` and the catch-all
  `f(X) = true [owise]`, of priority 200. At values the first never matches, so `f` is `true` at
  every KItem and `Hyp` holds. At `x₀ = inj{IOError,KItem}(j)`, for an element `j` of IOError, the first equation says
  `f(x₀) = true → f(x₀) = false` and the catch-all `f(x₀) ≠ true → f(x₀) = true`: no model has such
  a `j`. With G-nonempty every model had one; without it, IOError may be empty, as it is in the
  model whose sorts hold the values. The decidable facts are kernel decisions.
-/
import KcoreSpec.FaithfulSound

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace Faithful

namespace JunkWitness

open ML
open KoreAML (Inh)

def kIds : CellIds := { sort := nRegSorts, opt := some (nRegSorts + 1), label := nRegSyms + 2, no := some (nRegSyms + 3) }

/-- The configuration `<k> K </k>` with the generated counter, as ordinary sorts, constructors
and subsorts: the top cell's, its fragment's, the `k` cell's and the counter's. -/
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- The function `f`, numbered after the cell's symbols. -/
def fl : Sym := nRegSyms + 4

/-- `inj{IOError,KItem}(V0)`. -/
def pF : Term := .inj Srt.ioError Srt.kitem (.var 0)

/-- `f(inj{IOError,KItem}(F)) = false requires f(inj{IOError,KItem}(F))`. -/
def cl1 : Clause := { vars := [Srt.ioError], pats := [pF], req := some (.app fl [pF]), rhs := .dv Srt.bool (.bool false), ens := none }

/-- The catch-all `f(X) = true [owise]`. -/
def cl2 : Clause := { vars := [Srt.kitem], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool true), prio := 200, ens := none }

/-- `f : KItem → Bool`, with `cl1` and the catch-all. -/
def fn : Fn := { label := fl, args := [Srt.kitem], result := Srt.bool, clauses := [cl1, cl2] }

def c : Semantics :=
  { lib := { sortsBelowKItem := [Srt.bool, Srt.ioError] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblf"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [fn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem okAll : c.okAll = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem idsOK : c.idsOK = true := by decide +kernel
theorem namesNumbered : NamesNumbered c := namesNumbered_spec (by decide +kernel)

theorem ctors_not_err : c.ctorSigs.all (fun k => k.result != Srt.ioError) = true := by decide +kernel
theorem subs_not_err : c.subsorts.all (fun p => p.2 != Srt.ioError) = true := by decide +kernel
theorem coll_err : c.collOf Srt.ioError = none := by decide +kernel

/-- **No value has sort IOError**: no constructor and no subsort pair ends there, no literal is an
IOError (`dvOK`), and IOError is no collection sort. -/
theorem no_err (v : GroundTerm) : c.sortOf v ≠ some Srt.ioError := by
  cases v with
  | ctor f ts =>
    rw [Semantics.sortOf]
    cases hk : lookupSig c.ctorSigs f with
    | none => have : c.lookupOvl f = none := rfl
              have ho : c.lookupOpen f = none := c.lookupOpen_of_noRaw (by intro k hk; cases hk) f
              simp [this, ho]
    | some k =>
      simp only
      have hm := List.mem_of_find?_eq_some (by rw [← lookupSig_eq]; exact hk)
      have := List.all_eq_true.mp ctors_not_err k hm
      split <;> simp_all
  | inj a b t =>
    rw [Semantics.sortOf]
    split
    · rename_i h
      intro hb
      cases hb
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      have := List.all_eq_true.mp subs_not_err _ h.1.1
      simp at this
    · simp
  | dv s lit =>
    rw [Semantics.sortOf]
    split
    · rename_i h
      intro hs
      cases hs
      cases lit with
      | int _ => simp only [dvOK, beq_iff_eq] at h; exact absurd h (by decide)
      | bool _ => simp only [dvOK, beq_iff_eq] at h; exact absurd h (by decide)
      | float _ _ _ => simp only [dvOK, Bool.and_eq_true, beq_iff_eq] at h; exact absurd h.1 (by decide)
      | tok t =>
        simp only [dvOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ((h | h) | h) | ⟨h | h, -⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact absurd h (by decide +kernel)
        · exact absurd h (by decide)
        · exact absurd h (by decide +kernel)
    · simp
  | map s es =>
    intro h
    obtain ⟨_, _, _, _, _, _, hs⟩ := Semantics.sortOf_map_inv _ h
    subst hs
    rw [Semantics.sortOf, coll_err] at h
    cases h
  | set s es | list s es =>
    intro h
    have hs : s = Srt.ioError := by
      rw [Semantics.sortOf] at h
      split at h
      · split at h
        · first
            | exact Option.some.inj h
            | (split at h <;> first | exact Option.some.inj h | cases h)
        · cases h
      · cases h
    subst hs
    rw [Semantics.sortOf, coll_err] at h
    cases h

/-- `cl1` applies at no value: no substitution gives its variable an IOError value. -/
theorem cl1_noσ (σ : Subst) (h : c.WellSorted cl1.vars σ) : False := by
  obtain ⟨v, -, hv⟩ := h 0 Srt.ioError rfl
  exact no_err v hv

theorem lookup_f : c.lookupFn fl = some fn := rfl

/-- `f` is `true` at every KItem: `cl1` fails, so the catch-all decides. -/
theorem eval_f {vs : List GroundTerm} (hvs : c.sortsOf vs = some [Srt.kitem]) :
    Eval c fl vs (some (bool true)) := by
  cases vs with
  | nil => simp [Semantics.sortsOf] at hvs
  | cons w ws =>
  obtain ⟨s, ss, hw, h, he⟩ := sortsOf_cons.mp hvs
  cases he
  obtain rfl := sortsOf_nil_eq h
  refine .clause lookup_f (cl := cl2) (σ := [(0, w)]) (by simp [fn]) (fun i s hi => ?_)
    (.cons (.var ((by rw [List.lookup_cons, beq_self_eq_true]))) .nil) (fun t ht => nomatch ht) .top (fun cl hcl _ hlt => ?_) rfl .dv (fun t ht => nomatch ht) .top
  · cases i with
    | zero =>
      simp only [cl2, List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨w, (by rw [List.lookup_cons, beq_self_eq_true]), hw⟩
    | succ i => simp [cl2] at hi
  · simp only [fn, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl
    · exact .intro fun σ hσ _ => (cl1_noσ σ (Clause.wellSorted_of_at (by decide) hσ)).elim
    · simp at hlt

theorem hyp : Hyp c := by
  refine ⟨okAll, srReady, fun g hg vs hvs => ?_, fun g hg ht => ?_, fun g hg => ?_, fun g hg cl hcl => ?_, namesNumbered⟩
  · rw [List.mem_singleton.mp hg] at hvs ⊢; exact ⟨_, eval_f hvs⟩
  · rw [List.mem_singleton.mp hg] at ht; cases ht
  · rw [List.mem_singleton.mp hg]
    intro cl cl' hp hprio
    have h0 : pairs fn.clauses = [(cl1, cl2)] := rfl
    rw [h0, List.mem_singleton, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    simp [cl1, cl2] at hprio
  · rw [List.mem_singleton.mp hg] at hcl
    simp only [fn, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl
    · refine (matchIndependent_iff_noExs rfl).mpr ?_
      intro vs σ _ h _ _ _ _
      exact (cl1_noσ σ ((wellSortedAt_univ rfl).mp h.1)).elim
    · refine (matchIndependent_iff_noExs rfl).mpr ?_
      intro vs σ σ' _ _ _ _ _ _ _
      exact .inl ⟨rfl, rfl, rfl, rfl, fun i hi => (by simp [cl2, varOccs] at hi), fun t ht => (by simp [cl2] at ht)⟩

end JunkWitness

end Faithful

end KCore
