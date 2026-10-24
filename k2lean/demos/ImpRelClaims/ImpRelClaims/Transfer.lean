import ImpRel.Bisim
import KImpClaims.ImpSimpleSpec
import KClaims.Bisim

/-! Hand-written. A K claim proved once on kimp holds for the KRS IMP port.

`sum-N` of kimp's `imp-simple-spec.k` (`$s = 0; $n = N; while (0 < $n) { … }` ends with `$s` holding
`N(N+1)/2`, for every `N ≥ 0`) is proved on kimp by the generated claims (`KImpClaims`: the
claims tactic with `sum-loop` as a lemma, the loop's own claim proved by circularity). The
bisimulation `ImpRel.bisim` that `k2lean relate` generates between `KImp.Step` and `KrsImp.Step`
carries it to the port with `KClaims.AF.of_bisim`: the port's configuration below is the
translation of kimp's (`rfl`), it satisfies the bisimulation's invariant (an empty store), and
every kimp configuration in the claim's target translates to one in the port's target. No step of
the port is explored.

The continuation `K` is a translated kimp continuation: the port has constructs kimp lacks
(`staticExprDouble`), so a port continuation need not be a translation, and `bisim` relates only
translations. -/

namespace ImpRelClaims

open KPrelude KClaims ImpRel

/-- The port's `sum-N` program, written with the port's own constructors. -/
def sumN (K : KrsImp.SortK) (N G : Int) : KrsImp.SortGeneratedTopCell :=
  .«<generatedTop>»
    (.«<k>» (.kseq (.inj_Stmt
      (.stmtSyntaxSequence (.stmtSyntaxAssign (.mk "$s") (.inj_Int 0))
        (.stmtSyntaxSequence (.stmtSyntaxAssign (.mk "$n") (.inj_Int N))
          (.stmtSyntaxWhile (.inj_Expr (.opLt (.inj_Int 0) (.inj_Id (.mk "$n"))))
            (.stmtSyntaxBlock
              (.stmtSyntaxSequence
                (.stmtSyntaxAssign (.mk "$s") (.inj_Expr (.opAdd (.inj_Id (.mk "$s")) (.inj_Id (.mk "$n")))))
                (.stmtSyntaxAssign (.mk "$n") (.inj_Expr (.opSub (.inj_Id (.mk "$n")) (.inj_Int 1)))))))))) K))
    (.«<env>» MapHook.unit) (.«<generatedCounter>» G)

/-- The port's target: the program is consumed, `$s` holds `N(N+1)/2` and `$n` holds `0`. -/
def sumNPost (K : KrsImp.SortK) (N : Int) (d : KrsImp.SortGeneratedTopCell) : Prop :=
  ∃ (G' : Int) (r : Int) (m : KrsImp.SortMap),
    d = .«<generatedTop>» (.«<k>» K) (.«<env>» m) (.«<generatedCounter>» G') ∧
    IntHook.tdiv (IntHook.mul N (IntHook.add N 1)) 2 = some r ∧
    MapHook.concat (MapHook.element (.inj_Id (.mk "$s")) (.inj_Int r))
      (MapHook.element (.inj_Id (.mk "$n")) (.inj_Int 0)) = some m

/-- A configuration with an empty store satisfies the bisimulation's invariant. -/
theorem inv_unit {k : KImp.SortKCell} {g : KImp.SortGeneratedCounterCell} :
    Inv (.«<generatedTop>» k (.«<env>» MapHook.unit) g) :=
  ⟨fun p hp => by simp [MapHook.unit, ListIso.toList_ofList] at hp,
   fun p hp => by simp [MapHook.unit, ListIso.toList_ofList] at hp⟩

/-- `sum-N` for the KRS IMP port. -/
theorem sumN_holds (K : KImp.SortK) (N G : Int) (hN : IntHook.le 0 N = true) :
    AF KrsImp.Step (sumNPost (tr_SortK K) N) (sumN (tr_SortK K) N G) := by
  refine AF.of_bisim bisim ?_ ⟨inv_unit, rfl⟩ (KImpClaims.ImpSimpleSpec.Claim.«sum-N».holds K G N hN)
  rintro a b ⟨hi, rfl⟩ ⟨G', r, m, rfl, hr, hm⟩
  exact ⟨G', r, tr_SortMap m, rfl, hr, map_fwd rfl (inv_map0 hi) hm⟩

#k2l_assert_axioms sumN_holds

end ImpRelClaims
