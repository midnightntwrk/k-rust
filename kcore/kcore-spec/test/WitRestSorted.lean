/-
  Three conjuncts of `sortedOK` for which no witness was found in the no-model form (a semantics
  meeting every other condition of `coreOK` and `FnHyp`, failing the conjunct, whose `Γ` has no
  model). Run from the package root: `lake env lean -j1 test/WitRestSorted.lean`.

  Kernel-checked here, for each conjunct: a semantics meeting every other leaf condition of
  `coreOK` (the other conjuncts of `sortedOK`, `faithCoreOK`, `hooksApart`, `predsApart`, `idsOK`,
  `overloadsOK`) and `FnHyp`, with the conjunct false. So none of the three is implied by the others.
  - `c.subsortsOK`: `Dup.c` lists the subsort `KCell < KCellOpt` twice (`nodup` fails). `Dup.c0`,
    the list without the repetition, meets `coreOK` (`c0_core`); every constructor item of `Dup.c`
    but `KCellOpt`'s no-junk axiom is one of `Dup.c0` (`cons_sub`), that axiom having the injection
    from `KCell` as a disjunct twice (`gens_dup`); the signature's, the functions' and the
    collections' items are the same (`sig_same`, `fn_same`, `coll_same`).
  - `f.clauses.all (c.clauseSorted f …)`: `Ill.c` has a constructor sort `N` with one constant `n`
    and the functions `f, g : → N` with the clauses `f() => true`, `g() => false`.
  - `c.rules.all c.ruleSorted`: `Rhs.c` has the rule `<k> .K </k> … => 1`, whose right-hand side is
    an Int, not a configuration.

  Argued, not kernel-checked: `Γ` of each has a model.
  - `Dup.c`: `Γ` reads the subsorts through membership (`contains` in `sortOf`, `le`, the injection
    generators of `gens`, the coherence chains), so its premises are those of `Dup.c0` up to repeated
    items and the repeated disjunct (`φ ∨ φ` is `φ`), and `Dup.c0`'s value model is one. The reflexive and cyclic subsorts that `subsortsOK`
    also refuses are refused by `genWf` as well (`c.subsorts.all (p.1 != p.2)`, a part of
    `faithCoreOK`). A declared subsort from or to a sort outside the definition's: from an
    unnumbered sort it fails `sortsNumbered`, to Int it fails `genWf`; from Int, Bool, K or KItem to
    `N`, or from `N` to K or KItem, `subsortsOK` alone fails (seen by evaluation, not kept here), and
    no contradiction was found: the injections are generators that the free term algebra over the
    constructors and injections meets with its no-junk and distinctness axioms, the coherence of
    `KItem < N < KItem` (a cycle `declaredClosure` does not see, `N < KItem` being added after it)
    constraining only `inj{N,N}` and `inj{KItem,KItem}`, which no other axiom reads.
  - `Ill.c`: the equation of `f` is `\equals{N,R}(f(), true ∧ ⊤_N)` (`clauseRight`), which `sEquals`
    relativizes to `N`, and the arity item puts `f()` in `N`; in a model where `true` is no element of
    `N`, the right side is empty, and reading `f()` and `g()` as nothing meets both items while
    `true` and `false` stay apart. `Eval` gives `f() = true`, which `Γ` does not entail, so the
    conjunct is asked for the soundness of evaluation, not for a model.
  - `Rhs.c`: `Step` makes no step by the rule (its right-hand side's value is no configuration).
    The rule's right side is `1 ∧ ⊤_C` (`ruleRight`) and its axiom has the premise `⌈1 ∧ ⊤_C⌉`, which
    is empty in a model where `1` is no configuration, such as the value model of the semantics
    without the rule (which `coreOK` accepts: `Dup.c0`); there the axiom says nothing, and the other
    axioms are those of that semantics.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.WitRestSorted

open ML

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 3, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 4, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- The user sort `N` and its constant `n`. -/
def N : Srt := nRegSorts + 2
def nL : Sym := nRegSyms + 5

/-- A semantics without functions or parameters meets `FnHyp` once it reads no confined sort. -/
theorem fnHyp_of_nil {c : Semantics} (hf : c.fns = []) (hp : c.params = []) (hr : c.readsConfined = false) :
    FnHyp c :=
  ⟨fun _ h => absurd (hf ▸ h) List.not_mem_nil, fun _ h => absurd (hf ▸ h) List.not_mem_nil,
    fun _ h => absurd (hf ▸ h) List.not_mem_nil, fun _ h => absurd (hf ▸ h) List.not_mem_nil,
    openDecided_of_readsConfined hr, openLaws_of_plain fun _ h => absurd (hp ▸ h) List.not_mem_nil⟩

/-! ## `subsortsOK`: a subsort listed twice -/

namespace Dup

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt", "N"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisN", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lbln"]
    userSorts := cellSorts ++ [N]
    ctors := cellCtors ++ [⟨nL, [], N⟩]
    fns := []
    userSubsorts := cellSubsorts ++ [(nRegSorts, nRegSorts + 1)]
    pgmSort := Srt.k
    rules := [] }

/-- The same semantics without the repetition. -/
def c0 : Semantics := { c with userSubsorts := cellSubsorts }

theorem fnHyp : FnHyp c := fnHyp_of_nil rfl rfl (by decide +kernel)

set_option maxHeartbeats 1000000 in
/-- Every leaf condition of `coreOK` but `subsortsOK` holds, and `FnHyp`. -/
theorem meets_others : c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) = true ∧
    c.rules.all c.ruleSorted = true ∧ c.rulesPlain = true ∧ c.clausesPlain = true ∧ c.paramsPlain = true ∧
    c.faithCoreOK = true ∧ c.hooksApart = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧ FnHyp c :=
  ⟨by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, fnHyp⟩

theorem not_subsortsOK : c.subsortsOK = false := by decide +kernel

theorem c0_core : c0.coreOK = true := by decide_cheap

/-- Every constructor item of `c` but `KCellOpt`'s no-junk axiom is one of `c0`; that axiom has
the injection from `KCell` as a disjunct twice (`gens_dup`), `c0`'s once. -/
theorem cons_sub : (consItemsK c).all (fun it => it.label == "cons-nojunk SortKCellOpt" ||
    (consItemsK c0).any (fun it' => it'.pat == it.pat)) = true := by
  decide +kernel

theorem gens_dup : (c.gens (nRegSorts + 1)).length = 3 ∧ (c0.gens (nRegSorts + 1)).length = 2 := by decide +kernel

-- `sigItems` does not read the subsorts, so the two sides are one term once `c0` is unfolded.
theorem sig_same : (sigItems c).map (·.pat) = (sigItems c0).map (·.pat) := rfl
theorem fn_same : (fnItems c).map (·.pat) = (fnItems c0).map (·.pat) := by decide +kernel
theorem coll_same : c.allColls.flatMap (collAxioms c) = c0.allColls.flatMap (collAxioms c0) := by decide +kernel

end Dup

/-! ## `clauseSorted`: a function of a constructor sort whose right-hand side is a Bool -/

namespace Ill

def fL : Sym := nRegSyms + 6
def gL : Sym := nRegSyms + 7
def clF : Clause := { vars := [], pats := [], req := none, rhs := .dv Srt.bool (.bool true), ens := none }
def clG : Clause := { vars := [], pats := [], req := none, rhs := .dv Srt.bool (.bool false), ens := none }
/-- `f() => true` and `g() => false`, both of the result sort `N`. -/
def fF : Fn := ⟨fL, [], N, [clF], false⟩
def fG : Fn := ⟨gL, [], N, [clG], false⟩

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt", "N"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisN", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lbln", "Lblf", "Lblg"]
    userSorts := cellSorts ++ [N]
    ctors := cellCtors ++ [⟨nL, [], N⟩]
    fns := [fF, fG]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

theorem lookup_f : c.lookupFn fL = some fF := rfl
theorem lookup_g : c.lookupFn gL = some fG := rfl

/-- A clause without variables, patterns, `requires`, `ensures` or existential variables, of the
precondition `.top` and the right side's predicate `.top`, whose right-hand side is a domain value
gives that value. -/
theorem eval_const {f : Sym} {fn : Fn} {cl : Clause} {s : Srt} {l : Lit} (hfn : c.lookupFn f = some fn)
    (hcl : fn.clauses = [cl]) (hv : cl.vars = []) (hp : cl.pats = []) (hq : cl.req = none)
    (hr : cl.rhs = .dv s l) (he : cl.ens = none) (hpre : cl.pre = .top) (hx : cl.exs = [])
    (hpost : cl.post = .top) : Eval c f [] (some (.dv s l)) :=
  .clause (σ := []) hfn (by rw [hcl]; exact List.mem_singleton_self _) (fun i s' h => by rw [hv] at h; simp at h)
    (by rw [hp]; exact .nil) (fun _ h => by rw [hq] at h; cases h) (Clause.holds_preTop hpre _)
    (fun cl' h _ hlt => by rw [hcl] at h; obtain rfl := List.mem_singleton.mp h; exact absurd hlt (Nat.lt_irrefl _))
    hx (by rw [hr]; exact .dv) (fun _ h => by rw [he] at h; cases h) (Clause.holds_postTop hpost _)

theorem coherent_const {cl : Clause} {s : Srt} {l : Lit} (hr : cl.rhs = .dv s l) (he : cl.ens = none)
    (hx : cl.exs = []) : MatchIndependent c cl :=
  (matchIndependent_iff_noExs hx).mpr <|
    Coherent.of_rhs he he (fun _ _ _ _ _ _ _ _ => .inl ⟨rfl, fun i hi => by rw [hr] at hi; cases hi⟩) hx hx

theorem fnHyp : FnHyp c := by
  refine ⟨fun fn hfn vs hvs => ?_, fun fn hfn ht => ?_, fun fn hfn => ?_, fun fn hfn cl hcl => ?_,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain fun _ h => absurd h List.not_mem_nil⟩
  · rcases List.mem_cons.mp hfn with rfl | hfn
    · obtain rfl := sortsOf_nil_eq hvs
      exact ⟨_, eval_const lookup_f rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
    · obtain rfl := List.mem_singleton.mp hfn
      obtain rfl := sortsOf_nil_eq hvs
      exact ⟨_, eval_const lookup_g rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
  · rcases List.mem_cons.mp hfn with rfl | hfn
    · cases ht
    · obtain rfl := List.mem_singleton.mp hfn; cases ht
  · intro cl cl' h
    rcases List.mem_cons.mp hfn with rfl | hfn
    · exact absurd h (by rw [show pairs fF.clauses = [] from rfl]; exact List.not_mem_nil)
    · obtain rfl := List.mem_singleton.mp hfn
      exact absurd h (by rw [show pairs fG.clauses = [] from rfl]; exact List.not_mem_nil)
  · rcases List.mem_cons.mp hfn with rfl | hfn
    · obtain rfl := List.mem_singleton.mp hcl; exact coherent_const rfl rfl rfl
    · obtain rfl := List.mem_singleton.mp hfn
      obtain rfl := List.mem_singleton.mp hcl; exact coherent_const rfl rfl rfl

set_option maxHeartbeats 1000000 in
/-- Every leaf condition of `coreOK` but `clauseSorted` holds, and `FnHyp`. -/
theorem meets_others : c.subsortsOK = true ∧
    c.rules.all c.ruleSorted = true ∧ c.rulesPlain = true ∧ c.clausesPlain = true ∧ c.paramsPlain = true ∧
    c.faithCoreOK = true ∧ c.hooksApart = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧ FnHyp c :=
  ⟨by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, fnHyp⟩

theorem not_clauseSorted : c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) = false := by
  decide +kernel

/-- `Eval` gives `f() = true`, a value outside `N`. -/
theorem eval_f : Eval c fL [] (some (.dv Srt.bool (.bool true))) := eval_const lookup_f rfl rfl rfl rfl rfl rfl rfl rfl rfl
theorem true_sort : c.sortOf (.dv Srt.bool (.bool true)) = some Srt.bool := by decide +kernel

end Ill

/-! ## `ruleSorted`: a rule whose right-hand side is not a configuration -/

namespace Rhs

def cfg (t : Term) : Term :=
  .app topLabel [.app (nRegSyms + 3) [t], .app counterLabel [.dv Srt.int (.int 0)]]

/-- `<k> .K </k> <generatedCounter> 0 </generatedCounter> => 1`. -/
def r : Rule := { vars := [], lhs := cfg (.app dotk []), req := none, rhs := .dv Srt.int (.int 1), ens := none, prio := 50 }

def c : Semantics := { Dup.c with userSubsorts := cellSubsorts, rules := [r] }

theorem fnHyp : FnHyp c := fnHyp_of_nil rfl rfl (by decide +kernel)

set_option maxHeartbeats 1000000 in
/-- Every leaf condition of `coreOK` but `ruleSorted` holds, and `FnHyp`. -/
theorem meets_others : c.subsortsOK = true ∧
    c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) = true ∧
    c.rulesPlain = true ∧ c.clausesPlain = true ∧ c.paramsPlain = true ∧
    c.faithCoreOK = true ∧ c.hooksApart = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧ FnHyp c :=
  ⟨by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, fnHyp⟩

theorem not_ruleSorted : c.rules.all c.ruleSorted = false := by decide +kernel

/-- The rule's right-hand side has a value of the sort Int, no configuration. -/
theorem rhs_sort : c.sortOf (.dv Srt.int (.int 1)) = some Srt.int := by decide +kernel

/-- Without the rule it is `Dup.c0`. -/
theorem c0_eq : ({ c with rules := [] } : Semantics) = Dup.c0 := rfl

end Rhs

/-- info: 'KCore.Faithful.WitRestSorted.Dup.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dup.meets_others

/-- info: 'KCore.Faithful.WitRestSorted.Ill.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ill.meets_others

/-- info: 'KCore.Faithful.WitRestSorted.Rhs.meets_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rhs.meets_others

end KCore.Faithful.WitRestSorted
