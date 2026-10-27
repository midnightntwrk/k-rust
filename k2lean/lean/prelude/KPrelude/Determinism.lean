import KPrelude.Rules
import KPrelude.Tactic
import KPrelude.Logic

/-!
# Determinism modulo overlapping rules, and the closers of the generated determinism proofs

A generated `Determinism` module states determinism of `Step` at every configuration where no
listed pair of rules applies at once (`noOverlap c = true`); with an empty list that is every
configuration. A pair `(r, r')` is in the list when the generator could not show that the two
rules never both apply; every pair that is not listed is proved not to (the kernel checks a
small proof per pair), so the list is a hypothesis of the theorem, never an assumption about
the classifier.

The closers below are the certificates the generator chooses per surviving goal of a rule's
inversion (`k2l_case tag => tac`); each one is a small search over the hypotheses that the
kernel checks, not a decision procedure.
-/

/-- The injection algebra of a generated definition (`inj_A_C (inj_B_A x) = inj_B_C x`,
`proj_A_C (inj_B_A x) = some (inj_B_C x)`), tagged in its `Determinism` module. -/
register_simp_attr k2l_det_alg

namespace KPrelude

/-- Two rules of one priority rank (same applicability and step relations). -/
structure Overlap (α : Type) where
  {A : α → Prop}
  {R : α → α → Prop}
  fst : Rule α A R
  snd : Rule α A R

/-- Both rules of the pair apply at `c` (their left-hand sides match and requires are `true`). -/
def Overlap.both {α : Type} (o : Overlap α) (c : α) : Bool :=
  (o.fst.run c).applies && (o.snd.run c).applies

/-- No pair of the list applies at `c` with both of its rules. -/
def noOverlapIn {α : Type} (os : List (Overlap α)) (c : α) : Bool :=
  os.all fun o => !o.both c

theorem noOverlapIn_fst {α : Type} {os : List (Overlap α)} {c : α} (h : noOverlapIn os c = true)
    {o : Overlap α} (hm : o ∈ os) (h₁ : (o.fst.run c).applies = true) : (o.snd.run c).applies = false := by
  have := List.all_eq_true.1 h o hm
  simp only [Overlap.both, h₁, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact this

theorem noOverlapIn_snd {α : Type} {os : List (Overlap α)} {c : α} (h : noOverlapIn os c = true)
    {o : Overlap α} (hm : o ∈ os) (h₂ : (o.snd.run c).applies = true) : (o.fst.run c).applies = false := by
  have := List.all_eq_true.1 h o hm
  simp only [Overlap.both, h₂, Bool.and_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact this

@[simp] theorem noOverlapIn_nil {α : Type} (c : α) : noOverlapIn ([] : List (Overlap α)) c = true := rfl

open Lean Meta Elab Tactic

register_option k2l.det.verbose : Bool := {
  defValue := false
  descr := "k2l_case: report the predicted goals that inversion already closed"
}

/-- `k2l_case tag => tac`: run the certificate `tac` on every goal whose tag ends with `tag` (a
constructor name of the inverted relation), which `tac` must close. There is one such goal after
an inversion, or one per case when the lemma first split its own left-hand side (a rule whose
first `<k>` item is a variable of a sort, split by the sort's leaves). When no goal has that tag
(the inversion already closed it) this does nothing. When `tac` fails on a goal, that goal is
kept, with a warning, for the closers that follow (`k2l_default`), so a wrong prediction costs
time and is reported, but never decides the proof. -/
syntax (name := k2lCase) "k2l_case " ident " => " tacticSeq : tactic

@[tactic k2lCase] def evalK2lCase : Tactic := fun stx => do
  let tag := stx[1].getId
  let tac := stx[3]
  let verbose := k2l.det.verbose.get (← getOptions)
  let gs ← getUnsolvedGoals
  let mut kept : Array MVarId := #[]
  let mut found := false
  for g in gs do
    unless tag.isSuffixOf (← g.getTag) do
      kept := kept.push g
      continue
    found := true
    if verbose then logInfo m!"k2l_case {tag}: goal"
    let s ← saveState
    setGoals [g]
    -- a certificate that exceeds the recursion depth or the heartbeats fails like any other
    let ok ← tryCatchRuntimeEx
      (do
        -- without error recovery: a failing step fails its alternative (no logged error, no
        -- admitted goal)
        withoutRecover (evalTactic tac)
        unless (← getUnsolvedGoals).isEmpty do throwError "the certificate left goals"
        pure none)
      (fun e => pure (some e))
    if let some e := ok then
      s.restore
      logWarning m!"k2l_case {tag}: certificate failed ({e.toMessageData}); left to the default closer"
      kept := kept.push g
  if verbose && !found then logInfo m!"k2l_case {tag}: no such goal"
  setGoals kept.toList

/-- `k2l_guard tac`: `tac`, with a failure by recursion depth or heartbeats turned into an ordinary
error, so that the next alternative of a `first` runs (an unfolding that does not terminate in a
large context fails instead of ending the proof). -/
syntax (name := k2lGuard) "k2l_guard " tacticSeq : tactic

@[tactic k2lGuard] def evalK2lGuard : Tactic := fun stx => do
  let s ← saveState
  let r ← tryCatchRuntimeEx (do withoutRecover (evalTactic stx[1]); pure none) (fun e => pure (some e))
  if let some e := r then
    s.restore
    throwError "k2l_guard: {e.toMessageData}"

/-- Report, as a warning, that the main goal reached the fallback closers (a goal the pair
classification did not predict, or whose certificate failed). -/
elab "k2l_warn_fallback" : tactic => do
  logWarning m!"k2l_fallback: {← getMainTag}"

/-- With `k2l.det.verbose`, report the goals that reach the default closer (for counting). -/
elab "k2l_note_default" : tactic => do
  if k2l.det.verbose.get (← getOptions) then logInfo m!"k2l_default: {← getMainTag}"

/-- Close the goal by `cases` on one equation hypothesis whose two sides reduce to different
constructors: a requires that evaluates to `false`, a projection into the wrong sort, a literal
that differs. -/
elab "k2l_refute_eqs" : tactic => withMainContext do
  let lctx ← getLCtx
  -- the lemma's own (named) hypotheses first, then the partner's (inaccessible) ones
  let ds := lctx.decls.toArray.reverse.filterMap id
  let named := ds.filter (fun d => !d.userName.hasMacroScopes)
  let anon := ds.filter (fun d => d.userName.hasMacroScopes)
  for ldecl in named ++ anon do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    unless ty.isEq do continue
    let s ← saveState
    try
      let h ← Term.exprToSyntax ldecl.toExpr
      evalTactic (← `(tactic| cases $h:term))
      if (← getGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "k2l_refute_eqs: no refutable equation"

/-- For each hypothesis `h : proj_A_B y = some x` with `y` a variable, replace `y` by
`inj_B_A x` (by the generated `inj_proj_A_B`). -/
elab "k2l_proj_inv" : tactic => do
  let mut progress := true
  let mut fuel := 16
  while progress && fuel > 0 do
    progress := false
    fuel := fuel - 1
    let found ← withMainContext do
      for ldecl in (← getLCtx) do
        if ldecl.isImplementationDetail then continue
        let ty ← instantiateMVars ldecl.type
        let some (_, lhs, _) := ty.eq? | continue
        let .const fn _ := lhs.getAppFn | continue
        let .str ns last := fn | continue
        unless last.startsWith "proj_" do continue
        let some y := lhs.getAppArgs.back? | continue
        unless y.isFVar do continue
        let lem := Name.str ns ("inj_" ++ last)
        unless (← getEnv).contains lem do continue
        let s ← saveState
        try
          let h ← Term.exprToSyntax ldecl.toExpr
          evalTactic (← `(tactic| (have k2l_e := $(mkIdent lem) $h; subst k2l_e)))
          return true
        catch _ => s.restore
      return false
    if found then progress := true

/-! ## Side conditions read as propositions

A `requires` clause is a Boolean built from hooks; two clauses that exclude each other usually do
so through their atoms (`I =/=Int 0` against `I ==Int 0`, `G <=Gas GAVAIL` against
`GAVAIL <Gas G`, a pattern literal that decides an atom of the other clause). `k2l_prop` reads
every comparison hook as the proposition it decides (`=/=` as the negation of `==`), splits the
connectives, substitutes the variables a pattern equates to a value, and closes the goal by
linear arithmetic or by simplification with every hypothesis. -/

/-- `decide p = true` is `p`, with the `Decidable` instance the term carries. `decide_eq_true_eq`
synthesizes its instance and applies only when that instance equals the term's at reducible
transparency; after `simp` has rewritten the arguments of a decided hook (`IntHook.le x c` unfolds
to `decide (x ≤ c)` before its argument `x = IntHook.add a b` becomes `a + b`), the term's instance
still mentions the old arguments, equal to the synthesized one only by unfolding the hook. -/
simproc_decl k2lDecideEqTrue (decide _ = true) := fun e => do
  let some (_, lhs, rhs) := e.eq? | return .continue
  unless rhs.isConstOf ``Bool.true && lhs.isAppOfArity ``Decidable.decide 2 do return .continue
  let p := lhs.appFn!.appArg!
  return .visit { expr := p, proof? := some (mkApp2 (mkConst ``decide_eq_true_eq) p lhs.appArg!) }

/-- `decide p = false` is `¬p`, with the instance the term carries (as `k2lDecideEqTrue`). -/
simproc_decl k2lDecideEqFalse (decide _ = false) := fun e => do
  let some (_, lhs, rhs) := e.eq? | return .continue
  unless rhs.isConstOf ``Bool.false && lhs.isAppOfArity ``Decidable.decide 2 do return .continue
  let p := lhs.appFn!.appArg!
  let pf := mkApp2 (mkConst ``decide_eq_false_iff_not) p lhs.appArg!
  return .visit { expr := mkNot p, proof? := some (mkApp3 (mkConst ``propext) e (mkNot p) pf) }

theorem BytesHook.length_eq_zero_iff (b : List UInt8) : BytesHook.length b = 0 ↔ b = BytesHook.empty := by
  simp [BytesHook.length, BytesHook.empty]
theorem StringHook.length_eq_zero_iff (s : String) : StringHook.length s = 0 ↔ s = "" := by
  simp [StringHook.length, String.length_eq_zero_iff]

namespace SetHook

open ListIso

variable {S K : Type} [Ord K] [ListIso S (K × Unit)] [MapRepr S K Unit] [Std.TransOrd K] [Std.LawfulEqOrd K]

theorem mem_of_inSet {k : K} {s : S} (h : inSet k s = true) : (k, ()) ∈ toList s := by
  unfold inSet MapHook.inKeys at h
  rw [MapRepr.lookupR_eq] at h
  cases hl : SAL.lookup k (toList s) with
  | none => simp [hl] at h
  | some u => cases u; exact SAL.lookup_mem hl

/-- Two sets with no common element (checked on the first one's elements, by evaluation) contain
no common `k`: membership of a variable in two disjoint sets of literals. -/
theorem inSet_disjoint {a b : S} (hd : (toList a).all (fun p => !inSet p.1 b) = true) {k : K}
    (ha : inSet k a = true) (hb : inSet k b = true) : False := by
  have := List.all_eq_true.1 hd _ (mem_of_inSet ha)
  simp [hb] at this

/-- A set included in another (checked on its elements). -/
theorem inSet_of_subset {a b : S} (hs : (toList a).all (fun p => inSet p.1 b) = true) {k : K}
    (ha : inSet k a = true) : inSet k b = true := by
  have := List.all_eq_true.1 hs _ (mem_of_inSet ha)
  simpa using this

end SetHook

theorem IntHook.ne_eq_not (a b : Int) : IntHook.ne a b = !IntHook.eq a b := by
  simp [IntHook.ne, IntHook.eq]
theorem KEqHook.ne_eq_not {α : Type} [DecidableEq α] (a b : α) : KEqHook.ne a b = !KEqHook.eq a b := rfl
theorem BoolHook.ne_eq_not (a b : Bool) : BoolHook.ne a b = !BoolHook.eq a b := rfl
theorem StringHook.ne_eq_not (a b : String) : StringHook.ne a b = !StringHook.eq a b := rfl

/-- The comparison hooks as the propositions they decide, and the connectives split, in the side
conditions (the hypotheses `… = true` and `… = false`; the configurations' equations are left
alone: they are large, and simplification would only traverse them). -/
elab "k2l_prop_norm" : tactic => withMainContext do
  let mut locs : Array Ident := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, _, rhs) := ty.eq? | continue
    unless rhs.isConstOf ``Bool.true || rhs.isConstOf ``Bool.false do continue
    if d.userName.hasMacroScopes then
      -- an inaccessible name: give it one
      let n := Name.mkSimple s!"k2l_sc{locs.size}"
      let g ← (← getMainGoal).rename d.fvarId n
      replaceMainGoal [g]
      locs := locs.push (mkIdent n)
    else
      locs := locs.push (mkIdent d.userName)
  if locs.isEmpty then throwError "k2l_prop_norm: no side condition"
  evalTactic (← `(tactic| simp only [KPrelude.IntHook.ne_eq_not, KPrelude.KEqHook.ne_eq_not, KPrelude.BoolHook.ne_eq_not,
    KPrelude.StringHook.ne_eq_not, KPrelude.IntHook.eq, KPrelude.IntHook.lt, KPrelude.IntHook.le,
    KPrelude.IntHook.gt, KPrelude.IntHook.ge, KPrelude.IntHook.add, KPrelude.IntHook.sub,
    KPrelude.IntHook.mul, KPrelude.BoolHook.and, KPrelude.BoolHook.or, KPrelude.BoolHook.not,
    KPrelude.BoolHook.eq, KPrelude.BoolHook.xor, KPrelude.BoolHook.implies, KPrelude.KEqHook.eq,
    KPrelude.StringHook.eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.not_eq_false', Bool.and_eq_false_iff, Bool.or_eq_false_iff, k2lDecideEqTrue,
    k2lDecideEqFalse, beq_iff_eq, Bool.not_not, Bool.true_and, Bool.and_true,
    Bool.false_and, Bool.and_false, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false,
    Bool.not_true, Bool.not_false, KPrelude.BytesHook.length_eq_zero_iff,
    KPrelude.StringHook.length_eq_zero_iff] at $locs*))

/-- Side conditions that exclude each other once read as propositions (see above). -/
macro "k2l_prop" : tactic => `(tactic| (
  try subst_vars
  try k2l_prop_norm
  first | omega | (simp_all; done) | (simp_all; omega)))

/-! ## Facts about collections, bytes and strings

A list pattern `ListItem(X) REST` never matches `.List`; two matches of one cell map at one key
bind one value; a byte sequence or string of length `0` is the empty one. Each is a lemma here;
`k2l_theory` uses them together with `k2l_prop`. -/

namespace ListHook

open ListIso

variable {L E : Type} [ListIso L E]

theorem toList_unit : toList (unit : L) = [] := toList_ofList _
theorem toList_concat_element (x : E) (t : L) : toList (concat (element x) t) = x :: toList t := by
  simp [concat, element, toList_ofList]
theorem toList_concat_element_right (t : L) (x : E) : toList (concat t (element x)) = toList t ++ [x] := by
  simp [concat, element, toList_ofList]

/-- Two matches of `ListItem(X) REST` against one list bind one head and one tail. -/
theorem concat_element_inj {x x' : E} {t t' : L} (h : concat (element x) t = concat (element x') t') :
    x = x' ∧ t = t' := by
  have := congrArg uncons h
  rw [uncons_concat_element, uncons_concat_element] at this
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this

theorem concat_element_eq_unit_iff (x : E) (t : L) : concat (element x) t = (unit : L) ↔ False := by
  constructor
  · intro h; have := congrArg toList h; simp [toList_concat_element, toList_unit] at this
  · intro h; exact h.elim
theorem unit_eq_concat_element_iff (x : E) (t : L) : (unit : L) = concat (element x) t ↔ False := by
  rw [eq_comm]; exact concat_element_eq_unit_iff x t
theorem concat_element_right_eq_unit_iff (t : L) (x : E) : concat t (element x) = (unit : L) ↔ False := by
  constructor
  · intro h; have := congrArg toList h; simp [toList_concat_element_right, toList_unit] at this
  · intro h; exact h.elim
theorem unit_eq_concat_element_right_iff (t : L) (x : E) : (unit : L) = concat t (element x) ↔ False := by
  rw [eq_comm]; exact concat_element_right_eq_unit_iff t x

end ListHook

open Lean Meta Elab Tactic in
/-- Two hypotheses `inSet k a = true`, `inSet k b = true` (or `= false`) over sets the kernel can
evaluate: refuted when the sets are disjoint (or the first included in the second). -/
elab "k2l_set_lits" : tactic => withMainContext do
  let mut ins : Array (Expr × Expr × Expr × Bool) := #[]  -- (k, s, proof, value)
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless lhs.isAppOf ``KPrelude.SetHook.inSet do continue
    let args := lhs.getAppArgs
    let some s := args.back? | continue
    let some k := args[args.size - 2]? | continue
    let v := rhs.isConstOf ``Bool.true
    unless v || rhs.isConstOf ``Bool.false do continue
    ins := ins.push (k, s, d.toExpr, v)
  for (k, a, ha, va) in ins do
    for (k', b, hb, vb) in ins do
      unless a != b && va do continue
      -- one element may be written through injection functions (`inj_JSONKey_KItem (inj_String x)`)
      -- and the other as the constructor they compute (`SortKItem.inj_String x`)
      unless k == k' || (← withoutModifyingState (isDefEq k k')) do continue
      let s ← saveState
      try
        let ha' ← Term.exprToSyntax ha
        let hb' ← Term.exprToSyntax hb
        if vb then
          evalTactic (← `(tactic| exact (KPrelude.SetHook.inSet_disjoint (by decide +kernel) $ha' $hb').elim))
        else
          evalTactic (← `(tactic| exact Bool.false_ne_true (Eq.trans (Eq.symm $hb') (KPrelude.SetHook.inSet_of_subset (by decide +kernel) $ha'))))
        if (← getGoals).isEmpty then return
        s.restore
      catch _ => s.restore
  throwError "k2l_set_lits: no two set memberships that exclude each other"

open Lean Meta Elab Tactic in
/-- For two hypotheses `concat (element x) t = l` and `concat (element x') t' = l` (one list matched
twice by `ListItem(X) REST`), identify `x` with `x'` and `t` with `t'` (`cases` on each). -/
partial def k2lListFundepLoop (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  if (← getGoals).isEmpty then return
  let found ← withMainContext do
    let mut seen : Array (Expr × Expr) := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, lhs, rhs) := ty.eq? | continue
      unless lhs.isAppOf ``KPrelude.ListHook.concat do continue
      let args := lhs.getAppArgs
      let some a := args[args.size - 2]? | continue
      unless a.isAppOf ``KPrelude.ListHook.element do continue
      match seen.find? (fun p => p.1 == rhs) with
      | some (_, h0) =>
        if (← instantiateMVars (← inferType h0)) == ty then continue
        let s ← saveState
        try
          let h0s ← Term.exprToSyntax h0
          let h1s ← Term.exprToSyntax d.toExpr
          evalTactic (← `(tactic| (obtain ⟨k2l_e1, k2l_e2⟩ := KPrelude.ListHook.concat_element_inj (Eq.trans $h0s (Eq.symm $h1s)); cases k2l_e1; cases k2l_e2)))
          return true
        catch _ => s.restore
      | none => seen := seen.push (rhs, d.toExpr)
    return false
  if found then k2lListFundepLoop (fuel - 1)

elab "k2l_list_fundep" : tactic => k2lListFundepLoop 16

open Lean Meta Elab Tactic in
/-- Substitute every hypothesis `l = ListHook.unit` (or `MapHook.unit`) whose left side is a
variable, so that a pattern matched against the same collection meets the unit. -/
elab "k2l_subst_units" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless lhs.isFVar do continue
    let .const n _ := rhs.getAppFn | continue
    unless n == ``KPrelude.ListHook.unit || n == ``KPrelude.MapHook.unit || n == ``KPrelude.SetHook.unit do continue
    try
      let h ← Term.exprToSyntax d.toExpr
      evalTactic (← `(tactic| subst $h:term))
    catch _ => pure ()

partial def k2lBoolAtoms (conn : List Name) (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let fn := e.getAppFn
  if let .const n _ := fn then
    if conn.contains n then
      let mut a := acc
      for x in e.getAppArgs do a ← k2lBoolAtoms conn x a
      return a
    if n == ``Bool.true || n == ``Bool.false then return acc
  if (← whnf (← inferType e)).isConstOf ``Bool && !e.hasLooseBVars && e.hasFVar then return acc.push e
  return acc

/-- Complementary Boolean conditions, propositionally: decompose the connectives of every
hypothesis into atoms that are `true` or `false`, and let each fact rewrite the others. -/
macro "k2l_bool_prop" : tactic => `(tactic| (
  simp_all only [KPrelude.BoolHook.and, KPrelude.BoolHook.or, KPrelude.BoolHook.not, KPrelude.BoolHook.xor,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.not_eq_false', Bool.and_eq_false_iff,
    Bool.or_eq_false_iff, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_true,
    Bool.true_or, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, true_and, and_true, false_and, and_false, or_false, false_or, not_true_eq_false,
    not_false_eq_true, reduceCtorEq]
  done))

/-- Case-split a Boolean atom (an application that is not a connective) that occurs in two
hypotheses `… = true`, simplifying the connectives in each case (complementary conditions). -/
elab "k2l_bool_cases1" : tactic => withMainContext do
  let conn := [``KPrelude.BoolHook.and, ``KPrelude.BoolHook.or, ``KPrelude.BoolHook.not, ``KPrelude.BoolHook.xor, ``KPrelude.BoolHook.eq, ``KPrelude.BoolHook.ne]
  let mut seen : Array (Expr × Nat) := #[]
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let some (t, lhs, _) := ty.eq? | continue
    unless (← whnf t).isConstOf ``Bool do continue
    for a in (← k2lBoolAtoms conn lhs #[]) do
      match seen.findIdx? (fun p => p.1 == a) with
      | some i => seen := seen.modify i (fun p => (p.1, p.2 + 1))
      | none => seen := seen.push (a, 1)
  for (a, n) in seen do
    if n < 2 then continue
    let s ← saveState
    try
      let t ← Term.exprToSyntax a
      evalTactic (← `(tactic| (cases k2l_hb : $t <;> simp only [k2l_hb, KPrelude.BoolHook.and, KPrelude.BoolHook.or, KPrelude.BoolHook.not, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, reduceCtorEq] at * <;> done)))
      if (← getGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "k2l_bool_cases: no complementary atom"

macro "k2l_bool_cases" : tactic => `(tactic| first | k2l_bool_cases1 | k2l_bool_prop | k2l_prop)

/-- `k2l_det_fundep` (the determinism closers' variant of `k2l_fundep` of `KPrelude.Tactic`, for
any non-variable left-hand side, not only `some`): identify what two hypotheses `e = a` and `e = b` with the same left-hand side `e` (not a
variable) determine: the results of one partial call made twice (`e = some a`), the rest of one map
match (`remove m k = r`), the head and tail of one list match (`uncons l = some (x, t)`). Derives
`a = b`, drops the second hypothesis, and lets `cases` unify (it closes the goal when `a` and `b`
are different constructors). -/
partial def k2lDetFundepLoop (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  if (← getGoals).isEmpty then return
  let found ← withMainContext do
    let mut seen : Array (Expr × Expr) := #[]
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let some (_, lhs, rhs) := ty.eq? | continue
      if lhs.isFVar || lhs.isMVar then continue
      if rhs.isConstOf ``Bool.true || rhs.isConstOf ``Bool.false then continue
      match seen.find? (fun p => p.1 == lhs) with
      | some (_, h0) =>
        -- a duplicate (the same equation twice) identifies nothing
        if (← instantiateMVars (← inferType h0)) == ty then continue
        let s ← saveState
        try
          let h0s ← Term.exprToSyntax h0
          let h1s ← Term.exprToSyntax ldecl.toExpr
          let h1i := mkIdent ldecl.userName
          if ldecl.userName.hasMacroScopes then
            evalTactic (← `(tactic| (have k2l_fd := (Eq.symm $h0s).trans $h1s; cases k2l_fd)))
          else
            evalTactic (← `(tactic| (have k2l_fd := (Eq.symm $h0s).trans $h1s; clear $h1i; cases k2l_fd)))
          return true
        catch _ => s.restore
      | none => seen := seen.push (lhs, ldecl.toExpr)
    return false
  if found then k2lDetFundepLoop (fuel - 1)

elab "k2l_det_fundep" : tactic => k2lDetFundepLoop 32

/-- The certificate of a rule against itself: both inversions give the same binders, except
the results of partial calls and map matches, which are functions of them. -/
macro "k2l_self" : tactic => `(tactic| first
  | rfl
  | (k2l_det_fundep; rfl)
  | (k2l_list_facts; k2l_det_fundep; k2l_map_facts; k2l_det_fundep; first | rfl | (simp_all; done))
  | (k2l_map_facts; simp_all; done))

/-- `k2l_omega [f, …]`: integer side conditions that exclude each other. Unfold the `INT`/`BOOL`
hooks (and `f, …`) to `decide` of linear facts, then `omega` (other subterms are atoms). -/
syntax "k2l_omega" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| k2l_omega) => `(tactic| k2l_omega [])
  | `(tactic| k2l_omega [$xs,*]) => `(tactic| (
    simp only [KPrelude.IntHook.lt, KPrelude.IntHook.le, KPrelude.IntHook.gt, KPrelude.IntHook.ge,
      KPrelude.IntHook.eq, KPrelude.IntHook.ne, KPrelude.IntHook.add, KPrelude.IntHook.sub,
      KPrelude.BoolHook.and, KPrelude.BoolHook.or, KPrelude.BoolHook.not, Bool.and_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, Bool.or_eq_false_iff,
      Bool.not_eq_false', k2lDecideEqTrue, k2lDecideEqFalse, $xs,*] at *
    omega))

section
open Lean Meta Elab Tactic

/-- Close `g` when a leaf condition `leafOK S l = true` (or `S.leaf l = true`, `hasLeaves S = true`) of the context is
false at the leaf tag `cases` substituted: a split of a tag `l : Tag` yields one case per sort of
the definition, and only the leaves of `S` survive; testing that one hypothesis is much cheaper
than `contradiction` over a context of configurations, case after case. -/
def k2lLeafRefuted (g : MVarId) : MetaM Bool := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless rhs.isConstOf ``Bool.true do continue
    let some (.str _ f) := lhs.getAppFn.constName? | continue
    unless f == "leafOK" || f == "leaf" || f == "hasLeaves" do continue
    if (← whnfD lhs).isConstOf ``Bool.false then
      g.assign (← mkFalseElim (← g.getType) (mkApp (mkConst ``Bool.false_ne_true) d.toExpr))
      return true
  return false

/-- Close `g` by `cases` on one of `fields` whose type is an inductive type without constructors. -/
abbrev k2lEmptyField (g : MVarId) (fields : Array Expr) : MetaM Bool := KPrelude.emptyField g fields

/-- Replace each variable of `g` that is a value of a builtin leaf (`x : Term SortInt`: the family
has a constructor `b_SortInt` at that index, and every other constructor is refuted there) by
that constructor's application (`Term.b_SortInt i`), so that a function matching on the injected
value reduces. With `reduceIndex`, the index of a variable's type is reduced first (a field of a
constructor split by `cases` has the type `Term (A2_1 tag c)`, whose index is `SortInt` only
after reduction). -/
def k2lUnfoldSingletons (g : MVarId) (reduceIndex : Bool := false) : MetaM MVarId := do
  let mut g := g
  let cands ← g.withContext do
    let mut acc : Array FVarId := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← whnfD d.type
      let .const n _ := ty.getAppFn | continue
      let some (.inductInfo iv) := (← getEnv).find? n | continue
      if iv.numIndices == 0 || iv.ctors.length < 2 then continue
      let some idx := ty.getAppArgs.back? | continue
      let idx ← if reduceIndex then whnfD idx else pure idx
      if idx.hasFVar || idx.hasMVar then continue
      -- a builtin constructor at this index
      let builtin ← iv.ctors.anyM fun c => do
        let .str _ cs := c | return false
        unless cs.startsWith "b_" do return false
        let some (.ctorInfo ci) := (← getEnv).find? c | return false
        let r ← forallTelescopeReducing ci.type fun _ r => pure r
        return r.getAppArgs.back? == some idx
      if builtin then acc := acc.push d.fvarId
    return acc
  for fid in cands do
    let s ← saveState
    try
      let subs ← g.cases fid
      let mut live : List MVarId := []
      for sg in subs do
        if (← k2lEmptyField sg.mvarId sg.fields) then continue
        if (← k2lLeafRefuted sg.mvarId) then continue
        live := live ++ [sg.mvarId]
      match live with
      | [g'] => g := g'
      | _ => s.restore
    catch _ => s.restore
  return g

/-- Prove a goal `t = T₁ ∨ … ∨ t = Tₙ` whose `t` is syntactically one of the `Tᵢ`. -/
partial def k2lProveDisj (g : MVarId) : MetaM Bool := do
  let ty ← instantiateMVars (← g.getType)
  if ty.isAppOfArity ``Or 2 then
    let a := ty.appFn!.appArg!
    let b := ty.appArg!
    if let some (_, u, v) := a.eq? then
      if u == v then
        g.assign (← mkAppOptM ``Or.inl #[a, b, ← mkEqRefl u])
        return true
    let m ← mkFreshExprMVar b
    g.assign (← mkAppOptM ``Or.inr #[a, b, m])
    k2lProveDisj m.mvarId!
  else if let some (_, u, v) := ty.eq? then
    if u == v then
      g.assign (← mkEqRefl u)
      return true
    return false
  else return false

/-- Split a leaf tag `l` (a field of a `cases` on a value of a sort with leaves) by the leaves its
condition `leafOK S l = true` allows: `l = T₁ ∨ … ∨ l = Tₙ`, proved by cases on a fresh tag in an
empty context, then one substitution per leaf. `cases l` itself makes one goal per sort of the
definition, each substituting `l` into the configurations of the context. `none`: no closed leaf
condition on `l`. -/
def k2lCasesLeafTag (g : MVarId) (l : FVarId) : MetaM (Option (List MVarId)) := g.withContext do
  let mut cond : Option (Expr × Expr) := none
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless rhs.isConstOf ``Bool.true && lhs.isApp do continue
    let some (.str _ f) := lhs.getAppFn.constName? | continue
    unless f == "leafOK" || f == "leaf" do continue
    unless lhs.appArg! == .fvar l && !lhs.appFn!.hasFVar && !lhs.appFn!.hasMVar do continue
    cond := some (lhs.appFn!, d.toExpr)
    break
  let some (p, hl) := cond | return none
  let lty ← whnfD (← l.getType)
  let .const tn [] := lty | return none
  let some (.inductInfo iv) := (← getEnv).find? tn | return none
  let mut leaves : Array Expr := #[]
  for c in iv.ctors do
    if (← whnfD (mkApp p (mkConst c))).isConstOf ``Bool.true then leaves := leaves.push (mkConst c)
  let some last := leaves.back? | return none
  let disj (x : Expr) : MetaM Expr := do
    let eqs ← leaves.mapM fun t => mkEq x t
    return eqs.pop.foldr (fun e acc => mkOr e acc) (← mkEq x last)
  let stmt ← withLocalDeclD `x lty fun x => do
    withLocalDeclD `hx (← mkEq (mkApp p x) (mkConst ``Bool.true)) fun hx => do
      mkForallFVars #[x, hx] (← disj x)
  let aux ← mkFreshExprMVar stmt
  let (x, ag) ← aux.mvarId!.intro1
  let (_, ag) ← ag.intro1
  for sg in (← ag.cases x) do
    if (← k2lLeafRefuted sg.mvarId) then continue
    unless (← k2lProveDisj sg.mvarId) do return none
  let pr ← instantiateMVars (mkApp2 aux (.fvar l) hl)
  let g1 ← g.assert `k2l_leaf (← disj (.fvar l)) pr
  let (hf, g1) ← g1.intro1
  let mut out : List MVarId := []
  let mut cur := g1
  let mut hcur := hf
  for _ in [0:leaves.size - 1] do
    let subs ← cur.cases hcur
    let some s0 := subs[0]? | return none
    let some s1 := subs[1]? | return none
    let .fvar e0 := s0.fields[0]! | return none
    out := out ++ [← subst s0.mvarId e0]
    let .fvar e1 := s1.fields[0]! | return none
    cur := s1.mvarId
    hcur := e1
  out := out ++ [← subst cur hcur]
  return some out

end

open Lean Meta Elab Tactic in
/-- `cases` on the variable `x`, then on each field of an enumeration type it introduces (the
constructor tag of a sort's nullary constructors). -/
def k2lCasesEnum (g : MVarId) (x : FVarId) : MetaM (List MVarId) := do
  let subs ← g.cases x
  let mut out : List MVarId := []
  for s in subs.toList do
    let mut cur : List MVarId := [s.mvarId]
    for f in s.fields do
      let .fvar fid := f | continue
      let mut next : List MVarId := []
      for g' in cur do
        let isEnum ← g'.withContext do
          let some d := (← getLCtx).find? fid | return false
          let ty ← whnfD d.type
          let .const n _ := ty.getAppFn | return false
          let some (.inductInfo iv) := (← getEnv).find? n | return false
          iv.ctors.allM fun c => do
            let some (.ctorInfo ci) := (← getEnv).find? c | return false
            return ci.numFields == 0
        if isEnum then
          match ← k2lCasesLeafTag g' fid with
          | some gs => next := next ++ gs
          | none => next := next ++ ((← g'.cases fid).toList.map (·.mvarId))
        else
          next := next ++ [g']
      cur := next
    -- the cases that contradict a leaf condition or bind a value of an empty type
    for g' in cur do
      if (← k2lLeafRefuted g') then continue
      if (← k2lEmptyField g' s.fields) then continue
      out := out ++ [← k2lUnfoldSingletons g']
  return out

/-- The free variables of an expression outside binders. -/
partial def k2lFVars (e : Expr) (acc : Array FVarId) : Array FVarId :=
  match e with
  | .fvar x => if acc.contains x then acc else acc.push x
  | .app f a => k2lFVars a (k2lFVars f acc)
  | .mdata _ b => k2lFVars b acc
  | _ => acc

open Lean Meta Elab Tactic in
/-- The variables of term type that occur as arguments in a Boolean equation hypothesis. -/
def k2lSplitCandidates : TacticM (Array FVarId) := withMainContext do
  let mut out : Array FVarId := #[]
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let some (t, lhs, _) := ty.eq? | continue
    let t ← whnf t
    unless t.isConstOf ``Bool || t.isAppOf ``Option do continue
    for x in k2lFVars lhs #[] do
      if out.contains x then continue
      let xty ← whnfR (← inferType (.fvar x))
      if xty.getAppFn.isConst && !(xty.isConstOf ``Bool) && !(xty.isConstOf ``Int) then
        out := out.push x
  return out

/-- `k2l_split_cases [f, …]`: conditions that exclude each other once a variable they test is
fixed to a constructor. Case-split one such variable (and the constructor tag it introduces),
then refute every case by evaluation or arithmetic. -/
syntax "k2l_split_cases" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| k2l_split_cases) => do evalTactic (← `(tactic| k2l_split_cases []))
  | `(tactic| k2l_split_cases [$xs,*]) => do
    -- the functions' own matches: unfold them, split the hypotheses on their discriminants,
    -- refute each branch
    let s0 ← saveState
    try
      evalTactic (← `(tactic| simp only [$xs,*] at *))
      evalTactic (← `(tactic| repeat' (k2l_split_hyps <;> try (first | k2l_refute_eqs | (simp only [reduceCtorEq, Option.some.injEq, Bool.false_eq_true, Bool.true_eq_false] at *; done)))))
      if (← getUnsolvedGoals).isEmpty then return
      s0.restore
    catch _ => s0.restore
    let close ← `(tactic| first
      | k2l_refute_eqs
      | (simp only [$xs,*] at *; done)
      | (simp only [$xs,*] at *; k2l_refute_eqs)
      | k2l_omega [$xs,*]
      -- a partial call evaluated to `some (IntHook.lt a b)`: bind its result, then arithmetic
      | (simp only [$xs,*, Option.some.injEq] at *; subst_vars; k2l_omega))
    -- close `g`, or split one more candidate other than `x` and close every case (conditions
    -- that test two variables, `GAVAIL <Gas G` against `G <=Gas GAVAIL`)
    let closeIn (g : MVarId) : TacticM Bool := do
      setGoals [g]
      try (do evalTactic close; return (← getUnsolvedGoals).isEmpty) catch _ => pure false
    let closeOrSplit (g : MVarId) (x : FVarId) : TacticM Bool := do
      let s ← saveState
      if (← closeIn g) then return true
      s.restore
      setGoals [g]
      for y in (← k2lSplitCandidates) do
        if y == x then continue
        let s' ← saveState
        let ok ← try
            let gs ← k2lCasesEnum g y
            gs.allM closeIn
          catch _ => pure false
        if ok then return true
        s'.restore
      return false
    for x in (← k2lSplitCandidates) do
      let s ← saveState
      let mg ← getMainGoal
      let ok ← try
          let gs ← k2lCasesEnum mg x
          gs.allM (closeOrSplit · x)
        catch _ => pure false
      if ok then
        setGoals []
        return
      s.restore
    throwError "k2l_split_cases: no variable whose cases all close"

/-- For each hypothesis `e = some x` (a partial call bound by a rule) whose `e` evaluates to a
constructor, substitute `x` by its value (`cases`, kept only when it leaves one goal). -/
partial def k2lBindsLoop (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  if (← getGoals).isEmpty then return
  let found ← withMainContext do
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let some (_, lhs, rhs) := ty.eq? | continue
      unless rhs.isAppOfArity ``Option.some 2 && rhs.appArg!.isFVar && !lhs.isFVar do continue
      let s ← saveState
      try
        let h ← Term.exprToSyntax ldecl.toExpr
        evalTactic (← `(tactic| cases $h:term))
        if (← getGoals).length == 1 then return true
        s.restore
      catch _ => s.restore
    return false
  if found then k2lBindsLoop (fuel - 1)

/-- Each round substitutes one bound variable away, so the hypotheses bound the rounds (a rule
that builds a set of eighteen literals binds eighteen partial `concat` calls). -/
elab "k2l_eval_binds" : tactic => do
  if (← getGoals).isEmpty then return
  let n ← withMainContext do return (← getLCtx).foldl (fun n _ => n + 1) 0
  k2lBindsLoop (n + 1)

open Lean Meta Elab Tactic in
/-- `cases` on every equation hypothesis between two constructor applications that leaves one
goal (it identifies a leaf tag with a constant). -/
elab "k2l_cases_ctor_eqs" : tactic => do
  let mut fuel := 16
  while fuel > 0 do
    fuel := fuel - 1
    let found ← withMainContext do
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        let some (_, l, r) := ty.eq? | continue
        unless (← isConstructorApp l) && (← isConstructorApp r) && l != r do continue
        let s ← saveState
        try
          let gs ← (← getMainGoal).cases d.fvarId
          if gs.size == 1 then
            replaceMainGoal (gs.toList.map (·.mvarId))
            return true
          if gs.isEmpty then
            replaceMainGoal []
            return true
          s.restore
        catch _ => s.restore
      return false
    if !found || (← getGoals).isEmpty then return

open Lean Meta Elab Tactic in
/-- A hypothesis without free variables that `decide` refutes (a leaf condition `leafOK S l` at a
leaf `l` of another sort, a comparison of literals). -/
elab "k2l_closed_false" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless !ty.hasFVar && !ty.hasMVar && (← isProp ty) do continue
    let s ← saveState
    try
      let h ← Term.exprToSyntax d.toExpr
      withoutRecover <| evalTactic (← `(tactic| exact absurd $h (by decide +kernel)))
      if (← getGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "k2l_closed_false: no refutable closed hypothesis"

open Lean Meta Elab Tactic in
/-- The variables `x` of the injections `inj_T_A x` in `e`. -/
partial def k2lInjVars (e : Expr) (acc : Array FVarId) : Array FVarId :=
  match e with
  | .app f a =>
    let acc := k2lInjVars f (k2lInjVars a acc)
    match e.getAppFn with
    | .const (.str _ s) _ =>
      if s.startsWith "inj_" then
        match e.getAppArgs.back? with
        | some (.fvar x) => if acc.contains x then acc else acc.push x
        | _ => acc
      else acc
    | _ => acc
  | .mdata _ b => k2lInjVars b acc
  | _ => acc

open Lean Meta Elab Tactic in
/-- The injection constants `inj_T_A` applied in `e`. -/
partial def k2lInjConsts (e : Expr) (acc : Array Name) : Array Name :=
  match e with
  | .app f a => k2lInjConsts f (k2lInjConsts a acc)
  | .const n@(.str _ s) _ => if s.startsWith "inj_" && !acc.contains n then acc.push n else acc
  | .mdata _ b => k2lInjConsts b acc
  | _ => acc

open Lean Meta Elab Tactic in
/-- `k2l_leaf_split` at the variable `x`: the goals it leaves. -/
def k2lLeafSplitAt (g : MVarId) (x : FVarId)
    (extra : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) : TacticM (List MVarId) := do
  -- the side conditions that mention `x`: only these are unfolded and split
  let hs ← g.withContext do
    let mut acc : Array Name := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      -- the side conditions (`… = true`, `… = false`) only
      let some (_, _, rhs) := ty.eq? | continue
      unless rhs.isConstOf ``Bool.true || rhs.isConstOf ``Bool.false do continue
      if ty.containsFVar x then acc := acc.push d.userName
    return acc
  -- the predicates unfolded first, with the injection algebra (a projection of an injection of
  -- disjoint leaves is `none`), before `x` is split
  setGoals [g]
  if !extra.isEmpty && !hs.isEmpty then
    let locs := hs.map mkIdent
    try evalTactic (← `(tactic| simp only [$extra,*] at $locs*)) catch _ => pure ()
  let [g] ← getUnsolvedGoals | return []
  let gs ← g.cases x
  let mut out : List MVarId := []
  for sg in gs do
    let g' := sg.mvarId
    -- the constructors of the family other than the leaf injection have an empty tag type here
    let empty ← g'.withContext do
      for f in sg.fields do
        let .fvar fid := f | continue
        let some d := (← getLCtx).find? fid | continue
        let ty ← whnfD d.type
        let .const n _ := ty.getAppFn | continue
        if let some (.inductInfo iv) := (← getEnv).find? n then
          if iv.ctors.isEmpty then return some fid
      return none
    if let some fid := empty then
      if (← g'.cases fid).isEmpty then continue
    setGoals [g']
    let locs := hs.map mkIdent
    -- unfold the injections the side conditions apply, in rounds: an injection function unfolds to
    -- the constructor abbreviation `SortS.inj_T`, which is itself unfolded in the next round, so
    -- that both sides of an equation are `Term.inj` applications
    let mut seen : Array Name := #[]
    for _ in [0:3] do
      let some cur := (← getUnsolvedGoals).head? | break
      let names ← cur.withContext do
        let mut acc := #[]
        for n in hs do
          let some d := (← getLCtx).findFromUserName? n | continue
          acc := k2lInjConsts (← instantiateMVars d.type) acc
        return acc
      let fresh := names.filter (!seen.contains ·)
      if fresh.isEmpty && !seen.isEmpty then break
      seen := seen ++ fresh
      let lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
        seen.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
      -- `==K` unfolds to `decide (a = b)`: read it as the equation, which `injections` takes apart
      let lemmas := lemmas ++ extra ++
        #[← `(Lean.Parser.Tactic.simpLemma| k2lDecideEqTrue), ← `(Lean.Parser.Tactic.simpLemma| k2lDecideEqFalse)]
      try evalTactic (← `(tactic| simp only [$lemmas,*] at $locs*)) catch _ => pure ()
    let gs' ← getUnsolvedGoals
    if gs'.isEmpty then continue
    -- split the matches of those hypotheses
    let mut work : List MVarId := gs'
    let mut done : List MVarId := []
    let mut fuel := 64
    while !work.isEmpty && fuel > 0 do
      fuel := fuel - 1
      let cur := work.head!
      work := work.tail!
      let fields := sg.fields.filterMap fun f => if let .fvar i := f then some i else none
      let r ← cur.withContext do
        for d in (← getLCtx) do
          if d.isImplementationDetail then continue
          -- a side condition, or an equation `split` introduced, about the injected value
          let ty ← instantiateMVars d.type
          unless hs.contains d.userName || fields.any (ty.containsFVar ·) do continue
          let r ← try Lean.Meta.splitLocalDecl? cur d.fvarId catch _ => pure none
          if let some gs := r then return some gs
        return none
      match r with
      | some gs => work := gs ++ work
      | none => done := done ++ [cur]
    for g'' in done ++ work do
      setGoals [g'']
      try evalTactic (← `(tactic| first | k2l_closed_false | (injections; k2l_cases_ctor_eqs; k2l_closed_false) | (simp only [Bool.false_eq_true, Bool.true_eq_false, reduceCtorEq] at *; done) | (simp_all; done))) catch _ => pure ()
      out := out ++ (← getUnsolvedGoals)
  return out

open Lean Meta Elab Tactic in
/-- A sort predicate (a function whose equations test the leaf of their argument) at the injection
of a variable `x` of another sort: `cases x` (the value of a sort with leaves is the injection of a
leaf value), unfold the injections, so that the predicate's `match` tests the leaf tag, and split
it; each branch that matches another sort's leaf contradicts `x`'s leaf condition. -/
syntax "k2l_leaf_split" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| k2l_leaf_split $[[$extra,*]]?) => do
  let extra : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := (extra.map (·.getElems)).getD #[]
  let g ← getMainGoal
  let rest := (← getGoals).tail
  -- the candidates: the injected variables of the side conditions first (the refutation is about
  -- their leaves), then those of the other hypotheses
  let xs ← g.withContext do
    let mut side := #[]
    let mut all := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let isSide := match ty.eq? with
        | some (_, _, rhs) => rhs.isConstOf ``Bool.true || rhs.isConstOf ``Bool.false
        | none => false
      if isSide then side := k2lInjVars ty side
      all := k2lInjVars ty all
    return (all, side ++ all.filter (!side.contains ·))
  let (all, cands) := xs
  let some x0 := all[0]? | throwError "k2l_leaf_split: no injected variable"
  let s0 ← saveState
  for x in cands[:4] do
    s0.restore
    setGoals [g]
    let out ← k2lLeafSplitAt g x extra
    if out.isEmpty then
      setGoals rest
      return
  -- none closes: the goals of the first injected variable
  s0.restore
  setGoals [g]
  let out ← k2lLeafSplitAt g x0 extra
  setGoals (out ++ rest)

/-- The closer of last resort for two side conditions that exclude each other through the
theories of their atoms: identify what two matches of one pattern bind (list heads and tails,
cell-map values, partial calls), evaluate the partial calls whose value reduces, substitute
collections equated to their unit, rule out a list pattern against `.List` and a variable in two
disjoint sets of literals (`k2l_set_lits`), and read the side conditions as propositions
(`k2l_prop`) with the facts on byte and string lengths. -/
macro "k2l_theory" : tactic => `(tactic| (
  (try k2l_list_fundep) <;>
  k2l_list_facts <;>
  k2l_map_facts <;>
  k2l_det_fundep <;>
  (try k2l_subst_units) <;>
  (try simp only [KPrelude.ListHook.concat_element_eq_unit_iff, KPrelude.ListHook.unit_eq_concat_element_iff,
    KPrelude.ListHook.concat_element_right_eq_unit_iff, KPrelude.ListHook.unit_eq_concat_element_right_iff] at *) <;>
  (try k2l_eval_binds) <;>
  first
    | done
    | k2l_refute_eqs
    | k2l_set_lits
    | ((try subst_vars) <;>
       (try k2l_prop_norm) <;>
       (try k2l_split_ands) <;>
       (try subst_vars) <;>
       first | done | k2l_set_lits | k2l_closed_false | omega | (simp_all; done) | (simp_all; omega))))


/-- Two literals that differ: substitute the variables equated to literals, then refute an
equation between literals by `decide`. -/
elab "k2l_lits" : tactic => do
  evalTactic (← `(tactic| subst_vars))
  withMainContext do
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      unless ty.isEq && !ty.hasFVar && !ty.hasMVar do continue
      let s ← saveState
      try
        let h ← Term.exprToSyntax ldecl.toExpr
        withoutRecover <| evalTactic (← `(tactic| exact absurd $h (by decide)))
        if (← getGoals).isEmpty then return
        s.restore
      catch _ => s.restore
    throwError "k2l_lits: no equation between different literals"

/-- `k2l_eval [f, …]`: a requires that evaluates to `false` under the other rule's match.
Refute it by `cases` on an equation hypothesis; otherwise replace projected variables by
injections and evaluate with the injection algebra, the Boolean connectives and the definitions
`f, …` (the functions the two requires call), then refute. -/
syntax "k2l_eval" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| k2l_eval) => `(tactic| k2l_eval [])
  | `(tactic| k2l_eval [$xs,*]) => `(tactic| first
    | k2l_guard k2l_refute_eqs
    | k2l_guard (k2l_eval_binds; k2l_refute_eqs)
    | k2l_guard (k2l_eval_binds; k2l_lits)
    | k2l_guard (k2l_proj_inv; first
        | k2l_refute_eqs
        | (simp only [k2l_det_alg, KPrelude.BoolHook.and, KPrelude.BoolHook.not, KPrelude.BoolHook.or,
            Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_true, Bool.true_or,
            Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false,
            Bool.false_eq_true, Bool.true_eq_false, reduceCtorEq, Option.some.injEq, $xs,*] at *; done)
        | (simp only [k2l_det_alg, $xs,*] at *; k2l_refute_eqs)
        | (simp only [k2l_det_alg, Option.some.injEq, $xs,*] at *; subst_vars;
           simp only [KPrelude.BoolHook.and, KPrelude.BoolHook.not, KPrelude.BoolHook.or, Bool.and_true,
             Bool.true_and, Bool.and_false, Bool.false_and, Bool.not_true, Bool.not_false,
             Bool.false_eq_true, Bool.true_eq_false, reduceCtorEq] at *; done))
    | k2l_guard (k2l_proj_inv; simp only [k2l_det_alg] at *; k2l_leaf_split [k2l_det_alg, KPrelude.BoolHook.or, KPrelude.BoolHook.and, KPrelude.BoolHook.not, $xs,*]; done)
    | k2l_guard k2l_theory
    | k2l_guard (k2l_proj_inv; simp only [k2l_det_alg, $xs,*] at *; k2l_theory))

open Lean Meta Elab Tactic in
/-- A partial call bound by a rule, `e = some x`, whose arguments are all literals and whose value
the kernel computes to be `none`: the rule has no step there. -/
elab "k2l_undef_bind" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless rhs.isAppOfArity ``Option.some 2 && !lhs.hasMVar do continue
    -- closed but for instances (`[Hooks]`, which the evaluation does not reach)
    let mut closed := true
    for x in (collectFVars {} lhs).fvarIds do
      if (← isClass? (← x.getType)).isNone then closed := false
    unless closed do continue
    let s ← saveState
    try
      let h ← Term.exprToSyntax d.toExpr
      let e ← Term.exprToSyntax lhs
      withoutRecover <| evalTactic (← `(tactic|
        exact absurd (Eq.trans (Eq.symm $h) (show $e = none by decide +kernel)) (Option.some_ne_none _)))
      if (← getGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "k2l_undef_bind: no bound call that evaluates to none"

/-- `k2l_undef [f, …]`: one rule's result is undefined where both rules apply. Substitute the
literals the other rule's pattern fixes, then refute the bound call by evaluating it to `none`;
otherwise evaluate as `k2l_eval` does. -/
syntax "k2l_undef" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| k2l_undef) => `(tactic| k2l_undef [])
  | `(tactic| k2l_undef [$xs,*]) => `(tactic| first
    | k2l_guard ((try subst_vars); k2l_undef_bind)
    | k2l_eval [$xs,*])

/-- `k2l_smt [f, …]`: side conditions the classifier separated by arithmetic (z3, every other
subterm an atom): `omega` after the hooks are unfolded, after identifying repeated partial calls,
then with `f, …` unfolded too, then evaluation. -/
syntax "k2l_smt" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| k2l_smt) => `(tactic| k2l_smt [])
  | `(tactic| k2l_smt [$xs,*]) => `(tactic| first
    | k2l_guard k2l_omega
    | k2l_guard (k2l_det_fundep; k2l_omega)
    | k2l_guard k2l_theory
    | k2l_guard (k2l_det_fundep; k2l_omega [$xs,*])
    | k2l_guard k2l_eval [$xs,*]
    | k2l_guard k2l_bool_cases
    | k2l_guard (k2l_det_fundep; k2l_bool_cases)
    | k2l_guard (simp_all [KPrelude.KEqHook.eq, KPrelude.KEqHook.ne, KPrelude.IntHook.eq, KPrelude.IntHook.ne,
        KPrelude.IntHook.lt, KPrelude.IntHook.le, KPrelude.IntHook.gt, KPrelude.IntHook.ge, k2lDecideEqTrue,
        k2lDecideEqFalse, $xs,*]; done)
    | k2l_guard (simp_all [KPrelude.KEqHook.eq, KPrelude.KEqHook.ne, KPrelude.IntHook.eq, KPrelude.IntHook.ne,
        KPrelude.IntHook.lt, KPrelude.IntHook.le, KPrelude.IntHook.gt, KPrelude.IntHook.ge, k2lDecideEqTrue,
        k2lDecideEqFalse, $xs,*]; omega))


/-! ## Splitting a left-hand side by the sort of its first `<k>` item

A rule whose first `<k>` item is a variable of a sort `S` (`G:Gas ~> #deductGas`) has no key of
its own: its key is the key of whatever value of `S` the configuration holds. Its determinism
lemma first replaces the item by the injection of that value (`inj_S_KItem G`) and then splits
`G` by its leaf (and, below an injection whose key names the injected constructor, by that
constructor) until the key reduces, so that each case inverts only the rules of one key. -/

/-- Whether `e` reduces to a constructor application. -/
def k2lReducesToCtor (e : Expr) : MetaM Bool := do
  let e ← whnfD e
  return (← isConstructorApp e) || (e.isAppOf ``False)

/-- The names of the fields of a case of `cases` that are values of an inductive family with
non-enumeration constructors (the candidates for a further split). -/
def k2lTermFields (g : MVarId) (fields : Array Expr) : MetaM (List Name) := g.withContext do
  let mut out : List Name := []
  for f in fields do
    let .fvar fid := f | continue
    let some d := (← getLCtx).find? fid | continue
    let ty ← whnfD d.type
    if (← isProp ty) then continue
    let .const n _ := ty.getAppFn | continue
    let some (.inductInfo iv) := (← getEnv).find? n | continue
    let enum ← iv.ctors.allM fun c => do
      let some (.ctorInfo ci) := (← getEnv).find? c | return false
      return ci.numFields == 0
    unless enum do out := out ++ [d.userName]
  return out

/-- Whether the key argument of the hypothesis `h : REL key c c'` reduces to a constructor. -/
def k2lKeyReduces (g : MVarId) (h : Name) : MetaM Bool := g.withContext do
  let some hd := (← getLCtx).findFromUserName? h | throwError "k2l_key_cases: no hypothesis {h}"
  let ty ← instantiateMVars hd.type
  let some k := ty.getAppArgs[0]? | throwError "k2l_key_cases: {h} has no key argument"
  k2lReducesToCtor k

/-- Case-split the variables named `cands` (and the fields their cases introduce) until the key
argument of the hypothesis `h : REL key c c'` reduces to a constructor; cases that contradict a
leaf condition are dropped. With `singletons`, before each split the variables that are values of
a builtin leaf are replaced by that leaf's constructor (`k2lUnfoldSingletons`), which makes no
case: a key that matches a builtin argument (`#mkArray(_, N:Int)`, whose `N` is the field
`Term.b_SortInt n` of the constructor) reduces without splitting the other arguments. -/
partial def k2lKeyCasesGo (g : MVarId) (h : Name) (cands : List Name) (fuel : Nat)
    (singletons : Bool := false) : MetaM (List MVarId) := do
  if (← k2lKeyReduces g h) then return [g]
  if singletons then
    let s ← saveState
    let g' ← k2lUnfoldSingletons g (reduceIndex := true)
    if g' != g && (← k2lKeyReduces g' h) then return [g']
    s.restore
  if fuel = 0 then throwError "k2l_key_cases: the key does not reduce"
  match cands with
  | [] => throwError "k2l_key_cases: the key does not reduce after the splits"
  | x :: rest =>
    let some xd ← g.withContext (return (← getLCtx).findFromUserName? x)
      | k2lKeyCasesGo g h rest fuel singletons
    let subs ← g.cases xd.fvarId
    let mut out : List MVarId := []
    for s in subs do
      let more ← k2lTermFields s.mvarId s.fields
      -- the enumeration fields (a constructor or leaf tag): split them too
      let mut cur : List MVarId := [s.mvarId]
      for f in s.fields do
        let .fvar fid := f | continue
        let some fname ← s.mvarId.withContext (return ((← getLCtx).find? fid).map (·.userName))
          | continue
        let mut next : List MVarId := []
        for g' in cur do
          let isEnum ← g'.withContext do
            let some d := (← getLCtx).findFromUserName? fname | return none
            let ty ← whnfD d.type
            let .const n _ := ty.getAppFn | return none
            let some (.inductInfo iv) := (← getEnv).find? n | return none
            let e ← iv.ctors.allM fun c => do
              let some (.ctorInfo ci) := (← getEnv).find? c | return false
              return ci.numFields == 0
            return if e && !iv.ctors.isEmpty then some d.fvarId else none
          match isEnum with
          | some fv =>
            match ← k2lCasesLeafTag g' fv with
            | some gs => next := next ++ gs
            | none => next := next ++ ((← g'.cases fv).toList.map (·.mvarId))
          | none => next := next ++ [g']
        cur := next
      for g' in cur do
        if (← k2lLeafRefuted g') then continue
        -- a field of an empty type (the constructors of the family other than the leaf
        -- injection, at a sort with leaves): `cases` on it, not `contradiction`, which inspects
        -- every hypothesis of the context (each a configuration) and costs seconds per case
        if (← k2lEmptyField g' s.fields) then continue
        if (← try g'.contradiction; pure true catch _ => pure false) then continue
        out := out ++ (← k2lKeyCasesGo g' h (more ++ rest) (fuel - 1) singletons)
    return out

/-- `k2l_key_cases h [x, …]`: split the variables `x, …` of the main goal until the key of
`h : REL (Det.key c) c c'` reduces (`k2lKeyCasesGo`), so that `cases h` inverts one key's
relation in each case. When that search fails, it is repeated from the start with the builtin
leaves replaced before each split; a search that succeeds is the first one, unchanged. -/
elab "k2l_key_cases " h:ident " [" xs:ident,* "]" : tactic => do
  let g ← getMainGoal
  let cs := xs.getElems.toList.map (·.getId)
  let s ← saveState
  let gs ← try k2lKeyCasesGo g h.getId cs 4
    catch e => do
      s.restore
      try k2lKeyCasesGo g h.getId cs 4 (singletons := true) catch _ => throw e
  replaceMainGoal gs

/-- `k2l_gen_index h`: for `h : R c c'` (after unfolding the key's relation to the inductive one),
replace the configuration `c` by a variable `k2l_c` with the equation `k2l_hc : c = k2l_c`, so
that `cases h` leaves the unification of the two left-hand sides to `cases k2l_hc`, or to a
disjointness lemma that takes the equation as it is. -/
elab "k2l_gen_index " h:ident : tactic => withMainContext do
  let some d := (← getLCtx).findFromUserName? h.getId | throwError "k2l_gen_index: no {h.getId}"
  let ty ← whnfD (← instantiateMVars d.type)
  let g ← (← getMainGoal).replaceLocalDeclDefEq d.fvarId ty
  replaceMainGoal [g]
  let args := ty.getAppArgs
  -- `False` (a key without rules): nothing to generalize, `cases` closes the goal
  let some c := args[args.size - 2]? | return
  let cs ← Term.exprToSyntax c
  -- the names are the user's (no macro scopes): the certificates refer to `k2l_hc`
  evalTactic (← `(tactic| generalize $(mkIdent `k2l_hc) : $cs = $(mkIdent `k2l_c) at $h:ident))

/-! ## Closers used by every generated determinism proof -/

/-- Equal right-hand sides under both matches. -/
macro "k2l_join" : tactic => `(tactic| first | k2l_self | (simp_all; done))

/-- Every closer in turn, with a warning: a goal the classification did not predict. -/
macro "k2l_fallback" : tactic => `(tactic| (k2l_warn_fallback; first
  | k2l_guard k2l_self
  | k2l_guard k2l_refute_eqs
  | k2l_guard k2l_bool_cases
  | k2l_guard k2l_eval
  | k2l_guard k2l_omega
  | k2l_guard (k2l_map_facts; simp_all; done)
  | k2l_guard (k2l_proj_inv; simp_all [k2l_det_alg]; done)
  | k2l_guard (exfalso; k2l_theory)
  | k2l_guard (exfalso; k2l_proj_inv; simp only [k2l_det_alg] at *; k2l_theory)))

/-- The certificate of a goal the classification puts in the clash class: an equation
hypothesis whose sides are different constructors (otherwise the fallback). -/
macro "k2l_default" : tactic => `(tactic| (k2l_note_default; first | k2l_refute_eqs | (exfalso; k2l_list_facts; k2l_det_fundep; k2l_map_facts; k2l_det_fundep; first | done | k2l_refute_eqs | k2l_lits) | k2l_guard (exfalso; k2l_theory) | k2l_fallback))

/-! ## Overlaps are real

Each listed pair is witnessed (`Overlap.Witnessed`): at some configuration both rules step, to
different configurations, and both steps are steps of the definition's relation. So the list
holds no pair that is in fact separated (never both applicable) or joinable (both applicable,
with one result): it is exactly the definition's nondeterminism, not a classifier's opinion. -/

namespace DetEval

open Lean Meta

/-- A definition by well-founded recursion. The kernel does not unfold it: its fixpoint reduces
only through the accessibility proof of its measure, which does not reduce to a constructor.
Its unfolding equation (`f.eq_def`) holds all the same, so evaluation rewrites with it. -/
def isWFRec (env : Environment) (c : Name) : Bool := Elab.WF.eqnInfoExt.contains env c

/-- `whnf` at full transparency that leaves the definitions by well-founded recursion folded,
so that an evaluation stuck on one shows the call. -/
def whnfB (e : Expr) : MetaM Expr := do
  let env ← getEnv
  withTransparency .all <| withCanUnfoldPred (fun _ info => pure !(isWFRec env info.name)) (whnf e)

def isWFCall (e : Expr) : MetaM Bool := do
  let .const c _ := e.getAppFn | return false
  return isWFRec (← getEnv) c

/-- A head normal form below which evaluation does not continue. -/
def isValue (e : Expr) : MetaM Bool := do
  match e with
  | .lit _ | .lam .. | .sort _ | .forallE .. => return true
  | _ => match e.getAppFn with
    | .const c _ => return (← getEnv).isConstructor c
    | _ => return false

structure St where
  steps : Nat := 0
  limit : Nat
  /-- How many times each definition by well-founded recursion was unfolded. -/
  unfolded : Std.HashMap Name Nat := {}
  /-- `fuelOf` per definition (`none`: in a mutual block). -/
  fuels : Std.HashMap Name (Option (Expr × Expr)) := {}
  /-- Whether a constant's definition reaches a definition by well-founded recursion. -/
  reach : Std.HashMap Name Bool := {}

abbrev EvM := StateRefT St MetaM


/-- `e = c` from `e = b` and `b = c`, each `none` when it holds by reduction. -/
def trans? (e b c : Expr) (h₁ h₂ : Option Expr) : MetaM (Option Expr) := do
  match h₁, h₂ with
  | none, none => return none
  | some h, none | none, some h => return some h
  | some h₁, some h₂ =>
    let α ← inferType e
    return some (mkApp6 (mkConst ``Eq.trans [← getLevel α]) α e b c h₁ h₂)

/-- The call `w` of a definition by well-founded recursion, unfolded once by its unfolding
equation: the body at the arguments and the proof of `w = body`. -/
def unfoldWF (w : Expr) : MetaM (Expr × Expr) := do
  let .const c us := w.getAppFn | throwError "k2l_decide: not a call"
  let some eqn ← getUnfoldEqnFor? c (nonRec := true)
    | throwError "k2l_decide: no unfolding equation for {c}"
  let eqThm := mkConst eqn us
  let ty ← inferType eqThm
  let n := ty.getForallArity
  let args := w.getAppArgs
  unless n ≤ args.size do throwError "k2l_decide: {c} is not fully applied"
  let some (_, _, rhs) := (← instantiateForall ty (args.extract 0 n)).eq?
    | throwError "k2l_decide: unexpected unfolding equation of {c}"
  let mut h := mkAppN eqThm (args.extract 0 n)
  let mut r := rhs
  for a in args.extract n args.size do
    h ← mkCongrFun h a
    r := mkApp r a
  return (r, h)

/-- The proof `a : P[d]` as a proof of `P[x]`, along `hx : d = x` (`P` a proposition, `x` a free
variable). Built without unification, whose reduction does not see through a call by
well-founded recursion. -/
def castProof (x hx a P : Expr) (d : Expr) : MetaM Expr := do
  let α ← inferType x
  let Pfn ← mkLambdaFVars #[x] P
  let eq := mkApp6 (mkConst ``congrArg [← getLevel α, Level.one]) α (mkSort Level.zero) d x Pfn hx
  return mkApp4 (mkConst ``Eq.mp [Level.zero]) (P.replaceFVar x d) P eq a

/-- The argument `a : T[d]` as an argument of type `T[x]`, along `hx : d = x`: a proof is cast; a
function whose binders mention `x` only in hypotheses (the alternatives of a case analysis,
which receive `d = pattern`) is wrapped so that it casts those hypotheses back. -/
def castArg (x hx d a T : Expr) : MetaM Expr := do
  if ← isProp T then return ← castProof x hx a T d
  forallTelescopeReducing T fun ys body => do
    if (← whnfR body).containsFVar x.fvarId! then
      throwError "k2l_decide: an argument's type depends on the rewritten subterm"
    let hx' ← mkEqSymm hx
    let mut ys' := #[]
    for y in ys do
      let ty ← inferType y
      if ty.containsFVar x.fvarId! then
        unless ← isProp ty do throwError "k2l_decide: a binder's type depends on the rewritten subterm"
        -- `y : P[x]` back to `P[d]`: cast along `x = d`, with `d` abstracted
        let Pfn ← withLocalDeclD `z (← inferType x) fun z => do
          mkLambdaFVars #[z] (ty.replaceFVar x z)
        let eq := mkApp6 (mkConst ``congrArg [← getLevel (← inferType x), Level.one]) (← inferType x)
          (mkSort Level.zero) x d Pfn hx'
        ys' := ys'.push (mkApp4 (mkConst ``Eq.mp [Level.zero]) ty (ty.replaceFVar x d) eq y)
      else
        ys' := ys'.push y
    mkLambdaFVars ys (mkAppN a ys')

/-- `w = w'` where `w` is `f a₀ … aᵢ … aₙ` and `w'` has `v` in place of `aᵢ`, from `h : aᵢ = v`:
by `Eq.rec` on `h`, generalizing position `i`; an argument after it whose expected type mentions
position `i` is cast (`castArg`: a `match h : d with` compiles to a case analysis of `d` applied
to `rfl : d = d`, whose expected type becomes `d = x`, and may pass its alternatives, which
receive `d = pattern`, as further arguments). The type of the whole must not depend on position
`i`; at `v := aᵢ` the generalized term is `w` up to proof irrelevance and η. -/
def rewriteArg (w : Expr) (i : Nat) (v h : Expr) : MetaM (Expr × Expr) := do
  let f := w.getAppFn
  let args := w.getAppArgs
  let d := args[i]!
  let α ← inferType d
  withLocalDeclD `x α fun x => do
  withLocalDeclD `hx (← mkEq d x) fun hx => do
    let mut cur := mkAppN f ((args.extract 0 i).push x)
    for k in [i+1:args.size] do
      let ty ← whnf (← inferType cur)
      let .forallE _ dom _ _ := ty | throwError "k2l_decide: unexpected argument at {f}"
      let a := args[k]!
      if dom.containsFVar x.fvarId! then
        cur := mkApp cur (← castArg x hx d a dom)
      else
        cur := mkApp cur a
    let ty ← whnfR (← instantiateMVars (← inferType cur))
    if ty.containsFVar x.fvarId! then
      throwError "k2l_decide: the type of {f} depends on the rewritten argument"
    let motive ← mkLambdaFVars #[x, hx] (← mkEq w cur)
    let u ← getLevel α
    let refl ← mkEqRefl w
    let pf := mkApp6 (mkConst ``Eq.rec [Level.zero, u]) α d motive refl v h
    let w' := (← instantiateMVars cur).replaceFVars #[x, hx] #[v, h]
    return (w', ← mkExpectedTypeHint pf (← mkEq w w'))

/-- For `f` defined by well-founded recursion alone (not in a mutual block), with unfolding
equation `f xs = body[f, xs]`: the iteration `fuel n := Nat.rec f (fun _ g => F g) n` of its
functional `F := fun g xs => body[g, xs]`, as a function of `n`, and the proof of
`∀ n, fuel n = f` (by induction on `n`: `F f = f` is the unfolding equation, by extensionality).
`fuel n` reduces by `Nat.rec` alone, so the kernel evaluates a call of `fuel N` whose recursion
is at most `N` deep, where it does not evaluate `f`. -/
def fuelOf (fC : Expr) : MetaM (Option (Expr × Expr)) := do
  let .const c us := fC | return none
  let some info := Elab.WF.eqnInfoExt.find? (← getEnv) c | return none
  unless info.declNames.size == 1 do return none
  let some eqn ← getUnfoldEqnFor? c (nonRec := true) | return none
  let eqC := mkConst eqn us
  let T ← inferType fC
  let uT ← getLevel T
  let eqTy ← inferType eqC
  let F ← withLocalDeclD `g T fun g => forallTelescope eqTy fun xs eq => do
    let some (_, _, body) := eq.eq? | throwError "k2l_decide: unexpected unfolding equation of {c}"
    mkLambdaFVars #[g] (← mkLambdaFVars xs (body.replace fun e => if e == fC then some g else none))
  let hF ← forallTelescope eqTy fun xs _ => do
    let mut h ← mkEqSymm (mkAppN eqC xs)
    for x in xs.reverse do
      h ← mkFunExt (← mkLambdaFVars #[x] h)
    mkExpectedTypeHint h (← mkEq (mkApp F fC) fC)
  let nat := mkConst ``Nat
  let fuelAt (n : Expr) : Expr :=
    mkApp4 (mkConst ``Nat.rec [uT]) (.lam `n nat T .default) fC
      (.lam `n nat (.lam `g T (mkApp F (.bvar 0)) .default) .default) n
  let fuel ← withLocalDeclD `n nat fun n => mkLambdaFVars #[n] (fuelAt n)
  let hFuel ← withLocalDeclD `n nat fun n => do
    let motive ← withLocalDeclD `m nat fun m => do mkLambdaFVars #[m] (← mkEq (fuelAt m) fC)
    let succ ← withLocalDeclD `m nat fun m => do
      withLocalDeclD `ih (← mkEq (fuelAt m) fC) fun ih => do
        let step := mkApp6 (mkConst ``congrArg [uT, uT]) T T (fuelAt m) fC F ih
        mkLambdaFVars #[m, ih]
          (mkApp6 (mkConst ``Eq.trans [uT]) T (mkApp F (fuelAt m)) (mkApp F fC) fC step hF)
    mkLambdaFVars #[n] (mkApp4 (mkConst ``Nat.rec [Level.zero]) motive (← mkEqRefl fC) succ n)
  return some (fuel, hFuel)

/-- The kernel's head normal form of `w` when it is a value: the elaborator's reduction stops
at terms the kernel reduces (a function of a string literal). -/
def kernelValue? (w : Expr) : MetaM (Option Expr) := do
  match Kernel.whnf (← getEnv) (← getLCtx) w with
  | .ok r => return if ← isValue r then some r else none
  | .error _ => return none

/-- Whether unfolding `c` can reach a definition by well-founded recursion (through the values of
definitions, not of theorems). -/
partial def reachesWF (c : Name) : EvM Bool := do
  if let some b := (← get).reach[c]? then return b
  let env ← getEnv
  if isWFRec env c then
    modify fun s => { s with reach := s.reach.insert c true }
    return true
  -- provisionally `false`, which a cycle of definitions sees
  modify fun s => { s with reach := s.reach.insert c false }
  let some (.defnInfo d) := env.find? c | return false
  for x in d.value.getUsedConstants do
    if ← reachesWF x then
      modify fun s => { s with reach := s.reach.insert c true }
      return true
  return false

def mayReachWF (e : Expr) (except : Name := .anonymous) : EvM Bool :=
  e.getUsedConstants.anyM fun c => if c == except then pure false else reachesWF c

/-- `kernelValue?` for a term that cannot reach a definition by well-founded recursion: on one
that can, the kernel may try to reduce the fixpoint through its accessibility proof, which
reduces, if at all, in time quadratic in the recursion's depth. -/
def safeKernelValue? (e : Expr) : EvM (Option Expr) := do
  if ← mayReachWF e then return none
  kernelValue? e

/-- The value of `a` in the kernel, its constructor fields evaluated in turn, except the
recursive ones (the tail of a list stays as it is); `a` itself when the kernel does not reach a
value. -/
partial def kernelNF (a : Expr) : MetaM Expr := do
  let some r ← kernelValue? a | return a
  let .const c _ := r.getAppFn | return r
  let some (.ctorInfo ci) := (← getEnv).find? c | return r
  let mut args := r.getAppArgs
  for i in [ci.numParams:args.size] do
    let x := args[i]!
    if (← isProof x) || (← isType x) then continue
    if (← whnfR (← inferType x)).getAppFn.constName? == some ci.induct then continue
    args := args.set! i (← kernelNF x)
  return mkAppN r.getAppFn args

/-- `p`, by the kernel's evaluation of its `Decidable` instance; the auxiliary theorem is checked
when it is added, so a failure is reported here. `zetaDelta` keeps the closure from type checking
the proof in the elaborator first, whose reduction is slower than the kernel's and does not
unfold a `match` stuck on a call by well-founded recursion. -/
def kernelDecide (p : Expr) : MetaM Expr := do
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  let refl := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
  withOptions (Elab.async.set · false) <| mkAuxTheorem (zetaDelta := true) p (mkApp3 (mkConst ``of_decide_eq_true) p inst refl)

mutual

/-- Evaluate the closed `e` to a head normal form `v`, with a proof of `e = v` (`none` when `e`
reduces to `v`): reduce as the kernel does; unfold a call of a definition by well-founded
recursion by its unfolding equation; at a recursor stuck on its major premise (a `match` is
unfolded to its case analysis first) or a projection stuck on its structure, evaluate that
subterm and rewrite it by the equation found; at any other head, evaluate the arguments that
may reach such a call (`evArgs`). -/
partial def ev (e : Expr) : EvM (Expr × Option Expr) := do
  modify fun s => { s with steps := s.steps + 1 }
  let s ← get
  if s.steps > s.limit then
    throwError "k2l_decide: evaluation budget ({s.limit} steps) exhausted at {e.getAppFn}; unfolded {s.unfolded.toList}"
  -- the kernel first where it cannot reach a definition by well-founded recursion: it is far
  -- faster than the elaborator (literals, long lists)
  if let some r ← safeKernelValue? e then return (r, none)
  let some w ← tryCatchRuntimeEx (some <$> whnfB e) (fun ex =>
      if ex.isMaxRecDepth then pure none else throw ex)
    | do
      -- the elaborator's `whnf` recurses once per step of a long computation that reaches no
      -- definition by well-founded recursion (`List.length` of a long list under a comparison):
      -- the kernel evaluates such arguments, the others are evaluated here
      let (e', h) ← evArgs e (kernel := true)
      if e' == e then throwError "k2l_decide: evaluation too deep at {e.getAppFn}"
      let (v, h₂) ← ev e'
      return (v, ← trans? e e' v h h₂)
  if ← isValue w then return (w, none)
  if ← isWFCall w then
    let .const c _ := w.getAppFn | unreachable!
    modify fun s => { s with unfolded := s.unfolded.insert c (s.unfolded.getD c 0 + 1) }
    -- the kernel evaluates the call through its iteration `fuel N` (`fuelOf`)
    let fu ← match (← get).fuels[c]? with
      | some fu => pure fu
      | none => do
        let fu ← fuelOf w.getAppFn
        modify fun s => { s with fuels := s.fuels.insert c fu }
        pure fu
    let args := w.getAppArgs
    -- only where the kernel's evaluation reaches no other such definition (`safeKernelValue?`);
    -- `2^20` bounds the depth of the recursion
    if let some (fuel, hFuel) := fu then
      if !(← args.anyM (mayReachWF ·)) && !(← mayReachWF fuel c) then
        let n := mkRawNatLit 1048576
        let rhs := mkAppN (fuel.beta #[n]) args
        if let some v ← kernelValue? rhs then
          let T ← inferType w.getAppFn
          let β ← inferType w
          let app ← withLocalDeclD `g T fun g => mkLambdaFVars #[g] (mkAppN g args)
          -- `fuel N args = f args`, reversed
          let h := mkApp6 (mkConst ``congrArg [← getLevel T, ← getLevel β]) T β
            (fuel.beta #[n]) w.getAppFn app (hFuel.beta #[n])
          return (v, some (← mkExpectedTypeHint (← mkEqSymm h) (← mkEq e v)))
    let (rhs, h₁) ← unfoldWF w
    let (v, h₂) ← ev rhs
    return (v, ← trans? e rhs v (some h₁) h₂)
  if let .proj _ _ b := w then
    let (bv, hb) ← ev b
    let some hb := hb | do
      if let some r ← safeKernelValue? w then return (r, none)
      throwError "k2l_decide: evaluation stuck at a projection"
    let x ← mkFreshUserName `x
    let motive := Expr.lam x (← inferType b) (w.updateProj! (.bvar 0)) .default
    let hstep ← mkCongrArg motive hb
    let w' := w.updateProj! bv
    let (v, h₂) ← ev w'
    return (v, ← trans? e w' v (some hstep) h₂)
  let .const c us := w.getAppFn | do
    if let some r ← safeKernelValue? w then return (r, none)
    throwError "k2l_decide: evaluation stuck at {w.getAppFn}"
  if (← getMatcherInfo? c).isSome then
    let info ← getConstInfo c
    let some body := info.value? | throwError "k2l_decide: cannot unfold the matcher {c}"
    return ← ev ((body.instantiateLevelParams info.levelParams us).beta w.getAppArgs)
  let some (.recInfo r) := (← getEnv).find? c
    | do
      if let some r ← safeKernelValue? w then return (r, none)
      -- another head (`List.length` of a list that holds a call by well-founded recursion, a
      -- primitive `whnf` does not reduce): evaluate the arguments that may reach such a call
      -- down to their leaves, rewrite each by the equation found, and evaluate the new term
      let (w', hw) ← evArgs w
      if w' == w then throwError "k2l_decide: evaluation stuck at {c}"
      let (v, h₂) ← ev w'
      return (v, ← trans? e w' v hw h₂)
  let i := r.getMajorIdx
  let args := w.getAppArgs
  unless i < args.size do throwError "k2l_decide: {c} is not applied to its major premise"
  let (mv, hm) ← ev args[i]!
  let some hm := hm | do
    -- the major premise reduces to a constructor that the elaborator's `whnf` did not reach
    if mv != args[i]! then return ← ev (mkAppN w.getAppFn (args.set! i mv))
    if let some r ← safeKernelValue? w then return (r, none)
    throwError "k2l_decide: evaluation stuck at {c}"
  let (w', hstep) ← rewriteArg w i mv hm
  let (v, h₂) ← ev w'
  return (v, ← trans? e w' v (some hstep) h₂)

/-- `ev` down to the leaves of constructor applications (the fields that are neither types nor
proofs), so that the value contains no call the kernel would be stuck at; a subterm that reaches
no definition by well-founded recursion is left to the kernel. -/
partial def dnf (e : Expr) : EvM (Expr × Option Expr) := do
  unless ← mayReachWF e do return (e, none)
  let (v, h) ← ev e
  let fn := v.getAppFn
  let .const c _ := fn | return (v, h)
  let some (.ctorInfo ci) := (← getEnv).find? c | return (v, h)
  let mut args := v.getAppArgs
  let mut hacc := h
  for i in [ci.numParams:args.size] do
    let a := args[i]!
    if (← isProof a) || (← isType a) then continue
    let (va, ha) ← dnf a
    match ha with
    | none => args := args.set! i va
    | some ha =>
      let cur := mkAppN fn args
      let motive ← withLocalDeclD `x (← inferType a) fun x =>
        mkLambdaFVars #[x] (mkAppN fn (args.set! i x))
      let step ← mkCongrArg motive ha
      args := args.set! i va
      hacc ← trans? e cur (mkAppN fn args) hacc (some step)
  return (mkAppN fn args, hacc)

/-- `w = w'` where `w'` is `w` with each argument that may reach a definition by well-founded
recursion (neither a type nor a proof) evaluated by `dnf` and rewritten by `rewriteArg`; with
`kernel`, each other argument is replaced by its value in the kernel (`kernelNF`), which needs
no proof. `none` when the arguments changed by reduction only. -/
partial def evArgs (w : Expr) (kernel : Bool := false) : EvM (Expr × Option Expr) := do
  let mut cur := w
  let mut hacc : Option Expr := none
  for i in [:w.getAppNumArgs] do
    let a := cur.getAppArgs[i]!
    -- a function is a value; a type or a proof is not evaluated
    if a.isLambda || (← isProof a) || (← isType a) then continue
    unless ← mayReachWF a do
      if kernel then
        let v ← kernelNF a
        if v != a then cur := mkAppN cur.getAppFn (cur.getAppArgs.set! i v)
      continue
    let (va, ha) ← dnf a
    let some ha := ha | continue
    let (cur', hstep) ← rewriteArg cur i va ha
    hacc ← trans? w cur cur' hacc (some hstep)
    cur := cur'
  return (cur, hacc)

end

/-- `a = b` checked by the kernel's definitional equality (`Eq.refl a`), in an auxiliary
theorem. -/
def kernelRefl (a b : Expr) : MetaM Expr := do
  let ty ← mkEq a b
  withOptions (Elab.async.set · false) <|
    mkAuxTheorem (zetaDelta := true) ty (← mkExpectedTypeHint (← mkEqRefl a) ty)

/-- The constructor and arguments of `v` when it is a constructor application. -/
def ctorApp? (v : Expr) : MetaM (Option ConstructorVal) := do
  let .const c _ := v.getAppFn | return none
  let some (.ctorInfo ci) := (← getEnv).find? c | return none
  unless v.getAppNumArgs == ci.numParams + ci.numFields do return none
  return some ci

/-- `va = vb` for two values: identical ones by `rfl`; two applications of one constructor field
by field, each field that differs proved equal in turn and rewritten by congruence; other ones
by the kernel, its definitional equality first, then its evaluation of `decide`. The kernel
compares the values whole only where they are not applications of one constructor, so that a
long field (a list of many bytes) that is the same term on both sides is not traversed. -/
partial def eqProof (va vb : Expr) : MetaM Expr := do
  if va == vb then return ← mkEqRefl va
  if let some ci ← ctorApp? va then
    if let some ci' ← ctorApp? vb then
      if ci.name == ci'.name then
        let fn := va.getAppFn
        let bs := vb.getAppArgs
        let mut args := va.getAppArgs
        let mut h ← mkEqRefl va
        for i in [ci.numParams:args.size] do
          let a := args[i]!
          if a == bs[i]! || (← isProof a) || (← isType a) then continue
          let hi ← eqProof a bs[i]!
          let motive ← withLocalDeclD `x (← inferType a) fun x =>
            mkLambdaFVars #[x] (mkAppN fn (args.set! i x))
          let step ← mkCongrArg motive hi
          args := args.set! i bs[i]!
          h ← mkEqTrans h step
        return ← mkExpectedTypeHint h (← mkEq va vb)
  try kernelRefl va vb catch _ => kernelDecide (← mkEq va vb)

/-- `¬ va = vb` for two values: two applications of one constructor from a field that differs
(through the constructor's injectivity, `C.inj`); otherwise by the kernel's evaluation of
`decide`. -/
partial def neProof (va vb : Expr) : MetaM Expr := do
  if let some ci ← ctorApp? va then
    if let some ci' ← ctorApp? vb then
      if ci.name == ci'.name then
        let as := va.getAppArgs
        let bs := vb.getAppArgs
        for i in [ci.numParams:as.size] do
          let a := as[i]!
          if a == bs[i]! || (← isProof a) || (← isType a) then continue
          try
            let hi ← neProof a bs[i]!
            return ← withLocalDeclD `h (← mkEq va vb) fun h => do
              -- the conjunct `aᵢ = bᵢ` of `C.inj h`
              let mut c ← mkAppM (ci.name ++ `inj) #[h]
              let mut found := none
              for _ in [0:ci.numFields] do
                let ty ← whnfR (← inferType c)
                if let some (_, x, y) := ty.eq? then
                  if x == a && y == bs[i]! then found := some c
                  break
                let some (l, _) := ty.and? | break
                if let some (_, x, y) := l.eq? then
                  if x == a && y == bs[i]! then found := some (← mkAppM ``And.left #[c]); break
                c ← mkAppM ``And.right #[c]
              let some hai := found | throwError "k2l_decide: no conjunct for field {i} in {ci.name}.inj"
              mkLambdaFVars #[h] (mkApp hi hai)
          catch _ => continue
  kernelDecide (mkNot (← mkEq va vb))

/-- `a = b` or `¬ a = b` with both sides evaluated by `dnf` and the values compared by
`eqProof` or `neProof`. -/
def evalProof (p : Expr) (limit : Nat) : MetaM Expr := do
  let p' ← whnfR p
  let (neg, eq) := match p'.not? with
    | some q => (true, q)
    | none => match p'.arrow? with
      | some (q, f) => if f.isConstOf ``False then (true, q) else (false, p')
      | none => (false, p')
  let some (α, a, b) := eq.eq? | throwError "k2l_decide: not an equation: {p}"
  let (((va, ha), (vb, hb)), _) ← (do pure (← dnf a, ← dnf b) : EvM _).run { limit }
  let u ← getLevel α
  let symm? (h : Option Expr) (x y : Expr) : Option Expr :=
    h.map fun h => mkApp4 (mkConst ``Eq.symm [u]) α x y h
  if neg then
    let k ← neProof va vb
    withLocalDeclD `h (← mkEq a b) fun hab => do
      let h₁ ← trans? va a b (symm? ha a va) (some hab)
      let h₂ ← trans? va b vb h₁ hb
      let h₂ := h₂.getD hab
      mkLambdaFVars #[hab] (mkApp k h₂)
  else
    let k ← eqProof va vb
    let h₁ ← trans? a va vb ha (some k)
    let h₂ ← trans? a vb b h₁ (symm? hb b vb)
    return h₂.getD k

end DetEval

open Lean Meta Elab Tactic in
/-- `k2l_decide`: the kernel first, then evaluation. -/
def k2lDecide : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let p ← instantiateMVars (← g.getType)
    let byEval : TacticM Expr := do
      let pr ← DetEval.evalProof p 1000000
      withOptions (Elab.async.set · false) <| mkAuxTheorem (zetaDelta := true) p pr
    let pf ← try DetEval.kernelDecide p catch ex₁ => do
      try byEval catch ex₂ =>
        throwError "k2l_decide: the kernel fails:{indentD ex₁.toMessageData}\nand evaluation fails:{indentD ex₂.toMessageData}"
    g.assign pf
  replaceMainGoal []

/-- `decide`, checked by the kernel only: the goal's `Decidable` instance applied to `rfl`, in an
auxiliary theorem the kernel checks at once. Unlike `decide +kernel`, the goal may mention free
variables, such as the `Hooks` instance of a definition whose evaluation here does not reach a
hook. When the kernel's evaluation is stuck at a definition by well-founded recursion (which it
does not unfold), the goal, an equation or its negation, is proved by `DetEval.evalProof`: both
sides evaluated with those definitions' unfolding equations, the values compared field by field.
The proof uses no axiom beyond the ones of the definitions. -/
elab "k2l_decide" : tactic => k2lDecide

/-- At some configuration `c` both rules of `o` step (their matchers return `next`), to
different configurations, and both steps are `S`-steps (for a stratified relation: no rule of a
higher rank applies at `c`). -/
def Overlap.Witnessed {α : Type} (S : α → α → Prop) (o : Overlap α) : Prop :=
  ∃ c c₁ c₂, (o.fst.run c).next? = some c₁ ∧ (o.snd.run c).next? = some c₂ ∧ c₁ ≠ c₂ ∧
    S c c₁ ∧ S c c₂

end KPrelude
