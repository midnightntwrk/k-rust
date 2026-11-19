/-
  KCore, checked layer: the readiness conditions and `ok` read from the tables (A5, Tables.lean).

  - `transT`: the subsort relation is transitive, checked from each sort's supersorts (for each pair
    a < b, each supersort of b is one of a), about the number of pairs times their supersorts; the
    readable `srReady` and `matchReady` check it by a pass over pairs of pairs, quadratic.
  - `srReadyT`, `matchReadyT`, `okT`, `agreeObligationsT`: with `T = tables c` each gives the
    readable one (`srReady_of_T`, `matchReady_of_T`, `ok_of_T`, `agreeObligations_of_T`).
-/
import KcoreSpec.Tables
import KcoreSpec.MatchComplete

set_option autoImplicit false

namespace KCore

open Semantics

@[simp] theorem isCtor_tables {c : Semantics} (f : Sym) : (tables c).isCtor f = c.isCtor f := rfl

/-- The subsort relation is transitive, read from the supersort tries. -/
def Tables.transT (T : Tables) : Bool :=
  T.subs.all fun (a, b) => (NatMap.succs T.sup b).all fun d => T.sub a d

theorem trans_of_transT {c : Semantics} (h : (tables c).transT = true) :
    ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts := by
  intro a b d hab hbd
  simp only [Tables.transT, List.all_eq_true] at h
  have := h (a, b) hab d (by simp only [tables, NatMap.mem_group]; exact hbd)
  simpa using this

/-- The readable transitivity check holds when the relation is transitive. -/
theorem transCheck_of {l : List (Srt × Srt)} (h : ∀ a b d, (a, b) ∈ l → (b, d) ∈ l → (a, d) ∈ l) :
    (l.all fun (a, b) => l.all fun (b', d) => b != b' || l.contains (a, d)) = true := by
  simp only [List.all_eq_true]
  rintro ⟨a, b⟩ hab ⟨b', d⟩ hbd
  by_cases hb : b = b'
  · subst hb; simp [h a b d hab hbd]
  · simp [hb]

/-- `rangeKeysOK`, read from the tables: the subsort relation, the constructors' signatures by
number and the overloading symbols. -/
def Tables.rangeKeysT (T : Tables) : Bool :=
  T.subs.contains (Srt.range, Srt.kitem) ||
    match T.sig rangeCtor with
    | some k => k.result != Srt.range
    | none => match T.lookupOvl rangeCtor with
      | some o => o.sig.result != Srt.range
      | none => true

theorem rangeKeysT_tables (c : Semantics) : (tables c).rangeKeysT = c.rangeKeysOK := rfl

def Semantics.srReadyT (T : Tables) (c : Semantics) : Bool :=
  nodup (c.allFns.map (·.label)) && T.transT && T.rangeKeysT

theorem srReady_of_T {c : Semantics} {T : Tables} (hT : T = tables c) (h : c.srReadyT T = true) :
    c.srReady = true := by
  subst hT
  simp only [Semantics.srReadyT, Bool.and_eq_true] at h
  simp only [Semantics.srReady, Bool.and_eq_true]
  exact ⟨⟨h.1.1, transCheck_of (trans_of_transT h.1.2)⟩, (rangeKeysT_tables c) ▸ h.2⟩

def Semantics.matchReadyT (T : Tables) (c : Semantics) : Bool :=
  T.transT && (T.subs.all fun (a, b) => a != b) && (patternHooks.all fun f => !(T.sig f).isSome) &&
    c.ovls.isEmpty

theorem matchReady_of_T {c : Semantics} {T : Tables} (hT : T = tables c) (h : c.matchReadyT T = true) :
    c.matchReady = true := by
  subst hT
  simp only [Semantics.matchReadyT, Bool.and_eq_true] at h
  obtain ⟨⟨⟨htr, hir⟩, hph⟩, hno⟩ := h
  simp only [Semantics.matchReady, Bool.and_eq_true]
  exact ⟨⟨⟨transCheck_of (trans_of_transT htr), hir⟩, hph⟩, hno⟩

/-! ## `ok` read from the tables -/

namespace Semantics
variable (T : Tables) (c : Semantics)

def patCtxT : TermCtx := ⟨c.lib, T.subs, c.ctorSigs ++ hookSigs.filter (patternHooks.contains ·.name), true⟩

def rhsCtxT (fns : List CtorSig) : TermCtx :=
  ⟨c.lib, T.subs, c.ctorSigs ++ hookSigs ++ c.params.map (·.sig) ++ c.sortPreds.map Fn.sig ++ fns ++ c.ovlSigs,
    false⟩

def gensT (N : Srt) : List Gen :=
  (c.ctorSigs.filter (·.result == N)).map .ctor ++
  (c.ovlSigs.filter (·.result == N)).map .ctor ++
  (((c.params.filter (·.raw)).map (·.sig)).filter (·.result == N)).map .ctor ++
  (sortBy id ((T.subs.filter (·.2 == N)).map (·.1))).map .inj

def meetT (a b : Srt) : Bool :=
  T.le a b || T.le b a || T.subs.any fun (s, _) => T.le s a && T.le s b

def coversT : Nat → List Srt → List (List Term) → Bool
  | 0, _, _ => false
  | _ + 1, [], rows => !rows.isEmpty
  | n + 1, s :: ss, rows =>
    let varRows := rows.filterMap fun r => match r with
      | p :: ps => (match peelAs p with | .var _ => some ps | _ => none)
      | [] => none
    if c.enumerable s && varRows.length != rows.length then
      (c.gensT T s).all fun g => coversT n (g.argSorts ++ ss) (rows.filterMap (specialize g))
    else coversT n ss varRows

def subsortsOKT : Bool :=
  let subs := c.userSubsorts
  subs.all (fun (a, b) => a != b && (c.userSorts.contains a || c.libValueSorts.contains a) &&
    (c.userSorts.contains b || c.libConsSorts.contains b)) &&
  T.subs.all (fun (a, b) => a != b) &&
  nodup subs

def clauseOKT (f : Fn) (rhsHeads : List CtorSig) (cl : Clause) : Bool :=
  sortsOfTerms (c.patCtxT T) cl.vars cl.pats == some f.args &&
  noMapInList cl.pats &&
  binds cl.vars.length (varOccsList cl.pats) &&
  reqOK (c.rhsCtxT T rhsHeads) cl.vars cl.req &&
  sortOfTerm (c.rhsCtxT T rhsHeads) cl.vars cl.rhs == some f.result &&
  reqOK (c.rhsCtxT T rhsHeads) cl.vars cl.ens

def totalOKT (f : Fn) : Bool :=
  let tot := c.totalBefore f ++ c.sortPreds.map (·.label) ++ [f.label]
  c.shapesOK && decreasingOK c f (c.decArg f) &&
  c.coversT T (coverFuel f) f.args (coverRows f) &&
  f.clauses.all (fun cl => c.totalTerm tot cl.rhs) && f.clauses.all (·.ens.isNone)

def litsApartT (heads : List CtorSig) (vs : List Srt) : Term × Bool → Term × Bool → Bool
  | (A, b), (A', b') =>
      (Term.beq A A' && b != b' && sortOfTerm (c.rhsCtxT T heads) vs A == some Srt.bool) ||
      (match eqKLit (A, b), eqKLit (A', b') with
       | some (x, a), some (x', a') => Term.beq x x' && (sortOfTerm (c.rhsCtxT T heads) vs x).isSome &&
           c.groundValue a && c.groundValue a' && !Term.beq a a'
       | _, _ => false) ||
      complLits (c.rhsCtxT T heads) vs (A, b) (A', b') ||
      (match intBound (A, b), intBound (A', b') with
       | some (x, r), some (x', r') => Term.beq x x' && (sortOfTerm (c.rhsCtxT T heads) vs x).isSome &&
           boundsApart r r'
       | _, _ => false)

def litExcludedT (heads : List CtorSig) (vs : List Srt) (ls' : List (Term × Bool)) : Term × Bool → Bool
  | (.app f [A₁, A₂], true) =>
    if f == boolOr then
      ls'.any (c.litsApartT T heads vs (A₁, true)) && ls'.any (c.litsApartT T heads vs (A₂, true))
    else ls'.any (c.litsApartT T heads vs (.app f [A₁, A₂], true))
  | l => ls'.any (c.litsApartT T heads vs l)

def reqsExclusiveT (heads : List CtorSig) (vs : List Srt) : Option Term → Option Term → Bool
  | some q, some q' => (lits q).any (c.litExcludedT T heads vs (lits q'))
  | _, _ => false

def clausesExclusiveT (heads : List CtorSig) (cl cl' : Clause) : Bool :=
  cl.vars == cl'.vars && Term.beqList cl.pats cl'.pats && c.reqsExclusiveT T heads cl.vars cl.req cl'.req

def fnOKT (heads : List CtorSig) (f : Fn) : Bool :=
  f.clauses.all (c.clauseOKT T f heads)

def fnsOKT : Bool := c.fns.all (c.fnOKT T (c.fns.map Fn.sig))

def fnExclusiveOKT (heads : List CtorSig) (f : Fn) : Bool :=
  (pairs f.clauses).all (fun (cl, cl') => (cl.prio != cl'.prio && !cl.aside && !cl'.aside) ||
    !overlapList (meetT T) c.collHead cl.pats cl'.pats || (c.clauseFixed cl && c.clausesExclusiveT T heads cl cl') ||
      clausesAgree cl cl')

/-- `agreeObligations`, read from the tables. -/
def agreeObligationsT : List Sym :=
  (c.fns.filter fun f => !(c.ovls.isEmpty && c.fnExclusiveOKT T (c.fns.map Fn.sig) f)).map (·.label)

def ruleOKT (r : Rule) : Bool :=
  sortOfTerm (c.patCtxT T) r.vars r.lhs == some topCellSort &&
  noMapIn r.lhs &&
  binds r.vars.length (varOccs r.lhs) &&
  reqOK (c.rhsCtxT T (c.fns.map Fn.sig)) r.vars r.req &&
  reqOK (c.rhsCtxT T (c.fns.map Fn.sig)) r.vars r.ens &&
  sortOfTerm (c.rhsCtxT T (c.fns.map Fn.sig)) r.vars r.rhs == some topCellSort &&
  r.exs.isEmpty && r.pre.isTop && r.post.isTop

/-- `ok`, read from the tables. -/
def okT : Bool :=
  c.declsOK && (c.rulesPlain && (c.clausesPlain && (c.clausesPreTop && c.clausesNoExsTop)) && c.paramsPlain) && c.subsortsOKT T && c.fnsOKT T &&
    c.rules.all (c.ruleOKT T)

end Semantics

section
variable {c : Semantics}

@[simp] theorem patCtxT_tables : c.patCtxT (tables c) = c.patCtx := rfl
@[simp] theorem rhsCtxT_tables (fns : List CtorSig) : c.rhsCtxT (tables c) fns = c.rhsCtx fns := rfl

theorem meetT_tables : meetT (tables c) = c.meet := by
  funext a b; simp only [Semantics.meetT, Semantics.meet, le_tables, tables_subs]

theorem gensT_tables : c.gensT (tables c) = c.gens := rfl

theorem coversT_tables : ∀ n ss rows, c.coversT (tables c) n ss rows = c.covers n ss rows
  | 0, _, _ => by rw [Semantics.coversT, Semantics.covers]
  | _ + 1, [], _ => by rw [Semantics.coversT, Semantics.covers]
  | n + 1, s :: ss, rows => by
    rw [Semantics.coversT, Semantics.covers]
    simp only [coversT_tables n]; rfl

theorem totalOKT_tables (f : Fn) : c.totalOKT (tables c) f = c.totalOK f := by
  simp only [Semantics.totalOKT, Semantics.totalOK, coversT_tables]

theorem fnOKT_tables (heads : List CtorSig) (f : Fn) : c.fnOKT (tables c) heads f = c.fnOK heads f := by
  simp only [Semantics.fnOKT, Semantics.fnOK]; rfl

theorem fnsOKT_tables : c.fnsOKT (tables c) = c.fnsOK := by
  simp only [Semantics.fnsOKT, Semantics.fnsOK]
  exact congrArg (c.fns.all ·) (funext fun f => fnOKT_tables _ f)

theorem fnExclusiveOKT_tables (heads : List CtorSig) (f : Fn) :
    c.fnExclusiveOKT (tables c) heads f = c.fnExclusiveOK heads f := by
  simp only [Semantics.fnExclusiveOKT, Semantics.fnExclusiveOK, meetT_tables]; rfl

theorem agreeObligationsT_tables : c.agreeObligationsT (tables c) = c.agreeObligations := by
  simp only [Semantics.agreeObligationsT, Semantics.agreeObligations, fnExclusiveOKT_tables]

/-- The functions `agreeObligations` names, read from the tables. -/
theorem agreeObligations_of_T {T : Tables} (hT : T = tables c) {l : List Sym}
    (h : c.agreeObligationsT T = l) : c.agreeObligations = l := by
  subst hT; rw [← agreeObligationsT_tables]; exact h

theorem subsortsOK_of_T (h : c.subsortsOKT (tables c) = true) : c.subsortsOK = true := by
  simp only [Semantics.subsortsOKT, Semantics.subsortsOK, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨⟨h.1.1, fun p hp => h.1.2 p ?_⟩, h.2⟩
  simp only [tables_subs, Semantics.subsorts, List.mem_append]
  exact Or.inl hp

theorem ok_of_T {T : Tables} (hT : T = tables c) (h : c.okT T = true) : c.ok = true := by
  subst hT
  simp only [Semantics.okT, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hd, hs⟩, hf⟩, hr⟩ := h
  simp only [Semantics.ok, Bool.and_eq_true]
  refine ⟨⟨⟨hd, subsortsOK_of_T hs⟩, ?_⟩, hr⟩
  rw [fnsOKT_tables] at hf; exact hf

end

/-! ## `ok` in blocks: one decision for the declarations, functions and sorts, and one per block of
rules, joined by a generic lemma (ARCHITECTURE.md §3.8, `D/Facts`) -/

def Semantics.okHeadT (T : Tables) (c : Semantics) : Bool :=
  c.declsOK && (c.rulesPlain && (c.clausesPlain && (c.clausesPreTop && c.clausesNoExsTop)) && c.paramsPlain) && c.subsortsOKT T && c.fnsOKT T

/-- Rules lo, …, lo + len - 1 pass `ruleOKT`. -/
def Semantics.ruleRowsT (T : Tables) (c : Semantics) (lo len : Nat) : Bool :=
  (List.range' lo len).all fun i => match c.rules[i]? with
    | some r => c.ruleOKT T r
    | none => false

theorem ruleRowsT_add {T : Tables} {c : Semantics} {lo a b : Nat} (h1 : c.ruleRowsT T lo a = true)
    (h2 : c.ruleRowsT T (lo + a) b = true) : c.ruleRowsT T lo (a + b) = true := by
  simp only [Semantics.ruleRowsT, List.all_eq_true, List.mem_range'_1] at *
  intro m hm
  by_cases hma : m < lo + a
  · exact h1 m ⟨hm.1, hma⟩
  · exact h2 m ⟨by omega, by omega⟩

theorem okT_of_rows {T : Tables} {c : Semantics} (hh : c.okHeadT T = true)
    (hr : c.ruleRowsT T 0 c.rules.length = true) : c.okT T = true := by
  simp only [Semantics.okHeadT, Bool.and_eq_true] at hh
  simp only [Semantics.okT, Bool.and_eq_true, hh, true_and, List.all_eq_true]
  intro r hrm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrm
  simp only [Semantics.ruleRowsT, List.all_eq_true, List.mem_range'_1] at hr
  have := hr i ⟨Nat.zero_le _, by omega⟩
  simpa [List.getElem?_eq_getElem hi] using this

/-- Blocks joined with their boundaries given as equations (closed by `rfl` on numerals), so that
elaborating the join never unfolds the decision. -/
theorem ruleRowsT_join {T : Tables} {c : Semantics} {a m b n : Nat} (h1 : c.ruleRowsT T 0 a = true)
    (h2 : c.ruleRowsT T m b = true) (hm : a = m) (hn : a + b = n) : c.ruleRowsT T 0 n = true := by
  subst hm hn; exact ruleRowsT_add (by simpa using h1) (by simpa using h2)

theorem ruleRowsT_all {T : Tables} {c : Semantics} {n : Nat} (hn : c.rules.length = n)
    (h : c.ruleRowsT T 0 n = true) : c.ruleRowsT T 0 c.rules.length = true := hn ▸ h

end KCore
