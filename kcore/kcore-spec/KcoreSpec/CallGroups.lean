/-
  KCore, checked layer: termination of mutually recursive functions by a weight shared across their
  cycle, so that a rank of the functions (`ord`, CallRank.lean) names fewer functions.

  A function that calls one not ranked below it is named by the rank alone. Where the calls of a
  cycle all go to strictly lighter arguments (`argLt`, DecreasingL.lean), the cycle terminates as a
  whole: each function of the cycle has a decreasing argument position, and every call inside the
  cycle, self calls included, has at the callee's position an argument strictly lighter than the
  calling clause's pattern at the caller's. Evaluation terminates by induction on that weight, the
  calls out of the cycle reaching functions ranked below all of it.

  The cycles are read off `ord` as intervals of positions. A call from a function to one placed at
  or after it (itself aside) spans the two positions (`fwdSpans`); the spans that meet are merged
  (`spanOf`). For a rank that puts each strongly connected set of the call graph at consecutive
  positions, callees first, the merged intervals are those sets. Nothing of this is trusted: the
  interval I of a position is accepted (`groupOK`) only where every position of I has the interval
  I, I lies within `ord`, and every function placed in I calls functions placed in I only at
  strictly lighter arguments and other functions of the core only where they are placed before I
  (`memberOK`). The decreasing positions are found by a search (`groupPos`) and then checked.

  - `rankObligations c ord`: the functions some callee of which (a function of `c` other than
    itself) does not come before it in `ord`, unless the interval of its position is accepted; and
    the functions that apply a function-overloaded symbol (`fnOvlCallers`).
  - `terminates_of_rankL`: every function terminates, given the named ones and those
    `decObligationsL` names. By induction on a stage: a function of an accepted interval has the
    interval's last position, every other function its own; the calls of a function go to
    functions of a lower stage, or inside its accepted interval (`terminates_of_group`).
-/
import KcoreSpec.DecreasingL

set_option autoImplicit false

namespace KCore

open Det

/-- The span of each call from a function of `bad` to a function of `labels` placed at or after it
in `ord` (itself aside): the two positions. -/
def fwdSpans (ord labels : List Sym) (bad : List Fn) : List (Nat × Nat) :=
  bad.flatMap fun h => (h.callees.filter fun g =>
    g != h.label && labels.contains g && decide (ord.idxOf h.label ≤ ord.idxOf g)).map
      fun g => (ord.idxOf h.label, ord.idxOf g)

/-- One pass merging into the interval J the spans that meet it. -/
def spanStep (sp : List (Nat × Nat)) (J : Nat × Nat) : Nat × Nat :=
  sp.foldl (fun J s => if s.1 ≤ J.2 ∧ J.1 ≤ s.2 then (min J.1 s.1, max J.2 s.2) else J) J

/-- The interval of positions the spans connect to position p. -/
def spanOf (sp : List (Nat × Nat)) (p : Nat) : Nat × Nat :=
  Nat.repeat (spanStep sp) (sp.length + 1) (p, p)

/-- The decreasing position of the function labelled s in a list of positions (0 if none). -/
def posOf (pos : List (Sym × Nat)) (s : Sym) : Nat :=
  (pos.lookup s).getD 0

namespace Semantics
variable (c : Semantics)

/-- The functions of `c` whose label is at a position of the interval I of `ord`. -/
def groupMembers (ord : List Sym) (I : Nat × Nat) : List Fn :=
  (List.range' I.1 (I.2 + 1 - I.1)).flatMap fun q => c.fns.filter fun h => h.label == ord.getD q 0

/-- A function of the interval I, with decreasing positions d: in each clause, every call of a
function of `labels` placed in I has, at the callee's position, an argument strictly lighter than
the clause's pattern at the caller's position (`argLt`); every other call of a function of
`labels` is of one placed before I. -/
def memberOK (ord labels : List Sym) (I : Nat × Nat) (d : Sym → Nat) (h : Fn) : Bool :=
  h.clauses.all fun cl => (cl.rhs :: (cl.req.toList ++ cl.ens.toList)).all fun t => (Term.heads t).all fun g =>
    !labels.contains g ||
    if I.1 ≤ ord.idxOf g ∧ ord.idxOf g ≤ I.2 then
      (callsOf g t).all fun ts => match ts[d g]?, cl.pats[d h.label]? with
        | some a, some p => c.argLt a p
        | _, _ => false
    else decide (ord.idxOf g < I.1)

/-- The calls of h of functions of `labels` placed in I, each with its clause's patterns. -/
def _root_.KCore.groupCalls (ord labels : List Sym) (I : Nat × Nat) (h : Fn) : List (List Term × Sym × List Term) :=
  h.clauses.flatMap fun cl => (cl.rhs :: (cl.req.toList ++ cl.ens.toList)).flatMap fun t =>
    ((Term.heads t).eraseDups.filter fun g =>
      labels.contains g && decide (I.1 ≤ ord.idxOf g) && decide (ord.idxOf g ≤ I.2)).flatMap
        fun g => (callsOf g t).map fun ts => (cl.pats, g, ts)

/-- One pruning pass over the candidate positions: a position i of a function stays where each of
its calls in the group has an argument strictly lighter than the clause's pattern at i at some
candidate position of the callee. -/
def posStep (calls : List (Sym × List (List Term × Sym × List Term))) (cand : List (Sym × List Nat)) :
    List (Sym × List Nat) :=
  cand.map fun (s, is) => (s, is.filter fun i => ((calls.lookup s).getD []).all fun (pats, g, ts) =>
    ((cand.lookup g).getD []).any fun j => match ts[j]?, pats[i]? with
      | some a, some p => c.argLt a p
      | _, _ => false)

/-- A decreasing position for each function of the group: the first candidate left after pruning.
A search only: `memberOK` checks the positions. -/
def groupPos (ord labels : List Sym) (I : Nat × Nat) (mem : List Fn) : List (Sym × Nat) :=
  let calls := mem.map fun h => (h.label, groupCalls ord labels I h)
  let cand := Nat.repeat (c.posStep calls) (mem.length + 1)
    (mem.map fun h => (h.label, List.range h.args.length))
  cand.map fun (s, is) => (s, is.headD 0)

/-- Every function of `mem` is a function of the interval I with the positions `pos`. -/
def groupOKWith (ord labels : List Sym) (I : Nat × Nat) (mem : List Fn) (pos : List (Sym × Nat)) : Bool :=
  mem.all (c.memberOK ord labels I (posOf pos))

/-- The interval I is accepted: it lies within `ord`, each of its positions has the interval I, and
each function placed in it is a function of I (`memberOK`) with the positions `groupPos` finds. -/
def groupOK (ord labels : List Sym) (sp : List (Nat × Nat)) (I : Nat × Nat) : Bool :=
  decide (I.2 < ord.length) &&
  (List.range' I.1 (I.2 + 1 - I.1)).all (fun q => spanOf sp q == I) &&
  (let mem := c.groupMembers ord I
   c.groupOKWith ord labels I mem (c.groupPos ord labels I mem))

/-- The position p lies in its interval and the interval is accepted. -/
def groupOKAt (ord labels : List Sym) (sp : List (Nat × Nat)) (p : Nat) : Bool :=
  decide ((spanOf sp p).1 ≤ p) && decide (p ≤ (spanOf sp p).2) && c.groupOK ord labels sp (spanOf sp p)

/-- Of the functions `bad`, those whose position's interval is not accepted. -/
def rankNamed (ord labels : List Sym) (bad : List Fn) : List Sym :=
  (bad.filter fun f => !c.groupOKAt ord labels (fwdSpans ord labels bad) (ord.idxOf f.label)).map (·.label)

/-- The functions some callee of which `ord` does not rank below them (`rankedCallees`), unless
their position's interval is accepted (`groupOKAt`), and the functions that apply a
function-overloaded symbol (`fnOvlCallers`: the functions such a symbol overloads are callees no
rank counts): their termination is named. -/
def rankObligations (ord : List Sym) : List Sym :=
  c.rankNamed ord (c.fns.map (·.label)) (c.fns.filter fun f => !rankedCallees ord (c.fns.map (·.label)) f) ++
    c.fnOvlCallers

end Semantics

/-! ## Soundness -/

variable {c : Semantics}

/-- The decreasing position of a function of an accepted interval, at an argument list: the weight
of the argument there. -/
def groupMeasure (d : Sym → Nat) (h : Fn) (vs : List GroundTerm) : Nat :=
  ((vs[d h.label]?).map GroundTerm.weight).getD 0

/-- **A group of functions whose calls among themselves decrease in weight, and whose other calls
reach terminating functions, terminates**: by induction on the weight at the decreasing position,
for all functions of the interval I at once. Of each function of the interval, its clauses'
variables are held and the functions that the symbols it applies overload terminate, or it
terminates (`hheld`): the second kind has its result outright. -/
theorem terminates_of_groupN (hc : EvalCtxN c) {ord labels : List Sym} (hl : labels = c.fns.map (·.label))
    {I : Nat × Nat} {d : Sym → Nat}
    (hmem : ∀ h ∈ c.fns, I.1 ≤ ord.idxOf h.label → ord.idxOf h.label ≤ I.2 →
      c.memberOK ord labels I d h = true)
    (hheld : ∀ h ∈ c.fns, I.1 ≤ ord.idxOf h.label → ord.idxOf h.label ≤ I.2 →
      (c.HeldFn h ∧ ∀ g ∈ h.callees, OvlTerminates c g) ∨ Terminates c h.label)
    (hlow : ∀ g ∈ c.fns, ord.idxOf g.label < I.1 → Terminates c g.label) :
    ∀ h ∈ c.fns, I.1 ≤ ord.idxOf h.label → ord.idxOf h.label ≤ I.2 → Terminates c h.label := by
  suffices H : ∀ m, ∀ h ∈ c.fns, I.1 ≤ ord.idxOf h.label → ord.idxOf h.label ≤ I.2 →
      ∀ vs, c.sortsOf vs = some h.args → groupMeasure d h vs < m → ∃ r, Eval c h.label vs r by
    intro h hh h1 h2 fn' hfn' vs hvs
    rw [lookupFn_of_memN hc (List.mem_append_left _ hh)] at hfn'
    cases hfn'
    exact H _ h hh h1 h2 vs hvs (Nat.lt_succ_self _)
  intro m
  induction m with
  | zero => intro _ _ _ _ _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro h hh h1 h2 vs hvs hlt
    rcases hheld h hh h1 h2 with ⟨hb, hovl⟩ | hT
    case inr => exact hT h (lookupFn_of_memN hc (List.mem_append_left _ hh)) vs hvs
    refine eval_of_callsN hc (List.mem_append_left _ hh) hb hvs hovl
      (fun cl hcl σ hm t ht g ts hts gfn hg rs vs' hrs hall hsrt => ?_)
    have hmo := hmem h hh h1 h2
    simp only [Semantics.memberOK, List.all_eq_true] at hmo
    have htm : t ∈ cl.rhs :: (cl.req.toList ++ cl.ens.toList) := by
      rcases ht with rfl | ht | ht
      · exact List.mem_cons.mpr (.inl rfl)
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (Option.mem_toList.mpr ht))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (Option.mem_toList.mpr ht))
    have hgo := hmo cl hcl t htm g (mem_heads_of_callsOf t hts)
    obtain ⟨hgm, hglab⟩ := lookupFn_spec hg
    rcases List.mem_append.mp hgm with hgu | hgp
    · have hcont : labels.contains g = true := by
        rw [hl, ← hglab]; exact List.contains_iff_mem.mpr (List.mem_map_of_mem hgu)
      simp only [hcont, Bool.not_true, Bool.false_or] at hgo
      split at hgo
      · rename_i hin
        have hcall := List.all_eq_true.mp hgo ts hts
        split at hcall
        · rename_i a p ha hp
          obtain ⟨v, hvi, hpv⟩ := patVals_get hm hp
          rw [allSome_eq_map hall] at hrs
          obtain ⟨v', hv'i, hev⟩ := evalTerms_some_inv hrs ha
          have hw := argLt_weight a hcall hpv hev
          subst hglab
          refine ih gfn hgu hin.1 hin.2 vs' hsrt ?_
          have e1 : groupMeasure d gfn vs' = v'.weight := by simp [groupMeasure, hv'i]
          have e2 : groupMeasure d h vs = v.weight := by simp [groupMeasure, hvi]
          omega
        · cases hcall
      · have hlt' := of_decide_eq_true hgo
        subst hglab
        exact hlow gfn hgu hlt' gfn hg vs' hsrt
    · exact (hglab ▸ sortPreds_terminateN hc hgp) gfn hg vs' hsrt

/-- **A group of functions whose calls among themselves decrease in weight, and whose other calls
reach terminating functions, terminates**: by induction on the weight at the decreasing position,
for all functions of the interval I at once. -/
theorem terminates_of_group (hc : EvalCtx c) {ord labels : List Sym} (hl : labels = c.fns.map (·.label))
    {I : Nat × Nat} {d : Sym → Nat}
    (hmem : ∀ h ∈ c.fns, I.1 ≤ ord.idxOf h.label → ord.idxOf h.label ≤ I.2 →
      c.memberOK ord labels I d h = true)
    (hovl : ∀ h ∈ c.fns, ∀ g ∈ h.callees, OvlTerminates c g)
    (hlow : ∀ g ∈ c.fns, ord.idxOf g.label < I.1 → Terminates c g.label) :
    ∀ h ∈ c.fns, I.1 ≤ ord.idxOf h.label → ord.idxOf h.label ≤ I.2 → Terminates c h.label :=
  terminates_of_groupN hc.toN hl hmem
    (fun h hh _ _ => .inl ⟨hc.binds h (List.mem_append_left _ hh), hovl h hh⟩) hlow

theorem groupMembers_mem {ord : List Sym} {I : Nat × Nat} {h : Fn} (hh : h ∈ c.fns)
    (h1 : I.1 ≤ ord.idxOf h.label) (h2 : ord.idxOf h.label ≤ I.2) (hlen : I.2 < ord.length) :
    h ∈ c.groupMembers ord I := by
  simp only [Semantics.groupMembers, List.mem_flatMap, List.mem_filter, List.mem_range'_1, beq_iff_eq]
  refine ⟨ord.idxOf h.label, ⟨h1, by omega⟩, hh, ?_⟩
  have hl : ord.idxOf h.label < ord.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some, List.getElem_idxOf hl]

/-- What an accepted interval gives: it lies within `ord`, each of its positions has it as its
interval, and each function placed in it is a function of it with some decreasing positions. -/
theorem groupOK_spec {ord labels : List Sym} {sp : List (Nat × Nat)} {I : Nat × Nat}
    (h : c.groupOK ord labels sp I = true) :
    I.2 < ord.length ∧ (∀ q, I.1 ≤ q → q ≤ I.2 → spanOf sp q = I) ∧
    ∃ d : Sym → Nat, ∀ h ∈ c.fns, I.1 ≤ ord.idxOf h.label → ord.idxOf h.label ≤ I.2 →
      c.memberOK ord labels I d h = true := by
  simp only [Semantics.groupOK, Semantics.groupOKWith, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range'_1, beq_iff_eq] at h
  obtain ⟨⟨hlen, hq⟩, hm⟩ := h
  exact ⟨hlen, fun q h1 h2 => hq q ⟨h1, by omega⟩, _, fun g hg h1 h2 => hm g (groupMembers_mem hg h1 h2 hlen)⟩

/-- The stage of the position p: the last position of its interval where that is accepted, p
itself otherwise. -/
def stageOf (ok : Nat → Bool) (sp : List (Nat × Nat)) (p : Nat) : Nat :=
  if ok p then (spanOf sp p).2 else p

/-- Two positions x < y, x's interval accepted: the interval ends before y, or y is in it and has
it accepted as its own. -/
theorem groupOKAt_below {ord labels : List Sym} {sp : List (Nat × Nat)} {x y : Nat}
    (hx : c.groupOKAt ord labels sp x = true) (hxy : x < y) :
    (spanOf sp x).2 < y ∨ (c.groupOKAt ord labels sp y = true ∧ spanOf sp y = spanOf sp x) := by
  simp only [Semantics.groupOKAt, Bool.and_eq_true, decide_eq_true_eq] at hx
  obtain ⟨⟨hx1, hx2⟩, hg⟩ := hx
  by_cases hy : (spanOf sp x).2 < y
  · exact .inl hy
  · have hq := (groupOK_spec hg).2.1 y (by omega) (by omega)
    refine .inr ⟨?_, hq⟩
    simp only [Semantics.groupOKAt, Bool.and_eq_true, decide_eq_true_eq, hq]
    exact ⟨⟨by omega, by omega⟩, hg⟩

/-- A function not in `rankObligations` ranks its callees below it, or its position's interval is
accepted. -/
theorem not_rankObligations {ord : List Sym} {fn : Fn} (hmem : fn ∈ c.fns)
    (hN : fn.label ∉ c.rankObligations ord) :
    rankedCallees ord (c.fns.map (·.label)) fn = true ∨
      c.groupOKAt ord (c.fns.map (·.label))
        (fwdSpans ord (c.fns.map (·.label)) (c.fns.filter fun f => !rankedCallees ord (c.fns.map (·.label)) f))
        (ord.idxOf fn.label) = true := by
  cases h1 : rankedCallees ord (c.fns.map (·.label)) fn
  · cases h2 : c.groupOKAt ord (c.fns.map (·.label))
        (fwdSpans ord (c.fns.map (·.label)) (c.fns.filter fun f => !rankedCallees ord (c.fns.map (·.label)) f))
        (ord.idxOf fn.label)
    · exfalso
      apply hN
      unfold Semantics.rankObligations Semantics.rankNamed
      exact List.mem_append_left _
        (List.mem_map.mpr ⟨fn, List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hmem, by simp [h1]⟩, by simp [h2]⟩, rfl⟩)
    · exact .inr rfl
  · exact .inl rfl

/-- **`terminates_of_rankL` with the held variables asked function by function**: of each
function, its clauses' variables are held (`Semantics.HeldFn`) or it terminates (`hheld`). A
function of the second kind stands as one named: the induction on the stage takes its termination
as given, in an accepted interval too (`terminates_of_groupN`); one of the first kind is shown as
in `terminates_of_rankL`, the extension of a match to every variable read of that function alone. -/
theorem terminates_of_rankLH (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (ord : List Sym) (hheld : ∀ fn ∈ c.fns, c.HeldFn fn ∨ Terminates c fn.label)
    (hnamed : ∀ g ∈ c.rankObligations ord ++ c.decObligationsL, Terminates c g) :
    ∀ f, Terminates c f := by
  have hc := evalCtxN_of_all hok hsr hov
  obtain ⟨labels, hl⟩ : ∃ l, l = c.fns.map (·.label) := ⟨_, rfl⟩
  obtain ⟨sp, hsp⟩ : ∃ s, s = fwdSpans ord labels (c.fns.filter fun f => !rankedCallees ord labels f) :=
    ⟨_, rfl⟩
  have pos : ∀ (n : Nat) (fn : Fn), fn ∈ c.fns →
      stageOf (c.groupOKAt ord labels sp) sp (ord.idxOf fn.label) = n → Terminates c fn.label := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro fn hmem hn
      have ihs : ∀ g ∈ c.fns, stageOf (c.groupOKAt ord labels sp) sp (ord.idxOf g.label) < n →
          Terminates c g.label := fun g hg hlt => ih _ hlt g hg rfl
      by_cases hN : fn.label ∈ c.rankObligations ord ++ c.decObligationsL
      · exact hnamed _ hN
      rcases hheld fn hmem with hb | hT
      case inr => exact hT
      have hrk := not_rankObligations hmem (fun h => hN (List.mem_append_left _ h))
      have hovl : ∀ g ∈ fn.callees, OvlTerminates c g := fun g hg =>
        ovlTerminates_of_not_fnOvl (Semantics.not_fnOvl_of_not_caller hmem
          (fun h => hN (List.mem_append_left _ (show fn.label ∈ c.rankObligations ord from List.mem_append_right _ h))) hg)
      rw [← hl, ← hsp] at hrk
      cases hok' : c.groupOKAt ord labels sp (ord.idxOf fn.label) with
      | true =>
        -- the interval of fn's position is accepted
        have hok2 := hok'
        simp only [Semantics.groupOKAt, Bool.and_eq_true, decide_eq_true_eq] at hok2
        obtain ⟨⟨hp1, hp2⟩, hg⟩ := hok2
        obtain ⟨-, hq, d, hd⟩ := groupOK_spec hg
        have hstage : n = (spanOf sp (ord.idxOf fn.label)).2 := by
          rw [← hn]; simp [stageOf, hok']
        refine terminates_of_groupN hc hl hd
          (fun g hg _ _ => by
            by_cases hx : g.label ∈ c.fnOvlCallers
            · exact .inr (hnamed _ (List.mem_append_left _
                (show g.label ∈ c.rankObligations ord from List.mem_append_right _ hx)))
            · exact (hheld g hg).imp (fun hb => ⟨hb, fun x hx' =>
                ovlTerminates_of_not_fnOvl (Semantics.not_fnOvl_of_not_caller hg hx hx')⟩) id)
          (fun g hg hlt => ihs g hg ?_) fn hmem hp1 hp2
        -- a function placed before the interval has a lower stage
        by_cases hgo : c.groupOKAt ord labels sp (ord.idxOf g.label) = true
        · simp only [stageOf, hgo, ↓reduceIte]
          rcases groupOKAt_below hgo (y := (spanOf sp (ord.idxOf fn.label)).1) hlt with h | ⟨-, h⟩
          · omega
          · have hI := hq _ (Nat.le_refl _) (by omega)
            rw [hI] at h
            have hgo2 := hgo
            simp only [Semantics.groupOKAt, Bool.and_eq_true, decide_eq_true_eq] at hgo2
            rw [← h] at hgo2
            obtain ⟨⟨hg1, -⟩, -⟩ := hgo2
            omega
        · simp only [stageOf, hgo, Bool.false_eq_true, ↓reduceIte]; omega
      | false =>
        have hrk : rankedCallees ord labels fn = true := by
          rcases hrk with h | h
          · exact h
          · rw [hok'] at h; cases h
        have hstage : n = ord.idxOf fn.label := by
          rw [← hn]; simp [stageOf, hok']
        have hcallees : ∀ g ∈ fn.callees, g ≠ fn.label → Terminates c g := fun g hg hgl => by
          rcases rankedCallees_spec hrk hg with h | h | h
          · exact absurd h hgl
          · exact terminates_of_not_labelN hc (hl ▸ h)
          · intro gfn hgfn
            obtain ⟨hgm, hlab⟩ := lookupFn_spec hgfn
            rcases List.mem_append.mp hgm with hu | hp
            · subst hlab
              refine ihs gfn hu ?_ gfn hgfn
              by_cases hgo : c.groupOKAt ord labels sp (ord.idxOf gfn.label) = true
              · simp only [stageOf, hgo, ↓reduceIte]
                rcases groupOKAt_below hgo h with h' | ⟨h', -⟩
                · omega
                · rw [hok'] at h'; cases h'
              · simp only [stageOf, hgo, Bool.false_eq_true, ↓reduceIte]; omega
            · exact hlab ▸ sortPreds_terminateN hc hp gfn (hlab ▸ hgfn)
        have named : ¬ (c.decreasingOKL fn (c.decArgL fn) = false ∧
            (c.ctrReady && (ctrArgOf fn).isSome) = false) := fun ⟨h1, h2⟩ =>
          hN (List.mem_append_right _ (List.mem_map.mpr
            ⟨fn, List.mem_filter.mpr ⟨hmem, by simp [h1, h2]⟩, rfl⟩))
        cases hd : c.decreasingOKL fn (c.decArgL fn)
        · cases hx : (c.ctrReady && (ctrArgOf fn).isSome)
          · exact absurd ⟨hd, hx⟩ named
          · obtain ⟨hr, hsome⟩ := Bool.and_eq_true_iff.mp hx
            simp only [Semantics.ctrReady, Bool.and_eq_true, Bool.not_eq_true'] at hr
            obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
            exact terminates_of_ctrN hc hr.1.1 hr.1.2 hr.2 (List.mem_append_left _ hmem) hb (List.find?_some hi)
              hcallees hovl
        · exact terminates_of_decreasingLN hc (List.mem_append_left _ hmem) hb hd hcallees hovl
  intro f fn hfn
  obtain ⟨hgm, hlab⟩ := lookupFn_spec hfn
  subst hlab
  rcases List.mem_append.mp hgm with hu | hp
  · exact pos _ fn hu rfl fn hfn
  · exact sortPreds_terminateN hc hp fn hfn

/-- **A rank of the functions, cycles decreasing in a shared weight and self calls decreasing give
termination**: in a core that `sortedOK` and `srReady` accept, every function terminates, given
the termination of those `rankObligations` and `decObligationsL` name. By induction on the stage
(`stageOf`): a function of an accepted interval terminates with the whole interval
(`terminates_of_group`), its calls out of it reaching functions placed before the interval, of a
lower stage; any other function not named calls only itself and functions ranked below it, of a
lower stage, and its self calls decrease in weight (`terminates_of_decreasingL`) or at an Int counter
(`terminates_of_ctr`). -/
theorem terminates_of_rankL (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hrh : c.RightHeld)
    (ord : List Sym) (hnamed : ∀ g ∈ c.rankObligations ord ++ c.decObligationsL, Terminates c g) :
    ∀ f, Terminates c f :=
  terminates_of_rankLH hok hsr hov ord (fun _ hfn => .inl (hrh.heldFn hfn)) hnamed

/-- **`terminates_of_rankL` with the held variables asked of the held-named functions only**
(`Semantics.heldObligations`): of each, `HeldOwed` (its clauses' variables are held, or it has a
result at every argument list); the others' are held on the data. -/
theorem terminates_of_rankLN (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (ord : List Sym) (hheld : ∀ f ∈ c.heldObligations, HeldOwed c f)
    (hnamed : ∀ g ∈ c.rankObligations ord ++ c.decObligationsL, Terminates c g) :
    ∀ f, Terminates c f :=
  terminates_of_rankLH hok hsr hov ord
    (fun _ hfn => (heldOr_of_owed (evalCtxN_of_all hok hsr hov) hheld hfn).imp id And.left) hnamed

kernel_rfl Semantics.rankObligations_withHooks :
  ∀ (c : Semantics) (H : HookParams) (ord : List Sym), (c.withHooks H).rankObligations ord = c.rankObligations ord

end KCore
