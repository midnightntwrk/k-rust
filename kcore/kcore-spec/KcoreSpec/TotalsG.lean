/-
  KCore, checked layer: totality of the functions declared `[total]` from termination and
  functional evaluation, by induction on evaluation (`totals_of_G`).

  `totalOK` (Totals.lean) and its ranked forms show a function total by induction on the size of a
  decreasing argument, its right-hand sides calling only the total functions before it. Where every
  function terminates (`Terminates`) and evaluation is functional (`CoherentAll`), neither is
  needed: an evaluation of a function at an argument list is a finite derivation, and a property
  of all of them can be shown by induction on it. A function `totalOKG` accepts has a value at
  every argument list of its sorts, given that the functions declared total that it does not
  accept do (the named facts):
  - an evaluation that ends in a clause gives that clause's right-hand side's result, and a term
    `totalTermG` accepts has a value wherever its calls of total functions do, which are smaller
    evaluations inside it (or named);
  - no evaluation of a function `totalOKG` accepts ends in `Eval.rest`: some row of `coverRowsG`
    matches the arguments, and that row's clause cannot fail.
  So self calls need not decrease and the total functions called need not be ranked below.

  What `totalTermG` accepts beyond `totalTerm`: calls of every function declared `[total]` (and
  the sort predicates); the parameters an interpretation is total on (`ParamsTotal`); `ite{S}`
  implemented by the registry's `kIte`; a map collection's element symbol implemented by the
  registry's map element (`mapItemHead`, the generated `init…Cell` functions' cell-map items); the Int divisions (`/Int`, `%Int`, `divInt`, `modInt`)
  where the divisor is a non-zero Int literal or the clause's `requires` asserts it non-zero
  (`nonzeroIn`: `D =/=Int 0`, `notBool (D ==Int 0)`, a bound on D away from 0).

  What `coverRowsG` adds to `coverRows`: two clauses with one variable list and one pattern list,
  their pattern variables apart, whose `requires` are each defined (`totalTermG`) and of which one is
  `true` wherever both have values: their negations exclude each other (`reqsExclusive` on
  `negT`). Then the two together match wherever their patterns do, as a row without `requires`:
  `P` against `notBool P`, `X ==Int 0` against `X =/=Int 0`, `0 <=Int X` against `X <Int 0`.
-/
import KcoreSpec.ParamsTotal
import KcoreSpec.AgreeLists

set_option autoImplicit false

namespace KCore

open Det

namespace Semantics
variable (c : Semantics)

/-- The Int divisions: defined on two Ints whose second is not 0. -/
def _root_.KCore.divHooks : List Sym := [intTDiv, intTMod, intEDiv, intEMod]

/-- A literal of a `requires` that asserts the Int term `d` is not 0: a bound on `d` that 0 lies
outside of, or `d =/=Int 0` (`0 =/=Int d`, `notBool (d ==Int 0)`). -/
def litNonzero (d : Term) : Term × Bool → Bool
  | (A, b) =>
    (match intBound (A, b) with
     | some (u, lo, hi) => Term.beq u d &&
        ((match lo with | some l => decide (0 < l) | none => false) ||
         (match hi with | some h => decide (h < 0) | none => false))
     | none => false) ||
    (match A with
     | .app f [x, y] => cmpAsserted f b == some intNe &&
        ((Term.beq x d && intLitOf y == some 0) || (Term.beq y d && intLitOf x == some 0))
     | _ => false)

/-- The Int term `d` is not 0: a non-zero Int literal, or asserted so by a literal of `fs`. -/
def nonzeroIn (fs : List (Term × Bool)) (d : Term) : Bool :=
  (match intLitOf d with | some k => k != 0 | none => false) || fs.any (litNonzero d)

/-- The divisor of an Int division's arguments is `nonzeroIn fs`. -/
def divArgOK (fs : List (Term × Bool)) : List Term → Bool
  | [_, d] => nonzeroIn fs d
  | _ => false

/-- `ite{S}`: a parameter symbol implemented by `kIte` at the signature `Bool, S, S → S`. -/
def iteHead (f : Sym) : Bool :=
  !isHook f && match c.lookupParam f with
    | some k => k.impl == some kIte && iteSig k.sig
    | none => false

/-- A collection's element symbol for maps, `AccountCellMapItem`: a parameter symbol implemented
by the map element hook (`mapElem`) whose result sort is a map collection sort, with the
collection's key and value sorts as its two argument sorts. Its value at a key and a value of those
sorts is the one-entry map of its result sort. -/
def mapItemHead (f : Sym) : Bool :=
  !isHook f && match c.lookupParam f with
    | some k => k.impl == some mapElem && match k.sig.args, c.collOf k.sig.result with
      | [a, b], some co => co.kind == .map && co.key == a && co.val == some b
      | _, _ => false
    | none => false

/-- A head whose application to values of its argument sorts has a value, the literals `fs`
holding and the functions of `tot` total: a constructor, an interpreted symbol other than
`partialHooks`, an Int division by a term `nonzeroIn fs`, `ite{S}`, a parameter of `tp` no registry
hook implements (`totalParam`), a function of `tot`, a map collection's element symbol
(`mapItemHead`), an overloading symbol that is not function-overloaded (its normal form is defined
at every argument list; a function-overloaded one has, at arguments a function it overloads covers,
that function's value, which may be undefined). -/
def headTotalG (tot tp : List Sym) (fs : List (Term × Bool)) (f : Sym) (ts : List Term) : Bool :=
  c.isCtor f || (isHook f && !partialHooks.contains f) ||
  (divHooks.contains f && divArgOK fs ts) ||
  c.iteHead f || c.totalParam tp f ||
  (!isHook f && !c.isParam f && tot.contains f) || c.mapItemHead f ||
  ((c.lookupOvl f).isSome && c.isOvl f && !c.fnOvlSyms.contains f)

mutual
  /-- A term whose value is defined wherever its variables have values, the literals `fs` hold and
  the functions of `tot` are total: variables, domain values, injections, and applications of
  heads `headTotalG` admits. -/
  def totalTermG (tot tp : List Sym) (fs : List (Term × Bool)) : Term → Bool
    | .var _ => true
    | .dv _ _ => true
    | .inj _ _ t => totalTermG tot tp fs t
    | .as _ _ => false
    | .app f ts => c.headTotalG tot tp fs f ts && totalTermListG tot tp fs ts
    termination_by structural t => t
  def totalTermListG (tot tp : List Sym) (fs : List (Term × Bool)) : List Term → Bool
    | [] => true
    | t :: ts => totalTermG tot tp fs t && totalTermListG tot tp fs ts
    termination_by structural ts => ts
end

/-- The negation of a `requires`: `A` for `notBool A`, `notBool B` for any other B. -/
def _root_.KCore.negT (g : Term) : Term :=
  match g with
  | .app f [t] => if f == boolNot then t else .app boolNot [g]
  | _ => .app boolNot [g]

/-- Two clauses that match together where their patterns do: one variable list, one pattern list
whose variables occur once and bind every variable, `requires` each defined and never both `false`
(their negations `reqsExclusive`). -/
def guardPair (heads : List CtorSig) (tot tp : List Sym) (cl cl' : Clause) : Bool :=
  cl.vars == cl'.vars && Term.beqList cl.pats cl'.pats && nodup (varOccsList cl.pats) &&
  binds cl.vars.length (varOccsList cl.pats) && !c.isCtor boolNot &&
  match cl.req, cl'.req with
  | some g, some g' => c.totalTermG tot tp [] g && c.totalTermG tot tp [] g' &&
      c.reqsExclusive heads cl.vars (some (negT g)) (some (negT g'))
  | _, _ => false

/-- The covering rows: `coverRows`, and the patterns of each pair of clauses `guardPair` accepts. -/
def coverRowsG (heads : List CtorSig) (tot tp : List Sym) (f : Fn) : List (List Term) :=
  coverRows f ++ ((pairs f.clauses).filter fun p => c.guardPair heads tot tp p.1 p.2).map (·.1.pats)

/-- The functions declared `[total]` and the sort predicates. -/
def totalLabels : List Sym :=
  (c.fns.filter (·.total)).map (·.label) ++ c.sortPreds.map (·.label)

/-- A function with a value at every argument list of its sorts where every function terminates,
evaluation is functional, the functions declared total are total and the parameters `tp` are:
the values of the sorts the interpreted symbols read have their shapes (`shapesOK`); its covering
rows (`coverRowsG`) cover its argument sorts; every right-hand side is `totalTermG` over the
functions declared total, with its clause's `requires` literals. -/
def totalOKG (tp : List Sym) (f : Fn) : Bool :=
  c.shapesOK && c.covers (coverFuel f) f.args (c.coverRowsG (c.fns.map Fn.sig) c.totalLabels tp f) &&
  (f.clauses.all fun cl => c.totalTermG c.totalLabels tp (reqLits cl.req) cl.rhs) &&
  f.clauses.all (·.ens.isNone)

/-- `totalOKG`, the name the `--core` packages state: the rank is not read. -/
def totalOKP (_ord tp : List Sym) (f : Fn) : Bool := c.totalOKG tp f

/-- The functions declared `[total]` that `totalOKP` does not confirm (`totalOKP` is sound where
evaluation is functional, `totals_of_rankP`, whatever the patterns apply). -/
def totalObligationsRP (ord tp : List Sym) : List Sym :=
  (c.fns.filter fun f => f.total && !c.totalOKP ord tp f).map (·.label)

end Semantics

variable {c : Semantics}

/-! ## Values of the heads -/

theorem divHooks_isHook {f : Sym} (h : divHooks.contains f = true) : isHook f = true := by
  simp only [divHooks, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at h
  rcases h with rfl | rfl | rfl | rfl <;> rfl

theorem divHooks_sig {f : Sym} (h : divHooks.contains f = true) :
    lookupSig hookSigs f = some ⟨f, [Srt.int, Srt.int], Srt.int⟩ := by
  simp only [divHooks, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem divHooks_value {f : Sym} (h : divHooks.contains f = true) (x y : Int) (hy : y ≠ 0) :
    ∃ v, hook f [int x, int y] = some (some v) := by
  simp only [divHooks, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at h
  have hx : asInt (int x) = some x := by simp [asInt, int]
  have hy' : asInt (int y) = some y := by simp [asInt, int]
  rcases h with rfl | rfl | rfl | rfl
  · refine ⟨int (x.tdiv y), ?_⟩
    rw [show hook intTDiv [int x, int y] = some (int2 [int x, int y] fun a b => nonzero b (a.tdiv b)) from rfl]
    simp [int2, hx, hy', nonzero, hy]
  · refine ⟨int (x.tmod y), ?_⟩
    rw [show hook intTMod [int x, int y] = some (int2 [int x, int y] fun a b => nonzero b (a.tmod b)) from rfl]
    simp [int2, hx, hy', nonzero, hy]
  · refine ⟨int (x.ediv y), ?_⟩
    rw [show hook intEDiv [int x, int y] = some (int2 [int x, int y] fun a b => nonzero b (a.ediv b)) from rfl]
    simp [int2, hx, hy', nonzero, hy]
  · refine ⟨int (x.emod y), ?_⟩
    rw [show hook intEMod [int x, int y] = some (int2 [int x, int y] fun a b => nonzero b (a.emod b)) from rfl]
    simp [int2, hx, hy', nonzero, hy]

theorem asInt_int_inv {w : GroundTerm} {x : Int} (h : asInt w = some x) : w = int x := by
  cases w with
  | dv s lit =>
    cases lit with
    | int i =>
      simp only [asInt] at h
      by_cases hs : s = Srt.int
      · subst hs; simp at h; subst h; rfl
      · simp [hs] at h
    | _ => simp [asInt] at h
  | _ => simp [asInt] at h

/-- A term `nonzeroIn fs` with a value, the literals `fs` holding: its value is not 0. -/
theorem nonzeroIn_sound (hco : CoherentAll c) {σ : Subst} {fs : List (Term × Bool)} {d : Term} {y : Int}
    (hfs : ∀ l ∈ fs, EvalTerm c σ l.1 (some (bool l.2))) (h : Semantics.nonzeroIn fs d = true)
    (hd : EvalTerm c σ d (some (int y))) : y ≠ 0 := by
  simp only [Semantics.nonzeroIn, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨⟨A, b⟩, hm, hl⟩
  · cases hk : Semantics.intLitOf d with
    | none => rw [hk] at h; cases h
    | some k =>
      rw [hk] at h
      obtain ⟨w, hw, hwk⟩ := intLitOf_eval hk hd
      cases hw
      simp only [asInt, int, beq_self_eq_true, ite_true, Option.some.injEq] at hwk
      subst hwk
      simpa using h
  · have he := hfs _ hm
    simp only [Semantics.litNonzero, Bool.or_eq_true] at hl
    rcases hl with hl | hl
    · cases hb : Semantics.intBound (A, b) with
      | none => rw [hb] at hl; cases hl
      | some r =>
        obtain ⟨u, lo, hi⟩ := r
        rw [hb] at hl
        simp only [Bool.and_eq_true, Bool.or_eq_true] at hl
        obtain ⟨hu, hbd⟩ := hl
        have hu := Term.beq_sound hu
        subst hu
        obtain ⟨v, x, ev, hx, hlo, hhi⟩ := intBound_sound hb he
        have := EvalTerm.functional hco ev hd
        cases this
        simp only [asInt, int, beq_self_eq_true, ite_true, Option.some.injEq] at hx
        subst hx
        rcases hbd with hbd | hbd
        · cases lo with
          | none => cases hbd
          | some l => have := hlo l rfl; simp at hbd; omega
        · cases hi with
          | none => cases hbd
          | some h' => have := hhi h' rfl; simp at hbd; omega
    · cases A with
      | app f args =>
        rcases args with _ | ⟨x', _ | ⟨y', _ | ⟨_, _⟩⟩⟩
        · simp at hl
        · simp at hl
        · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hl
          obtain ⟨hg, hxy⟩ := hl
          obtain ⟨v, w, X, Y, ev, ew, hX, hY, hc⟩ := cmpAsserted_sound hg he
          have hne := hc.2.2.2.2.2 rfl
          rcases hxy with ⟨hx, hy⟩ | ⟨hy, hx⟩
          · have hx := Term.beq_sound hx
            subst hx
            obtain ⟨w', hw', hk⟩ := intLitOf_eval hy ew
            cases hw'
            rw [hY] at hk; cases hk
            have := EvalTerm.functional hco ev hd
            cases this
            simp only [asInt, int, beq_self_eq_true, ite_true, Option.some.injEq] at hX
            subst hX
            exact hne
          · have hy := Term.beq_sound hy
            subst hy
            obtain ⟨w', hw', hk⟩ := intLitOf_eval hx ev
            cases hw'
            rw [hX] at hk; cases hk
            have := EvalTerm.functional hco ew hd
            cases this
            simp only [asInt, int, beq_self_eq_true, ite_true, Option.some.injEq] at hY
            subst hY
            exact fun h => hne h.symm
        · simp at hl
      | _ => simp at hl

/-- `notBool A` false: A is true. -/
theorem not_inv_false {σ : Subst} {t : Term} (h : EvalTerm c σ (.app boolNot [t]) (some (bool false))) :
    EvalTerm c σ t (some (bool true)) := by
  generalize ht : Term.app boolNot [t] = t' at h
  generalize hr : some (bool false) = r at h
  cases h with
  | @ctor _ _ _ rs _ _ =>
    cases ht
    cases h' : allSome rs <;> rw [h'] at hr <;> cases hr
  | @hook _ _ _ rs r' _ _ hts hh hund =>
    cases ht
    obtain ⟨r₁, rfl, h1⟩ := evalTerms_one hts
    cases r₁ with
    | none => rw [hund (by simp [allSome])] at hr; cases hr
    | some w =>
      have hv := hh [w] (by simp [allSome])
      rw [Semantics.hookRes_of_notKey silentKey_boolNot, hook_not, Option.some.injEq] at hv
      subst hv
      obtain ⟨x, hx, he⟩ := Option.map_eq_some_iff.mp hr.symm
      have := bool_inj he
      simp only [Bool.not_eq_false'] at this
      subst this
      rw [asBool_some hx] at h1
      exact h1
  | param _ hhk _ _ _ => cases ht; rw [isHook_not] at hhk; cases hhk
  | call _ hhk _ _ _ _ => cases ht; rw [isHook_not] at hhk; cases hhk
  | callUndef _ _ _ _ _ => cases ht; cases hr
  | ovl _ ho _ => cases ht; have := (c.isOvl_parts ho).2.1; rw [isHook_not] at this; cases this
  | ovlFn _ ho => cases ht; have := (c.isOvl_parts ho).2.1; rw [isHook_not] at this; cases this
  | _ => cases ht

/-- A `requires` false: its negation (`negT`) is true. -/
theorem negT_true (hnc : c.isCtor boolNot = false) {σ : Subst} {g : Term}
    (h : EvalTerm c σ g (some (bool false))) : EvalTerm c σ (negT g) (some (bool true)) := by
  have build : EvalTerm c σ (.app boolNot [g]) (some (bool true)) :=
    EvalTerm.hook hnc isHook_not (.cons h .nil)
      (fun vs hvs => by
        simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
        subst hvs
        rw [Semantics.hookRes_of_notKey silentKey_boolNot, hook_not]; rfl)
      (fun h => by simp [allSome] at h)
  unfold negT
  split
  · rename_i f t
    split
    · rename_i hf
      have hf := beq_iff_eq.mp hf
      subst hf
      exact not_inv_false h
    · exact build
  · exact build

theorem headTotalG_cases {tot tp : List Sym} {fs : List (Term × Bool)} {f : Sym} {ts : List Term}
    (h : c.headTotalG tot tp fs f ts = true) :
    c.isCtor f = true ∨ (isHook f = true ∧ partialHooks.contains f = false) ∨
    (divHooks.contains f = true ∧ Semantics.divArgOK fs ts = true) ∨
    c.iteHead f = true ∨ c.totalParam tp f = true ∨
    (isHook f = false ∧ c.isParam f = false ∧ tot.contains f = true) ∨ c.mapItemHead f = true ∨
    c.isOvl f = true := by
  simp only [Semantics.headTotalG, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl h))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨h.1.1, h.1.2, h.2⟩)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr h.1.2))))))

/-- No label of `totalLabels` is the number of a symbol `lookupFn` finds no function under. -/
theorem totalLabels_of_lookupFn_none {f : Sym} (h : c.lookupFn f = none) : c.totalLabels.contains f = false := by
  rw [Semantics.lookupFn_eq] at h
  have key : ∀ fn ∈ c.allFns, fn.label ≠ f := fun fn hfn he => by
    have := List.find?_eq_none.mp h fn hfn
    simp [he] at this
  cases hc' : c.totalLabels.contains f with
  | false => rfl
  | true =>
    have hm := List.contains_iff_mem.mp hc'
    simp only [Semantics.totalLabels, List.mem_append, List.mem_map, List.mem_filter] at hm
    rcases hm with ⟨fn, ⟨hfn, -⟩, rfl⟩ | ⟨fn, hfn, rfl⟩
    · exact absurd rfl (key fn (List.mem_append_left _ hfn))
    · exact absurd rfl (key fn (List.mem_append_right _ hfn))

/-- An overloading symbol `headTotalG` admits over `totalLabels` is not function-overloaded: it is
none of the other heads. -/
theorem headTotalG_ovl {tp : List Sym} {fs : List (Term × Bool)} {f : Sym} {ts : List Term}
    (h : c.headTotalG c.totalLabels tp fs f ts = true) (ho : c.isOvl f = true) :
    c.fnOvlSyms.contains f = false := by
  obtain ⟨hct, hhk, hp, hfn, -⟩ := c.isOvl_parts ho
  have htl := totalLabels_of_lookupFn_none hfn
  simp only [Semantics.headTotalG, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h
  · rw [hct] at h; cases h
  · rw [hhk] at h; cases h.1
  · rw [divHooks_isHook h.1] at hhk; cases hhk
  · simp only [Semantics.iteHead, hhk, Bool.not_false, Bool.true_and] at h
    cases hl : c.lookupParam f with
    | none => rw [hl] at h; cases h
    | some _ => simp [Semantics.isParam, hl] at hp
  · simp only [Semantics.totalParam, Bool.and_eq_true] at h
    cases hl : c.lookupParam f with
    | none => rw [hl] at h; exact absurd h.2 (by simp)
    | some _ => simp [Semantics.isParam, hl] at hp
  · rw [htl] at h; cases h.2
  · simp only [Semantics.mapItemHead, hhk, Bool.not_false, Bool.true_and] at h
    cases hl : c.lookupParam f with
    | none => rw [hl] at h; cases h
    | some _ => simp [Semantics.isParam, hl] at hp
  · exact h.2

/-- A map collection's element symbol at a key and a value of the collection's sorts: the one-entry
map of its result sort. -/
theorem paramVal_mapItem {f : Sym} {kp : ParamSig} (hp : c.lookupParam f = some kp)
    (hk : kp.impl = some mapElem) {co : CollSig} (hco : c.collOf kp.sig.result = some co)
    (hkind : co.kind = .map) {V : Srt} (hval : co.val = some V) {x y : GroundTerm}
    (hx : c.sortOf x = some co.key) (hy : c.sortOf y = some V) :
    c.paramVal f [x, y] = some (.map kp.sig.result [(x, y)]) := by
  have hs : c.sortOf (.map kp.sig.result [(x, y)]) = some kp.sig.result :=
    (sortOf_mapS_map hco hkind).mpr ⟨V, hval, rfl,
      by simp [Semantics.entriesOK, Semantics.entryOK, hx, hy], rfl⟩
  unfold Semantics.paramVal
  rw [hp]
  simp only [hk]
  rw [Semantics.libArgs_coll c (by decide)]
  have hh : hook mapElem [x, y] = some (some (.map Srt.map [(x, y)])) := rfl
  rw [Semantics.hookRes_of_value hh]
  simp [Option.filter, GroundTerm.asSort, GroundTerm.withSort, hs]

/-! ## Rows -/

/-- A covering row's match of a clause's patterns, their variables apart: a well-sorted
substitution under which the patterns denote the arguments (`applies_of_row` without the
`requires`). -/
theorem matches_of_row {cl : Clause} {args : List Srt} {vs : List GroundTerm}
    (hpt : sortsOfTerms c.patCtxAll cl.vars cl.pats = some args)
    (hb : binds cl.vars.length (varOccsList cl.pats) = true)
    (hnd : (varOccsList cl.pats).Nodup) (hvs : c.sortsOf vs = some args)
    (hm : RowMatches c cl.pats vs) : ∃ σ, c.WellSorted cl.vars σ ∧ PatVals c σ cl.pats vs := by
  obtain ⟨σ, hk, hpv, hse⟩ := rowMatches_subst hm hpt hvs hnd
  refine ⟨σ, fun i s hi => ?_, hpv⟩
  have hlt : i < cl.vars.length := by
    rcases Nat.lt_or_ge i cl.vars.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hi; cases hi
  have hmem : i ∈ varOccsList cl.pats := by
    have := List.all_eq_true.mp hb i (List.mem_range.mpr hlt)
    exact List.contains_iff_mem.mp this
  obtain ⟨w, hw, he⟩ := lookup_of_mem_keys σ (by rw [hk]; exact hmem)
  obtain ⟨s', hs', hsw⟩ := hse _ he
  rw [hi] at hs'
  cases hs'
  exact ⟨w, hw, hsw⟩

/-- **A row's match gives a substitution of values on the patterns' variables**, of their sorts,
under which the patterns denote the arguments. -/
theorem matches_of_rowRH {cl : Clause} {args : List Srt} {vs : List GroundTerm}
    (hpt : sortsOfTerms c.patCtxAll cl.vars cl.pats = some args)
    (hnd : (varOccsList cl.pats).Nodup) (hvs : c.sortsOf vs = some args)
    (hm : RowMatches c cl.pats vs) :
    ∃ σ, c.WellSortedAt cl.vars (varOccsList cl.pats) σ ∧ PatVals c σ cl.pats vs := by
  obtain ⟨σ, hk, hpv, hse⟩ := rowMatches_subst hm hpt hvs hnd
  refine ⟨σ, fun i hmem s hi => ?_, hpv⟩
  obtain ⟨w, hw, he⟩ := lookup_of_mem_keys σ (by rw [hk]; exact hmem)
  obtain ⟨s', hs', hsw⟩ := hse _ he
  rw [hi] at hs'
  cases hs'
  exact ⟨w, hw, hsw⟩

theorem mem_coverRowsG {heads : List CtorSig} {tot tp : List Sym} {fn : Fn} {r : List Term}
    (h : r ∈ c.coverRowsG heads tot tp fn) :
    (∃ cl ∈ fn.clauses, cl.req = none ∧ (varOccsList cl.pats).Nodup ∧ cl.pats = r) ∨
    (∃ cl cl', (cl, cl') ∈ pairs fn.clauses ∧ c.guardPair heads tot tp cl cl' = true ∧ cl.pats = r) := by
  rcases List.mem_append.mp h with h | h
  · exact .inl (mem_coverRows h)
  · obtain ⟨⟨cl, cl'⟩, hp, rfl⟩ := List.mem_map.mp h
    obtain ⟨hp, hg⟩ := List.mem_filter.mp hp
    exact .inr ⟨cl, cl', hp, hg, rfl⟩

/-! ## The heads of a call -/

/-- The head of a well-sorted application that is no constructor, interpreted symbol nor
parameter: a function of the definition, found by `lookupFn`, whose argument sorts are the
application's. -/
theorem fn_of_head (hc : SortCtx c) {L : List CtorSig} (hL : HeadsOK c L) {f : Sym} {k : CtorSig}
    (hk' : lookupSig (c.rhsCtx L).heads f = some k) (hct : c.isCtor f = false) (hhk : isHook f = false)
    (hp : c.isParam f = false) (hno : c.isOvl f = false) : ∃ fn, c.lookupFn f = some fn ∧ fn.args = k.args := by
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hct)
  simp only [Semantics.rhsCtx, List.append_assoc] at hk'
  rw [lookupSig_append_of_none hnc, lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hhk),
    lookupSig_append_of_none (c.lookupSig_params_of_not hp)] at hk'
  obtain ⟨hkL, hkn⟩ := lookupSig_spec (lookup_drop_ovls (lookupOvl_none_of hc hno) hk')
  obtain ⟨fn, hfn, rfl⟩ := headsOK_preds hL k hkL
  refine ⟨fn, ?_, rfl⟩
  rw [← hkn, Semantics.lookupFn_eq]; exact find?_label hc.nodupFns hfn

/-- The head of a well-sorted application that is a parameter and no constructor nor interpreted
symbol: its signature is the parameter's. -/
theorem param_of_head {L : List CtorSig} {f : Sym} {k : CtorSig} {kp : ParamSig}
    (hk' : lookupSig (c.rhsCtx L).heads f = some k) (hct : c.isCtor f = false) (hhk : isHook f = false)
    (hlk : c.lookupParam f = some kp) : k = kp.sig := by
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hct)
  simp only [Semantics.rhsCtx, List.append_assoc] at hk'
  rw [lookupSig_append_of_none hnc, lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hhk),
    lookupSig_append_of_some (l' := c.sortPreds.map Fn.sig ++ (L ++ c.ovlSigs)) (k := kp.sig)
      (by rw [c.lookupSig_params, hlk]; rfl)] at hk'
  exact (Option.some.inj hk').symm

/-- The head of a well-sorted application that is an interpreted symbol and no constructor: its
signature is the hook's. -/
theorem hook_of_head {L : List CtorSig} {f : Sym} {k : CtorSig} (hk' : lookupSig (c.rhsCtx L).heads f = some k)
    (hct : c.isCtor f = false) : ∀ k₀, lookupSig hookSigs f = some k₀ → k = k₀ := by
  intro k₀ hk₀
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hct)
  simp only [Semantics.rhsCtx, List.append_assoc] at hk'
  rw [lookupSig_append_of_none hnc, lookupSig_append_of_some hk₀] at hk'
  exact (Option.some.inj hk').symm

/-! ## Totality by induction on evaluation -/

theorem clauseSorted_of_sortedOK (hok : c.sortedOK = true) {fn : Fn} (hfn : fn ∈ c.fns) {cl : Clause}
    (hcl : cl ∈ fn.clauses) : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args := by
  replace hok := Semantics.sortedOK_sorted hok
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  have := hok.1.2 fn hfn cl hcl
  simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at this
  replace this := this.1
  exact this.1.1.1.1.1

section Induction
variable {tot tp : List Sym}

/-- What the induction shows of an evaluation of a function: where the function is total or
`totalOKG` accepts it, at an argument list of its sorts, the result is a value. -/
def TotM1 (c : Semantics) (tp : List Sym) (f : Sym) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ fn, c.lookupFn f = some fn → (Total c f ∨ (fn ∈ c.fns ∧ c.totalOKG tp fn = true)) →
    c.sortsOf vs = some fn.args → ∃ v, r = some v

/-- `TotM1` with the held variables asked of the functions `totalOKG` accepts, one by one
(`Semantics.HeldFn`): the induction extends a match on a clause's patterns to every variable of the
clause for these functions alone. -/
def TotM1N (c : Semantics) (tp : List Sym) (f : Sym) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ fn, c.lookupFn f = some fn → (Total c f ∨ (fn ∈ c.fns ∧ c.totalOKG tp fn = true ∧ c.HeldFn fn)) →
    c.sortsOf vs = some fn.args → ∃ v, r = some v

/-- The `requires` of a clause that fails at a match, defined (`totalTermG`), is `false` there. -/
def TotReq (c : Semantics) (tot tp : List Sym) (σ : Subst) (cl : Clause) : Prop :=
  ∃ t, cl.req = some t ∧ ∀ L, HeadsOK c L → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool →
    c.totalTermG tot tp [] t = true → EvalTerm c σ t (some (bool false))

/-- What the induction shows of an evaluation of a term: well sorted, `totalTermG` over the
literals `fs` holding, its result is a value. -/
def TotM4 (c : Semantics) (tot tp : List Sym) (σ : Subst) (t : Term) (r : Option GroundTerm) : Prop :=
  ∀ L, HeadsOK c L → ∀ vars, c.WellSorted vars σ → ∀ s, sortOfTerm (c.rhsCtx L) vars t = some s →
    ∀ fs, (∀ l ∈ fs, EvalTerm c σ l.1 (some (bool l.2))) → c.totalTermG tot tp fs t = true →
      ∃ v, r = some v

def TotM5 (c : Semantics) (tot tp : List Sym) (σ : Subst) (ts : List Term) (rs : List (Option GroundTerm)) : Prop :=
  ∀ L, HeadsOK c L → ∀ vars, c.WellSorted vars σ → ∀ ss, sortsOfTerms (c.rhsCtx L) vars ts = some ss →
    ∀ fs, (∀ l ∈ fs, EvalTerm c σ l.1 (some (bool l.2))) → c.totalTermListG tot tp fs ts = true →
      ∃ vs : List GroundTerm, rs = vs.map some

variable (hok : c.sortedOK = true) (hc : EvalCtxN c) (hs : c.shapesOK = true) (hco : CoherentAll c) (hH : ParamsTotal c tp c.hooks)
  (hall : ∀ g ∈ c.totalLabels, ∀ gfn, c.lookupFn g = some gfn →
    Total c g ∨ (gfn ∈ c.fns ∧ c.totalOKG tp gfn = true ∧ c.HeldFn gfn))

include hc hall in
theorem tot_callN {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)} {vs : List GroundTerm}
    {r : Option GroundTerm} (hct : c.isCtor f = false) (hhk : isHook f = false) (hts : EvalTerms c σ ts rs)
    (hvs : allSome rs = some vs) (hev : Eval c f vs r) (hp : c.isParam f = false)
    (ihts : TotM5 c c.totalLabels tp σ ts rs)
    (ihf : TotM1N c tp f vs r) : TotM4 c c.totalLabels tp σ (.app f ts) r := by
  intro L hL vars hσ s ht fs hfs htt
  simp only [Semantics.totalTermG, Bool.and_eq_true] at htt
  obtain ⟨hhead, hargs'⟩ := htt
  obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
  obtain ⟨ws, hws⟩ := ihts L hL vars hσ _ hargs fs hfs hargs'
  subst hws
  rw [allSome_map_some] at hvs
  cases hvs
  have hsrt := EvalTerms.sorted hc.sort hts hL hσ hargs (allSome_map_some vs)
  obtain ⟨fn, hlook, hfa⟩ := fn_of_head hc.sort hL hk' hct hhk hp hev.isOvl_false
  have htl : c.totalLabels.contains f = true := by
    rcases headTotalG_cases hhead with h | h | h | h | h | h | h | h
    · rw [hct] at h; cases h
    · rw [hhk] at h; cases h.1
    · rw [divHooks_isHook h.1] at hhk; cases hhk
    · simp only [Semantics.iteHead, hhk, Bool.not_false, Bool.true_and] at h
      cases hl : c.lookupParam f with
      | none => rw [hl] at h; cases h
      | some _ => simp [Semantics.isParam, hl] at hp
    · simp only [Semantics.totalParam, Bool.and_eq_true] at h
      cases hl : c.lookupParam f with
      | none => rw [hl] at h; exact absurd h.2 (by simp)
      | some _ => simp [Semantics.isParam, hl] at hp
    · exact h.2.2
    · simp only [Semantics.mapItemHead, hhk, Bool.not_false, Bool.true_and] at h
      cases hl : c.lookupParam f with
      | none => rw [hl] at h; cases h
      | some _ => simp [Semantics.isParam, hl] at hp
    · rw [hev.isOvl_false] at h; cases h
  exact ihf fn hlook (hall f (List.contains_iff_mem.mp htl) fn hlook) (hfa ▸ hsrt)

include hok hc hs hco in
theorem tot_hookN {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)} {r : Option GroundTerm}
    (hct : c.isCtor f = false) (hhk : isHook f = true) (hts : EvalTerms c σ ts rs)
    (hh : ∀ vs, allSome rs = some vs → c.hookRes f vs = some r) (ihts : TotM5 c c.totalLabels tp σ ts rs) :
    TotM4 c c.totalLabels tp σ (.app f ts) r := by
  intro L hL vars hσ s ht fs hfs htt
  simp only [Semantics.totalTermG, Bool.and_eq_true] at htt
  obtain ⟨hhead, hargs'⟩ := htt
  obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
  obtain ⟨ws, hws⟩ := ihts L hL vars hσ _ hargs fs hfs hargs'
  subst hws
  have hsrt := EvalTerms.sorted hc.sort hts hL hσ hargs (allSome_map_some ws)
  have hr := hh ws (allSome_map_some ws)
  obtain ⟨k₀, hk₀⟩ := lookupSig_hookSigs_of_isHook hhk
  have hkk := hook_of_head hk' hct k₀ hk₀
  subst hkk
  rcases headTotalG_cases hhead with h | h | h | h | h | h | h | h
  · rw [hct] at h; cases h
  · obtain ⟨hmem, hname⟩ := lookupSig_spec hk₀
    obtain ⟨v, hv⟩ := hook_total hs k hmem (hname ▸ h.2) ws hsrt
    rw [hname] at hv
    rw [Semantics.hookRes_of_value hv] at hr
    exact ⟨v, (Option.some.inj hr).symm⟩
  · obtain ⟨hdiv, hnz⟩ := h
    rw [divHooks_sig hdiv] at hk₀
    cases hk₀
    obtain ⟨w₁, w₂, rfl, h1, h2⟩ := sortsOf_two hsrt
    obtain ⟨x, rfl⟩ := shape_int hs h1
    obtain ⟨y, rfl⟩ := shape_int hs h2
    rcases ts with _ | ⟨a, _ | ⟨d, _ | ⟨_, _⟩⟩⟩
    · simp [Semantics.divArgOK] at hnz
    · simp [Semantics.divArgOK] at hnz
    · simp only [Semantics.divArgOK] at hnz
      obtain ⟨r₁, r₂, he, _, e2⟩ := evalTerms_two hts
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at he
      obtain ⟨-, rfl, -⟩ := he
      have hy := nonzeroIn_sound hco hfs hnz e2
      obtain ⟨v, hv⟩ := divHooks_value hdiv x y hy
      rw [Semantics.hookRes_of_value hv] at hr
      exact ⟨v, (Option.some.inj hr).symm⟩
    · simp [Semantics.divArgOK] at hnz
  · simp [Semantics.iteHead, hhk] at h
  · simp only [Semantics.totalParam, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [(isHook_iff f).mp hhk] at h
    exact absurd h.1.1 (by simp)
  · rw [hhk] at h; cases h.1
  · simp [Semantics.mapItemHead, hhk] at h
  · rw [(c.isOvl_parts h).2.1] at hhk; cases hhk

include hc hs hH in
theorem tot_paramN {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)} {r : Option GroundTerm}
    (hct : c.isCtor f = false) (hhk : isHook f = false) (hp : c.isParam f = true) (hts : EvalTerms c σ ts rs)
    (hr : r = (allSome rs).bind (c.paramVal f)) (ihts : TotM5 c c.totalLabels tp σ ts rs) :
    TotM4 c c.totalLabels tp σ (.app f ts) r := by
  intro L hL vars hσ s ht fs hfs htt
  simp only [Semantics.totalTermG, Bool.and_eq_true] at htt
  obtain ⟨hhead, hargs'⟩ := htt
  obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
  obtain ⟨ws, hws⟩ := ihts L hL vars hσ _ hargs fs hfs hargs'
  subst hws
  have hsrt := EvalTerms.sorted hc.sort hts hL hσ hargs (allSome_map_some ws)
  rw [allSome_map_some, Option.bind_some] at hr
  cases hlk : c.lookupParam f with
  | none => simp [Semantics.isParam, hlk] at hp
  | some kp =>
    have hkk := param_of_head hk' hct hhk hlk
    subst hkk
    rcases headTotalG_cases hhead with h | h | h | h | h | h | h | h
    · rw [hct] at h; cases h
    · rw [hhk] at h; cases h.1
    · rw [divHooks_isHook h.1] at hhk; cases hhk
    · simp only [Semantics.iteHead, hhk, hlk, Bool.not_false, Bool.true_and, Bool.and_eq_true,
        beq_iff_eq, Semantics.iteSig] at h
      obtain ⟨himpl, hA⟩ := h
      rw [hA] at hsrt
      obtain ⟨w₀, w₁, w₂, rfl, h0, h1, h2⟩ := sortsOf_three hsrt
      obtain ⟨bb, rfl⟩ := shape_bool hs h0
      rw [paramVal_ite hlk himpl bb (by cases bb <;> assumption)] at hr
      exact ⟨_, hr⟩
    · simp only [Semantics.totalParam, Bool.and_eq_true] at h
      obtain ⟨⟨-, htp⟩, hpk⟩ := h
      rw [hlk] at hpk
      have hi : kp.impl = none := Option.isNone_iff_eq_none.mp hpk
      have hmem : kp ∈ c.params := by
        rw [Semantics.lookupParam_eq] at hlk; exact List.mem_of_find?_eq_some hlk
      have hname : kp.sig.name = f := by
        rw [Semantics.lookupParam_eq] at hlk
        have h1 := List.find?_some hlk
        exact beq_iff_eq.mp h1
      obtain ⟨v, hv, hsv⟩ := hH kp hmem hi (hname ▸ List.contains_iff_mem.mp htp) ws hsrt
      rw [hname] at hv
      rw [paramVal_of_total hlk hi hv hsv] at hr
      exact ⟨v, hr⟩
    · rw [hp] at h; cases h.2.1
    · simp only [Semantics.mapItemHead, hhk, hlk, Bool.not_false, Bool.true_and, Bool.and_eq_true,
        beq_iff_eq] at h
      obtain ⟨himpl, h⟩ := h
      split at h
      · rename_i a b co hargs hco
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨hkind, hkey⟩, hval⟩ := h
        rw [hargs] at hsrt
        obtain ⟨w₁, w₂, rfl, h1, h2⟩ := sortsOf_two hsrt
        rw [paramVal_mapItem hlk himpl hco hkind hval (hkey ▸ h1) h2] at hr
        exact ⟨_, hr⟩
      · cases h
    · rw [(c.isOvl_parts h).2.2.1] at hp; cases hp

include hok hc hs hco hH hall in
/-- **Every evaluation of a function `totalOKG` accepts whose clauses' variables are held (or of a
total one) at an argument list of its sorts gives a value**, by induction on the evaluation. The
held variables are read of the function evaluated alone, where no clause applies. -/
theorem eval_value_of_GN {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm} (h : Eval c f vs r) :
    TotM1N c tp f vs r :=
  Eval.rec (motive_1 := fun f vs r _ => TotM1N c tp f vs r)
    (motive_2 := fun vs cl _ => cl.pre = .top → ∀ σ, c.WellSorted cl.vars σ → PatVals c σ cl.pats vs →
      TotReq c c.totalLabels tp σ cl)
    (motive_3 := fun σ cl _ => cl.pre = .top → c.WellSorted cl.vars σ → TotReq c c.totalLabels tp σ cl)
    (motive_4 := fun σ t r _ => TotM4 c c.totalLabels tp σ t r)
    (motive_5 := fun σ ts rs _ => TotM5 c c.totalLabels tp σ ts rs)
    (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    -- a clause decides
    (fun {f fn₀ vs cl σ r} hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost _ _ _ ihrhs _ _ => by
      intro fn hlook hT hvs
      have e : fn = fn₀ := Option.some.inj (hlook.symm.trans hfn)
      subst e
      rcases hT with hT | ⟨hfn', hokG, hb⟩
      · obtain ⟨v, hv⟩ := hT fn hfn vs hvs
        exact ⟨v, Eval.functional hco (Eval.clause hfn hmem hσ hmatch hreq hpre hprio hex hrhs hens hpost) hv⟩
      · obtain ⟨L, hL, hrs⟩ := hc.sort.fns fn (List.mem_append_left _ hfn')
        simp only [Semantics.totalOKG, Bool.and_eq_true, List.all_eq_true] at hokG
        refine ihrhs L hL cl.vars hσ _ (hrs cl hmem) (reqLits cl.req) (fun l hl => ?_) (hokG.1.2 cl hmem)
        cases hq : cl.req with
        | none => rw [hq] at hl; simp [reqLits] at hl
        | some q =>
          rw [hq] at hl
          exact lits_sound (hreq q hq) hl)
    -- no clause applies
    (fun {f fn₀ vs} hfn hnone ihnone => by
      intro fn hlook hT hvs
      have e : fn = fn₀ := Option.some.inj (hlook.symm.trans hfn)
      subst e
      rcases hT with hT | ⟨hfn', hokG, hb⟩
      · obtain ⟨v, hv⟩ := hT fn hfn vs hvs
        exact ⟨v, Eval.functional hco (Eval.rest hfn hnone) hv⟩
      · exfalso
        simp only [Semantics.totalOKG, Bool.and_eq_true] at hokG
        replace hokG := hokG.1
        have hcls : ∀ cl ∈ fn.clauses, sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args := fun cl hcl =>
          clauseSorted_of_sortedOK hok hfn' hcl
        have htops : ∀ cl ∈ fn.clauses, cl.pre = .top :=
          Semantics.sortedOK_preTop hok fn (List.mem_append_left _ hfn')
        have htyped : ∀ r ∈ c.coverRowsG (c.fns.map Fn.sig) c.totalLabels tp fn,
            ∃ vars, RowTyped c vars fn.args r := by
          intro r hr
          rcases mem_coverRowsG hr with ⟨cl, hcl, _, _, rfl⟩ | ⟨cl, cl', hp, _, rfl⟩
          · exact ⟨cl.vars, rowTyped_of_sorts (hcls cl hcl)⟩
          · exact ⟨cl.vars, rowTyped_of_sorts (hcls cl (mem_pairs hp).1)⟩
        obtain ⟨r, hr, hm⟩ := covers_sound _ fn.args _ hokG.1.2 htyped vs hvs
        rcases mem_coverRowsG hr with ⟨cl, hcl, hreq, hnd, rfl⟩ | ⟨cl, cl', hp, hg, rfl⟩
        · -- the match on the patterns' variables extends to every variable (`RightHeld`)
          obtain ⟨σ, hσ, hpv⟩ := matches_of_rowRH (hcls cl hcl) hnd hvs hm
          have hcv : cl.condVars = [] := by
            simp [Clause.condVars, hreq, (Semantics.sortedOK_clause hok hfn' hcl).1, varOccsCond]
          have hσL : c.WellSortedAt cl.vars cl.leftVars σ := fun i hi =>
            hσ i (by simpa [Clause.leftVars, hcv] using hi)
          obtain ⟨σ', hws, hag⟩ := Semantics.extendHeld (hb cl hcl) hσL
          obtain ⟨t, ht, _⟩ := ihnone cl hcl (htops cl hcl) σ' hws
            (PatVals.congr_varsRH hpv fun j hj => hag j (List.mem_append_left _ hj))
          rw [hreq] at ht; cases ht
        · obtain ⟨hcl, hcl'⟩ := mem_pairs hp
          simp only [Semantics.guardPair, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hg
          obtain ⟨⟨⟨⟨⟨hvv, hpp⟩, hnd⟩, hbd⟩, hnc⟩, hq⟩ := hg
          have hpp := Term.beqList_sound hpp
          obtain ⟨σ, hσ, hpv⟩ := matches_of_row (hcls cl hcl) hbd (nodup_of_eq_true hnd) hvs hm
          obtain ⟨t, ht, hft⟩ := ihnone cl hcl (htops cl hcl) σ hσ hpv
          obtain ⟨t', ht', hft'⟩ := ihnone cl' hcl' (htops cl' hcl') σ (hvv ▸ hσ) (hpp ▸ hpv)
          rw [ht, ht'] at hq
          simp only [Bool.and_eq_true] at hq
          obtain ⟨⟨hg1, hg2⟩, hex⟩ := hq
          obtain ⟨L₁, hL₁, hq₁⟩ := hc.reqs fn (List.mem_append_left _ hfn')
          have hs1 := hq₁ cl hcl
          have hs2 := hq₁ cl' hcl'
          rw [ht] at hs1
          rw [ht'] at hs2
          simp only [reqOK, beq_iff_eq] at hs1 hs2
          have e1 := negT_true hnc (hft L₁ hL₁ hs1 hg1)
          have e2 := negT_true hnc (hft' L₁ hL₁ (hvv ▸ hs2) hg2)
          exact reqsExclusive_sound hex (.inl fun u hu => by
              cases hu; exact (EvalTerm.functional_hdet hco e1).2)
            (fun u hu => by cases hu; exact e1) (fun u hu => by cases hu; exact e2))
    -- a clause decides and its `ensures` is not `true`: no function `totalOKG` accepts has one
    (fun {f fn₀ vs cl σ t w} hfn hmem hσ hmatch hreq hpre hprio hex ht he hw _ _ _ _ => by
      intro fn hlook hT hvs
      have e : fn = fn₀ := Option.some.inj (hlook.symm.trans hfn)
      subst e
      rcases hT with hT | ⟨hfn', hokG, hb⟩
      · obtain ⟨v, hv⟩ := hT fn hfn vs hvs
        exact absurd (Eval.functional hco (Eval.ensFails hfn hmem hσ hmatch hreq hpre hprio hex ht he hw) hv) (by simp)
      · simp only [Semantics.totalOKG, Bool.and_eq_true, List.all_eq_true] at hokG
        have := hokG.2 cl hmem
        rw [ht] at this
        cases this)
    -- a clause with existential variables: `sortedOK` admits none
    (fun hfn hmem _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ => absurd ((Semantics.fnsNoExs_of_sortedOK hok).lookup hfn hmem) hne)
    (fun hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => absurd ((Semantics.fnsNoExs_of_sortedOK hok).lookup hfn hmem) hne)
    -- `Fails`
    (fun _ ih => fun htop σ hσ hm => ih σ (hσ.at _) hm htop hσ)
    -- `ReqFails`
    (fun {σ cl t r} ht he hr ihe => by
      intro _ hσ
      refine ⟨t, ht, fun L hL hsort htt => ?_⟩
      obtain ⟨v, rfl⟩ := ihe L hL cl.vars hσ _ hsort [] (by simp) htt
      have hsv := EvalTerm.sorted hc.sort he hL hσ hsort rfl
      obtain ⟨b, rfl⟩ := shape_bool hs hsv
      cases b
      · exact he
      · exact absurd rfl hr)
    -- `ReqFails` by the predicate: none is false, the predicate being `\top`
    (fun {σ cl} h _ => by
      intro htop
      rw [htop] at h
      exact absurd h.top_eq (by simp))
    -- variables
    (fun {σ i} => by
      intro L hL vars hσ s ht _ _ _
      obtain ⟨v, hv, _⟩ := hσ i s (sortOfTerm_var.mp ht)
      exact ⟨v, hv⟩)
    -- domain values
    (fun _ _ _ _ _ _ _ _ _ => ⟨_, rfl⟩)
    -- injections
    (fun {σ a b t r} _ ih => by
      intro L hL vars hσ s ht fs hfs htt
      obtain ⟨_, ht', _⟩ := sortOfTerm_inj.mp ht
      obtain ⟨v, rfl⟩ := ih L hL vars hσ _ ht' fs hfs (by simpa [Semantics.totalTermG] using htt)
      exact ⟨_, rfl⟩)
    -- constructors
    (fun {σ f ts rs} _ _ ihts => by
      intro L hL vars hσ s ht fs hfs htt
      simp only [Semantics.totalTermG, Bool.and_eq_true] at htt
      obtain ⟨k, _, hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨ws, rfl⟩ := ihts L hL vars hσ _ hargs fs hfs htt.2
      exact ⟨_, by rw [allSome_map_some]; rfl⟩)
    -- interpreted symbols
    (fun hct hhk hts hh _ ihts => tot_hookN hok hc hs hco hct hhk hts hh ihts)
    -- parameters
    (fun hct hhk hp hts hr ihts => tot_paramN hc hs hH hct hhk hp hts hr ihts)
    -- calls
    (fun hct hhk hts hvs hev hp ihts ihf => tot_callN hc hall hct hhk hts hvs hev hp ihts ihf)
    -- calls with an undefined argument
    (fun {σ f ts rs} _ _ _ hvs _ ihts => by
      intro L hL vars hσ s ht fs hfs htt
      simp only [Semantics.totalTermG, Bool.and_eq_true] at htt
      obtain ⟨k, _, hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨ws, rfl⟩ := ihts L hL vars hσ _ hargs fs hfs htt.2
      rw [allSome_map_some] at hvs; cases hvs)
    -- overloading symbols: the normal form of the arguments' values
    (fun {σ f ts rs} _ _ _ _ ihts => by
      intro L hL vars hσ s ht fs hfs htt
      simp only [Semantics.totalTermG, Bool.and_eq_true] at htt
      obtain ⟨k, _, hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨ws, rfl⟩ := ihts L hL vars hσ _ hargs fs hfs htt.2
      exact ⟨_, by rw [allSome_map_some]; rfl⟩)
    -- a function overload covers the arguments: `headTotalG` admits no function-overloaded symbol
    (fun {σ f ts rs vs o kg r} _ ho _ _ _ hcov _ _ _ => by
      intro L hL vars hσ s ht fs hfs htt
      simp only [Semantics.totalTermG, Bool.and_eq_true] at htt
      obtain ⟨o', ho', hkg, hb, -⟩ := OvlLaws.fnCover_some_parts hcov
      have hm := OvlLaws.fnOvlSyms_of_byFn (OvlLaws.mem_of_lookupOvl ho') hkg hb
      rw [(OvlLaws.lookupOvl_spec ho').1] at hm
      have := headTotalG_ovl htt.1 ho
      rw [List.contains_iff_mem.mpr hm] at this
      cases this)
    -- argument lists
    (fun _ _ _ _ _ _ _ _ _ => ⟨[], rfl⟩)
    (fun {σ t ts r rs} _ _ ih1 ih2 => by
      intro L hL vars hσ ss hts fs hfs htt
      obtain ⟨_, _, ht, hts', rfl⟩ := sortsOfTerms_cons.mp hts
      simp only [Semantics.totalTermListG, Bool.and_eq_true] at htt
      obtain ⟨v, rfl⟩ := ih1 L hL vars hσ _ ht fs hfs htt.1
      obtain ⟨vs, rfl⟩ := ih2 L hL vars hσ _ hts' fs hfs htt.2
      exact ⟨v :: vs, rfl⟩)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun _ _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    h

end Induction

/-! The forms over `EvalCtx` (the held variables of every function), from those above. -/
section InductionAll
variable {tot tp : List Sym}
variable (hok : c.sortedOK = true) (hc : EvalCtx c) (hs : c.shapesOK = true) (hco : CoherentAll c) (hH : ParamsTotal c tp c.hooks)
  (hall : ∀ g ∈ c.totalLabels, ∀ gfn, c.lookupFn g = some gfn → Total c g ∨ (gfn ∈ c.fns ∧ c.totalOKG tp gfn = true))

include hc hall in
theorem tot_call {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)} {vs : List GroundTerm}
    {r : Option GroundTerm} (hct : c.isCtor f = false) (hhk : isHook f = false) (hts : EvalTerms c σ ts rs)
    (hvs : allSome rs = some vs) (hev : Eval c f vs r) (hp : c.isParam f = false)
    (ihts : TotM5 c c.totalLabels tp σ ts rs)
    (ihf : TotM1 c tp f vs r) : TotM4 c c.totalLabels tp σ (.app f ts) r :=
  tot_callN hc.toN
    (fun g hg gfn hl => (hall g hg gfn hl).imp id fun h => ⟨h.1, h.2, hc.binds gfn (List.mem_append_left _ h.1)⟩)
    hct hhk hts hvs hev hp ihts (fun fn hl hT hsv => ihf fn hl (hT.imp id fun h => ⟨h.1, h.2.1⟩) hsv)

include hok hc hs hco in
theorem tot_hook {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)} {r : Option GroundTerm}
    (hct : c.isCtor f = false) (hhk : isHook f = true) (hts : EvalTerms c σ ts rs)
    (hh : ∀ vs, allSome rs = some vs → c.hookRes f vs = some r) (ihts : TotM5 c c.totalLabels tp σ ts rs) :
    TotM4 c c.totalLabels tp σ (.app f ts) r :=
  tot_hookN hok hc.toN hs hco hct hhk hts hh ihts

include hc hs hH in
theorem tot_param {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)} {r : Option GroundTerm}
    (hct : c.isCtor f = false) (hhk : isHook f = false) (hp : c.isParam f = true) (hts : EvalTerms c σ ts rs)
    (hr : r = (allSome rs).bind (c.paramVal f)) (ihts : TotM5 c c.totalLabels tp σ ts rs) :
    TotM4 c c.totalLabels tp σ (.app f ts) r :=
  tot_paramN hc.toN hs hH hct hhk hp hts hr ihts

include hok hc hs hco hH hall in
/-- **Every evaluation of a function `totalOKG` accepts (or of a total one) at an argument list of
its sorts gives a value**, by induction on the evaluation. -/
theorem eval_value_of_G {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm} (h : Eval c f vs r) :
    TotM1 c tp f vs r := fun fn hl hT hvs =>
  eval_value_of_GN hok hc.toN hs hco hH
    (fun g hg gfn hl => (hall g hg gfn hl).imp id fun h => ⟨h.1, h.2, hc.binds gfn (List.mem_append_left _ h.1)⟩)
    h fn hl (hT.imp id fun h' => ⟨h'.1, h'.2, hc.binds fn (List.mem_append_left _ h'.1)⟩) hvs

end InductionAll

/-- **`totals_of_rankP` with the held variables asked function by function**: of each function,
its clauses' variables are held (`Semantics.HeldFn`) or it is total where declared `[total]`
(`hheld`). A function of the second kind stands as one named; the induction on evaluation
(`eval_value_of_GN`) reads the held variables of the functions of the first kind alone. -/
theorem totals_of_rankPH (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hheld : ∀ fn ∈ c.fns, c.HeldFn fn ∨ (fn.total = true → Total c fn.label))
    (hterm : ∀ g, Terminates c g) (hco : CoherentAll c) (ord tp : List Sym) (hH : ParamsTotal c tp c.hooks)
    (hnamed : ∀ g ∈ c.totalObligationsRP ord tp, Total c g) :
    ∀ f fn, c.lookupFn f = some fn → fn.total = true → Total c f := by
  have hc := evalCtxN_of_all hok hsr hov
  have named : ∀ fn ∈ c.fns, fn.total = true → c.totalOKG tp fn = false → Total c fn.label :=
    fun fn hfn ht hT => hnamed _ (List.mem_map.mpr ⟨fn, List.mem_filter.mpr ⟨hfn, by
      simp [ht, Semantics.totalOKP, hT]⟩, rfl⟩)
  intro f fn hfn htot
  obtain ⟨hgm, hlab⟩ := lookupFn_spec hfn
  subst hlab
  rcases List.mem_append.mp hgm with hu | hp
  · cases hT : c.totalOKG tp fn
    · exact named fn hu htot hT
    rcases hheld fn hu with hb | hT'
    case inr => exact hT' htot
    have hs : c.shapesOK = true := by
      simp only [Semantics.totalOKG, Bool.and_eq_true] at hT; exact hT.1.1.1
    have hall : ∀ g ∈ c.totalLabels, ∀ gfn, c.lookupFn g = some gfn →
        Total c g ∨ (gfn ∈ c.fns ∧ c.totalOKG tp gfn = true ∧ c.HeldFn gfn) := by
      intro g hg gfn hgfn
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        obtain ⟨hg'm, hg't⟩ := List.mem_filter.mp hg'
        rw [lookupFn_of_memN hc (List.mem_append_left _ hg'm)] at hgfn
        cases hgfn
        cases hT' : c.totalOKG tp gfn
        · exact .inl (named gfn hg'm hg't hT')
        · exact (hheld gfn hg'm).elim (fun hb' => .inr ⟨hg'm, rfl, hb'⟩) fun hT'' => .inl (hT'' hg't)
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
        exact .inl (sortPreds_totalN hc hp)
    intro fn' hfn' vs hvs
    obtain ⟨r, hr⟩ := hterm fn.label fn' hfn' vs hvs
    rw [hfn] at hfn'
    cases hfn'
    obtain ⟨v, rfl⟩ := eval_value_of_GN hok hc hs hco hH hall hr fn hfn (.inr ⟨hu, hT, hb⟩) hvs
    exact ⟨v, hr⟩
  · exact sortPreds_totalN hc hp

/-- **Every function declared `[total]` is total**, in a core that `sortedOK` and `srReady`
accept whose clauses' variables are held (`RightHeld`), every function terminating, evaluation functional and the interpretation total on the
parameters `tp`, given those `totalObligationsRP` names: an evaluation exists (termination) and its
result is a value (`eval_value_of_G`). -/
theorem totals_of_rankP (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hrh : c.RightHeld) (hterm : ∀ g, Terminates c g) (hco : CoherentAll c) (ord tp : List Sym) (hH : ParamsTotal c tp c.hooks)
    (hnamed : ∀ g ∈ c.totalObligationsRP ord tp, Total c g) :
    ∀ f fn, c.lookupFn f = some fn → fn.total = true → Total c f :=
  totals_of_rankPH hok hsr hov (fun _ hfn => .inl (hrh.heldFn hfn)) hterm hco ord tp hH hnamed

/-- **`totals_of_rankP` with the held variables asked of the held-named functions only**
(`Semantics.heldObligations`): of each, `HeldOwed` (its clauses' variables are held, or it has a
result at every argument list, a value where it is `[total]`); the others' are held on the data. -/
theorem totals_of_rankPN (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hheld : ∀ f ∈ c.heldObligations, HeldOwed c f)
    (hterm : ∀ g, Terminates c g) (hco : CoherentAll c) (ord tp : List Sym) (hH : ParamsTotal c tp c.hooks)
    (hnamed : ∀ g ∈ c.totalObligationsRP ord tp, Total c g) :
    ∀ f fn, c.lookupFn f = some fn → fn.total = true → Total c f :=
  totals_of_rankPH hok hsr hov
    (fun _ hfn => (heldOr_of_owed (evalCtxN_of_all hok hsr hov) hheld hfn).imp id And.right) hterm hco ord tp hH hnamed

kernel_rfl Semantics.totalObligationsRP_withHooks :
  ∀ (c : Semantics) (H : HookParams) (ord tp : List Sym),
    (c.withHooks H).totalObligationsRP ord tp = c.totalObligationsRP ord tp

end KCore
