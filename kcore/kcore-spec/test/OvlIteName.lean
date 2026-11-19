/-
  The conjunct of `overloadsOK` "an overloading symbol is not named like `ite` at a sort": no
  witness was found, that is, no semantics that meets every other condition of `coreOK` and
  `FnHyp`, fails only that conjunct, and whose `Γ` has no model. The conjunct appears to be needed
  for the step to be entailed (argued below, not kernel-checked), which is a different failure from
  `Γ` having no model.
  Run from the package root: `lake env lean -j1 test/OvlIteName.lean`.

  Kernel-checked here:
  - `overloadsOK_split`: `overloadsOK` is the conjunction of `ovlsButIte` (its conditions but this
    one) and `ovlsPlain` (this one), for every semantics.
  - `c`, one overloading symbol `Lblite{KCell}` (`ite` at the numbered sort `KCell`, the only
    symbol so named), `Int → K`, overloading nothing: every other condition of `coreOK`, `itesApart`
    among them, and `FnHyp` hold (`meets_others`, `ovlsButIte_c`), and
    `ovlsPlain` does not (`not_ovlsPlain`). So the conjunct is not implied by the others.
  - `pattern_head`, `value_head`, `heads_differ`: for every semantics and every symbol named like
    `ite` at a sort X, a pattern or right-hand side (`Term.kore`) applies it as `Lblite{SortX}(…)`,
    while a value (`GroundTerm.kore`, hence `den`) and the constructor and overload items (`toK`,
    through `consItemsK`) write it under its own name `Lblite{X}(…)`, a different head.

  Argued, not kernel-checked:
  - `Γ` has a model. Of the head `Lblite ⬝ SortX` `Γ` states the overloading symbol's arity
    (`symArityItem`) and, through rules and clauses, what their right-hand sides apply it to; of
    the plain head it states the constructor items and overload equations. Reading both heads
    as the symbol's normal form (`norm`), as the canonical model's `resolve` does once
    `itesApart` holds (`find_ite`), meets each of these as it does for a plainly named symbol.
    Nothing else in `Γ` names `Lblite` at `SortX`: the registry's `Lblite` (`kIte`) is applied
    to a Bool's element first, and `itesApart` leaves no other symbol at X. Building that model in
    the kernel is the canonical model's construction without the conjunct, which it reads through
    `OvlLaws.ovl_parts` (its fourth part, in FaithfulCollPat.lean's `kernel_arity` steps).
  - The step to a value applying the symbol is not entailed. For a rule `… => Lblite{X}(1)`,
    `Step` gives the successor `.ctor o [1]`, whose `den` is the plain head applied to 1, while
    `famEx c r σ` (the rule's right-hand side, `ruleRight`, through `Term.kore`) applies
    `Lblite{SortX}`, and `Γ` equates the two heads nowhere. `c` here has no rule; test/OvlIteSoundC.lean
    adds one and kernel-checks that its theory with the step's closure has a model and that
    `SoundC` fails: the conjunct is asked for soundness, not for `Γ`'s model.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.OvlIteName

open ML

/-- `overloadsOK`'s conditions but "not named like `ite` at a sort": those on each overloading
symbol, and that no pattern applies a function-overloaded symbol (`ovlPatsOK`). -/
def ovlsButIte (c : Semantics) : Bool :=
  (c.ovls.zipIdx.all fun (o, i) =>
    c.isOvl o.sig.name && c.lookupOvl o.sig.name == some o &&
    (Faithful.consSorts c).contains o.sig.result &&
    o.over.all (fun g => (lookupSig c.ctorSigs g).isSome || (c.ovls.take i).any (·.sig.name == g) ||
      c.fns.any (·.label == g)) &&
    (c.ovlOver o).length == o.over.length &&
    (c.ovlOver o).all (c.ovlPairOK o) &&
    ((c.ovlOver o).all fun k1 => (c.ovlOver o).all fun k2 => c.ovlCoherent k1 k2) &&
    (c.ovlClosure o.sig.name).all fun g => !c.fns.any (·.label == g) || o.over.contains g) &&
  c.ovlPatsOK

/-- "An overloading symbol is not named like an instance" (`instDecode?`), which excludes a name
like `ite` at a sort. -/
def ovlsPlain (c : Semantics) : Bool :=
  c.ovls.zipIdx.all fun (o, _) => (instDecode? (c.symName o.sig.name)).isNone

/-- `overloadsOK` is `ovlsButIte` and `ovlsPlain`. -/
theorem overloadsOK_split (c : Semantics) : c.overloadsOK = (ovlsButIte c && ovlsPlain c) := by
  rw [Bool.eq_iff_iff]
  simp only [Semantics.overloadsOK, ovlsButIte, ovlsPlain, List.all_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨h, hp⟩
    refine ⟨⟨fun x hx => ?_, hp⟩, fun x hx => (h x hx).1.1.1.1.1.1.2⟩
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, -⟩, d⟩, e⟩, f⟩, g⟩, k⟩, l⟩ := h x hx
    exact ⟨⟨⟨⟨⟨⟨⟨a, b⟩, d⟩, e⟩, f⟩, g⟩, k⟩, l⟩
  · rintro ⟨⟨h1, hp⟩, h2⟩
    refine ⟨fun x hx => ?_, hp⟩
    obtain ⟨⟨⟨⟨⟨⟨⟨a, b⟩, d⟩, e⟩, f⟩, g⟩, k⟩, l⟩ := h1 x hx
    exact ⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, h2 x hx⟩, d⟩, e⟩, f⟩, g⟩, k⟩, l⟩

/-! ## The two heads of a symbol named like `ite` -/

theorem lblite_plain : iteSort? "Lblite" = none := by decide

/-- A pattern applies a symbol named like `ite` at X as `Lblite{SortX}(…)`. -/
theorem pattern_head {c : Semantics} {f : Sym} {X : String} (hi : iteSort? (c.symName f) = some X)
    (vs : List KoreAML.Var) (ts : List Term) :
    Term.kore c vs (.app f ts) = .app ⟨⟨"Lblite"⟩⟩ [KoreAML.srt X] (Term.koreList c vs ts) := by
  simp only [Term.kore, hi]

/-- A value writes every constructor term under its symbol's own name. -/
theorem value_head (c : Semantics) (f : Sym) (vs : List GroundTerm) :
    GroundTerm.kore c (.ctor f vs) = .app ⟨⟨c.symName f⟩⟩ [] (GroundTerm.koreList c vs) := by
  simp only [GroundTerm.kore]

/-- The constructor and overload items name a symbol by its own name. -/
theorem toK_name (c : Semantics) (k : CtorSig) :
    toK c k = ⟨c.symName k.name, k.args.map c.sortName, c.sortName k.result⟩ := rfl

/-- The two heads differ: the own name of a symbol named like `ite` at a sort is not `Lblite`. -/
theorem heads_differ {c : Semantics} {f : Sym} {X : String} (hi : iteSort? (c.symName f) = some X) :
    c.symName f ≠ "Lblite" := fun h => by rw [h, lblite_plain] at hi; cases hi

/-! ## A semantics that fails the conjunct only -/

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

/-- The overloading symbol `Lblite{KCell} : Int → K`, overloading nothing. -/
def fSig : CtorSig := ⟨nRegSyms + 4, [Srt.int], Srt.k⟩
def o : OvlSig := ⟨fSig, []⟩

def c : Semantics :=
  { lib := { ctors := [⟨kconfigValue, [Srt.k], Srt.kitem⟩] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblite{KCell}"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := []
    ovls := [o] }

theorem sortedOK : c.sortedOK = true := by decide_cheap

/-- `c` has no function: `FnHyp` holds. -/
theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

set_option maxHeartbeats 1000000 in
/-- Every condition of `coreOK` but `overloadsOK` holds, and `FnHyp`. -/
theorem meets_others : c.sortedOK = true ∧ c.faithCoreOK = true ∧
    c.predsApart = true ∧ c.idsOK = true ∧ FnHyp c :=
  ⟨sortedOK, by decide_cheap, by decide_cheap, by decide_cheap, fnHyp⟩

/-- Every condition of `overloadsOK` but this one holds. -/
theorem ovlsButIte_c : ovlsButIte c = true := by decide +kernel

/-- The conjunct fails: the overloading symbol is named like `ite` at `KCell`. -/
theorem not_ovlsPlain : ovlsPlain c = false := by decide +kernel

theorem not_overloadsOK : c.overloadsOK = false := by
  rw [overloadsOK_split, not_ovlsPlain, Bool.and_false]

theorem ite_f : iteSort? (c.symName fSig.name) = some "KCell" := by decide +kernel

/-- `itesApart` holds: `Lblite{KCell}` is the only symbol named like an instance, at a numbered
sort. -/
theorem itesApart_c : Model.itesApart c = true := by decide_cheap

/-- In `c`, a right-hand side applying the symbol and the value it builds have different heads. -/
theorem rhs_value_heads (vs : List KoreAML.Var) (ts : List Term) (ws : List GroundTerm) :
    Term.kore c vs (.app fSig.name ts) = .app ⟨⟨"Lblite"⟩⟩ [KoreAML.srt "KCell"] (Term.koreList c vs ts) ∧
    GroundTerm.kore c (.ctor fSig.name ws) = .app ⟨⟨"Lblite{KCell}"⟩⟩ [] (GroundTerm.koreList c ws) :=
  ⟨pattern_head ite_f vs ts, value_head c fSig.name ws⟩

end KCore.Faithful.OvlIteName
