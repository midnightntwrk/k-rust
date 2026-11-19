/-
  KCore. The decidable conditions on a semantics that the matching-logic theory `Γ`
  (Faithful.lean) reads beyond `okAll` and `srReady`, joined in one check, `Semantics.faithOK`,
  which `wf` reads (Tie.lean).

  Step soundness (FaithfulSound.lean, `HypSound`) reads that the names and sort numbers of the
  functions are well formed (`namesNumbered`), that values are generated (`genWf`), that no
  collection sort holds a domain value (`collSortsOK`), that the definition's collections are
  built by the parameters their names denote (`collsOK`), and that every symbol a left-hand side
  may apply is one the downward reading covers (`patHeadsOK`). The existence of a model
  (ModelCarrier.lean, `HypModel`) reads in addition that symbols and sorts are named apart
  (`namesApartK`), literals told apart by their text (`LitsApart`), the sorts of values and
  symbols numbered (`sortsNumbered`), collection symbols apart from constructors
  (`collsNotCtors`), symbols named like `ite` apart by their sort (`itesApart`), hooks,
  parameters and constructors apart (`kindsApart`), each constructor listed once (`ctorsOnce`),
  and functions apart from the other kinds (`fnsApart`). The two facts of those hypotheses that
  `wf` decides by its other conjuncts are not repeated: the map pattern symbols are not
  constructors (`patHooksApart`, `NamesApart.patHooks_of_wf`), and the definition's own sorts and
  symbols are numbered (`idsOK`, a conjunct of `namesOK`).
-/
import KcoreSpec.Evaluation
import KcoreSpec.Emit
import KcoreSpec.Kore.Distinct
import KcoreSpec.RightHeld

set_option autoImplicit false

namespace KCore

/-- The library collection of a kind (whose hooks a collection sort's symbols have). A range map's
is RANGEMAP's sort and symbols, the fourth row of `builtinColls`. -/
def builtinColl : CollKind → CollSig
  | .map => builtinColls[0] | .set => builtinColls[1] | .list => builtinColls[2]
  | .rangeMap => ⟨Srt.rangeMap, .rangeMap, Srt.range, some Srt.kitem, rmUnit, rmElem, rmConcat⟩

namespace Faithful

/-- Every sort the semantics numbers: the registry's and the definition's own. -/
def kernelSorts (c : Semantics) : List Srt := List.range (nRegSorts + c.sortNames.length)

/-- Every symbol the semantics gives a signature: its constructors, its functions (the sort
predicates among them), its parameter symbols, the interpreted hooked symbols and its overloading
symbols. -/
def kernelSyms (c : Semantics) : List CtorSig :=
  c.ctorSigs ++ c.allFns.map Fn.sig ++ c.params.map (·.sig) ++ hookSigs ++ c.ovlSigs

/-- The constructor sorts: K, KItem, the definition's sorts (the cell sorts among them) and the
library's sorts with generators, less the definition's own collection sorts (`c.colls`, whose
values are collections), the token sorts (`c.lib.tokenSorts`, whose values are their literals)
and the sorts hooked to a library carrier (`c.lib.carriers`, whose values are its literals). -/
def consSorts (c : Semantics) : List Srt :=
  ([Srt.k, Srt.kitem] ++ sortBy c.sortName (c.userSorts ++ c.libCtorSorts)).filter
    fun s => !(c.colls.any (·.sort == s)) && !c.lib.tokenSorts.contains s && c.lib.carriers.all (·.1 != s)

/-- `Semantics.sortName` with the semantics' own names read from an array. -/
def sortNameArrCs (a : Array String) (s : Srt) : String :=
  if s < nRegSorts then regSortNames.getD s "" else a.getD (s - nRegSorts) ""

theorem sortNameArrCs_toArray (c : Semantics) : sortNameArrCs c.sortNames.toArray = c.sortName := by
  funext s
  simp only [sortNameArrCs, Semantics.sortName, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]

/-- Inserting by a key is inserting the element paired with its key by the pair's first component. -/
theorem insertBy_keyedCs {α β : Type} [LT β] [DecidableRel (α := β) (· < ·)] (key : α → β) (a : α)
    (l : List α) :
    insertBy Prod.fst (key a, a) (l.map fun x => (key x, x)) = (insertBy key a l).map fun x => (key x, x) := by
  induction l with
  | nil => rfl
  | cons b bs ih => by_cases h : key a < key b <;> simp [insertBy, h, ih]

/-- Sorting by a key is sorting the elements paired with their keys by the pairs' first components. -/
theorem sortBy_keyedCs {α β : Type} [LT β] [DecidableRel (α := β) (· < ·)] (key : α → β) (l : List α) :
    sortBy Prod.fst (l.map fun x => (key x, x)) = (sortBy key l).map fun x => (key x, x) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [sortBy, List.map_cons, List.foldr_cons] at ih ⊢; rw [ih, insertBy_keyedCs]

/-- `consSorts`, with each sort's name computed once, from an array, and sorted as a pair with it. -/
def consSortsArr (c : Semantics) : List Srt :=
  let nm := c.sortNames.toArray
  ([Srt.k, Srt.kitem] ++
      (sortBy Prod.fst ((c.userSorts ++ c.libCtorSorts).map fun s => (sortNameArrCs nm s, s))).map Prod.snd).filter
    fun s => !(c.colls.any (·.sort == s)) && !c.lib.tokenSorts.contains s && c.lib.carriers.all (·.1 != s)

@[csimp] theorem consSorts_eq_arr : @consSorts = @consSortsArr := by
  funext c
  simp only [consSorts, consSortsArr, sortNameArrCs_toArray, sortBy_keyedCs, List.map_map, Function.comp_def,
    List.map_id']

/-- A constructor sort is its own carrier. -/
theorem carrier_of_consSorts {c : Semantics} {s : Srt} (h : s ∈ consSorts c) : c.lib.carrier s = s := by
  unfold consSorts at h
  exact Lib.carrier_of_not _ (by simp only [List.mem_filter, Bool.and_eq_true] at h; exact h.2.2)

/-- The sorts whose distinct values denote distinct elements: Int, Bool, KConfigVar (whose values
are its tokens, `dvOK`), Float, String and Bytes (whose values are their literals, whatever the
imports), the library's token and byte sorts, every collection sort, and the sorts hooked to a
library carrier. -/
def distinctSorts (c : Semantics) : List Srt :=
  [Srt.int, Srt.bool, Srt.kconfigVar, Srt.float, Srt.string, Srt.bytes] ++ c.lib.tokenSorts ++ c.lib.byteSorts ++
    c.allColls.map (·.sort) ++ c.lib.carriers.map (·.1)

/-- The value sort of the map collection `k`, at which `Γ` reads its entries' values: its `val`,
and the sort 0 for a collection without one (a set's or a list's axioms read no value sort). -/
def valSort (k : CollSig) : Srt := k.val.getD 0

/-- A sort whose distinct values `Γ` makes distinct elements: K and the sorts below KItem, by the
graph of `_==K_`; the sorts of `distinctSorts`, by the distinctness axiom. -/
def apartSort (c : Semantics) (s : Srt) : Bool :=
  s == Srt.k || s == Srt.kitem || c.sortsBelowKItem.contains s || (distinctSorts c).contains s

/-- **Generated values.** Every constructor's result sort and every subsort pair's upper sort is a
constructor sort, no subsort pair is reflexive, a constructor sort has no domain values and is no
collection sort, the constructor sorts are `apartSort`, and an open generator's (a raw parameter's)
result sort is a constructor sort, which is flat: no constructor and no overloading symbol bears the
open generator's name, every constructor of its result sort has no argument, no overloading
symbol has that result sort and no subsort pair has it as upper sort. Decidable on the data. It
says that a
value of a constructor sort is a constructor or an injection applied to values, which is what makes
the constructors' axioms of `Γ` (read at that sort) describe it (a Float literal's sort, Float, is no
constructor sort), and that distinct values of every
sort are distinct elements (KConfigVar's by `distinctSorts`). Flatness makes the constructors of an
open generator's sort nullary and lets no injection and no overloading symbol end at that sort, so
a constructor of the sort builds one element, a value's. -/
def genWf (c : Semantics) : Bool :=
  c.ctorSigs.all (fun k => (consSorts c).contains k.result) &&
  c.subsorts.all (fun p => (consSorts c).contains p.2 && p.1 != p.2) &&
  (consSorts c).all (fun s => apartSort c s && s != Srt.int && s != Srt.bool && s != Srt.kconfigVar &&
    !c.lib.tokenSorts.contains s && !c.lib.byteSorts.contains s && (c.collOf s).isNone && s != Srt.float &&
    s != Srt.string && s != Srt.bytes) &&
  c.params.all (fun k => !k.raw || (consSorts c).contains k.sig.result) &&
  c.params.all (fun k => !k.raw ||
    (c.ctorSigs.all (fun g => g.name != k.sig.name && (g.result != k.sig.result || g.args.isEmpty)) &&
     c.ovlSigs.all (fun g => g.name != k.sig.name && g.result != k.sig.result) &&
     c.subsorts.all (fun p => p.2 != k.sig.result)))

/-- A collection sort holds no domain value: it is not Int, Bool, KConfigVar, Float, String, Bytes,
or a token or byte sort of the library. Decidable on the data. -/
def collSortOK (c : Semantics) (s : Srt) : Bool :=
  s != Srt.int && s != Srt.bool && s != Srt.kconfigVar && !c.lib.tokenSorts.contains s &&
    !c.lib.byteSorts.contains s && s != Srt.float && s != Srt.string && s != Srt.bytes &&
    c.lib.carriers.all (·.1 != s)

/-- A collection sort is its own carrier. -/
theorem carrier_of_collSortOK {c : Semantics} {s : Srt} (h : collSortOK c s = true) : c.lib.carrier s = s :=
  Lib.carrier_of_not _ (by unfold collSortOK at h; simp only [Bool.and_eq_true] at h; exact h.2)

/-- Every collection sort of the semantics holds no domain value. -/
def collSortsOK (c : Semantics) : Bool := c.allColls.all fun k => collSortOK c k.sort

/-- The argument sorts of a collection's element symbol: key and value (`valSort`) for a map or a
range map, the element sort otherwise. -/
def elemArgs (k : CollSig) : List Srt :=
  match k.kind with
  | .map | .rangeMap => [k.key, valSort k]
  | _ => [k.key]

/-- The definition's collection `k` is the collection of its sort (`collOf`), and its unit,
element and concatenation are parameter symbols, not named like a hook or like an instance of a
sort-parametric symbol (`instDecode?`),
whose declarations (the first of their names) have the collection's sorts and are implemented by
the library's symbols of its kind; a map collection has a value sort. Decidable on the data;
`collOK` (which `wf` checks) says that such parameters are declared, this says that they are the
ones the names denote. -/
def collSymsOK (c : Semantics) (k : CollSig) : Bool :=
  decide (c.collOf k.sort = some k) &&
  [k.unit, k.elem, k.concat].all (fun f => !isHook f && (instDecode? (c.symName f)).isNone) &&
  decide (c.lookupParam k.unit = some { sig := ⟨k.unit, [], k.sort⟩, impl := some (builtinColl k.kind).unit }) &&
  decide (c.lookupParam k.elem = some { sig := ⟨k.elem, elemArgs k, k.sort⟩, impl := some (builtinColl k.kind).elem }) &&
  decide (c.lookupParam k.concat =
    some { sig := ⟨k.concat, [k.sort, k.sort], k.sort⟩, impl := some (builtinColl k.kind).concat }) &&
  (k.kind != .map || k.val.isSome)

/-- A parameter implemented by a map pattern symbol or by a set or list one (`collPatternHooks`): a
collection pattern symbol when it is not a hook (`isCollPat`). -/
def collImpl (kp : ParamSig) : Bool :=
  match kp.impl with
  | some g => patternHooks.contains g || collPatternHooks.contains g
  | none => false

/-- The definition's collections are well formed (`collSymsOK`), and every parameter implemented by
a map, set or list pattern symbol (`collImpl`) is the unit, element or concatenation of one of
them. Decidable on the data. -/
def collsOK (c : Semantics) : Bool :=
  c.colls.all (collSymsOK c) &&
  c.params.all fun kp => !collImpl kp ||
    c.colls.any fun k => kp.sig.name == k.unit || kp.sig.name == k.elem || kp.sig.name == k.concat

/-- A pattern symbol the downward reading covers, besides the constructors: a map pattern symbol,
a collection pattern symbol (`isCollPat`: the library set's and list's, a parameter implemented
by a map, set or list pattern symbol) or an overloading symbol (`isOvl`). -/
def downHead (c : Semantics) (f : Sym) : Bool := patternHooks.contains f || c.isCollPat f || c.isOvl f

/-- Every symbol a left-hand side's context gives a signature to (`patCtxAll`) is a constructor
or a symbol the downward reading covers (`downHead`). Decidable on the data. -/
def patHeadsOK (c : Semantics) : Bool :=
  c.patCtxAll.heads.all fun k => c.isCtor k.name || downHead c k.name

/-- The names and sort numbers of the functions are well formed: no constructor, and no symbol that
an overloading symbol overloads, is named like an instance of a sort-parametric symbol
(`instDecode?`: a value and an overload's equation write such a symbol under its name), and every
sort of a function is a numbered sort. `NamesNumbered` (Faithful.lean) follows from it. -/
def namesNumbered (c : Semantics) : Bool :=
  c.ctorSigs.all (fun k => (instDecode? (c.symName k.name)).isNone) &&
  c.ovls.all (fun o => o.over.all fun g => (instDecode? (c.symName g)).isNone) &&
  c.allFns.all fun fn => (fn.result :: fn.args).all fun s => decide (s < nRegSorts + c.sortNames.length)

namespace Model

/-- `NamesApartK`, decided. -/
def namesApartK (c : Semantics) : Bool :=
  (kernelSyms c).all (fun k => (kernelSyms c).all fun k' => c.symName k.name != c.symName k'.name || k == k') &&
  (kernelSyms c).all (fun k => c.symName k.name != "inj") &&
  (kernelSorts c).all (fun s => (kernelSorts c).all fun s' => c.sortName s != c.sortName s' || s == s')

/-- No token or byte sort of the library is Int, Bool or Float: a literal's text then determines the
literal at each sort (`Lit.text` on the literals `dvOK` admits). -/
def LitsApart (c : Semantics) : Bool :=
  !(c.lib.tokenSorts ++ c.lib.byteSorts).contains Srt.int &&
  !(c.lib.tokenSorts ++ c.lib.byteSorts).contains Srt.bool &&
  !(c.lib.tokenSorts ++ c.lib.byteSorts).contains Srt.float

/-- Every sort a value may have, and every sort of a symbol the semantics gives a signature, is a
numbered sort (`kernelSorts`): the sorts of `kernelSyms` (a constructor term has its constructor's
result sort), both sorts of each subsort pair (an injection has its upper one), the library's
token and byte sorts (whose literals are values), and the sorts of every collection. The
interpretation reads a sort by its name among the numbered sorts only, so a value of any other
sort would denote no element of its sort. `NamesNumbered` says this of the functions only, and
`idsOK` of the definition's own sorts only. -/
def sortsNumbered (c : Semantics) : Bool :=
  (kernelSyms c).all (fun k => (k.result :: k.args).all fun s => decide (s < nRegSorts + c.sortNames.length)) &&
  c.subsorts.all (fun p => decide (p.1 < nRegSorts + c.sortNames.length) && decide (p.2 < nRegSorts + c.sortNames.length)) &&
  (c.lib.tokenSorts ++ c.lib.byteSorts ++ c.lib.carriers.map (·.1)).all (fun s => decide (s < nRegSorts + c.sortNames.length)) &&
  c.allColls.all (fun k => decide (k.sort < nRegSorts + c.sortNames.length) &&
    decide (k.key < nRegSorts + c.sortNames.length) && decide (valSort k < nRegSorts + c.sortNames.length))

/-- No unit, element or concatenation symbol of a collection is a constructor: the interpretation
reads a constructor first, so such a symbol would build a constructor term where the collection's
value is meant. `patHooksApart` says this of the library map's symbols only. -/
def collsNotCtors (c : Semantics) : Bool :=
  c.allColls.all fun k => [k.unit, k.elem, k.concat].all fun f => !c.isCtor f

/-- Every symbol with a signature whose name the decoder reads as an instance `h{x₁,…,xₙ}` of a
sort-parametric symbol `h` (`instDecode?`) is named at numbered sorts, all such symbols of one head
are named at one number of sorts, and no such head is `inj`. The interpretation reads the head `h`
applied to sort arguments as the instance named at those sorts (`resolve`, for `Lblite` at one
sort, which `Γ` writes so: `symArityItem`, the graphs of `ΓDomains`), so a sort name that names no
sort would leave the instance's graph without an element; a head at two numbers of sorts would make
`h` applied to its first sorts both a result and a partial application; and `inj` is the head of
the injections. Two instance-named symbols with one decoding are one symbol, by `namesApartK` and
the decoder's exactness (`instsApart`). -/
def itesApart (c : Semantics) : Bool :=
  (kernelSyms c).all fun k =>
    (match instDecode? (c.symName k.name) with
      | some (_, xs) => xs.all fun x => (kernelSorts c).any fun s => c.sortName s == x
      | none => true) &&
    (match instDecode? (c.symName k.name) with
      | some (h, xs) => (kernelSyms c).all fun k' =>
          match instDecode? (c.symName k'.name) with
          | some (h', xs') => h' != h || xs'.length == xs.length
          | none => true
      | none => true) &&
    (match instDecode? (c.symName k.name) with
      | some (h, _) => h != "inj"
      | none => true)

/-- What `itesApart` says of an instance-named symbol of `kernelSyms`: its sort names name
numbered sorts, every symbol of `kernelSyms` named at the same head has as many sorts, and the
head is not `inj`. -/
theorem itesApart_inst {c : Semantics} (h : itesApart c = true) {k : CtorSig} (hk : k ∈ kernelSyms c)
    {hd : String} {xs : List String} (hi : instDecode? (c.symName k.name) = some (hd, xs)) :
    (∀ x ∈ xs, ∃ s ∈ kernelSorts c, c.sortName s = x) ∧
    (∀ k' ∈ kernelSyms c, ∀ xs' : List String, instDecode? (c.symName k'.name) = some (hd, xs') →
      xs'.length = xs.length) ∧
    hd ≠ "inj" := by
  have h1 := List.all_eq_true.mp h k hk
  simp only [hi, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq] at h1
  obtain ⟨⟨h1, h2⟩, h3⟩ := h1
  refine ⟨h1, fun k' hk' xs' hi' => ?_, h3⟩
  have := h2 k' hk'
  simp only [hi', bne_self_eq_false, Bool.false_or, beq_iff_eq] at this
  exact this

/-- **Two symbols of `kernelSyms` with one decoding are one symbol**: their names are one name
(`instDecode?_inj`), and `namesApartK` names distinct symbols apart. -/
theorem instsApart {c : Semantics} (hn : namesApartK c = true) {k k' : CtorSig} (hk : k ∈ kernelSyms c)
    (hk' : k' ∈ kernelSyms c) {p : String × List String} (hi : instDecode? (c.symName k.name) = some p)
    (hi' : instDecode? (c.symName k'.name) = some p) : k = k' := by
  have he := instDecode?_inj hi hi'
  simp only [namesApartK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at hn
  exact (hn.1.1 k hk k' hk').resolve_left (fun hne => hne he)

/-- A symbol of `kernelSyms` named like `ite` at a sort X is named at a numbered sort. -/
theorem itesApart_iteSorted {c : Semantics} (h : itesApart c = true) {k : CtorSig} (hk : k ∈ kernelSyms c)
    {X : String} (hi : iteSort? (c.symName k.name) = some X) : ∃ s ∈ kernelSorts c, c.sortName s = X :=
  (itesApart_inst h hk (iteSort?_eq_some.1 hi)).1 X (List.mem_singleton_self X)

/-- No two symbols of `kernelSyms` are named like `ite` at one sort. -/
theorem itesOnce_of_namesApartK {c : Semantics} (hn : namesApartK c = true) {k k' : CtorSig}
    (hk : k ∈ kernelSyms c) (hk' : k' ∈ kernelSyms c) {X : String} (hi : iteSort? (c.symName k.name) = some X)
    (hi' : iteSort? (c.symName k'.name) = some X) : k = k' :=
  instsApart hn hk hk' (iteSort?_eq_some.1 hi) (iteSort?_eq_some.1 hi')

/-- The interpreted hooks and the parameters are not constructors, and no parameter is an
interpreted hook: the interpretation reads a constructor first, then a hook, then a parameter, so
a symbol of two kinds would be read as the first, against the graph `Γ` states of the other.
`hooksApart` says this of the user's constructors and functions only, and is not part of `Hyp`. -/
def kindsApart (c : Semantics) : Bool :=
  hookSigs.all (fun k => !c.isCtor k.name) &&
  c.params.all (fun kp => !c.isCtor kp.sig.name && !isHook kp.sig.name)

/-- No constructor is listed twice: the names of `ctorSigs` are distinct. `Semantics.gens` reads a
sort's constructors from `ctorSigs`, and `ΓCons` states the distinctness of every pair of them, so
a constructor listed twice is said to be apart from itself (ModelDupCtorWitness.lean).
`namesApartK` does not exclude it: the two entries are one signature. -/
def ctorsOnce (c : Semantics) : Bool := nodup (c.ctorSigs.map (·.name))

/-- No function is named like a constructor, an interpreted hook or a parameter: the interpretation
reads a constructor, then a hook, then a parameter, then a function, so a function of another kind's
name would be read as that symbol, against its equations, and `Γ` has no model when the function's
equation gives the symbol another value than its constructor term (ModelFnCtorWitness.lean).
`idsOK` numbers the user's functions apart from the user's constructors and parameters; the
library's constructors and the registry's parameters are numbered by no check. -/
def fnsApart (c : Semantics) : Bool :=
  c.allFns.all fun fn => !c.isCtor fn.label && !isHook fn.label && !c.isParam fn.label

/-! ### `namesApartK` by sorted codes

`namesApartK` compares every two symbols' names, quadratic in their number. `namesApartFast`
decides the same by the strictly ascending sorted codes of the names (`KoreAML.Distinct`): of the
distinct signatures, and of the numbered sorts. -/

/-- The names of the distinct signatures of `kernelSyms` and those of the numbered sorts are
distinct (their codes, sorted, ascend), and no symbol is named `inj`. -/
def namesApartFast (c : Semantics) : Bool :=
  let ks := (kernelSyms c).eraseDups
  KoreAML.Distinct.codesDistinct (KoreAML.Distinct.passesFor ks.length) (ks.map fun k => c.symName k.name) &&
  (kernelSyms c).all (fun k => c.symName k.name != "inj") &&
  KoreAML.Distinct.codesDistinct (KoreAML.Distinct.passesFor (kernelSorts c).length)
    ((kernelSorts c).map c.sortName)

theorem kore_nodup_spec : ∀ {l : List String}, KoreAML.nodup l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: as, h => by
    simp only [KoreAML.nodup, Bool.and_eq_true] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, kore_nodup_spec h.2⟩
    rw [List.contains_iff_mem.mpr hm] at h
    cases h.1

theorem inj_of_nodup_map {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, _, hx, _, _, _ => absurd hx List.not_mem_nil
  | a :: l, h, x, hx, y, hy, he => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd (he ▸ List.mem_map_of_mem hy') h.1
    · exact absurd (he.symm ▸ List.mem_map_of_mem hx') h.1
    · exact inj_of_nodup_map h.2 x hx' y hy' he

theorem namesApartK_of_fast {c : Semantics} (h : namesApartFast c = true) : namesApartK c = true := by
  simp only [namesApartFast, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have n1 := kore_nodup_spec (KoreAML.Distinct.nodup_of_codes h1)
  have n3 := kore_nodup_spec (KoreAML.Distinct.nodup_of_codes h3)
  simp only [namesApartK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq]
  refine ⟨⟨fun k hk k' hk' => ?_, fun k hk => ?_⟩, fun s hs s' hs' => ?_⟩
  · by_cases he : c.symName k.name = c.symName k'.name
    · exact Or.inr (inj_of_nodup_map n1 k (List.mem_eraseDups.mpr hk) k' (List.mem_eraseDups.mpr hk') he)
    · exact Or.inl he
  · simpa using List.all_eq_true.mp h2 k hk
  · by_cases he : c.sortName s = c.sortName s'
    · exact Or.inr (inj_of_nodup_map n3 s hs s' hs' he)
    · exact Or.inl he

end Model

end Faithful

/-! ## Confined sorts -/

mutual
  /-- The variables a term holds under constructors and injections only. -/
  def ctorOccs (c : Semantics) : Term → List Nat
    | .var i => [i]
    | .app f ts => if c.isCtor f then ctorOccsList c ts else []
    | .inj _ _ t => ctorOccs c t
    | .as t i => ctorOccs c t ++ [i]
    | .dv _ _ => []
    termination_by structural t => t
  def ctorOccsList (c : Semantics) : List Term → List Nat
    | [] => []
    | t :: ts => ctorOccs c t ++ ctorOccsList c ts
    termination_by structural ts => ts
end

/-- Every value of s is a literal: no constructor, overloading symbol, open generator or injection
ends at s, and s is no token, byte, collection or carrier sort. -/
def Semantics.litSort (c : Semantics) (s : Srt) : Bool :=
  c.ctorSigs.all (·.result != s) && c.ovlSigs.all (·.result != s) && c.subsorts.all (·.2 != s) &&
  c.params.all (fun k => !(k.raw && k.sig.result == s)) && (c.collOf s).isNone &&
  !c.lib.tokenSorts.contains s && !c.lib.byteSorts.contains s && c.lib.carriers.all (·.1 != s)

/-- Confined at depth k: Bool with only literals; or a constructor sort with a generator, each of
whose generators takes arguments of sorts confined at a smaller depth and is no overloading symbol
that overloads a function. A sort without a generator is not confined: the text holds no sentence
about which elements it has. A function an overloading generator overloads gives the generator's
application at covered arguments a function's value, which need not be a value's. -/
def Semantics.confinedAt (c : Semantics) : Nat → Srt → Bool
  | 0, s => s == Srt.bool && c.litSort s
  | k + 1, s => c.confinedAt 0 s ||
      ((Faithful.consSorts c).contains s && !(c.gens s).isEmpty &&
        (c.gens s).all fun g => g.argSorts.all (c.confinedAt k) &&
          match g with
          | .ctor kg => c.ovls.all fun o => o.sig.name != kg.name || o.over.all fun f => c.fns.all (·.label != f)
          | .inj _ => true)

/-- **The sorts every element of which the theory states to be a value's.** -/
def Semantics.confined (c : Semantics) (s : Srt) : Bool :=
  c.confinedAt (Faithful.kernelSorts c).length s

/-- The clause's conditions are closed over open variables of which one is not of a confined
sort. -/
def Clause.needsWitness (c : Semantics) (cl : Clause) : Bool :=
  cl.reqOpen && cl.reqClosed && !cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false

namespace Semantics
variable (c : Semantics)

/-- The symbols f reaches along the overloads, f among them, in at most `n` steps. -/
def ovlReach : Nat → Sym → List Sym
  | 0, f => [f]
  | n + 1, f => f :: match c.lookupOvl f with
    | some o => o.over.flatMap (ovlReach n)
    | none => []

/-- The symbols f reaches along the overloads, f among them (f alone for a symbol that overloads
none). -/
def ovlClosure (f : Sym) : List Sym := c.ovlReach (c.ovls.length + 1) f

end Semantics

/-- The functions in the overload closure of f: those of `c.fns` labelled by a symbol of
`ovlClosure f`. -/
def Semantics.fnOverloads (c : Semantics) (f : Sym) : List Fn :=
  (c.ovlClosure f).flatMap fun g => c.fns.filter (·.label == g)

/-- An overloading symbol each function in whose overload closure takes arguments of confined sorts. -/
def Semantics.ovlHeld (c : Semantics) (f : Sym) : Bool :=
  c.isOvl f && (c.fnOverloads f).all fun fn => fn.args.all c.confined

/-- The clause `f(dotk, T) = T` over the one variable `T : K`, with no `requires`, no `ensures`, no
existential variable and `\top` predicates. -/
def Clause.appendDotX (cl : Clause) : Bool :=
  match cl.vars, cl.pats, cl.req, cl.rhs, cl.ens, cl.exs, cl.pre, cl.post with
  | [s], [.app d [], .var 0], none, .var 0, none, [], .top, .top => s == Srt.k && d == dotk
  | _, _, _, _, _, _, _, _ => false

/-- The clause `f(kseq(I, KS), T) = kseq(I, f(KS, T))` over the variables `I : KItem`, `KS : K`,
`T : K`, with no `requires`, no `ensures`, no existential variable and `\top` predicates. -/
def Clause.appendKseqX (f : Sym) (cl : Clause) : Bool :=
  match cl.vars, cl.pats, cl.req, cl.rhs, cl.ens, cl.exs, cl.pre, cl.post with
  | [s0, s1, s2], [.app k0 [.var 0, .var 1], .var 2], none, .app k1 [.var 0, .app g [.var 1, .var 2]],
      none, [], .top, .top =>
    s0 == Srt.kitem && s1 == Srt.k && s2 == Srt.k && k0 == kseq && k1 == kseq && g == f
  | _, _, _, _, _, _, _, _ => false

/-- K's `append`: f is a function of the definition, of `(K, K) → K`, named like no `ite` and no
hooked or parameter symbol, whose clauses are `f(dotk, T) = T` and
`f(kseq(I, KS), T) = kseq(I, f(KS, T))` of one priority (`Clause.appendDotX`,
`Clause.appendKseqX`); K is a constructor sort whose generators are `kseq` and `dotk` alone. Every
element of K is then `dotk` or a `kseq` (K's no-junk item), and the two equations, with `kseq` and
`dotk`'s injectivity and distinctness, make the arguments of an application of f that is a value's
element values' elements. -/
def Semantics.appendHeldX (c : Semantics) (f : Sym) : Bool :=
  !isHook f && !c.isParam f && (iteSort? (c.symName f)).isNone && (Faithful.consSorts c).contains Srt.k &&
  (match c.gens Srt.k with
    | [.ctor a, .ctor b] => a == ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩ && b == ⟨dotk, [], Srt.k⟩
    | _ => false) &&
  match c.lookupFn f with
  | some fn => fn.args == [Srt.k, Srt.k] && fn.result == Srt.k &&
    match fn.clauses with
    | [a, b] => a.prio == b.prio && ((a.appendDotX && b.appendKseqX f) || (b.appendDotX && a.appendKseqX f))
    | _ => false
  | none => false

/-- The symbols under which a value's element has values' elements as arguments: the unit, element
and concatenation symbols of a map, list or set collection, an overloading symbol each function
in whose overload closure takes arguments of confined sorts (`ovlHeld`), and K's `append`
(`appendHeldX`). -/
def Semantics.holds (c : Semantics) (f : Sym) : Bool :=
  patternHooks.contains f || c.isCollPat f || c.ovlHeld f || c.appendHeldX f

mutual
  /-- The variables a term holds under constructors, injections and the symbols under which a
  value's element has values' elements as arguments (`holds`). -/
  def heldOccs (c : Semantics) : Term → List Nat
    | .var i => [i]
    | .app f ts => if c.isCtor f || c.holds f then heldOccsList c ts else []
    | .inj _ _ t => heldOccs c t
    | .as t i => heldOccs c t ++ [i]
    | .dv _ _ => []
  def heldOccsList (c : Semantics) : List Term → List Nat
    | [] => []
    | t :: ts => heldOccs c t ++ heldOccsList c ts
end

mutual
  /-- A variable held under constructors and injections only is held (`heldOccs`). -/
  theorem ctorOccs_subset_heldOccs (c : Semantics) : ∀ (t : Term), ∀ i ∈ ctorOccs c t, i ∈ heldOccs c t
    | .var _, i, hi => by simpa [ctorOccs, heldOccs] using hi
    | .app f ts, i, hi => by
      unfold ctorOccs at hi
      unfold heldOccs
      by_cases hf : c.isCtor f = true
      · rw [if_pos hf] at hi
        rw [if_pos (by rw [hf]; rfl)]
        exact ctorOccsList_subset_heldOccsList c ts i hi
      · rw [if_neg hf] at hi
        cases hi
    | .inj _ _ t, i, hi => by
      unfold ctorOccs at hi
      unfold heldOccs
      exact ctorOccs_subset_heldOccs c t i hi
    | .as t j, i, hi => by
      unfold ctorOccs at hi
      unfold heldOccs
      rcases List.mem_append.mp hi with hi | hi
      · exact List.mem_append_left _ (ctorOccs_subset_heldOccs c t i hi)
      · exact List.mem_append_right _ hi
    | .dv _ _, i, hi => by simp [ctorOccs] at hi
  /-- `ctorOccs_subset_heldOccs` over a list of terms. -/
  theorem ctorOccsList_subset_heldOccsList (c : Semantics) :
      ∀ (ts : List Term), ∀ i ∈ ctorOccsList c ts, i ∈ heldOccsList c ts
    | [], i, hi => by simp [ctorOccsList] at hi
    | t :: ts, i, hi => by
      unfold ctorOccsList at hi
      unfold heldOccsList
      rcases List.mem_append.mp hi with hi | hi
      · exact List.mem_append_left _ (ctorOccs_subset_heldOccs c t i hi)
      · exact List.mem_append_right _ (ctorOccsList_subset_heldOccsList c ts i hi)
end

/-- t is the variable i or an injection of it, and `ok` admits every variable of u. -/
def fixesBy (ok : Nat → Bool) (i : Nat) (t u : Term) : Bool :=
  (match t with
   | .var j => j == i
   | .inj _ _ (.var j) => j == i
   | _ => false) && (varOccs u).all ok

/-- The condition, n variables in scope, where it holds equates the variable i with a term whose
variables `ok` admits. Under a binder its variable is admitted where `adm` admits its sort, or
where `val` admits its sort and the body fixes it by a term over the other admitted variables. -/
def Cond.fixes (adm val : Srt → Bool) : (Nat → Bool) → Nat → Nat → Cond → Bool
  | ok, i, _, .mem _ t u => fixesBy ok i t u
  | ok, i, _, .equals _ t u => fixesBy ok i t u || fixesBy ok i u t
  | ok, i, n, .and p q => Cond.fixes adm val ok i n p || Cond.fixes adm val ok i n q
  | ok, i, n, .or p q => Cond.fixes adm val ok i n p && Cond.fixes adm val ok i n q
  | ok, i, n, .ex s body =>
      let here := adm s || (val s && Cond.fixes adm val (fun j => j != n && ok j) n (n + 1) body)
      Cond.fixes adm val (fun j => if j == n then here else ok j) i (n + 1) body
  | _, _, _, _ => false

/-- Each binder of a condition ranges where values and elements agree: an `exMatch` variable is
held by its pattern under constructors and injections, or is of a confined sort; an `ex` variable
is of a confined sort, or of a sort with a value (`Semantics.valued`) where the body fixes it by a
term over the other variables (`Cond.fixes`); an `all` variable is of a confined sort. -/
def Cond.bound (c : Semantics) (n : Nat) : Cond → Bool
  | .exMatch ys _ p _ body =>
      (List.range ys.length).all (fun j =>
        (ctorOccs c p).contains (n + j) || (ys[j]?.map c.confined).getD false) &&
      Cond.bound c (n + ys.length) body
  | .ex s body =>
      (c.confined s || (c.valued s && Cond.fixes c.confined c.valued (fun j => j != n) n (n + 1) body)) &&
      Cond.bound c (n + 1) body
  | .all s body => c.confined s && Cond.bound c (n + 1) body
  | .not p => Cond.bound c n p
  | .and p q | .or p q | .implies p q => Cond.bound c n p && Cond.bound c n q
  | _ => true

/-- The existential variables the predicate fixes, in rounds: by a term over the variables that are
not existential, the other existential ones of a sort `adm` admits and the ones fixed in an
earlier round. -/
def Clause.fixedExs (adm val : Srt → Bool) (cl : Clause) : List Nat :=
  (List.range cl.exs.length).foldl (fun acc _ =>
    cl.exs.filter fun i => acc.contains i ||
      Cond.fixes adm val (fun j => !cl.exs.contains j || acc.contains j ||
        (j != i && (cl.vars[j]?.map adm).getD false)) i cl.vars.length cl.post) []

/-! ## Function-overloaded symbols in patterns -/

mutual
  /-- The applied symbols of a term: the symbol of every application in it, through `as`,
  injections and the arguments of every application (collection pattern symbols among them). -/
  def symOccs : Term → List Sym
    | .var _ => []
    | .app f ts => f :: symOccsList ts
    | .inj _ _ t => symOccs t
    | .as t _ => symOccs t
    | .dv _ _ => []
    termination_by structural t => t
  def symOccsList : List Term → List Sym
    | [] => []
    | t :: ts => symOccs t ++ symOccsList ts
    termination_by structural ts => ts
end

/-- The patterns of a condition: the pattern of each `exMatch` in it, through `not`, `and`, `or`,
`implies`, `ex`, `all` and the body of an `exMatch`. The terms a condition evaluates (an
`exMatch`'s scrutinee, the sides of `ceil`, `equals`, `mem`) are not patterns. -/
def condPats : Cond → List Term
  | .not p => condPats p
  | .and p q => condPats p ++ condPats q
  | .or p q => condPats p ++ condPats q
  | .implies p q => condPats p ++ condPats q
  | .exMatch _ _ p _ body => p :: condPats body
  | .ex _ body => condPats body
  | .all _ body => condPats body
  | .top | .bot | .ceil _ _ | .equals _ _ _ | .mem _ _ _ => []

/-- A generator that is a function-overloaded symbol: an overloading symbol (`isOvl`) with a
declaration, among `fnOvlSyms`. -/
def Semantics.fnOvl (c : Semantics) : Gen → Bool
  | .ctor k => c.isOvl k.name && (c.lookupOvl k.name).isSome && c.fnOvlSyms.contains k.name
  | .inj _ => false

/-- No function-overloaded symbol is applied in a rule's left side, a clause's patterns, or the
pattern of an `exMatch` of a rule's or a clause's `pre` or `post`. -/
def Semantics.ovlPatsOK (c : Semantics) : Bool :=
  let bad := fun (t : Term) => (symOccs t).any c.fnOvlSyms.contains
  c.rules.all (fun r => !bad r.lhs && (condPats r.pre ++ condPats r.post).all (!bad ·)) &&
  c.fns.all fun f => f.clauses.all fun cl =>
    cl.pats.all (!bad ·) && (condPats cl.pre ++ condPats cl.post).all (!bad ·)

/-! ## Overloading symbols -/

namespace Semantics
variable (c : Semantics)

/-- The overload of `o`'s symbol by the symbol of `kg` is well formed: kg has as many arguments,
each of its argument sorts and its result sort at most `o`'s. -/
def ovlPairOK (o : OvlSig) (kg : CtorSig) : Bool :=
  kg.args.length == o.sig.args.length && (kg.args.zip o.sig.args).all (fun (A, B) => c.le A B) &&
    c.le kg.result o.sig.result

/-- The signature `kg` and, for an overloading symbol, the signatures of the symbols it overloads. -/
def ovlDown (kg : CtorSig) : List CtorSig :=
  kg :: match c.lookupOvl kg.name with
    | some o => c.ovlOver o
    | none => []

/-- **Two overloads of one symbol agree**, those of `k1` and `k2`: at some position no sort lies
below both argument sorts (no value lies in both), or a symbol h, `k1` or one it overloads and `k2`
or one it overloads, covers every value lying in both: at each position, each sort at most both
argument sorts is at most h's. -/
def ovlCoherent (k1 k2 : CtorSig) : Bool :=
  let lower := fun (A1 A2 : Srt) => (A1 :: A2 :: c.subsorts.map (·.1)).filter fun C => c.le C A1 && c.le C A2
  (k1.args.zip k2.args).any (fun (A1, A2) => (lower A1 A2).isEmpty) ||
  ((c.ovlDown k1).filter fun h => (c.ovlDown k2).contains h).any fun h =>
    h.args.length == k1.args.length &&
      ((h.args.zip k1.args).zip k2.args).all fun ((H, A1), A2) => (lower A1 A2).all fun C => c.le C H

/-- **The overloading symbols are well formed**: each is an overloading symbol of no other kind
(`isOvl`) declared once, named plainly (not like an instance of a sort-parametric symbol,
`instDecode?`, so its applications in patterns and right-hand sides are written as its values are), of a constructor sort; each symbol it overloads is a constructor, an
overloading symbol listed before it (so the overloads are acyclic and `norm`'s steps suffice) or a
function of the definition, of its arity, with argument and result sorts at most its own
(`ovlPairOK`); any two overloads of one symbol agree (`ovlCoherent`); it lists every function among
the symbols it reaches along the overloads (`ovlClosure`), so that the symbols overloading a
function are those listing one; and no pattern applies a function-overloaded symbol (`ovlPatsOK`).
Decidable on the data. -/
def overloadsOK : Bool :=
  (c.ovls.zipIdx.all fun (o, i) =>
    c.isOvl o.sig.name && c.lookupOvl o.sig.name == some o && (instDecode? (c.symName o.sig.name)).isNone &&
    (Faithful.consSorts c).contains o.sig.result &&
    o.over.all (fun g => (lookupSig c.ctorSigs g).isSome || (c.ovls.take i).any (·.sig.name == g) ||
      c.fns.any (·.label == g)) &&
    (c.ovlOver o).length == o.over.length &&
    (c.ovlOver o).all (c.ovlPairOK o) &&
    ((c.ovlOver o).all fun k1 => (c.ovlOver o).all fun k2 => c.ovlCoherent k1 k2) &&
    (c.ovlClosure o.sig.name).all fun g => !c.fns.any (·.label == g) || o.over.contains g) &&
  c.ovlPatsOK

end Semantics

open Faithful Faithful.Model in
/-- **The decidable conditions of the theory**: what step soundness (`HypSound`) and the existence
of a model (`HypModel`) read of a semantics beyond `okAll`, `srReady`, the map pattern symbols'
apartness from the constructors and the numbering of the definition's own sorts and symbols,
which `wf` decides otherwise. -/
def Semantics.faithOK (c : Semantics) : Bool :=
  namesNumbered c && genWf c && collSortsOK c && collsOK c && patHeadsOK c &&
  namesApartK c && LitsApart c && sortsNumbered c && collsNotCtors c && itesApart c &&
  kindsApart c && ctorsOnce c && fnsApart c

open Faithful Faithful.Model in
/-- **The decidable conditions of the theory that soundness and completeness read**: those of
`faithOK` but `collsNotCtors`, which `kindsApart` and `collsOK` imply (`collsNotCtors_of`,
FaithfulCollPat.lean). -/
def Semantics.faithCoreOK (c : Semantics) : Bool :=
  namesNumbered c && genWf c && collSortsOK c && collsOK c && patHeadsOK c &&
  namesApartK c && LitsApart c && sortsNumbered c && itesApart c &&
  kindsApart c && ctorsOnce c && fnsApart c

open Faithful Faithful.Model in
theorem Semantics.faithCoreOK_of_faithOK {c : Semantics} (h : c.faithOK = true) : c.faithCoreOK = true := by
  simp only [Semantics.faithOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, -⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  simp only [Semantics.faithCoreOK, h1, h2, h3, h4, h5, h6, h7, h8, h10, h11, h12, h13, Bool.and_self]

open Faithful Faithful.Model in
/-- `faithOK` from its conjuncts, the names' apartness by sorted codes (`namesApartFast`): each a
decision of its own. -/
theorem Semantics.faithOK_of_parts {c : Semantics} (h1 : namesNumbered c = true) (h2 : genWf c = true)
    (h3 : collSortsOK c = true) (h4 : collsOK c = true) (h5 : patHeadsOK c = true)
    (h6 : namesApartFast c = true) (h7 : LitsApart c = true) (h8 : sortsNumbered c = true)
    (h9 : collsNotCtors c = true) (h10 : itesApart c = true) (h11 : kindsApart c = true)
    (h12 : ctorsOnce c = true) (h13 : fnsApart c = true) : c.faithOK = true := by
  simp only [Semantics.faithOK, h1, h2, h3, h4, h5, namesApartK_of_fast h6, h7, h8, h9, h10, h11, h12,
    h13, Bool.and_self]

/-! ## Patterns that apply no function-overloaded symbol -/

/-- No symbol applied in `p` is function-overloaded: what `ovlPatsOK` holds of a rule's left side,
a clause's patterns and the pattern of an `exMatch`. -/
abbrev Semantics.NoFnOvlIn (c : Semantics) (p : Term) : Prop := (symOccs p).any c.fnOvlSyms.contains = false

/-- `NoFnOvlIn` of each term of a list. -/
abbrev Semantics.NoFnOvlInL (c : Semantics) (ps : List Term) : Prop :=
  (symOccsList ps).any c.fnOvlSyms.contains = false

namespace NoFnOvlIn
variable {c : Semantics}

theorem app {f : Sym} {ps : List Term} (h : c.NoFnOvlIn (.app f ps)) : f ∉ c.fnOvlSyms ∧ c.NoFnOvlInL ps := by
  unfold Semantics.NoFnOvlIn at h
  rw [symOccs, List.any_cons, Bool.or_eq_false_iff] at h
  exact ⟨fun hm => (by rw [List.contains_iff_mem.mpr hm] at h; exact Bool.noConfusion h.1), h.2⟩

theorem inj {a b : Srt} {p : Term} (h : c.NoFnOvlIn (.inj a b p)) : c.NoFnOvlIn p := by
  unfold Semantics.NoFnOvlIn at h; rw [symOccs] at h; exact h

theorem as {p : Term} {i : Nat} (h : c.NoFnOvlIn (.as p i)) : c.NoFnOvlIn p := by
  unfold Semantics.NoFnOvlIn at h; rw [symOccs] at h; exact h

theorem cons {p : Term} {ps : List Term} (h : c.NoFnOvlInL (p :: ps)) : c.NoFnOvlIn p ∧ c.NoFnOvlInL ps := by
  unfold Semantics.NoFnOvlInL at h
  rw [symOccsList, List.any_append, Bool.or_eq_false_iff] at h
  exact h

theorem nil : c.NoFnOvlInL [] := by
  unfold Semantics.NoFnOvlInL; rw [symOccsList]; rfl

theorem mk_cons {p : Term} {ps : List Term} (h : c.NoFnOvlIn p) (hs : c.NoFnOvlInL ps) : c.NoFnOvlInL (p :: ps) := by
  unfold Semantics.NoFnOvlInL
  rw [symOccsList, List.any_append, Bool.or_eq_false_iff]
  exact ⟨h, hs⟩

theorem mk_app {f : Sym} {ps : List Term} (hf : f ∉ c.fnOvlSyms) (hs : c.NoFnOvlInL ps) : c.NoFnOvlIn (.app f ps) := by
  unfold Semantics.NoFnOvlIn
  rw [symOccs, List.any_cons, Bool.or_eq_false_iff]
  refine ⟨?_, hs⟩
  cases hc : c.fnOvlSyms.contains f with
  | false => rfl
  | true => exact absurd (List.contains_iff_mem.mp hc) hf

theorem mem : ∀ {ps : List Term}, c.NoFnOvlInL ps → ∀ p ∈ ps, c.NoFnOvlIn p
  | _ :: _, h, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (cons h).1
    · exact mem (cons h).2 p hp

theorem of_each : ∀ {ps : List Term}, (∀ p ∈ ps, c.NoFnOvlIn p) → c.NoFnOvlInL ps
  | [], _ => nil
  | p :: ps, h => mk_cons (h p (List.mem_cons_self ..)) (of_each fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem append {ps qs : List Term} (h : c.NoFnOvlInL ps) (h' : c.NoFnOvlInL qs) : c.NoFnOvlInL (ps ++ qs) :=
  of_each fun p hp => (List.mem_append.mp hp).elim (mem h p) (mem h' p)

/-- No term applies a function-overloaded symbol where there is none. -/
theorem of_nil (h : c.fnOvlSyms = []) (p : Term) : c.NoFnOvlIn p := by
  unfold Semantics.NoFnOvlIn; rw [h]; simp

theorem ofL_nil (h : c.fnOvlSyms = []) (ps : List Term) : c.NoFnOvlInL ps := by
  unfold Semantics.NoFnOvlInL; rw [h]; simp

end NoFnOvlIn

namespace Semantics
variable {c : Semantics}

/-- `overloadsOK`'s condition on the patterns. -/
theorem overloadsOK_pats (h : c.overloadsOK = true) : c.ovlPatsOK = true := by
  unfold overloadsOK at h; exact (Bool.and_eq_true_iff.mp h).2

/-- A rule's left side applies no function-overloaded symbol. -/
theorem ovlPats_lhs (h : c.ovlPatsOK = true) {r : Rule} (hr : r ∈ c.rules) : c.NoFnOvlIn r.lhs := by
  simp only [ovlPatsOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  exact (h.1 r hr).1

/-- The pattern of an `exMatch` of a rule's `pre` or `post` applies no function-overloaded symbol. -/
theorem ovlPats_ruleCond (h : c.ovlPatsOK = true) {r : Rule} (hr : r ∈ c.rules) {p : Term}
    (hp : p ∈ condPats r.pre ++ condPats r.post) : c.NoFnOvlIn p := by
  simp only [ovlPatsOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  exact (h.1 r hr).2 p hp

/-- A clause's patterns apply no function-overloaded symbol. -/
theorem ovlPats_pats (h : c.ovlPatsOK = true) {f : Fn} (hf : f ∈ c.fns) {cl : Clause} (hcl : cl ∈ f.clauses) :
    c.NoFnOvlInL cl.pats := by
  simp only [ovlPatsOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  exact NoFnOvlIn.of_each (h.2 f hf cl hcl).1

/-- The pattern of an `exMatch` of a clause's `pre` or `post` applies no function-overloaded
symbol. -/
theorem ovlPats_clauseCond (h : c.ovlPatsOK = true) {f : Fn} (hf : f ∈ c.fns) {cl : Clause}
    (hcl : cl ∈ f.clauses) {p : Term} (hp : p ∈ condPats cl.pre ++ condPats cl.post) : c.NoFnOvlIn p := by
  simp only [ovlPatsOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
  exact (h.2 f hf cl hcl).2 p hp

end Semantics

variable {c : Semantics}

mutual
  /-- A term well sorted over `patCtxNF` is well sorted over `patCtxAll` and applies no
  function-overloaded symbol. -/
  theorem sortOfTerm_of_nf {vars : List Srt} : ∀ (t : Term) {s : Srt},
      sortOfTerm c.patCtxNF vars t = some s → sortOfTerm c.patCtxAll vars t = some s ∧ c.NoFnOvlIn t
    | .var _, _, h => ⟨by simpa [sortOfTerm] using h, by simp [Semantics.NoFnOvlIn, symOccs]⟩
    | .dv _ _, _, h => ⟨(sortOfTerm_dv (x := c.patCtxAll)).mpr ((sortOfTerm_dv (x := c.patCtxNF)).mp h),
      by simp [Semantics.NoFnOvlIn, symOccs]⟩
    | .app f ts, _, h => by
      obtain ⟨k, hk, hargs, rfl⟩ := sortOfTerm_app.mp h
      obtain ⟨hk', hf⟩ := patCtxNF_lookup.mp hk
      obtain ⟨h1, h2⟩ := sortsOfTerms_of_nf ts hargs
      exact ⟨sortOfTerm_app.mpr ⟨k, hk', h1, rfl⟩, NoFnOvlIn.mk_app hf h2⟩
    | .inj a b t, _, h => by
      obtain ⟨hab, ht, rfl⟩ := sortOfTerm_inj.mp h
      obtain ⟨h1, h2⟩ := sortOfTerm_of_nf t ht
      refine ⟨sortOfTerm_inj.mpr ⟨hab, h1, rfl⟩, ?_⟩
      unfold Semantics.NoFnOvlIn; rw [symOccs]; exact h2
    | .as t i, s, h => by
      obtain ⟨hi, ht⟩ := Exec.sortOfTerm_as h
      obtain ⟨h1, h2⟩ := sortOfTerm_of_nf t ht
      refine ⟨sortOfTerm_as_introNF patCtxAll_asOK hi h1, ?_⟩
      unfold Semantics.NoFnOvlIn; rw [symOccs]; exact h2
  theorem sortsOfTerms_of_nf {vars : List Srt} : ∀ (ts : List Term) {ss : List Srt},
      sortsOfTerms c.patCtxNF vars ts = some ss → sortsOfTerms c.patCtxAll vars ts = some ss ∧ c.NoFnOvlInL ts
    | [], _, h => ⟨sortsOfTerms_nil.mpr (sortsOfTerms_nil.mp h), NoFnOvlIn.nil⟩
    | t :: ts, _, h => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp h
      obtain ⟨a1, a2⟩ := sortOfTerm_of_nf t h1
      obtain ⟨b1, b2⟩ := sortsOfTerms_of_nf ts h2
      exact ⟨sortsOfTerms_cons.mpr ⟨s, ss', a1, b1, rfl⟩, NoFnOvlIn.mk_cons a2 b2⟩
end

mutual
  /-- A term well sorted over `patCtxAll` that applies no function-overloaded symbol is well sorted
  over `patCtxNF`. -/
  theorem sortOfTerm_to_nf {vars : List Srt} : ∀ (t : Term) {s : Srt},
      sortOfTerm c.patCtxAll vars t = some s → c.NoFnOvlIn t → sortOfTerm c.patCtxNF vars t = some s
    | .var _, _, h, _ => by simpa [sortOfTerm] using h
    | .dv _ _, _, h, _ => (sortOfTerm_dv (x := c.patCtxNF)).mpr ((sortOfTerm_dv (x := c.patCtxAll)).mp h)
    | .app f ts, _, h, hn => by
      obtain ⟨k, hk, hargs, rfl⟩ := sortOfTerm_app.mp h
      exact sortOfTerm_app.mpr ⟨k, patCtxNF_lookup.mpr ⟨hk, (NoFnOvlIn.app hn).1⟩, sortsOfTerms_to_nf ts hargs (NoFnOvlIn.app hn).2, rfl⟩
    | .inj a b t, _, h, hn => by
      obtain ⟨hab, ht, rfl⟩ := sortOfTerm_inj.mp h
      exact sortOfTerm_inj.mpr ⟨hab, sortOfTerm_to_nf t ht (NoFnOvlIn.inj hn), rfl⟩
    | .as t i, s, h, hn => by
      obtain ⟨hi, ht⟩ := Exec.sortOfTerm_as h
      exact sortOfTerm_as_introNF patCtxNF_asOK hi (sortOfTerm_to_nf t ht (NoFnOvlIn.as hn))
  theorem sortsOfTerms_to_nf {vars : List Srt} : ∀ (ts : List Term) {ss : List Srt},
      sortsOfTerms c.patCtxAll vars ts = some ss → c.NoFnOvlInL ts → sortsOfTerms c.patCtxNF vars ts = some ss
    | [], _, h, _ => sortsOfTerms_nil.mpr (sortsOfTerms_nil.mp h)
    | t :: ts, _, h, hn => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp h
      exact sortsOfTerms_cons.mpr ⟨s, ss', sortOfTerm_to_nf t h1 (NoFnOvlIn.cons hn).1,
        sortsOfTerms_to_nf ts h2 (NoFnOvlIn.cons hn).2, rfl⟩
end

/-- A term well sorted over `patCtxNF` is well sorted over `patCtxAll`. -/
theorem sortOfTerm_all_of_nf {vars : List Srt} {t : Term} {s : Srt}
    (h : sortOfTerm c.patCtxNF vars t = some s) : sortOfTerm c.patCtxAll vars t = some s :=
  (sortOfTerm_of_nf t h).1

theorem sortsOfTerms_all_of_nf {vars : List Srt} {ts : List Term} {ss : List Srt}
    (h : sortsOfTerms c.patCtxNF vars ts = some ss) : sortsOfTerms c.patCtxAll vars ts = some ss :=
  (sortsOfTerms_of_nf ts h).1

/-- Without function-overloaded symbols no pattern applies one. -/
theorem Semantics.ovlPatsOK_of_fnOvlSyms_nil (h : c.fnOvlSyms = []) : c.ovlPatsOK = true := by
  simp [Semantics.ovlPatsOK, h]

/-- A term is well sorted over `patCtxNF` exactly when it is over `patCtxAll` and applies no
function-overloaded symbol. -/
theorem sortOfTerm_nf_iff {vars : List Srt} {t : Term} {s : Srt} :
    sortOfTerm c.patCtxNF vars t = some s ↔ sortOfTerm c.patCtxAll vars t = some s ∧ c.NoFnOvlIn t :=
  ⟨sortOfTerm_of_nf t, fun h => sortOfTerm_to_nf t h.1 h.2⟩

end KCore
