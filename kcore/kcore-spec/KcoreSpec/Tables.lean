/-
  KCore, checked layer: a definition's derived tables as data (ARCHITECTURE.md §7, A5).

  Every decision about a definition reduces the frozen definitions themselves, and those compute
  their derived tables (the subsort relation, closed; the constructors' signatures by number) in
  each decision. At KEVM's size the closure alone costs about 11 M heartbeats a decision
  (findings/P1.2-tables.md). So the checked decisions take the tables as an argument `T : Tables`,
  which the generator writes as data (built by a command, `tables_of`), with one kernel fact
  `T = tables c` per definition; one lemma per decision says that with `T = tables c` it gives the
  readable condition. `Step` and the frozen definitions do not read `T` (ARCHITECTURE.md §3.10).

  Here: `Tables`, `tables`, the trie reads (`sub`, `below`, `sig`) with their meaning, and
  `sortOfT`, the sort of a ground term read from `T`, equal to `Semantics.sortOf` at `tables c` at a
  value that applies no open generator (`rawFree`).
-/
import KcoreSpec.Value

set_option autoImplicit false

namespace KCore

/-- A definition's derived tables. -/
structure Tables where
  /-- the subsort relation (`Semantics.subsorts`: the declared pairs closed, the cells' and those
  into KItem) -/
  subs : List (Srt × Srt)
  /-- each sort's strict supersorts, by number -/
  sup : NatMap (List Srt)
  /-- each sort's strict subsorts, by number -/
  inf : NatMap (List Srt)
  /-- the constructors' signatures by number (`lookupSig c.ctorSigs`) -/
  sigs : NatMap CtorSig
  /-- the collection sorts (`Semantics.allColls`) -/
  colls : List CollSig
  /-- the overloading symbols (`Semantics.ovls`) -/
  ovls : List OvlSig
  deriving Repr, DecidableEq, Inhabited

/-- The tables of a definition, computed. -/
def tables (c : Semantics) : Tables where
  subs := c.subsorts
  sup := NatMap.group c.subsorts
  inf := NatMap.group (c.subsorts.map fun p => (p.2, p.1))
  sigs := NatMap.ofList (c.ctorSigs.map fun k => (k.name, k))
  colls := c.allColls
  ovls := c.ovls

namespace Tables
variable (T : Tables)

/-- a < b, read from a's supersorts. -/
def sub (a b : Srt) : Bool := (NatMap.succs T.sup a).contains b

/-- a ≤ b. -/
def le (a b : Srt) : Bool := a == b || T.sub a b

/-- The sorts strictly below a. -/
def below (a : Srt) : List Srt := NatMap.succs T.inf a

def sig (f : Sym) : Option CtorSig := T.sigs.find f

/-- f is a constructor (`Semantics.isCtor`, read from the trie). -/
def isCtor (f : Sym) : Bool := (T.sig f).isSome

/-- The collection sort s (`Semantics.collOf`). -/
def collOf (s : Srt) : Option CollSig := T.colls.find? (·.sort == s)

/-- `Semantics.lookupOvl`, read from `T`. -/
def lookupOvl (f : Sym) : Option OvlSig := T.ovls.find? (·.sig.name == f)

/-- `Semantics.lies`, read from `T`. -/
def lies (A B : Srt) : GroundTerm → Bool
  | .inj C _ _ => A == B || T.le C A
  | _ => A == B

/-- `Semantics.ovlCovers`, read from `T`. -/
def ovlCovers (kf kg : CtorSig) (vs : List GroundTerm) : Bool :=
  kg.args.length == kf.args.length && vs.length == kf.args.length &&
    ((kg.args.zip kf.args).zip vs).all fun ((A, B), v) => T.lies A B v

/-- `Semantics.ovlOver`, read from `T`. -/
def ovlOver (o : OvlSig) : List CtorSig :=
  o.over.filterMap fun g => (T.sig g).or ((T.lookupOvl g).map (·.sig))

/-- `Semantics.uncovered`, read from `T`. -/
def uncovered (f : Sym) (vs : List GroundTerm) : Bool :=
  match T.lookupOvl f with
  | none => true
  | some o => (T.ovlOver o).all fun kg => !T.ovlCovers o.sig kg vs

end Tables

section
variable {c : Semantics}

@[simp] theorem tables_subs : (tables c).subs = c.subsorts := rfl

@[simp] theorem sub_tables (a b : Srt) : (tables c).sub a b = c.subsorts.contains (a, b) := by
  unfold Tables.sub tables
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, NatMap.mem_group]

@[simp] theorem le_tables_eq (a b : Srt) : (tables c).le a b = (a == b || c.subsorts.contains (a, b)) := by
  simp [Tables.le]

theorem le_tables (a b : Srt) : (tables c).le a b = c.le a b := by
  simp [Semantics.le]

theorem mem_below_tables (a x : Srt) : x ∈ (tables c).below a ↔ (x, a) ∈ c.subsorts := by
  unfold Tables.below tables
  simp only [NatMap.mem_group, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨u, v⟩, h, rfl, rfl⟩; exact h
  · intro h; exact ⟨(x, a), h, rfl, rfl⟩

theorem sig_tables (f : Sym) : (tables c).sig f = lookupSig c.ctorSigs f := rfl

theorem collOf_tables (s : Srt) : (tables c).collOf s = c.collOf s := rfl

theorem lookupOvl_tables (f : Sym) : (tables c).lookupOvl f = c.lookupOvl f := rfl

theorem uncovered_tables (f : Sym) (vs : List GroundTerm) : (tables c).uncovered f vs = c.uncovered f vs := by
  have hl : ∀ A B v, (tables c).lies A B v = c.lies A B v := by
    intro A B v; cases v <;> simp [Tables.lies, Semantics.lies, Semantics.le]
  have hc : ∀ kf kg vs, (tables c).ovlCovers kf kg vs = c.ovlCovers kf kg vs := by
    intro kf kg vs; simp only [Tables.ovlCovers, Semantics.ovlCovers, hl]
  have ho : ∀ o, (tables c).ovlOver o = c.ovlOver o := by
    intro o
    simp only [Tables.ovlOver, Semantics.ovlOver, sig_tables, lookupOvl_tables]
    congr 1; funext g
    rw [lookupSig_eq, lookupSig_eq, List.find?_append, Semantics.lookupOvl,
      Semantics.ovlSigs, List.find?_map]
    rfl
  simp only [Tables.uncovered, Semantics.uncovered, lookupOvl_tables, ho, hc]
  rfl

end

/-! ## The sort of a ground term, read from the tables -/

mutual
  /-- `Semantics.sortOf` with the subsort test and the constructor lookup read from `T`. -/
  def sortOfT (T : Tables) (l : Lib) : GroundTerm → Option Srt
    | .ctor f ts => match T.sig f with
      | some k => if sortsOfT T l ts == some k.args then some k.result else none
      | none => match T.lookupOvl f with
        | some o => if sortsOfT T l ts == some o.sig.args && T.uncovered f ts then some o.sig.result
                    else none
        | none => none
    | .inj a b t => if T.sub a b && !t.isInj && sortOfT T l t == some a then some b
                    else none
    | .dv s lit => if dvOK l s lit then some s else none
    | .map s es => match T.collOf s with
      | some k => match k.val with
        | some vs => if (match k.kind with | .map => keysSorted es | .rangeMap => rangesOK es | _ => false)
                        && entriesOKT T l k.key vs es then some s
                     else none
        | none => none
      | none => none
    | .set s es => match T.collOf s, sortsOfT T l es with
      | some k, some ss => if k.kind == .set && elemsSorted es && ss.all (· == k.key) then some s
                           else none
      | _, _ => none
    | .list s es => match T.collOf s, sortsOfT T l es with
      | some k, some ss => if k.kind == .list && ss.all (· == k.key) then some s else none
      | _, _ => none
    termination_by structural t => t
  def sortsOfT (T : Tables) (l : Lib) : List GroundTerm → Option (List Srt)
    | [] => some []
    | t :: ts => match sortOfT T l t, sortsOfT T l ts with
      | some s, some ss => some (s :: ss)
      | _, _ => none
    termination_by structural ts => ts
  def entriesOKT (T : Tables) (l : Lib) (ks vs : Srt) : List (GroundTerm × GroundTerm) → Bool
    | [] => true
    | e :: es => entryOKT T l ks vs e && entriesOKT T l ks vs es
    termination_by structural es => es
  def entryOKT (T : Tables) (l : Lib) (ks vs : Srt) : GroundTerm × GroundTerm → Bool
    | (k, v) => sortOfT T l k == some ks && sortOfT T l v == some vs
    termination_by structural e => e
end

/-! The tables give the sort at a value that applies no open generator (`rawFree`): their sort
holds no interpretation, and an open generator's application is a value where the interpretation
leaves it raw. -/

mutual
  theorem sortOfT_tables (c : Semantics) :
      ∀ t, c.rawFree t = true → sortOfT (tables c) c.lib t = c.sortOf t
    | .ctor f ts, hv => by
      simp only [Semantics.rawFree, Bool.and_eq_true, Bool.not_eq_true'] at hv
      rw [sortOfT, Semantics.sortOf, sig_tables, sortsOfT_tables c ts hv.2, lookupOvl_tables,
        uncovered_tables, c.lookupOpen_none_of_any hv.1] <;> try rfl
    | .inj a b t, hv => by
      rw [Semantics.rawFree] at hv
      rw [sortOfT, Semantics.sortOf, sub_tables, sortOfT_tables c t hv] <;> try rfl
    | .dv s lit, _ => by rw [sortOfT, Semantics.sortOf] <;> try rfl
    | .map s es, hv => by
      rw [Semantics.rawFree] at hv
      rw [sortOfT, Semantics.sortOf, collOf_tables]
      cases c.collOf s with
      | none => rfl
      | some k =>
        cases hk : k.val with
        | none => simp only [hk]
        | some vs => simp only [hk, entriesOKT_tables c k.key vs es hv]; rfl
    | .set s es, hv => by
      rw [Semantics.rawFree] at hv
      rw [sortOfT, Semantics.sortOf, sortsOfT_tables c es hv, collOf_tables]; rfl
    | .list s es, hv => by
      rw [Semantics.rawFree] at hv
      rw [sortOfT, Semantics.sortOf, sortsOfT_tables c es hv, collOf_tables]; rfl
    termination_by structural t => t
  theorem sortsOfT_tables (c : Semantics) :
      ∀ ts, c.rawFreeList ts = true → sortsOfT (tables c) c.lib ts = c.sortsOf ts
    | [], _ => by rw [sortsOfT, Semantics.sortsOf] <;> try rfl
    | t :: ts, h => by
      simp only [Semantics.rawFreeList, Bool.and_eq_true] at h
      rw [sortsOfT, Semantics.sortsOf, sortOfT_tables c t h.1, sortsOfT_tables c ts h.2] <;> try rfl
    termination_by structural ts => ts
  theorem entriesOKT_tables (c : Semantics) (ks vs : Srt) :
      ∀ es, c.rawFreeEntries es = true → entriesOKT (tables c) c.lib ks vs es = c.entriesOK ks vs es
    | [], _ => by rw [entriesOKT, Semantics.entriesOK] <;> try rfl
    | e :: es, h => by
      simp only [Semantics.rawFreeEntries, Bool.and_eq_true] at h
      rw [entriesOKT, Semantics.entriesOK, entryOKT_tables c ks vs e h.1, entriesOKT_tables c ks vs es h.2] <;>
        try rfl
    termination_by structural es => es
  theorem entryOKT_tables (c : Semantics) (ks vs : Srt) :
      ∀ e, c.rawFreeEntry e = true → entryOKT (tables c) c.lib ks vs e = c.entryOK ks vs e
    | (k, v), h => by
      simp only [Semantics.rawFreeEntry, Bool.and_eq_true] at h
      rw [entryOKT, Semantics.entryOK, sortOfT_tables c k h.1, sortOfT_tables c v h.2] <;> try rfl
    termination_by structural e => e
end

/-- A sort decided from the tables is the sort, at a value that applies no open generator (decided
where the value is closed). -/
theorem sortOf_of_T {c : Semantics} {T : Tables} (hT : T = tables c) {t : GroundTerm} {s : Option Srt}
    (h : sortOfT T c.lib t = s) (hv : c.rawFree t = true := by decide +kernel) : c.sortOf t = s := by
  subst hT; rw [← sortOfT_tables c t hv]; exact h

end KCore
