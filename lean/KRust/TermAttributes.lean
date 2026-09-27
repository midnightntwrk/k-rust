/-
The backend term model and its construction-time attributes: case studies 1 (`ceil_free`,
ticket OT-01) and 3 (`has_macro_or_alias` and the saturated k-cell count, ticket OT-02) of
`draft/lean-verification/README.md`. Core Lean only.

Equality. The model's `=` on `Term` is Rust's `Eq for Term` (term.rs:1118-1123), not a coarser
equality: applications keep their sort arguments, variables their sort, collections their
definition, and `Sym` keeps an `other` field for every `Symbol` field the walks do not read. Rust
`Eq` is `Arc::ptr_eq || (hash == hash && kind == kind)`; the hash is a function of the kind
(`Term::new` :919-923), so both disjuncts are structural equality of the kind. `Sort`, `Name` and
`KoreString` are modelled as strings, so the model assumes their Rust equality and order are those
of an injective string encoding.

The attributes `ceilFree`, `hasMacro` and `kCells`, and the fetch `fetchK`, were designed here
(OT-01, OT-02) before the Rust had them; the functions they replace (`ceil_term_recursive`,
`macro_or_alias_symbol`, `find_k_cells`) are modelled from the Rust at the anchor commit.
OT-01 implements `ceilFree` as crates/k-rust-backend/src/term.rs `ceil_free` (with `key_header`
and `share_one_key_header` for `keyHeader` and `oneHeader`), stored by `Term::new` in
`TermAttributes::ceil_free`; `ceil_term_recursive` returns at once when it is set, and the
walk it replaces is kept as `ceil_term_node`. The lean bridge compares the stored attribute with
`ceilFree` at every subterm (`tests::lean_bridge::attributes`). OT-02 implements `hasMacro` and
`kCells` as term.rs `has_macro_or_alias` and `k_cells`, stored by `Term::new`, and `fetchK` as
rule.rs `fetch_k_cell`; `macro_or_alias_symbol` runs the walk (now
`first_macro_or_alias_symbol`) only when the flag is set, and `rule_index` fetches the cell only
when the count is 1. The bridge compares the two stored attributes at every subterm and
`fetch_k_cell` with `fetchK`; `find_k_cells` is kept, test-only, as the walk `findK` models.

Rust modelled here, anchors verified at ce4084a5 (the sites are unchanged since 2aec72c7):
  crates/k-rust-backend/src/term.rs
    VariableKind :77-80, Variable :83-87, FunctionType :116-119, SymbolType :122-125
    SymbolAttributes :128-144, Symbol :166-172, Symbol::is :176-178 (all derive Eq and Ord)
    TermKind              :227-259
    TermAttributes        :262-269
    Term::and             :294-299  (concrete_after_normalization = false)
    application_raw       :325-347
    domain_value          :428-441, variable :443-449
    injection             :451-469  (flattens inj-of-inj, copies the child's attributes)
    Term::map             :471-509  (entries.sort() on (key, value) pairs; a repeated key is kept, with the same value or not)
    Term::list            :511-560
    Term::set             :562-595  (elements.sort(); a repeated element is kept: concatenation is nilpotent)
    with_evaluated_cache  :611-618  (copies the kind, changes only `evaluated`)
    visit_symbols         :760-805, macro_or_alias_symbol :808-816
    structurally_distinct_after_normalization, certified_normal_application (KK-59)
    Term::new             :919-923  (private; the only place a TermData is built)
    combine_attributes    :1085-1110 (empty conjunction is true)
    PartialEq / Ord       :1118-1137 (Eq = pointer or (hash and kind); Ord = derived order on kind)
  crates/k-rust-kore/src/names.rs:45  (KCell spelling)
  crates/k-rust-backend/src/definedness.rs
    ceil_term :94-97, ceil_term_recursive :99-189,
    normalized_ground_terms_are_distinct :196-214, apply_ceil_equation :216,
    not_in_collection :284, deduplicate :307-310
  crates/k-rust-backend/src/rule.rs
    rule_index :766-777, find_k_cells :789-840

Hypotheses (named, with their Rust tests in lean/README.md): `TotalOrder.trans`,
`TotalOrder.antisym`, `WF`, `Oracles.dedup_nil`.
-/

set_option linter.unusedSimpArgs false

namespace KRust.TermAttributes

/-! ## 1. The data -/

/-- `Sort` (a structured Rust type) and `KoreString`/`Name` are modelled as strings.
Assumption: the Rust types' equality is the string equality of this encoding. -/
abbrev SortName := String

/-- `FunctionType` (term.rs:116-119). -/
inductive FunctionType where
  | Partial
  | Total
deriving DecidableEq, Repr

/-- `SymbolType` (term.rs:122-125). -/
inductive SymbolType where
  | constructor
  | function : FunctionType → SymbolType
deriving DecidableEq, Repr

/-- `Symbol` with the attributes the walks read (term.rs:128-172). `other` stands for every other
field, so that `Sym` equality is the derived equality of `Symbol`. -/
structure Sym where
  name             : String
  symbolType       : SymbolType
  anywhere         : Bool
  declaredFunction : Bool
  injective        : Bool
  macroOrAlias     : Bool
  other            : String
deriving DecidableEq, Repr

/-- `WellKnownSymbol::KCell.as_str()` (k-rust-kore names.rs:45). -/
def kCellName : String := "Lbl'-LT-'k'-GT-'"

/-- `symbol.is(WellKnownSymbol::KCell)` (term.rs:176-178): a name comparison. -/
def Sym.isKCell (s : Sym) : Bool := s.name == kCellName

def Sym.isPartial (s : Sym) : Bool := s.symbolType == .function .Partial

/-- `VariableKind` (term.rs:77-80). -/
inductive VarKind where
  | element
  | set
deriving DecidableEq, Repr

/-- `TermKind` (term.rs:227-259), constructor for constructor. A collection's `Arc<…Definition>`
is modelled by an opaque name `defn`, so that equality and order still see it. -/
inductive Term where
  | and  : Term → Term → Term
  | app  : (symbol : Sym) → (sortArgs : List SortName) → (args : List Term) → Term
  | dv   : (sort : SortName) → (value : String) → Term
  | var  : VarKind → (sort : SortName) → (name : String) → Term
  | inj  : (source target : SortName) → Term → Term
  | map  : (defn : String) → (entries : List (Term × Term)) → (rest : Option Term) → Term
  | list : (defn : String) → (heads : List Term) → (rest : Option (Term × List Term)) → Term
  | set  : (defn : String) → (elements : List Term) → (rest : Option Term) → Term
deriving Repr, Inhabited

/-! ### Equality

Rust `Eq for Term` (term.rs:1118-1123) is `Arc::ptr_eq || (hash == hash && kind == kind)`.
`hash` is `calculate_hash(&kind)` set by `Term::new` (:919-923), so it is a function of the kind,
and pointer equality implies kind equality; both disjuncts therefore reduce to structural equality
of the kind. The model's `=` is that structural equality.
Lean 4.34 cannot derive `DecidableEq` (nor `ReflBEq`/`LawfulBEq`) for a nested inductive, so the
Boolean equality is written out and proved lawful. `termination_by structural` is needed
(two arguments of the nested type), so that the kernel can evaluate it (`decide`). -/

mutual
def Term.beq : Term → Term → Bool
  | .and a b, .and a' b'           => Term.beq a a' && Term.beq b b'
  | .app s ss as, .app s' ss' as'   => s == s' && ss == ss' && Term.beqList as as'
  | .dv s v, .dv s' v'             => s == s' && v == v'
  | .var k s n, .var k' s' n'      => k == k' && s == s' && n == n'
  | .inj s t a, .inj s' t' a'      => s == s' && t == t' && Term.beq a a'
  | .map d es r, .map d' es' r'    => d == d' && Term.beqEntries es es' && Term.beqOpt r r'
  | .list d hs r, .list d' hs' r'  => d == d' && Term.beqList hs hs' && Term.beqRest r r'
  | .set d es r, .set d' es' r'    => d == d' && Term.beqList es es' && Term.beqOpt r r'
  | _, _                           => false
termination_by structural a _ => a
def Term.beqList : List Term → List Term → Bool
  | [], []             => true
  | a :: as, b :: bs   => Term.beq a b && Term.beqList as bs
  | _, _               => false
termination_by structural as _ => as
def Term.beqEntries : List (Term × Term) → List (Term × Term) → Bool
  | [], []                     => true
  | (k, v) :: es, (k', v') :: es' => Term.beq k k' && Term.beq v v' && Term.beqEntries es es'
  | _, _                       => false
termination_by structural es _ => es
def Term.beqOpt : Option Term → Option Term → Bool
  | none, none         => true
  | some a, some b     => Term.beq a b
  | _, _               => false
termination_by structural a _ => a
def Term.beqRest : Option (Term × List Term) → Option (Term × List Term) → Bool
  | none, none                   => true
  | some (m, ts), some (m', ts') => Term.beq m m' && Term.beqList ts ts'
  | _, _                         => false
termination_by structural r _ => r
end

mutual
theorem Term.beq_iff : ∀ a b : Term, Term.beq a b = true ↔ a = b
  | .and a1 a2, b => by
      cases b <;> simp [and_assoc, Term.beq, Term.beq_iff a1, Term.beq_iff a2]
  | .app _ _ as, b => by
      cases b <;> simp [and_assoc, Term.beq, Term.beqList_iff as]
  | .dv _ _, b => by cases b <;> simp [and_assoc, Term.beq]
  | .var _ _ _, b => by cases b <;> simp [and_assoc, Term.beq]
  | .inj _ _ a, b => by cases b <;> simp [and_assoc, Term.beq, Term.beq_iff a]
  | .map _ es r, b => by
      cases b <;> simp [and_assoc, Term.beq, Term.beqEntries_iff es, Term.beqOpt_iff r]
  | .list _ hs r, b => by
      cases b <;> simp [and_assoc, Term.beq, Term.beqList_iff hs, Term.beqRest_iff r]
  | .set _ es r, b => by
      cases b <;> simp [and_assoc, Term.beq, Term.beqList_iff es, Term.beqOpt_iff r]
theorem Term.beqList_iff : ∀ as bs : List Term, Term.beqList as bs = true ↔ as = bs
  | [], bs => by cases bs <;> simp [and_assoc, Term.beqList]
  | a :: as, bs => by
      cases bs <;> simp [and_assoc, Term.beqList, Term.beq_iff a, Term.beqList_iff as]
theorem Term.beqEntries_iff : ∀ as bs : List (Term × Term), Term.beqEntries as bs = true ↔ as = bs
  | [], bs => by cases bs <;> simp [and_assoc, Term.beqEntries]
  | (k, v) :: as, bs => by
      rcases bs with _ | ⟨⟨k', v'⟩, bs⟩ <;>
        simp [and_assoc, Term.beqEntries, Term.beq_iff k, Term.beq_iff v, Term.beqEntries_iff as, and_assoc]
theorem Term.beqOpt_iff : ∀ a b : Option Term, Term.beqOpt a b = true ↔ a = b
  | none, b => by cases b <;> simp [and_assoc, Term.beqOpt]
  | some a, b => by cases b <;> simp [and_assoc, Term.beqOpt, Term.beq_iff a]
theorem Term.beqRest_iff : ∀ a b : Option (Term × List Term), Term.beqRest a b = true ↔ a = b
  | none, b => by cases b <;> simp [and_assoc, Term.beqRest]
  | some (m, ts), b => by
      rcases b with _ | ⟨m', ts'⟩ <;>
        simp [and_assoc, Term.beqRest, Term.beq_iff m, Term.beqList_iff ts]
end

instance : DecidableEq Term := fun a b => decidable_of_iff _ (Term.beq_iff a b)

/-! ## 2. The stored attribute `concrete_after_normalization` and structural distinctness -/

/- `concrete_after_normalization` as the constructors compute it. It is stored in
`TermAttributes`; the stored value equals this function because `Term::new` (term.rs:919-923) is
private and is the only construction site, and `with_evaluated_cache` (:611-618) changes only
`evaluated`.
- `and`: false (:294-299);
- application: `(constructor || (anywhere && !declared_function)) && children` (:325-347);
- domain value: true (:428-441); variable: the default, false (:443-449, :271-282);
- injection: the child's attributes (:451-469);
- collections: the conjunction over all children, true when empty (:495-500, :546-551, :586,
  and `combine_attributes` :1085-1110). -/
mutual
def concrete : Term → Bool
  | .and _ _        => false
  | .app s _ args   => (s.symbolType == .constructor || (s.anywhere && !s.declaredFunction))
                         && concreteList args
  | .dv _ _         => true
  | .var _ _ _      => false
  | .inj _ _ t      => concrete t
  | .map _ es rest  => concreteEntries es && concreteOpt rest
  | .list _ hs rest => concreteList hs && concreteRest rest
  | .set _ es rest  => concreteList es && concreteOpt rest
def concreteList : List Term → Bool
  | []      => true
  | t :: ts => concrete t && concreteList ts
def concreteEntries : List (Term × Term) → Bool
  | []           => true
  | (k, v) :: es => concrete k && concrete v && concreteEntries es
def concreteOpt : Option Term → Bool
  | none   => true
  | some t => concrete t
def concreteRest : Option (Term × List Term) → Bool
  | none         => true
  | some (m, ts) => concrete m && concreteList ts
end

/- `structurally_distinct_with` (term.rs), complete; `structurally_distinct_after_normalization`
is the instance whose `injd` is constantly false. `ev` is the stored `evaluated` attribute, which
the model does not compute from the kind: `with_evaluated_cache` sets it on an anywhere
application only when the simplifier found every equation inapplicable, so an anywhere
application decides only when `ev` certifies it as a normal form (term.rs
`certified_normal_application`); a constructor application always decides. `injd` is the answer
for two injections with different sources or targets, opened in Rust by the `injections`
callback (definedness.rs `ground_terms_structurally_distinct`: the sort graph's
`InjectionEquality`, with the recursive comparison of a split pair); the model keeps it opaque. -/
mutual
def structDistinct (ev : Term → Bool) (injd : Term → Term → Bool) (a b : Term) : Bool :=
  decide (a ≠ b) && concrete a && concrete b &&
  match a, b with
  | .dv s v, .dv s' v' => s != s' || v != v'
  | .app f fs as, .app g gs bs =>
      if !((f.symbolType == .constructor || ev (.app f fs as))
          && (g.symbolType == .constructor || ev (.app g gs bs))) then false
      else if f.name != g.name || fs != gs then true
      else structDistinctZip ev injd as bs
  | .inj s t x, .inj s' t' y =>
      if s == s' && t == t' then structDistinct ev injd x y else injd (.inj s t x) (.inj s' t' y)
  | .app f fs as, .inj _ _ _ => f.symbolType == .constructor || ev (.app f fs as)
  | .inj _ _ _, .app g gs bs => g.symbolType == .constructor || ev (.app g gs bs)
  | _, _ => false
/-- `left_arguments.iter().zip(right_arguments).any(…)`. -/
def structDistinctZip (ev : Term → Bool) (injd : Term → Term → Bool) :
    List Term → List Term → Bool
  | a :: as, b :: bs => structDistinct ev injd a b || structDistinctZip ev injd as bs
  | _, _             => false
end

/-! ## 3. Today's walk: `ceil_term_recursive`, position for position -/

/-- Predicates `ceil_term` can emit (rule.rs `Predicate`, the variants built by definedness.rs). -/
inductive Pred where
  | ceil    : Term → Pred
  | notEq   : Term → Term → Pred   -- Predicate::Not(Box::new(Predicate::Equals(l, r)))
  | opaque  : Nat → Pred           -- whatever a ceil equation or not_in_collection produces

/-- What `ceil_term_recursive` calls and this proof does not open. -/
structure Oracles where
  /-- `apply_ceil_equation` (definedness.rs:216). -/
  ceilEquation    : Term → Option (List Pred)
  /-- `matches!(match_terms_in_definition(MatchMode::Rewrite, definition, l, r), Failed(_))`
  (definedness.rs:204-213). -/
  matchFails      : Term → Term → Bool
  /-- The stored `evaluated` attribute (term.rs `TermAttributes`), which only the simplifier's
  fixed-point cache sets on an anywhere application. -/
  evaluated       : Term → Bool
  /-- The sort graph's answer for two injections with different sources or targets
  (definedness.rs `ground_terms_structurally_distinct`). -/
  injectionsDistinct : Term → Term → Bool
  /-- `not_in_collection` (definedness.rs:284). -/
  notInCollection : String → Term → Term → Pred
  /-- `deduplicate` (definedness.rs:307-310). -/
  dedup           : List Pred → List Pred
  /-- Hypothesis: `deduplicate` of an empty vector is empty (`retain` on an empty vector).
  Rust test: definedness.rs `tests::deduplicate_keeps_an_empty_vector_empty`. -/
  dedup_nil       : dedup [] = []

/-- `normalized_ground_terms_are_distinct` (definedness.rs), opened: the structural test first,
then, for two certified normal forms (concrete and `evaluated`), the matcher in both directions. -/
def normDistinct (O : Oracles) (l r : Term) : Bool :=
  structDistinct O.evaluated O.injectionsDistinct l r
    || (concrete l && O.evaluated l && concrete r && O.evaluated r
        && O.matchFails l r && O.matchFails r l)

/-- Per position: the pairwise obligations against every later key, then the not-in obligation
(definedness.rs:135-147). -/
def mapSide (O : Oracles) : List (Term × Term) → Option Term → List Pred
  | [], _ => []
  | (k, _) :: es, rest =>
      (es.filterMap fun e => if normDistinct O k e.1 then none else some (.notEq k e.1))
      ++ (match rest with
          | some r => [O.notInCollection "MAP.in_keys" k r]
          | none   => [])
      ++ mapSide O es rest

/-- definedness.rs:166-178. -/
def setSide (O : Oracles) : List Term → Option Term → List Pred
  | [], _ => []
  | k :: es, rest =>
      (es.filterMap fun k' => if normDistinct O k k' then none else some (.notEq k k'))
      ++ (match rest with
          | some r => [O.notInCollection "SET.in" k r]
          | none   => [])
      ++ setSide O es rest

/- `ceil_term_recursive` (definedness.rs:99-189). Each arm builds its list, then `deduplicate`. -/
mutual
def ceilTerm (O : Oracles) : Term → List Pred
  | .app s ss args =>
      if s.isPartial then
        O.dedup ((O.ceilEquation (.app s ss args)).getD [.ceil (.app s ss args)] ++ ceilList O args)
      else
        O.dedup (ceilList O args)
  | .and l r         => O.dedup (ceilTerm O l ++ ceilTerm O r)
  | .inj _ _ t       => O.dedup (ceilTerm O t)
  | .dv _ _          => O.dedup []
  | .var .element _ _ => O.dedup []
  | .var .set s x    => O.dedup [.ceil (.var .set s x)]
  | .map _ es rest   => O.dedup (ceilEntries O es ++ ceilOpt O rest ++ mapSide O es rest)
  | .list _ hs rest  => O.dedup (ceilList O hs ++ ceilRest O rest)
  | .set _ es rest   => O.dedup (ceilList O es ++ ceilOpt O rest ++ setSide O es rest)
def ceilList (O : Oracles) : List Term → List Pred
  | []      => []
  | t :: ts => ceilTerm O t ++ ceilList O ts
def ceilEntries (O : Oracles) : List (Term × Term) → List Pred
  | []           => []
  | (k, v) :: es => ceilTerm O k ++ ceilTerm O v ++ ceilEntries O es
def ceilOpt (O : Oracles) : Option Term → List Pred
  | none   => []
  | some t => ceilTerm O t
def ceilRest (O : Oracles) : Option (Term × List Term) → List Pred
  | none         => []
  | some (m, ts) => ceilTerm O m ++ ceilList O ts
end

/-! ## 4. The attribute `ceil_free` (OT-01, narrowed key class) -/

/-- The header of a key whose distinctness from another key with the same header
`structurally_distinct_after_normalization` decides: a domain value, or an injection with a given
source and target of a domain value. -/
inductive Header where
  | dv
  | inj (source target : SortName)
deriving DecidableEq

def keyHeader : Term → Option Header
  | .dv _ _            => some .dv
  | .inj s t (.dv _ _) => some (.inj s t)
  | _                  => none

/-- OT-01's narrowed class: every key has a header, and all keys share the first one. -/
def oneHeader : List Term → Bool
  | []      => true
  | k :: ks => (keyHeader k).isSome && ks.all fun k' => keyHeader k' == keyHeader k

/-- Adjacent keys differ; computed at construction on the already-sorted entries. -/
def adjacentKeysDiffer : List (Term × Term) → Bool
  | a :: b :: rest => decide (a.1 ≠ b.1) && adjacentKeysDiffer (b :: rest)
  | _              => true

/-- Adjacent set elements differ; computed at construction on the already-sorted elements. A
repeated element is kept by `Term::set` (concatenation is nilpotent, so the set is `\bottom`). -/
def adjacentElementsDiffer : List Term → Bool
  | a :: b :: rest => decide (a ≠ b) && adjacentElementsDiffer (b :: rest)
  | _              => true

/- `ceil_free`, computed bottom-up by the constructors. `and` is the conjunction: its arm of
`ceil_term_recursive` only concatenates its sides (definedness.rs:117-121), which settles the
question OT-01 leaves open. -/
mutual
def ceilFree : Term → Bool
  | .app s _ args   => !s.isPartial && ceilFreeList args
  | .and l r        => ceilFree l && ceilFree r
  | .inj _ _ t      => ceilFree t
  | .dv _ _         => true
  | .var k _ _      => k == .element
  | .map _ es rest  => ceilFreeEntries es && rest.isNone
                         && oneHeader (es.map (·.1)) && adjacentKeysDiffer es
  | .list _ hs rest => ceilFreeList hs && ceilFreeRest rest
  | .set _ es rest  => ceilFreeList es && rest.isNone && oneHeader es && adjacentElementsDiffer es
def ceilFreeList : List Term → Bool
  | []      => true
  | t :: ts => ceilFree t && ceilFreeList ts
def ceilFreeEntries : List (Term × Term) → Bool
  | []           => true
  | (k, v) :: es => ceilFree k && ceilFree v && ceilFreeEntries es
def ceilFreeRest : Option (Term × List Term) → Bool
  | none         => true
  | some (m, ts) => ceilFree m && ceilFreeList ts
end

/-! ## 5. The data-format invariants -/

/-- `Ord for Term` (term.rs:1133-1137): the derived order on `TermKind`. Abstract, with the laws
the proof uses; `antisym` is "`Ord` is consistent with `Eq`". Only `trans` and `antisym` are used.
Hypothesis, checked by the property tests of k-rust-backend `tests/backend/term_order.rs`
(`ord_for_term_is_transitive`, `ord_for_term_equal_is_eq`). -/
structure TotalOrder (le : Term → Term → Bool) : Prop where
  trans   : ∀ a b c, le a b = true → le b c = true → le a c = true
  antisym : ∀ a b, le a b = true → le b a = true → a = b

/-- The derived lexicographic order on `(Term, Term)` that `Vec::sort` uses (term.rs:488). -/
def lexLe (le : Term → Term → Bool) (a b : Term × Term) : Bool :=
  (le a.1 b.1 && !le b.1 a.1) || (le a.1 b.1 && le b.1 a.1 && le a.2 b.2)

/-- Every adjacent pair satisfies `r` (what `sort` leaves behind). -/
def Adjacent {α} (r : α → α → Prop) : List α → Prop
  | a :: b :: rest => r a b ∧ Adjacent r (b :: rest)
  | _              => True

/- What the constructors guarantee and the proof uses: map entries sorted (term.rs:488), set
elements sorted (`sort`, :579). Neither constructor deduplicates: `ceil_free` checks
adjacent keys itself, and adjacent set elements likewise (a set keeps a repeated element).
Hypothesis: every term the public constructors build satisfies `WF`, checked by the property test
`constructed_collections_are_sorted` of k-rust-backend `tests/backend/term_order.rs`. -/
mutual
def WF (le : Term → Term → Bool) : Term → Prop
  | .app _ _ args   => WFList le args
  | .and l r        => WF le l ∧ WF le r
  | .inj _ _ t      => WF le t
  | .dv _ _         => True
  | .var _ _ _      => True
  | .map _ es rest  => Adjacent (fun a b => lexLe le a b = true) es ∧ WFEntries le es ∧ WFOpt le rest
  | .list _ hs rest => WFList le hs ∧ WFRest le rest
  | .set _ es rest  => Adjacent (fun a b => le a b = true) es ∧ WFList le es ∧ WFOpt le rest
def WFList (le : Term → Term → Bool) : List Term → Prop
  | []      => True
  | t :: ts => WF le t ∧ WFList le ts
def WFEntries (le : Term → Term → Bool) : List (Term × Term) → Prop
  | []           => True
  | (k, v) :: es => WF le k ∧ WF le v ∧ WFEntries le es
def WFOpt (le : Term → Term → Bool) : Option Term → Prop
  | none   => True
  | some t => WF le t
def WFRest (le : Term → Term → Bool) : Option (Term × List Term) → Prop
  | none         => True
  | some (m, ts) => WF le m ∧ WFList le ts
end

/-! ## 6. Sortedness lemmas (core `List.Pairwise`; no Mathlib `Sorted`/`Chain`) -/

/-- Adjacent pairs related by a transitive relation make every ordered pair related. -/
theorem adjacent_pairwise {α} {r : α → α → Prop} (htr : ∀ a b c, r a b → r b c → r a c) :
    ∀ l : List α, Adjacent r l → l.Pairwise r
  | [], _ => .nil
  | [_], _ => by simp
  | a :: b :: rest, ⟨hab, h⟩ => by
      have ih := adjacent_pairwise htr (b :: rest) h
      refine List.Pairwise.cons ?_ ih
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hab
      · exact htr _ _ _ hab ((List.pairwise_cons.mp ih).1 x hx)

theorem Adjacent.imp {α} {r s : α → α → Prop} (h : ∀ a b, r a b → s a b) :
    ∀ l : List α, Adjacent r l → Adjacent s l
  | [], _ | [_], _ => trivial
  | _ :: b :: rest, ⟨hab, hr⟩ => ⟨h _ _ hab, Adjacent.imp h (b :: rest) hr⟩

/-- "Below and different" is transitive for a total order consistent with equality. -/
theorem strict_trans {le : Term → Term → Bool} (hle : TotalOrder le) :
    ∀ a b c : Term, (le a b = true ∧ a ≠ b) → (le b c = true ∧ b ≠ c) → (le a c = true ∧ a ≠ c) := by
  intro a b c ⟨hab, nab⟩ ⟨hbc, nbc⟩
  refine ⟨hle.trans _ _ _ hab hbc, ?_⟩
  rintro rfl
  exact nbc (hle.antisym _ _ hbc hab)

/-- `adjacentElementsDiffer` as the relation it checks. -/
theorem adjacentElementsDiffer_adjacent :
    ∀ es : List Term, adjacentElementsDiffer es = true → Adjacent (fun a b => a ≠ b) es
  | [], _ | [_], _ => trivial
  | a :: b :: rest, h => by
      simp only [adjacentElementsDiffer, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, adjacentElementsDiffer_adjacent (b :: rest) h.2⟩

/-- `adjacentKeysDiffer` as the relation it checks. -/
theorem adjacentKeysDiffer_adjacent :
    ∀ es : List (Term × Term), adjacentKeysDiffer es = true → Adjacent (fun a b => a.1 ≠ b.1) es
  | [], _ | [_], _ => trivial
  | a :: b :: rest, h => by
      simp only [adjacentKeysDiffer, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, adjacentKeysDiffer_adjacent (b :: rest) h.2⟩

theorem adjacent_and {α} {r s : α → α → Prop} :
    ∀ l : List α, Adjacent r l → Adjacent s l → Adjacent (fun a b => r a b ∧ s a b) l
  | [], _, _ | [_], _, _ => trivial
  | _ :: b :: rest, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨⟨h1, h3⟩, adjacent_and (b :: rest) h2 h4⟩

/-- Map keys are pairwise distinct: entries sorted by `(key, value)` (term.rs:488), and the
attribute checked that adjacent keys differ. -/
theorem map_keys_pairwise_distinct {le : Term → Term → Bool} (hle : TotalOrder le)
    (es : List (Term × Term)) (hs : Adjacent (fun a b => lexLe le a b = true) es)
    (hadj : adjacentKeysDiffer es = true) : es.Pairwise (fun a b => a.1 ≠ b.1) := by
  have hkey : Adjacent (fun a b : Term × Term => le a.1 b.1 = true ∧ a.1 ≠ b.1) es := by
    refine Adjacent.imp ?_ es (adjacent_and es hs (adjacentKeysDiffer_adjacent es hadj))
    intro a b ⟨hl, hne⟩
    refine ⟨?_, hne⟩
    simp only [lexLe, Bool.or_eq_true, Bool.and_eq_true] at hl
    rcases hl with ⟨h, _⟩ | ⟨⟨h, _⟩, _⟩ <;> exact h
  refine (adjacent_pairwise ?_ es hkey).imp fun h => h.2
  intro a b c hab hbc
  exact strict_trans hle a.1 b.1 c.1 hab hbc

/-- Set elements are pairwise distinct: sorted (term.rs:579), and the attribute checked that
adjacent elements differ. -/
theorem set_pairwise_distinct {le : Term → Term → Bool} (hle : TotalOrder le) (es : List Term)
    (hs : Adjacent (fun a b => le a b = true) es) (hadj : adjacentElementsDiffer es = true) :
    es.Pairwise (· ≠ ·) :=
  (adjacent_pairwise (strict_trans hle) es
    (adjacent_and es hs (adjacentElementsDiffer_adjacent es hadj))).imp fun h => h.2

/-! ## 7. Structural distinctness decides the narrowed key class -/

theorem oneHeader_same : ∀ ks : List Term, oneHeader ks = true →
    ∀ k ∈ ks, ∀ k' ∈ ks, (keyHeader k).isSome ∧ keyHeader k = keyHeader k'
  | [], _ => by simp
  | k :: ks, h => by
      simp only [oneHeader, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
      obtain ⟨hs, hall⟩ := h
      have hx : ∀ x ∈ k :: ks, keyHeader x = keyHeader k := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact hall x hx
      intro a ha b hb
      rw [hx a ha, hx b hb]
      exact ⟨hs, rfl⟩

theorem keyHeader_some {k : Term} {h : Header} (hk : keyHeader k = some h) :
    (∃ s v, k = .dv s v ∧ h = .dv) ∨ (∃ s t a x, k = .inj s t (.dv a x) ∧ h = .inj s t) := by
  unfold keyHeader at hk
  split at hk
  · cases hk; exact .inl ⟨_, _, rfl, rfl⟩
  · cases hk; exact .inr ⟨_, _, _, _, rfl, rfl⟩
  · cases hk

theorem ne_or_ne_of_ne {α β} [DecidableEq α] {a a' : α} {b b' : β}
    (h : ¬(a = a' ∧ b = b')) : ¬a = a' ∨ ¬b = b' := by
  by_cases ha : a = a'
  · exact .inr fun hb => h ⟨ha, hb⟩
  · exact .inl ha

/-- Two distinct keys with the same header are structurally distinct (term.rs), whatever `ev` and `injd`: the
`self == other` guard is false, both keys are concrete, and the arm for their header decides. -/
theorem structDistinct_complete (ev : Term → Bool) (injd : Term → Term → Bool) (k k' : Term)
    (h : (keyHeader k).isSome) (hh : keyHeader k = keyHeader k') (hne : k ≠ k') :
    structDistinct ev injd k k' = true := by
  obtain ⟨hdr, hk⟩ := Option.isSome_iff_exists.mp h
  have hk' : keyHeader k' = some hdr := hh ▸ hk
  rcases keyHeader_some hk with ⟨s, v, rfl, rfl⟩ | ⟨s, t, a, x, rfl, rfl⟩ <;>
  rcases keyHeader_some hk' with ⟨s', v', rfl, h2⟩ | ⟨s', t', a', x', rfl, h2⟩ <;>
    simp only [reduceCtorEq, Header.inj.injEq] at h2
  · simp only [structDistinct, concrete]
    simpa [hne] using ne_or_ne_of_ne fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  · obtain ⟨rfl, rfl⟩ := h2
    simp only [structDistinct, concrete]
    have : ¬(a = a' ∧ x = x') := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
    simpa [hne, Ne.symm] using ne_or_ne_of_ne this

/-! ## 8. The side obligations vanish on the narrowed class -/

theorem mapSide_none (O : Oracles) : ∀ es : List (Term × Term),
    es.Pairwise (fun a b => normDistinct O a.1 b.1 = true) → mapSide O es none = []
  | [], _ => rfl
  | (k, v) :: es, h => by
      rw [List.pairwise_cons] at h
      simp only [mapSide, mapSide_none O es h.2, List.append_nil, List.filterMap_eq_nil_iff]
      intro e he
      simp [h.1 e he]

theorem setSide_none (O : Oracles) : ∀ es : List Term,
    es.Pairwise (fun a b => normDistinct O a b = true) → setSide O es none = []
  | [], _ => rfl
  | k :: es, h => by
      rw [List.pairwise_cons] at h
      simp only [setSide, setSide_none O es h.2, List.append_nil, List.filterMap_eq_nil_iff]
      intro e he
      simp [h.1 e he]

theorem map_normDistinct {le : Term → Term → Bool} (hle : TotalOrder le) (O : Oracles)
    (es : List (Term × Term)) (hs : Adjacent (fun a b => lexLe le a b = true) es)
    (hadj : adjacentKeysDiffer es = true) (hh : oneHeader (es.map (·.1)) = true) :
    es.Pairwise (fun a b => normDistinct O a.1 b.1 = true) := by
  refine (map_keys_pairwise_distinct hle es hs hadj).imp_of_mem ?_
  intro a b ha hb hne
  have := oneHeader_same _ hh a.1 (List.mem_map_of_mem ha) b.1 (List.mem_map_of_mem hb)
  simp [normDistinct, structDistinct_complete O.evaluated O.injectionsDistinct a.1 b.1 this.1 this.2 hne]

theorem set_normDistinct {le : Term → Term → Bool} (hle : TotalOrder le) (O : Oracles)
    (es : List Term) (hs : Adjacent (fun a b => le a b = true) es)
    (hadj : adjacentElementsDiffer es = true) (hh : oneHeader es = true) :
    es.Pairwise (fun a b => normDistinct O a b = true) := by
  refine (set_pairwise_distinct hle es hs hadj).imp_of_mem ?_
  intro a b ha hb hne
  have := oneHeader_same _ hh a ha b hb
  simp [normDistinct, structDistinct_complete O.evaluated O.injectionsDistinct a b this.1 this.2 hne]

/-! ## 9. Case study 1: the attribute is sound for the early return

Equality proved: list equality of `ceil_term_recursive`'s output (the empty list), for every
definition (every `Oracles`). No hypothesis about the matcher: the narrowed key class is decided by
`structurally_distinct_after_normalization` alone. Hypotheses: `WF` (what `Term::map`/`Term::set`
guarantee) and `TotalOrder le` (`Ord for Term` is transitive and consistent with `Eq`). -/
mutual
theorem ceilFree_sound (O : Oracles) {le : Term → Term → Bool} (hle : TotalOrder le) :
    ∀ t, WF le t → ceilFree t = true → ceilTerm O t = []
  | .app s ss args, hw, hc => by
      simp only [ceilFree, Bool.and_eq_true, Bool.not_eq_true'] at hc
      simp [ceilTerm, hc.1, ceilList_sound O hle args hw hc.2, O.dedup_nil]
  | .and l r, hw, hc => by
      simp only [ceilFree, Bool.and_eq_true] at hc
      simp [ceilTerm, ceilFree_sound O hle l hw.1 hc.1, ceilFree_sound O hle r hw.2 hc.2,
        O.dedup_nil]
  | .inj _ _ t, hw, hc => by
      simp [ceilTerm, ceilFree_sound O hle t hw hc, O.dedup_nil]
  | .dv _ _, _, _ => by simp [ceilTerm, O.dedup_nil]
  | .var .element _ _, _, _ => by simp [ceilTerm, O.dedup_nil]
  | .var .set _ _, _, hc => by simp [ceilFree] at hc
  | .map _ es rest, hw, hc => by
      simp only [ceilFree, Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
      obtain ⟨⟨⟨he, rfl⟩, hh⟩, hadj⟩ := hc
      simp [ceilTerm, ceilEntries_sound O hle es hw.2.1 he, ceilOpt,
        mapSide_none O es (map_normDistinct hle O es hw.1 hadj hh), O.dedup_nil]
  | .list _ hs rest, hw, hc => by
      simp only [ceilFree, Bool.and_eq_true] at hc
      simp [ceilTerm, ceilList_sound O hle hs hw.1 hc.1, ceilRest_sound O hle rest hw.2 hc.2,
        O.dedup_nil]
  | .set _ es rest, hw, hc => by
      simp only [ceilFree, Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
      obtain ⟨⟨⟨he, rfl⟩, hh⟩, hadj⟩ := hc
      simp [ceilTerm, ceilList_sound O hle es hw.2.1 he, ceilOpt,
        setSide_none O es (set_normDistinct hle O es hw.1 hadj hh), O.dedup_nil]
theorem ceilList_sound (O : Oracles) {le : Term → Term → Bool} (hle : TotalOrder le) :
    ∀ ts, WFList le ts → ceilFreeList ts = true → ceilList O ts = []
  | [], _, _ => rfl
  | t :: ts, hw, hc => by
      simp only [ceilFreeList, Bool.and_eq_true] at hc
      simp [ceilList, ceilFree_sound O hle t hw.1 hc.1, ceilList_sound O hle ts hw.2 hc.2]
theorem ceilEntries_sound (O : Oracles) {le : Term → Term → Bool} (hle : TotalOrder le) :
    ∀ es, WFEntries le es → ceilFreeEntries es = true → ceilEntries O es = []
  | [], _, _ => rfl
  | (k, v) :: es, hw, hc => by
      simp only [ceilFreeEntries, Bool.and_eq_true] at hc
      simp [ceilEntries, ceilFree_sound O hle k hw.1 hc.1.1, ceilFree_sound O hle v hw.2.1 hc.1.2,
        ceilEntries_sound O hle es hw.2.2 hc.2]
theorem ceilRest_sound (O : Oracles) {le : Term → Term → Bool} (hle : TotalOrder le) :
    ∀ r, WFRest le r → ceilFreeRest r = true → ceilRest O r = []
  | none, _, _ => rfl
  | some (m, ts), hw, hc => by
      simp only [ceilFreeRest, Bool.and_eq_true] at hc
      simp [ceilRest, ceilFree_sound O hle m hw.1 hc.1, ceilList_sound O hle ts hw.2 hc.2]
end

/-! ## 10. Case study 3a: `has_macro_or_alias` replaces the `macro_or_alias_symbol` walk (OT-02) -/

/- `macro_or_alias_symbol` (term.rs:808-816): the first symbol with `macro_or_alias` in the
preorder of `visit_symbols` (:760-805). -/
mutual
def firstMacro : Term → Option String
  | .app s _ args   => if s.macroOrAlias then some s.name else firstMacroList args
  | .and l r        => (firstMacro l).or (firstMacro r)
  | .inj _ _ t      => firstMacro t
  | .dv _ _         => none
  | .var _ _ _      => none
  | .map _ es rest  => (firstMacroEntries es).or (firstMacroOpt rest)
  | .list _ hs rest => (firstMacroList hs).or (firstMacroRest rest)
  | .set _ es rest  => (firstMacroList es).or (firstMacroOpt rest)
def firstMacroList : List Term → Option String
  | []      => none
  | t :: ts => (firstMacro t).or (firstMacroList ts)
def firstMacroEntries : List (Term × Term) → Option String
  | []           => none
  | (k, v) :: es => ((firstMacro k).or (firstMacro v)).or (firstMacroEntries es)
def firstMacroOpt : Option Term → Option String
  | none   => none
  | some t => firstMacro t
def firstMacroRest : Option (Term × List Term) → Option String
  | none         => none
  | some (m, ts) => (firstMacro m).or (firstMacroList ts)
end

/- The attribute `has_macro_or_alias`: the symbol's flag at an application, or any child's. -/
mutual
def hasMacro : Term → Bool
  | .app s _ args   => s.macroOrAlias || hasMacroList args
  | .and l r        => hasMacro l || hasMacro r
  | .inj _ _ t      => hasMacro t
  | .dv _ _         => false
  | .var _ _ _      => false
  | .map _ es rest  => hasMacroEntries es || hasMacroOpt rest
  | .list _ hs rest => hasMacroList hs || hasMacroRest rest
  | .set _ es rest  => hasMacroList es || hasMacroOpt rest
def hasMacroList : List Term → Bool
  | []      => false
  | t :: ts => hasMacro t || hasMacroList ts
def hasMacroEntries : List (Term × Term) → Bool
  | []           => false
  | (k, v) :: es => hasMacro k || hasMacro v || hasMacroEntries es
def hasMacroOpt : Option Term → Bool
  | none   => false
  | some t => hasMacro t
def hasMacroRest : Option (Term × List Term) → Bool
  | none         => false
  | some (m, ts) => hasMacro m || hasMacroList ts
end

/- Exact, not just sound: the flag is false iff the walk finds nothing. -/
mutual
theorem hasMacro_iff : ∀ t, hasMacro t = false ↔ firstMacro t = none
  | .app s _ args => by
      cases h : s.macroOrAlias <;> simp [hasMacro, firstMacro, h, hasMacroList_iff args]
  | .and l r => by simp [hasMacro, firstMacro, hasMacro_iff l, hasMacro_iff r]
  | .inj _ _ t => by simp [hasMacro, firstMacro, hasMacro_iff t]
  | .dv _ _ | .var _ _ _ => by simp [hasMacro, firstMacro]
  | .map _ es rest => by
      simp [hasMacro, firstMacro, hasMacroEntries_iff es, hasMacroOpt_iff rest]
  | .list _ hs rest => by
      simp [hasMacro, firstMacro, hasMacroList_iff hs, hasMacroRest_iff rest]
  | .set _ es rest => by
      simp [hasMacro, firstMacro, hasMacroList_iff es, hasMacroOpt_iff rest]
theorem hasMacroList_iff : ∀ ts, hasMacroList ts = false ↔ firstMacroList ts = none
  | [] => by simp [hasMacroList, firstMacroList]
  | t :: ts => by simp [hasMacroList, firstMacroList, hasMacro_iff t, hasMacroList_iff ts]
theorem hasMacroEntries_iff : ∀ es, hasMacroEntries es = false ↔ firstMacroEntries es = none
  | [] => by simp [hasMacroEntries, firstMacroEntries]
  | (k, v) :: es => by
      simp [hasMacroEntries, firstMacroEntries, hasMacro_iff k, hasMacro_iff v,
        hasMacroEntries_iff es, and_assoc]
theorem hasMacroOpt_iff : ∀ o, hasMacroOpt o = false ↔ firstMacroOpt o = none
  | none => by simp [hasMacroOpt, firstMacroOpt]
  | some t => by simp [hasMacroOpt, firstMacroOpt, hasMacro_iff t]
theorem hasMacroRest_iff : ∀ r, hasMacroRest r = false ↔ firstMacroRest r = none
  | none => by simp [hasMacroRest, firstMacroRest]
  | some (m, ts) => by simp [hasMacroRest, firstMacroRest, hasMacro_iff m, hasMacroList_iff ts]
end

/-- Equality proved: the optimized `macro_or_alias_symbol` returns the same `Option<Name>` as
today's walk (the walk still runs when the flag is set, so the reported name, and with it the
`SurvivingMacroOrAlias` halt reason, is unchanged). -/
theorem macro_shortcut_eq (t : Term) :
    (if hasMacro t then firstMacro t else none) = firstMacro t := by
  cases h : hasMacro t
  · simp [(hasMacro_iff t).mp h]
  · simp

/-! ## 11. Case study 3b: the saturated k-cell count replaces `find_k_cells` (OT-02) -/

/- Every k cell not nested in a k cell, in `find_k_cells` order, with no early exit. A
specification device; the Rust has no such function. -/
mutual
def allK : Term → List Term
  | .app s ss args  => if s.isKCell then [.app s ss args] else allKList args
  | .and l r        => allK l ++ allK r
  | .inj _ _ t      => allK t
  | .dv _ _         => []
  | .var _ _ _      => []
  | .map _ es rest  => allKEntries es ++ allKOpt rest
  | .list _ hs rest => allKList hs ++ allKRest rest
  | .set _ es rest  => allKList es ++ allKOpt rest
def allKList : List Term → List Term
  | []      => []
  | t :: ts => allK t ++ allKList ts
def allKEntries : List (Term × Term) → List Term
  | []           => []
  | (k, v) :: es => allK k ++ allK v ++ allKEntries es
def allKOpt : Option Term → List Term
  | none   => []
  | some t => allK t
def allKRest : Option (Term × List Term) → List Term
  | none         => []
  | some (m, ts) => allK m ++ allKList ts
end

/- `find_k_cells` (rule.rs:789-840): the `cells.len() > 1` early exit at every call, as an
accumulator. The check is repeated in each equation, and `termination_by structural` names the
term argument: without it Lean 4.34 sees two candidate arguments of a nested type (the accumulator
is a `List Term` too), gives up on structural recursion, and falls back to well-founded recursion,
which the kernel cannot reduce. -/
mutual
def findK : Term → List Term → List Term
  | .app s ss args, acc  => if acc.length > 1 then acc else
                             if s.isKCell then acc ++ [.app s ss args] else findKList args acc
  | .and l r, acc        => if acc.length > 1 then acc else findK r (findK l acc)
  | .inj _ _ u, acc      => if acc.length > 1 then acc else findK u acc
  | .dv _ _, acc         => acc
  | .var _ _ _, acc      => acc
  | .map _ es rest, acc  => if acc.length > 1 then acc else findKOpt rest (findKEntries es acc)
  | .list _ hs rest, acc => if acc.length > 1 then acc else findKRest rest (findKList hs acc)
  | .set _ es rest, acc  => if acc.length > 1 then acc else findKOpt rest (findKList es acc)
termination_by structural t _ => t
def findKList : List Term → List Term → List Term
  | [], acc      => acc
  | t :: ts, acc => findKList ts (findK t acc)
termination_by structural ts _ => ts
def findKEntries : List (Term × Term) → List Term → List Term
  | [], acc           => acc
  | (k, v) :: es, acc => findKEntries es (findK v (findK k acc))
termination_by structural es _ => es
def findKOpt : Option Term → List Term → List Term
  | none, acc   => acc
  | some t, acc => findK t acc
termination_by structural o _ => o
def findKRest : Option (Term × List Term) → List Term → List Term
  | none, acc         => acc
  | some (m, ts), acc => findKList ts (findK m acc)
termination_by structural r _ => r
end

/-- Saturating addition: the count is capped at 2. -/
def satAdd (a b : Nat) : Nat := min 2 (a + b)

/- The attribute `k_cells` (OT-02): 1 at a k cell whatever its children hold (where
`find_k_cells` stops descending), otherwise the saturated sum of the children's counts. -/
mutual
def kCells : Term → Nat
  | .app s _ args   => if s.isKCell then 1 else kCellsList args
  | .and l r        => satAdd (kCells l) (kCells r)
  | .inj _ _ t      => kCells t
  | .dv _ _         => 0
  | .var _ _ _      => 0
  | .map _ es rest  => satAdd (kCellsEntries es) (kCellsOpt rest)
  | .list _ hs rest => satAdd (kCellsList hs) (kCellsRest rest)
  | .set _ es rest  => satAdd (kCellsList es) (kCellsOpt rest)
def kCellsList : List Term → Nat
  | []      => 0
  | t :: ts => satAdd (kCells t) (kCellsList ts)
def kCellsEntries : List (Term × Term) → Nat
  | []           => 0
  | (k, v) :: es => satAdd (satAdd (kCells k) (kCells v)) (kCellsEntries es)
def kCellsOpt : Option Term → Nat
  | none   => 0
  | some t => kCells t
def kCellsRest : Option (Term × List Term) → Nat
  | none         => 0
  | some (m, ts) => satAdd (kCells m) (kCellsList ts)
end

theorem satAdd_min (a b : List Term) :
    satAdd (min 2 a.length) (min 2 b.length) = min 2 (a ++ b).length := by
  simp only [satAdd, List.length_append]; omega

mutual
theorem kCells_eq : ∀ t, kCells t = min 2 (allK t).length
  | .app s _ args => by
      cases h : s.isKCell <;> simp [kCells, allK, h, kCellsList_eq args]
  | .and l r => by simp only [kCells, allK, kCells_eq l, kCells_eq r, satAdd_min]
  | .inj _ _ t => by simp only [kCells, allK, kCells_eq t]
  | .dv _ _ | .var _ _ _ => by simp [kCells, allK]
  | .map _ es rest => by simp only [kCells, allK, kCellsEntries_eq es, kCellsOpt_eq rest, satAdd_min]
  | .list _ hs rest => by simp only [kCells, allK, kCellsList_eq hs, kCellsRest_eq rest, satAdd_min]
  | .set _ es rest => by simp only [kCells, allK, kCellsList_eq es, kCellsOpt_eq rest, satAdd_min]
theorem kCellsList_eq : ∀ ts, kCellsList ts = min 2 (allKList ts).length
  | [] => by simp [kCellsList, allKList]
  | t :: ts => by simp only [kCellsList, allKList, kCells_eq t, kCellsList_eq ts, satAdd_min]
theorem kCellsEntries_eq : ∀ es, kCellsEntries es = min 2 (allKEntries es).length
  | [] => by simp [kCellsEntries, allKEntries]
  | (k, v) :: es => by
      simp only [kCellsEntries, allKEntries, kCells_eq k, kCells_eq v, kCellsEntries_eq es,
        satAdd_min]
theorem kCellsOpt_eq : ∀ o, kCellsOpt o = min 2 (allKOpt o).length
  | none => by simp [kCellsOpt, allKOpt]
  | some t => by simp only [kCellsOpt, allKOpt, kCells_eq t]
theorem kCellsRest_eq : ∀ r, kCellsRest r = min 2 (allKRest r).length
  | none => by simp [kCellsRest, allKRest]
  | some (m, ts) => by simp only [kCellsRest, allKRest, kCells_eq m, kCellsList_eq ts, satAdd_min]
end

/-- Composing two truncated appends is one truncated append of the concatenation. -/
theorem take_step (acc a b : List Term) :
    (acc ++ a.take (2 - acc.length)) ++ b.take (2 - (acc ++ a.take (2 - acc.length)).length)
      = acc ++ (a ++ b).take (2 - acc.length) := by
  rw [List.append_assoc, List.take_append]
  congr 2
  simp only [List.length_append, List.length_take]
  congr 1
  omega

/- `find_k_cells` with any accumulator appends the first cells of `allK`, up to two in all. -/
mutual
theorem findK_eq : ∀ t acc, findK t acc = acc ++ (allK t).take (2 - acc.length)
  | .app s ss args, acc => by
      by_cases hl : acc.length > 1
      · simp [findK, hl]; omega
      · cases h : s.isKCell
        · simp [findK, allK, hl, h, findKList_eq args acc]
        · have : 2 - acc.length = (1 - acc.length) + 1 := by omega
          simp [findK, allK, hl, h, this]
  | .and l r, acc => by
      by_cases hl : acc.length > 1
      · simp [findK, hl]; omega
      · simp only [findK, hl, ite_false, allK, findK_eq l, findK_eq r, take_step]
  | .inj _ _ u, acc => by
      by_cases hl : acc.length > 1
      · simp [findK, hl]; omega
      · simp only [findK, hl, ite_false, allK, findK_eq u]
  | .dv _ _, acc | .var _ _ _, acc => by simp [findK, allK]
  | .map _ es rest, acc => by
      by_cases hl : acc.length > 1
      · simp [findK, hl]; omega
      · simp only [findK, hl, ite_false, allK, findKEntries_eq es, findKOpt_eq rest, take_step]
  | .list _ hs rest, acc => by
      by_cases hl : acc.length > 1
      · simp [findK, hl]; omega
      · simp only [findK, hl, ite_false, allK, findKList_eq hs, findKRest_eq rest, take_step]
  | .set _ es rest, acc => by
      by_cases hl : acc.length > 1
      · simp [findK, hl]; omega
      · simp only [findK, hl, ite_false, allK, findKList_eq es, findKOpt_eq rest, take_step]
theorem findKList_eq : ∀ ts acc, findKList ts acc = acc ++ (allKList ts).take (2 - acc.length)
  | [], acc => by simp [findKList, allKList]
  | t :: ts, acc => by simp only [findKList, allKList, findK_eq t, findKList_eq ts, take_step]
theorem findKEntries_eq :
    ∀ es acc, findKEntries es acc = acc ++ (allKEntries es).take (2 - acc.length)
  | [], acc => by simp [findKEntries, allKEntries]
  | (k, v) :: es, acc => by
      simp only [findKEntries, allKEntries, findK_eq k, findK_eq v, findKEntries_eq es, take_step]
theorem findKOpt_eq : ∀ o acc, findKOpt o acc = acc ++ (allKOpt o).take (2 - acc.length)
  | none, acc => by simp [findKOpt, allKOpt]
  | some t, acc => by simp only [findKOpt, allKOpt, findK_eq t]
theorem findKRest_eq : ∀ r acc, findKRest r acc = acc ++ (allKRest r).take (2 - acc.length)
  | none, acc => by simp [findKRest, allKRest]
  | some (m, ts), acc => by
      simp only [findKRest, allKRest, findK_eq m, findKList_eq ts, take_step]
end

/- The fetch of OT-02: descend only into the first child whose count is nonzero. In Rust each
`kCells` below is an O(1) read of the stored attribute. -/
mutual
def fetchK : Term → Option Term
  | .app s ss args  => if s.isKCell then some (.app s ss args) else fetchKList args
  | .and l r        => if kCells l = 0 then fetchK r else fetchK l
  | .inj _ _ t      => fetchK t
  | .dv _ _         => none
  | .var _ _ _      => none
  | .map _ es rest  => if kCellsEntries es = 0 then fetchKOpt rest else fetchKEntries es
  | .list _ hs rest => if kCellsList hs = 0 then fetchKRest rest else fetchKList hs
  | .set _ es rest  => if kCellsList es = 0 then fetchKOpt rest else fetchKList es
def fetchKList : List Term → Option Term
  | []      => none
  | t :: ts => if kCells t = 0 then fetchKList ts else fetchK t
def fetchKEntries : List (Term × Term) → Option Term
  | []           => none
  | (k, v) :: es => if kCells k = 0 then (if kCells v = 0 then fetchKEntries es else fetchK v)
                    else fetchK k
def fetchKOpt : Option Term → Option Term
  | none   => none
  | some t => fetchK t
def fetchKRest : Option (Term × List Term) → Option Term
  | none         => none
  | some (m, ts) => if kCells m = 0 then fetchKList ts else fetchK m
end

theorem min2_zero (l : List Term) : min 2 l.length = 0 ↔ l = [] := by
  rw [← List.length_eq_zero_iff]; omega

theorem head?_pick (a b : List Term) :
    (if min 2 a.length = 0 then b.head? else a.head?) = (a ++ b).head? := by
  cases a <;> simp

mutual
theorem fetchK_eq : ∀ t, fetchK t = (allK t).head?
  | .app s _ args => by cases h : s.isKCell <;> simp [fetchK, allK, h, fetchKList_eq args]
  | .and l r => by simp only [fetchK, allK, kCells_eq l, fetchK_eq l, fetchK_eq r, head?_pick]
  | .inj _ _ t => by simp only [fetchK, allK, fetchK_eq t]
  | .dv _ _ | .var _ _ _ => by simp [fetchK, allK]
  | .map _ es rest => by
      simp only [fetchK, allK, kCellsEntries_eq es, fetchKEntries_eq es, fetchKOpt_eq rest,
        head?_pick]
  | .list _ hs rest => by
      simp only [fetchK, allK, kCellsList_eq hs, fetchKList_eq hs, fetchKRest_eq rest, head?_pick]
  | .set _ es rest => by
      simp only [fetchK, allK, kCellsList_eq es, fetchKList_eq es, fetchKOpt_eq rest, head?_pick]
theorem fetchKList_eq : ∀ ts, fetchKList ts = (allKList ts).head?
  | [] => rfl
  | t :: ts => by
      simp only [fetchKList, allKList, kCells_eq t, fetchK_eq t, fetchKList_eq ts, head?_pick]
theorem fetchKEntries_eq : ∀ es, fetchKEntries es = (allKEntries es).head?
  | [] => rfl
  | (k, v) :: es => by
      simp only [fetchKEntries, allKEntries, kCells_eq k, kCells_eq v, fetchK_eq k, fetchK_eq v,
        fetchKEntries_eq es, head?_pick, List.append_assoc]
theorem fetchKOpt_eq : ∀ o, fetchKOpt o = (allKOpt o).head?
  | none => rfl
  | some t => by simp only [fetchKOpt, allKOpt, fetchK_eq t]
theorem fetchKRest_eq : ∀ r, fetchKRest r = (allKRest r).head?
  | none => rfl
  | some (m, ts) => by
      simp only [fetchKRest, allKRest, kCells_eq m, fetchK_eq m, fetchKList_eq ts, head?_pick]
end

/-- What `rule_index` (rule.rs:766-777) keeps from the walk: the cell when there is exactly one. -/
def single : List Term → Option Term
  | [c] => some c
  | _   => none

/-- Case study 3b. Equality proved: the optimized rule-index cell (branch on the stored count, and
fetch only when it is 1) is the same `Option` cell as today's `rule_index` computes from
`find_k_cells`. No sentinel: the count saturates at 2 and the caller branches on it. -/
theorem rule_index_same (t : Term) :
    (if kCells t = 1 then fetchK t else none) = single (findK t []) := by
  rw [kCells_eq, fetchK_eq, findK_eq]
  rcases h : allK t with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp [single]

end KRust.TermAttributes
