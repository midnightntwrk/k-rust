/-
Rust anchors verified at a493ba273:
  crates/k-rust-backend/src/substitution.rs:293-312 (`saturate_with`),
  crates/k-rust-backend/src/substitution/saturation_tests.rs:10-25 (the old loop,
    frozen from substitution.rs:264-285 at 8ff88a783),
  crates/k-rust-backend/src/tests/lean_bridge/substitution.rs:75-128 (observations).

The model covers the changed saturation schedule: snapshot lookup, removal, callback inputs, restoration, result placement, the round bound and convergence.
`apply` is an arbitrary value-based callback indexed by call number.
Production passes `substitute`; the bridge supplies arbitrary answers over equality-class IDs of real Rust values and checks the complete callback trace and final bindings.
Both schedules give the callback equal values and maps in the same order, so this proof needs no model of unchanged term reconstruction or premise about acyclicity.
-/
namespace KRust.SubstitutionSaturation

/-- The value-level lookup view of the ordered substitution map.
Rust: `crates/k-rust-backend/src/substitution.rs:65` at `a493ba273`. -/
abbrev Env (V T : Type) := V → Option T

/-- The remaining bindings after `BTreeMap::remove` in the saturation helper.
Rust: `crates/k-rust-backend/src/substitution.rs:302-304` at `a493ba273`. -/
def erase {V T : Type} [DecidableEq V] (s : Env V T) (x : V) : Env V T :=
  fun y => if y = x then none else s y

/-- Installing a value with `BTreeMap::insert` in the saturation helper.
Rust: `crates/k-rust-backend/src/substitution.rs:306` at `a493ba273`. -/
def put {V T : Type} [DecidableEq V] (s : Env V T) (x : V) (value : T) : Env V T :=
  fun y => if y = x then some value else s y

/-- Exact equality of the restored map with its original snapshot.
Rust: `crates/k-rust-backend/src/substitution.rs:302-306` at `a493ba273`. -/
theorem restore_eq {V T : Type} [DecidableEq V] (s : Env V T) (x : V) (value : T)
    (h : s x = some value) : put (erase s x) x value = s := by
  funext y
  by_cases hy : y = x
  · subst y; simp [put, h]
  · simp [put, erase, hy]

/-- One callback input: its key, old value and snapshot with that key removed.
Rust: `crates/k-rust-backend/src/substitution.rs:301-305` at `a493ba273`. -/
structure Call (V T : Type) where
  key : V
  value : T
  others : Env V T

/-- Sweep state: restored snapshot, output map, callback index and trace.
The loop tests convergence against the sweep snapshot, as Rust tests against `previous`.
Rust: `crates/k-rust-backend/src/substitution.rs:297-311` at `a493ba273`. -/
structure Result (V T : Type) where
  snapshot : Env V T
  bindings : Env V T
  cursor : Nat
  calls : List (Call V T)

/-- Record callback inputs in the Rust loop's iteration order.
Rust: `crates/k-rust-backend/src/tests/lean_bridge/substitution.rs:84-99` at `a493ba273`. -/
def prepend {V T : Type} (call : Call V T) (result : Result V T) : Result V T :=
  { result with calls := call :: result.calls }

/-- Old round: iterate snapshot keys, copy and erase independently for each callback, then write its result.
Rust: `crates/k-rust-backend/src/substitution/saturation_tests.rs:14-20` at `a493ba273`. -/
def oldSweep {V T : Type} [DecidableEq V]
    (apply : Nat → T → Env V T → T) :
    List V → Env V T → Env V T → Nat → Result V T
  | [], snapshot, output, cursor => ⟨snapshot, output, cursor, []⟩
  | x :: xs, snapshot, output, cursor =>
    match snapshot x with
    | none => oldSweep apply xs snapshot output cursor
    | some value =>
      let others := erase snapshot x
      prepend ⟨x, value, others⟩
        (oldSweep apply xs snapshot (put output x (apply cursor value others)) (cursor + 1))

/-- New round: remove from the snapshot, call, then restore before the next key.
Rust: `crates/k-rust-backend/src/substitution.rs:301-307` at `a493ba273`. -/
def restoringSweep {V T : Type} [DecidableEq V]
    (apply : Nat → T → Env V T → T) :
    List V → Env V T → Env V T → Nat → Result V T
  | [], snapshot, output, cursor => ⟨snapshot, output, cursor, []⟩
  | x :: xs, snapshot, output, cursor =>
    match snapshot x with
    | none => restoringSweep apply xs snapshot output cursor
    | some value =>
      let others := erase snapshot x
      prepend ⟨x, value, others⟩
        (restoringSweep apply xs (put others x value)
          (put output x (apply cursor value others)) (cursor + 1))

/-- Exact equality of the restored snapshot, output map, cursor and callback trace of old and new rounds.
Holds for every value-based callback, key order and map, without an acyclicity premise.
Rust: `crates/k-rust-backend/src/substitution.rs:301-307 and crates/k-rust-backend/src/substitution/saturation_tests.rs:14-20` at `a493ba273`. -/
theorem sweep_eq {V T : Type} [DecidableEq V] (apply : Nat → T → Env V T → T)
    (keys : List V) (snapshot output : Env V T) (cursor : Nat) :
    restoringSweep apply keys snapshot output cursor = oldSweep apply keys snapshot output cursor := by
  induction keys generalizing snapshot output cursor with
  | nil => rfl
  | cons x xs ih =>
    simp only [restoringSweep, oldSweep]
    cases h : snapshot x with
    | none => exact ih _ _ _
    | some value =>
      simp only [restore_eq snapshot x value h]
      rw [ih]

/-- Bounded rounds with the Rust convergence-test placement.
`same` is arbitrary; the bridge compares every binding in the fixed domain.
Rust: `crates/k-rust-backend/src/substitution.rs:297-311` at `a493ba273`. -/
def run {V T : Type}
    (sweep : List V → Env V T → Env V T → Nat → Result V T)
    (same : Env V T → Env V T → Bool) (keys : List V) :
    Nat → Env V T → Nat → Result V T
  | 0, snapshot, cursor => ⟨snapshot, snapshot, cursor, []⟩
  | n + 1, snapshot, cursor =>
    let round := sweep keys snapshot snapshot cursor
    if same round.bindings round.snapshot then round
    else
      let rest := run sweep same keys n round.bindings round.cursor
      { rest with calls := round.calls ++ rest.calls }

/-- Exact final-map, call-count and complete callback-trace equality, including early stopping.
No hypothesis about the callback's results, candidate graphs or dependency ranks is used.
Rust: `crates/k-rust-backend/src/substitution.rs:293-312 and crates/k-rust-backend/src/substitution/saturation_tests.rs:10-25` at `a493ba273`. -/
theorem saturation_eq {V T : Type} [DecidableEq V]
    (apply : Nat → T → Env V T → T) (same : Env V T → Env V T → Bool)
    (keys : List V) (rounds : Nat) (snapshot : Env V T) (cursor : Nat) :
    run (restoringSweep apply) same keys rounds snapshot cursor =
      run (oldSweep apply) same keys rounds snapshot cursor := by
  have hs : restoringSweep apply = oldSweep apply := by
    funext ks s o c
    exact sweep_eq apply ks s o c
  rw [hs]

/-- Materialize the fixed finite domain in order, as the bridge enumerates the actual BTreeMap.
Rust: `crates/k-rust-backend/src/tests/lean_bridge/substitution.rs:117-128` at `a493ba273`. -/
def entries {V T : Type} (keys : List V) (s : Env V T) : List (V × T) :=
  keys.filterMap fun x => (s x).map (x, ·)

/-- Executable conformance specialization over key ordinals, Term equality-class IDs and arbitrary callback answers.
It models the saturation helper with the test callback, whose answers may be any value.
Rust: `crates/k-rust-backend/src/tests/lean_bridge/substitution.rs:75-106` at `a493ba273`. -/
def replay (restoring : Bool) (initial : List (Nat × Nat)) (answers : List Nat) : Result Nat Nat :=
  let keys := initial.map Prod.fst
  let snapshot : Env Nat Nat := fun x => initial.lookup x
  let apply := fun cursor value (_ : Env Nat Nat) => answers[cursor]?.getD value
  let same := fun s t => keys.all fun x => s x == t x
  let sweep := if restoring then restoringSweep apply else oldSweep apply
  run sweep same keys keys.length snapshot 0

/-- Exact observable equality of both bridged specializations, for every answer stream.
Rust: `crates/k-rust-backend/src/tests/lean_bridge/substitution.rs:75-106` at `a493ba273`. -/
theorem replay_eq (initial : List (Nat × Nat)) (answers : List Nat) :
    replay true initial answers = replay false initial answers := by
  exact saturation_eq _ _ _ _ _ _

end KRust.SubstitutionSaturation
