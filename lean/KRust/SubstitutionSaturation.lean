/-
Source: crates/k-rust-backend/src/substitution.rs:264-285 at 8ff88a783 (old loop),
and the remove/apply/restore saturation helper introduced with this model.

Only the changed computation is modeled: the round snapshot, removing one binding,
passing the old value and the remaining snapshot to an unchanged callback, restoring
that binding, writing the result, and the bounded loop's convergence test.
`apply` is arbitrary and indexed by call number. In production it is `substitute`;
the bridge specializes it to arbitrary supplied answers, over IDs of actual Rust
Variable/Term values, and compares the complete callback trace and final map.
No term reconstruction, SCC or acyclicity assumption is needed: both implementations
pass extensionally equal maps and the same term to every callback in the same order.
-/
namespace KRust.SubstitutionSaturation

abbrev Env (V T : Type) := V → Option T

/-- `BTreeMap::remove`'s remaining bindings, substitution.rs saturation helper.
Source anchor: 8ff88a783:274-275 for the old clone/remove loop. -/
def erase {V T : Type} [DecidableEq V] (s : Env V T) (x : V) : Env V T :=
  fun y => if y = x then none else s y

/-- `BTreeMap::insert` in the saturation helper: install a value at one key. -/
def put {V T : Type} [DecidableEq V] (s : Env V T) (x : V) (value : T) : Env V T :=
  fun y => if y = x then some value else s y

/-- Exact equality of the restored map with its original snapshot.
Mirrors remove/insert in the saturation helper; old anchor 8ff88a783:274-275. -/
theorem restore_eq {V T : Type} [DecidableEq V] (s : Env V T) (x : V) (value : T)
    (h : s x = some value) : put (erase s x) x value = s := by
  funext y
  by_cases hy : y = x
  · subst y; simp [put, h]
  · simp [put, erase, hy]

/-- One callback input, including the map after removing the current binding.
Mirrors the arguments of `substitute(value, &others)`, 8ff88a783:276. -/
structure Call (V T : Type) where
  key : V
  value : T
  others : Env V T

/-- Sweep state: the snapshot after the final restoration, output map, callback index and trace.
The loop uses the sweep snapshot for its convergence test, as the Rust uses `previous`. -/
structure Result (V T : Type) where
  snapshot : Env V T
  bindings : Env V T
  cursor : Nat
  calls : List (Call V T)

def prepend {V T : Type} (call : Call V T) (result : Result V T) : Result V T :=
  { result with calls := call :: result.calls }

/-- Old round: iterate the snapshot's ordered keys, copy and erase independently
for each callback, then write its result. Source: 8ff88a783:271-277. -/
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
Mirrors the remove/apply/restore helper that replaces 8ff88a783:271-277. -/
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

/-- Exact snapshot, output map, cursor and callback-trace equality of old and new rounds.
Mirrors old clone/remove at 8ff88a783:271-277 and the remove/apply/restore helper.
Holds for every callback, key order and map, without an acyclicity premise. -/
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

/-- Bounded rounds with the Rust convergence-test placement, 8ff88a783:270-282.
`same` is arbitrary; the bridge uses equality of all bindings in the fixed domain. -/
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
Mirrors the whole saturation loop at 8ff88a783:270-282 and its restoring replacement.
No hypothesis about `substitute`, candidate graphs, ranks or callback results is used. -/
theorem saturation_eq {V T : Type} [DecidableEq V]
    (apply : Nat → T → Env V T → T) (same : Env V T → Env V T → Bool)
    (keys : List V) (rounds : Nat) (snapshot : Env V T) (cursor : Nat) :
    run (restoringSweep apply) same keys rounds snapshot cursor =
      run (oldSweep apply) same keys rounds snapshot cursor := by
  have hs : restoringSweep apply = oldSweep apply := by
    funext ks s o c
    exact sweep_eq apply ks s o c
  rw [hs]

/-- Materialize the fixed finite domain in order; models BTreeMap iteration.
The bridge's keys are the ordered ordinals of the actual Rust variables. -/
def entries {V T : Type} (keys : List V) (s : Env V T) : List (V × T) :=
  keys.filterMap fun x => (s x).map (x, ·)

/-- Concrete executable specialization for the conformance bridge.
Values are equality-class IDs of real immutable Terms; answers are arbitrary callback results.
Mirrors the production saturation helper with a test callback, not term reconstruction.
Source: old loop at 8ff88a783:264-282 and its replacement helper. -/
def replay (restoring : Bool) (initial : List (Nat × Nat)) (answers : List Nat) : Result Nat Nat :=
  let keys := initial.map Prod.fst
  let snapshot : Env Nat Nat := fun x => initial.lookup x
  let apply := fun cursor value (_ : Env Nat Nat) => answers[cursor]?.getD value
  let same := fun s t => keys.all fun x => s x == t x
  let sweep := if restoring then restoringSweep apply else oldSweep apply
  run sweep same keys keys.length snapshot 0

/-- Exact observable equality of the two bridged specializations, for every answer stream.
Mirrors the production restoring helper and test-only old saturation helper. -/
theorem replay_eq (initial : List (Nat × Nat)) (answers : List Nat) :
    replay true initial answers = replay false initial answers := by
  exact saturation_eq _ _ _ _ _ _

end KRust.SubstitutionSaturation
