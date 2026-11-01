import TwoParamOkConf.Views
import TwoParam.Invariants

/-! The instance the witnesses run at, and each witness's legality, by hand.

`seg` runs a segment as the coroutine language does (`tests/fixtures/corout`: `add`, `dbl`,
`loop`, to the next `yield` or the code's end), within a bound on its steps: the segment's
register and the code after its `yield`. A segment longer than the bound has no value (`none`),
so its resume does not step; the witnesses' segments take a few steps each. It is computable, so
the elaborator's search and the kernel run it; `TwoParamInst.hooks`, the segments as corout's own
runs, is not (it chooses a run's end), so the witnesses cannot run at it.

Each witness is the initial configuration of its program (`TwoParam.init`), and every initial
configuration satisfies `valsOk` (its `<vals>` is empty; `Invariant.init_holds`). -/

namespace TwoParamOkConf

open KPrelude TwoParam

/-- `A ; B`, within `n` statements of `A`. -/
def app : Nat → SortStmts → SortStmts → SortStmts
  | n + 1, .«_;_» S R, T => .«_;_» S (app n R T)
  | _, _, T => T

/-- At most `n` steps of the coroutine language from register `R` and code `C`, to a `yield`
(the register, and the code after it) or the code's end. -/
def run : Nat → Int → SortStmts → Option (Int × SortStmts)
  | n + 1, R, .«_;_» (.«add(_)» I) C => run n (R + I) C
  | n + 1, R, .«_;_» .dbl C => run n (R * 2) C
  | n + 1, R, .«_;_» (.«loop(_,_)» M (.«{_}» B)) C =>
    if M > 0 then run n R (app 1000 B (.«_;_» (.«loop(_,_)» (M - 1) (.«{_}» B)) C)) else run n R C
  | _ + 1, R, .«_;_» .yield C => some (R, C)
  | _ + 1, R, .«.List{"_;__TWOPARAM-SYNTAX_Stmts_Stmt_Stmts"}_Stmts» =>
    some (R, .«.List{"_;__TWOPARAM-SYNTAX_Stmts_Stmt_Stmts"}_Stmts»)
  | _, _, _ => none

/-- The segments of `twoparam`, run within 1000 steps. -/
def seg : TwoParam.Hooks where
  «fn.segReg(_,_)_TWOPARAM_Int_Int_Stmts» R C := (run 1000 R C).map (·.1)
  «fn.segCode(_,_)_TWOPARAM_Stmts_Int_Stmts» R C := (run 1000 R C).map (·.2)

attribute [local instance] seg

/-- A map literal of one binding is that binding. -/
theorem ofEntries_one {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V] (k : K) (v : V) :
    (MapHook.ofEntries [(k, v)] : M) = MapHook.element k v := by
  simp [MapHook.ofEntries, MapHook.update_def, MapHook.element, MapHook.unit, ListIso.toList_ofList,
    SAL.insert]

/-- An empty map literal is the empty map. -/
theorem ofEntries_nil {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V] :
    (MapHook.ofEntries [] : M) = MapHook.unit := rfl

/-- A configuration that is initial satisfies the invariant. -/
theorem legal_of_init {c : SortGeneratedTopCell} (pgm : SortPgm) (h : c = init pgm) : Invariant c :=
  h ▸ Invariant.init_holds pgm

local macro "init_legal" : tactic => `(tactic| (refine legal_of_init ?pgm ?h; case h => simp only [init, ofEntries_one, ofEntries_nil]; rfl))

theorem hand.witness.«two-news».legal : Invariant witness.«two-news» := by
  unfold witness.«two-news»; init_legal
theorem hand.witness.«two-resumes».legal : Invariant witness.«two-resumes» := by
  unfold witness.«two-resumes»; init_legal
theorem hand.witness.«lit-and-oid».legal : Invariant witness.«lit-and-oid» := by
  unfold witness.«lit-and-oid»; init_legal
theorem hand.witness.«two-spends».legal : Invariant witness.«two-spends» := by
  unfold witness.«two-spends»; init_legal

end TwoParamOkConf
