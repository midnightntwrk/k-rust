/-
  The steps of the three rules of fixture e3-reqens, under every interpretation of the parameters:
  K 7.1.337 kompile's text (`f2-examples/e3-reqens.kompile.kore`) of

      rule <k> a(X) => b(X) ... </k> requires X >Int 0
      rule <k> b(X) => c(X) ... </k> ensures X >Int 0
      rule <k> c(X) => d(X) ... </k> requires X >Int 0 ensures X >Int 1

  read by the reader, each statement over `c.withHooks H` for every `H : HookParams`, `c` the
  reading. Run from the package root: `lake env lean -j1 test/ReqensStepH.lean`.

  The reader reads sentence 164 as the rule `a(X) => b(X)` with `req := X >Int 0`, sentence 165 as
  `b(X) => c(X)` with `ens := X >Int 0`, and sentence 166 as `c(X) => d(X)` with both
  (`read_shape`); test/TieE3Reqens.lean ties Γ's item of each rule to its sentence
  (`rule0_from_text`, `rule1_from_text`, `rule2_from_text`).

  ## Why no statement depends on H
  The rules' checks on the parsed data (`Cert.checkStep`, `Cert.stuckCheck`) read no interpretation
  (`Cert.checkStep_withHooks`): the text declares no parameter that is an open generator (`noRaw`),
  and `_>Int_` has a value at every pair of Ints, so no point the checks evaluate is a silent one.

  - `req_steps H`: `a(1)` steps to `b(1)`; `a(0)` has no successor: the `requires` is false there.
  - `ens_steps H`: `b(1)` steps to `c(1)`; `b(0)` has no successor: the left side matches and the
    `ensures` is false there, so the right side with its `ensures` is empty.
  - `reqens_steps H`: `c(2)` steps to `d(2)`; `c(1)` has no successor, where the `requires` holds
    and the `ensures` fails; `c(0)` has none, where the `requires` fails.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open KCore.TieRuleLhs (cfgH step_everyH stuck_everyH)

namespace ReqensStepH

definition_of defn from "f2-examples/e3-reqens.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def exp : Srt := 32
def kCell : Sym := 383
def symA : Sym := 385
def symB : Sym := 386
def symC : Sym := 387
def symD : Sym := 388

theorem names_ok : c.sortName exp = "Exp" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" ∧ c.symName symC = "Lblc" ∧
    c.symName symD = "Lbld" ∧ c.symName intGt = "Lbl'Unds-GT-'Int'Unds'" := by
  decide +kernel

/-- The rules as read: the `requires` is `Rule.req`, the `ensures` is `Rule.ens`; no existential
variable, no `pre`, no `post`. -/
theorem read_shape : c.rules.map (fun r => (r.req, r.ens, r.exs, r.pre.isTop, r.post.isTop)) =
    [(some (.app intGt [.var 0, .dv Srt.int (.int 0)]), none, [], true, true),
     (none, some (.app intGt [.var 0, .dv Srt.int (.int 0)]), [], true, true),
     (some (.app intGt [.var 0, .dv Srt.int (.int 0)]), some (.app intGt [.var 0, .dv Srt.int (.int 1)]), [], true, true)] :=
  rfl

/-- The rules' heads: `a(X) => b(X)`, `b(X) => c(X)`, `c(X) => d(X)`, X the variable 0. -/
theorem read_sides : c.rules.map (fun r => (r.lhs, r.rhs)) =
    [(.app topLabel [.app kCell [.app kseq [.inj exp Srt.kitem (.app symA [.var 0]), .var 1]], .var 2],
      .app topLabel [.app kCell [.app kseq [.inj exp Srt.kitem (.app symB [.var 0]), .var 1]], .var 2]),
     (.app topLabel [.app kCell [.app kseq [.inj exp Srt.kitem (.app symB [.var 0]), .var 1]], .var 2],
      .app topLabel [.app kCell [.app kseq [.inj exp Srt.kitem (.app symC [.var 0]), .var 1]], .var 2]),
     (.app topLabel [.app kCell [.app kseq [.inj exp Srt.kitem (.app symC [.var 0]), .var 1]], .var 2],
      .app topLabel [.app kCell [.app kseq [.inj exp Srt.kitem (.app symD [.var 0]), .var 1]], .var 2])] :=
  rfl

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hcf : c.clausesFixed = true := by decide +kernel
private theorem hag : c.agreeObligations = [] := by decide +kernel
private theorem hna : c.asideFree = true := by decide +kernel

/-- `<k> f(n) </k>`, the counter at 0. -/
def cfg (f : Sym) (n : Int) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj exp Srt.kitem (.ctor f [.dv Srt.int (.int n)]), .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

def A0 : Config c := ⟨cfg symA 0, by decide +kernel⟩
def A1 : Config c := ⟨cfg symA 1, by decide +kernel⟩
def B0 : Config c := ⟨cfg symB 0, by decide +kernel⟩
def B1 : Config c := ⟨cfg symB 1, by decide +kernel⟩
def C0 : Config c := ⟨cfg symC 0, by decide +kernel⟩
def C1 : Config c := ⟨cfg symC 1, by decide +kernel⟩
def C2 : Config c := ⟨cfg symC 2, by decide +kernel⟩
def D2 : Config c := ⟨cfg symD 2, by decide +kernel⟩

/-- **`requires`, for every interpretation**: `a(1)` steps to `b(1)`, and `a(0)` has no successor:
the premise `X >Int 0 = true` of the left side is false there. -/
theorem req_steps (H : HookParams) :
    Step (c.withHooks H) (cfgH noRaw A1 H) (cfgH noRaw B1 H) ∧ ∀ y, ¬ Step (c.withHooks H) (cfgH noRaw A0 H) y :=
  ⟨step_everyH hok hsr hmr noRaw (n := 50) (by decide +kernel) H,
   stuck_everyH hok hsr hmr noRaw hcf hag hna (n := 50) (by decide +kernel) H⟩

/-- **`ensures`, for every interpretation**: `b(1)` steps to `c(1)`, and `b(0)` has no successor:
the conjunct `X >Int 0 = true` of the right side is false there. -/
theorem ens_steps (H : HookParams) :
    Step (c.withHooks H) (cfgH noRaw B1 H) (cfgH noRaw C1 H) ∧ ∀ y, ¬ Step (c.withHooks H) (cfgH noRaw B0 H) y :=
  ⟨step_everyH hok hsr hmr noRaw (n := 50) (by decide +kernel) H,
   stuck_everyH hok hsr hmr noRaw hcf hag hna (n := 50) (by decide +kernel) H⟩

/-- **`requires` with `ensures`, for every interpretation**: `c(2)` steps to `d(2)`; `c(1)` has no
successor, where the `requires` holds and the `ensures` `X >Int 1` fails; `c(0)` has none, where
the `requires` fails. -/
theorem reqens_steps (H : HookParams) :
    Step (c.withHooks H) (cfgH noRaw C2 H) (cfgH noRaw D2 H) ∧
    (∀ y, ¬ Step (c.withHooks H) (cfgH noRaw C1 H) y) ∧ ∀ y, ¬ Step (c.withHooks H) (cfgH noRaw C0 H) y :=
  ⟨step_everyH hok hsr hmr noRaw (n := 50) (by decide +kernel) H,
   stuck_everyH hok hsr hmr noRaw hcf hag hna (n := 50) (by decide +kernel) H,
   stuck_everyH hok hsr hmr noRaw hcf hag hna (n := 50) (by decide +kernel) H⟩

/-- info: 'ReqensStepH.req_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms req_steps
/-- info: 'ReqensStepH.ens_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ens_steps
/-- info: 'ReqensStepH.reqens_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reqens_steps

end ReqensStepH
