import KPrio.Equations

/-! The row route alone (`k2l_eqn_row`, `k2l_eqn_rows_o`): equations of kprio's generated library
proved again by their own rows only, without the other proofs of the generated `first`, which
`prio`'s tables are small enough to close as well. Each statement is the generated theorem's
(`type_of%`), so it cannot drift from it; a binder's name is the generated one, which the
no-match premises are cited by. One equation per shape:

* `dec_1`: a bit-pattern row, the first;
* `dec_2`: a literal row inside the family of the first, which its `requires` excludes;
* `dec_3`: the default row (`owise`), after both rows excluded by its no-match premises;
* `field_3`: a bit-pattern row after a bit-pattern row and a literal row of its priority. -/

set_option maxHeartbeats 100000

open KPrio KPrelude

namespace KPrioClaims.Rows

example : type_of% @KPrio.Eqn.«dec(_)_PRIO_Instr_Int_1» := by
  intros
  k2l_eqn_row K.«dec(_)_PRIO_Instr_Int» [K.«dec(_)_PRIO_Instr_Int», K.«dec(_)_PRIO_Instr_Int».rule1]

example : type_of% @KPrio.Eqn.«dec(_)_PRIO_Instr_Int_2» := by
  k2l_eqn_row K.«dec(_)_PRIO_Instr_Int» [K.«dec(_)_PRIO_Instr_Int», K.«dec(_)_PRIO_Instr_Int».rule1, K.«dec(_)_PRIO_Instr_Int».rule2]

example : type_of% @KPrio.Eqn.«dec(_)_PRIO_Instr_Int_3» := by
  intro Gen0 howise0 howise1
  k2l_eqn_rows_o K.«dec(_)_PRIO_Instr_Int» [(howise0, K.«dec(_)_PRIO_Instr_Int».rule1), (howise1, K.«dec(_)_PRIO_Instr_Int».rule2)] [K.«dec(_)_PRIO_Instr_Int».rule3]

example : type_of% @KPrio.Eqn.«field(_)_PRIO_Int_Int_3» := by
  intros
  k2l_eqn_row K.«field(_)_PRIO_Int_Int» [K.«field(_)_PRIO_Int_Int», K.«field(_)_PRIO_Int_Int».rule1, K.«field(_)_PRIO_Int_Int».rule2, K.«field(_)_PRIO_Int_Int».rule3]

end KPrioClaims.Rows
