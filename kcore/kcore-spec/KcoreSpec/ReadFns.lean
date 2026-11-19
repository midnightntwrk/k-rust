/-
  An import point for the reading functions over `RawEqn` of an equation's right side that holds
  a matching-logic connective. They are Parse.lean's, beside the reader that calls them
  (`clausesBody`): `dropEmptyAlts`, `exRead`, `frRead`, `hoistExists`, and `ceRead` with `orCut`,
  `cutCeils`, `memOf` and `ceilExCond`; `valuedSort` is the test of a value `hoistExists` takes on
  a built definition.
-/
import KcoreSpec.Parse
