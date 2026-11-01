import Lake
open Lake DSL

/-- The parameterized two-layer prototype (the fixture `twoparam`) under its outputs' invariant
`valsOk` alone, without the script's well-formedness: the races of two tasks for one creation, one
segment or one spend remain, and programs `valsOk` admits refute them, run at an instance of the
segments (`TwoParamOkConf.seg`). Its own project: the library `twoparamok`, generated with
`--invariant valsOk@T`, has the module names of `twoparam`. -/
package «TwoParamOkConf» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require k2lean from "../../lean"
require «TwoParam» from "../../generated/twoparamok"

@[default_target]
lean_lib TwoParamOkConf
