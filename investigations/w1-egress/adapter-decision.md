# W1-A candidate adapter decision

## Decision

Use the hidden official-K `--post-process` hook only as the bounded temporary
egress demonstrated by this packet. It accepts KAST v4 after all 32 Kore
frontend passes, returns JSON KAST to official K, and then reaches official
Kore emission, Haskell compilation, and execution. It is adequate for identity
and carefully feature-isolated edits to already-concretized sentences. It is
not the production R2-G transformation boundary.

The next preferred adapter is an in-process official-K driver that exposes the
`Definition` returned by `parseDefinitionAndResolveBubbles`, applies the typed
transformation in memory, and then invokes `KoreBackend.steps()`. That is a new
shared adapter packet; W1-A did not implement it. This boundary would trust
official parsing/disambiguation and CF-01 through CF-03 while leaving the
meaning-bearing lowering passes to run after transformation.

## Trust boundary of the demonstrated route

Trusted before transformation:

- outer and inner parsing, disambiguation, and sort inference;
- default/user configuration parsing and all CF-01/CF-02/CF-03 generation;
- every selected Kore frontend pass, including function-with-configuration,
  contexts, strictness, cell concretization, and both sentence-numbering
  passes; and
- pre- and post-compilation checks performed before `--post-process`.

Trusted after transformation:

- `JsonParser` acceptance of returned KAST v4;
- official `ModuleToKORE`, Haskell backend compilation, program parsing, and
  execution.

The adapter must therefore preserve the invariants of fully compiled KAST.
No official lowering or validation pass repairs a returned transformation.

## Limitations

- `--post-process` is a hidden option, not a stable public compatibility API.
- It is too late for observation-cell augmentation, strictness/context edits,
  function signature changes, or edits requiring cell concretization.
- `ToJson` omits inner-term attributes. This is sufficient for the tested
  post-pipeline emission, but emitted `parsed.json` cannot be replayed through
  pre-compilation checks or frontend passes.
- JSON parsing reifies Scala sets and changes array order. The checked
  normalization policy intentionally does not hide this, so full
  `compiled.json` identity is not claimed. Final Kore and the explicit
  sentence identity/provenance projection are the structural oracle.
- `UNIQUE_ID` survives a post-process body edit unchanged because numbering
  already ran. It is an identity token here, not a post-edit body fingerprint.

## Fallback

For an immediate configuration/observation edit, regenerate ordinary K source
and let official K own configuration generation. The source fixture in this
packet proves that official K deterministically generates and executes an
added `<observation>` cell, but there is no available canonical definition
emitter from typed KAST, so this is not yet a typed G1 egress.

Do not reconstruct CF output, missing inner-term attributes, or independent
Kore in this adapter. Those are separate packets or a D1 scope decision.
