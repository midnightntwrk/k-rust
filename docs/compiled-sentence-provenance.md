# Compiled sentence provenance

`kompile::compile_loaded_definition` returns `CompiledKoreArtifacts::sentence_provenance` alongside `definition_kore` and `execution_definition`.
The map key is the `UNIQUE_ID` that a backend reports for an emitted rule or claim.
Every rule and claim in `execution_definition` contributes an entry.
Equal-content sentences can have one `UNIQUE_ID`; their input addresses are combined in execution-definition module order and local sentence order, with each address listed once.

An `EmittedSentenceProvenance` entry has `input_addresses`, `input_sentence_kinds`, and `generated_by`.
The kind map is keyed by each listed address and records the sentence kind at the input boundary, before loading or compilation can remove or expand it.
`generated_by` is present when no input sentence contributed to the identity; it names the `GeneratingPass` from the origin receipt.
The relation's addresses come only from the compiler's input-address carrier, not from `source`, `location`, or origin-receipt links.

An `InputAddress` has an `input` space, module name, and module-local sentence index.
`InputSpace::Compile` addresses index `LoadedDefinition::definition` as passed to compilation; text-loaded definitions use this space.
`InputSpace::Structured` addresses index the `Definition` passed to `outer::load_structured`, before configuration expansion.
The loaded source table preserves the original kinds of structured sentences that loading removes.
Callers that keep their own source or mutant identifiers should map those identifiers to input addresses and compose that map with `sentence_provenance`.

Frontend `Diagnostic::input_addresses` copies the addresses of the sentence or attributes that raised it, in their existing order.
Diagnostics built from a source location alone have an empty list.
The napi and wasm diagnostic objects expose the same list as `inputAddresses`, with each address represented by `{ input: "structured" | "compile", module: string, index: number }`.

The input-address carrier and origin receipts do not appear in KORE or KAST v4 and do not affect `UNIQUE_ID` digests.
