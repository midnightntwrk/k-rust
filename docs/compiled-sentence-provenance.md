# Compiled sentence provenance

`kompile::compile_loaded_definition` returns `CompiledKoreArtifacts::sentence_provenance` alongside `definition_kore` and `execution_definition`.
The map key is the `UNIQUE_ID` that a backend reports for an emitted rule or claim.
The key set covers the rules and claims emitted in `definition_kore` and `macros_kore`.
Rules and claims in execution modules outside the emitted main module's visible catalog have no entry.
Equal-content sentences can have one `UNIQUE_ID`; their input addresses are combined in emission order, with each address listed once.

An `EmittedSentenceProvenance` entry has `input_addresses`, `input_sentence_kinds`, and `generated_by`.
The kind map is keyed by each listed address and records the sentence kind at the input boundary, before loading or compilation can remove or expand it.
`generated_by` is present when no input sentence contributed to the identity; it names the `GeneratingPass` from the origin receipt.
The relation's addresses come only from the compiler's input-address carrier, not from `source`, `location`, or origin-receipt links.

An `InputAddress` has an `input` space, module name, and module-local sentence index.
`InputSpace::Compile` addresses index `LoadedDefinition::definition()` as passed to compilation; text-loaded definitions and values rebuilt with `LoadedDefinition::from_loaded_parts` or `with_definition` use this space (`LoadedDefinition::addressing()` is `InputAddressing::Compile`).
`InputSpace::Structured` addresses index the `Definition` passed to `outer::load_structured`, before configuration expansion; they are kept for that call's unedited result, whose `addressing()` is `InputAddressing::Structured`.
The loaded source table preserves the original kinds of structured sentences that loading removes.
Callers that keep their own source or mutant identifiers should map those identifiers to input addresses and compose that map with `sentence_provenance`.

Frontend `Diagnostic::input_addresses` copies the addresses of the sentence or attributes that raised it, in their existing order.
Diagnostics built from a source location alone have an empty list.
The napi and wasm diagnostic objects expose the same list as `inputAddresses`, with each address represented by `{ input: "structured" | "compile", module: string, index: number }`.

The input-address carrier and origin receipts do not appear in KORE or KAST v4 and do not affect `UNIQUE_ID` digests.

## Origin receipts and their documents

An origin receipt (`OriginRecord`) holds the generating pass, an origin set, and an optional destination anchor.
The origin set's value is the ordered, duplicate-free list `OriginSet::links` returns; equality, ordering and `Debug` of a set are those of that list.
A set is held as an immutable shared node whose parts are links and other sets, and it denotes the first-occurrence union of its parts.
A changed term node's set names at most five parts: its counterpart's prior set, its own prior set, the counterpart's span, its own span, and the set it inherits from the node above it (at a field root, its sentence's set).
Naming a set costs one part however many links it denotes, so recording, holding and writing receipts is linear in the definition.
A sentence's receipt always names a flat set, one whose parts are all links.
`Term::identical`, the reuse test of incremental resolution, compares receipts by allocation: a receipt is identical only to itself.

A destination anchor names a module, a sentence, the sentence's index in its module, and a path: the field of the sentence, then one child index per level.
A child index is a step of `Term::children`, which lists a node's children in one order (a rewrite's left then right side, an alias's pattern then alias, an application's or a sequence's items), annotations taking no step; `Sentence::term_at` resolves a path to the subterm it names.
Its module and sentence names are shared by every receipt of one sentence, and its path shares its parent's path.

`KRUST-PROVENANCE` version 8 writes the definition, its `sources` table, and three tables that receipts and metadata name by index:

- `originSets`: each entry is an array of parts, a link (`{"kind":"source","source":s,"start","end"}` or `{"kind":"sentence","uniqueId"}`) or a reference to an earlier entry (`{"kind":"set","set":j}`).
  An entry is in normal form: it names no entry without parts, repeats no part, and is not a single reference; no two entries are equal.
- `anchors`: each entry is a root (`{"module","sentence","sentenceIndex"}`, the empty path) or a step (`{"parent":k,"step":t}`, entry `k`'s path extended by `t`, with `k` earlier).
- `termMetadata`: each entry addresses a node by `moduleIndex`, `sentenceIndex`, `field` and `node`, the node's index in the preorder walk of the field (annotations are not nodes; children in order), in strictly increasing address order.

Every source reference, in a span, a link or the `org.krust.provenance.SourceId` attribute, is an index into `sources`.
A receipt is `{"pass","origins":i,"destination":a|null}`.

The bytes of a document are a function of the definition and of each receipt's pass, destination and normal form, where the normal form of a set is its unfolding (every named set replaced by its own parts, whatever is shared) with the normal-form rules applied entry by entry.
They do not depend on which sets or paths share memory, so decoding a document and writing it again gives the same bytes, and a compilation of a decoded definition writes the same documents as a compilation of the source.
They are not a function of the link lists alone: two sets with equal lists can be written as different entries.
The reader reads `format` and `version` first, skipping every other member, so it refuses every other version by its version whatever the shape of that version's body; it also refuses any version 8 document that breaks the table rules above.
