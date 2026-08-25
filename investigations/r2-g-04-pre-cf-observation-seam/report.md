# R2-G-04 pre-CF observation seam investigation

Status: pass on 19 August 2026.

Primary classification: `pin-private-seam-needs-hook`.

## Verdict

Pinned K contains the required typed midpoint, but the installed lifecycle
does not expose a composable function there. `DefinitionParsing` converts each
configuration `Bubble` to an official `Configuration` with typed body,
`ensures`, attributes, source/location provenance, and inner production/sort
metadata. In the same private one-argument method it immediately checks cells,
calls `GenerateSentencesFromConfigDecl.gen`, removes the `Configuration`, and
returns generated sentences.

The strongest non-forbidden candidate is protected subclassing. Its
two-argument `resolveConfigBubbles(Definition, Module)` override compiles, but
the input still contains bubbles and `super` returns only after CF generation.
The typed one-argument operation is private; the checked override probe fails
with `method does not override or implement a method from a supertype`.
Diagnostic reflection and `javap` agree on the modifiers. This is not a
reflection-based production route.

Guice cannot open the midpoint in this pin. `KompileFrontEnd` obtains ordinary
frontend/backend services, constructs `Kompile`, and the `Kompile` constructor
directly creates its `private final DefinitionParsing`. No source binding for
`DefinitionParsing` exists. Replacing a provider therefore does not intercept
configuration parsing.

Three complete probe cycles passed: the first established the classification,
the second bound checked evidence, and the third added explicit installed
`Configuration` metadata and construction-bytecode checks. There was no packet
ambiguity requiring a split.

## Pin and source binding

- Activation: `f4dcd7e6684e491195104145555990dd192c5c8a`.
- K: v7.1.337 at `4a46d1231473b599c699160132fd6e76a5c46406`.
- Installed frontend jar:
  `c02efedc7b07e46d20e55543bfb2160c73af3e6a80d71436689656c4b7caf4d2`.
- `DefinitionParsing.java`:
  `cbc98fa208ba1d09d1c5b17b97aa73b0b275df433d85a49bfe56e9e5209773b3`.
- `GenerateSentencesFromConfigDecl.java`:
  `87b1c19f487bf4056b1131d687df9d2d8ec413a4789a84134ebdcea0dde65c57`.
- `Kompile.java`:
  `a63e1a3cd3947af73da253a6808d5e09a6475f1ed55aec36faf06c77465c0c31`.
- `KompileFrontEnd.java`:
  `cea3d4674c74feb18f6572516c4ff8af38399167f73285ef92c4db5f4e324c84`.

The exact installed paths, known pre-existing K-source status
(`M pyk/uv.lock`), replay environment, probe hashes, and bytecode-output
hashes are in `results.json`. `verify.sh` fails closed on a different installed
pin, source revision, jar hash, source hash, or pre-existing task output.

## Pin-local lifecycle map

| order | official symbol | visibility | observed value / composition result |
| ---: | --- | --- | --- |
| 1 | `DefinitionParsing.parseDefinitionAndResolveBubbles` | public | trims the outer definition, then owns both config and non-config resolution |
| 2 | `resolveConfigBubbles(Definition, Module)` | protected | inserts default configuration and `MAP`; input contains config bubbles; output is already post-CF |
| 3 | `resolveConfigBubbles(Definition)` | private | parses config bubbles into official `Configuration` values |
| 4 | `defWithParsedConfigs` | private local | the desired typed midpoint at source lines 489–493 |
| 5 | `checkConfigCells` | private | checks parsed configurations before generation |
| 6 | `GenerateSentencesFromConfigDecl.gen` | public static | consumes body, `ensures`, attributes, and extension module at lines 535–540 |
| 7 | `resolveNonConfigBubbles` | private | parses rules only after generated config sentences exist |
| 8 | `Kompile.run(... Function<Definition,Definition> ...)` | public | invokes its function after step 7 and pre-compilation checks; this is the accepted post-CF adapter position |
| construction | `KompileFrontEnd -> new Kompile -> new DefinitionParsing` | public frontend; private-final field | no `DefinitionParsing` provider is consulted |

The public `gen` method is not itself a lifecycle seam: callers must already
possess the official typed `Configuration` and extension module. Obtaining
those from ordinary input would require copying the private parsing pipeline,
reflective invocation, or source/JSON reconstruction.

## Candidate matrix

| route | identity | typed augmentation | post-CF pairing | verdict / missing API |
| --- | --- | --- | --- | --- |
| `Kompile.run` definition function | proven by accepted replay | too late; `Configuration` removed | yes | rejected; needs pre-gen callback |
| `DefinitionParsing` subclass | protected delegation compiles | typed midpoint private | only with a custom parse route | rejected; needs callback inside private operation |
| Guice/provider override | cannot enter parser construction | no | no | rejected; parser is directly constructed private-final |
| direct public `gen` | not a lifecycle identity route | can generate only if typed input already exists | only after forbidden pipeline copy | rejected; needs typed-input callback, not a new generator |
| post-CF adapter construction | identity proven | cannot request official cell generation | already accepted | rejected; needs earlier paired callback |
| ordinary source regeneration | not typed identity | works and uses official CF | yes | fallback only; not a typed seam |

The complete per-route values, metadata, lifecycle entry, forbidden mechanism,
and smallest missing API are recorded in `candidate-matrix.json` and embedded
in `results.json`.

## Executable probe results

The installed-artifact probe verifies:

- the public outer entry, protected wrapper, private typed operation, public
  generator, `Kompile.run` signature, and private-final parser field from the
  installed development jar;
- a protected identity-delegation subclass compiles and links;
- an augmentation-mode surface check reports no interceptable typed value;
- overriding the private typed operation fails compilation with exit 1 and
  the committed diagnostic; and
- source and installed bytecode observations agree.

Two controls localize the failure:

1. The accepted R2-G-01 post-CF identity replay still passes; P3 returns the
   same official `Definition` reference.
2. The existing ordinary-source observation fixture still lets official CF
   generate `ObservationCell`, its initializer, and cell labels. Runtime is
   `<k> 1`, `<state> 2`, `<observation> 0`; erasing observation equals baseline
   `<k>`/`<state>`.

Thus official typed configuration parsing/generation works, and the accepted
post-CF adapter works. Only external composition at their midpoint is absent.

## Minimum hook

The smallest sufficient hook is an identity-defaulting
`UnaryOperator<Configuration> transformConfiguration`, threaded through the
`DefinitionParsing`/`Kompile` invocation. It should run once per parsed
configuration immediately after bubble conversion and before
`checkConfigCells` and `GenerateSentencesFromConfigDecl.gen`.

The required order is:

```text
default config insertion -> MAP import -> typed config parsing/inference
  -> transformConfiguration -> cell checks -> official CF generation
  -> non-config bubble parsing -> pre-compilation checks
  -> OfficialDefinitionAdapter v1 -> KoreBackend.steps -> backend
```

The host should reject a null result, a non-`Configuration` result, lost
source/location or required inner metadata, and transformer exceptions before
constructing CF output. The default callback is identity. Official K retains
ownership of parsing, cell checks, CF-01 through CF-03, later parsing, checks,
lowering, and execution.

This is a small upstream/internal hook, not project ownership of the CF
algorithm and not a new configuration/observation patch contract.

## Remaining unknowns

- Whether upstream prefers a `UnaryOperator<Configuration>` parameter, an
  internal service object, or a module-aware callback with the same placement.
- The exact validation vocabulary for a future K-authored augmentation result;
  this packet intentionally defines no shared schema.
- Upgrade stability of the internal callback once introduced.
- Conservative observation-rule instrumentation remains untested and must not
  start before the inert-cell hook oracle passes.

## Recommended next packet

Add the minimal pin-local/upstream configuration callback, then replay its
identity mode and one inert `<observation>`-cell augmentation through official
CF, the accepted post-CF adapter, lowering, Haskell compilation, execution, and
repeatability checks. Do not add events, rule instrumentation, matchers, a
shared patch schema, C1, or C2 in that packet.
