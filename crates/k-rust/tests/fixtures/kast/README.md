# KAST fixtures

`terms.json` contains KAST JSON v4 envelopes. The token, application, sequence,
variable, and rewrite terms were reduced from real terms in the pinned
`runtimeverification/k` checkout's pyk profiling data. `KAs` and
`InjectedKLabel` complete the seven-node Java `JsonParser`/`ToJson` schema.

The upstream material is redistributed under the repository's BSD 3-Clause
license; see `../kore/LICENSE.md`.

`kast-data.kast` is the frontend's own textual KAST parser fixture.

`definition.json` is a compact reduction of the K frontend's `imp-outer-json`
regression output. It preserves the compiled-definition envelope, flat module,
import, sentence, production-item, typed-attribute, and nested-term shapes.
It also retains the optional `precedeRegex`/`followRegex` fields of a regex
terminal, with the value `"#"` (no restriction) that most of that artifact's
regex terminals carry; a document that states a restriction is refused (see
`docs/compatibility.md`, "Token precede and follow restrictions").
