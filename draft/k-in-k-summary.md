# K-in-K project summary

## Executive summary

K-in-K is an experimental, partial semantics of the K Framework's frontend,
written in K itself. Its goal is to make the compilation of a K language
definition into Kore explicit as a sequence of K rewrite rules. Kore is the
Matching Logic representation consumed by K's execution and proof backends.
In that sense, K-in-K is analogous to a small “K in K” or compiler
bootstrapping experiment: a K definition treats other K definitions as data and
rewrites their frontend constructs into backend-level declarations and axioms.

The repository is most valuable as a compact example of *metacircular
specification* and of testing a semantics transformation. It is not a complete
reimplementation of the K frontend, a verified compiler, or a suitable base for
a modern K project. Development ran from 2018 to January 2020. Its parser and
build depend on historical K infrastructure, including K-light and K's now
removed OCaml backend, and several major frontend passes were left unfinished.

## What problem it addresses

K lets language designers define syntax, configurations, and rewrite rules.
Those convenient frontend constructs ultimately need a precise interpretation
as Kore/Matching Logic. K-in-K attempts to expose that interpretation as a
formal, executable transformation rather than leaving it implicit in a
conventional compiler implementation.

The intended progression is telescopic:

```text
K frontend
  -> frontend constructs represented as syntax trees
  -> EKore (Kore extended with selected K constructs)
  -> Kore declarations and Matching Logic axioms
  -> execution by a Kore backend
```

“EKore” is the project's bridge language. It extends Kore with K syntax
productions, rules, contexts, configurations, attributes, rewrites,
`requires`, backtick applications, and `#token`. The source defines both
concrete forms for parsing and abstract forms for matching in rewrite rules.
This avoids ambiguities between K's outer syntax and the similar-looking inner
term syntax.

The project is metacircular but not self-contained. K's existing toolchain
first compiles the K-in-K semantics. The resulting interpreter then transforms
an input definition. Parsing is partly delegated to K-light through shell calls,
and generated Kore is executed by K's Haskell backend. It therefore specifies
part of K *using* K without bootstrapping the whole framework from itself.

## Implemented transformation pipeline

The central semantics is in `src/kink.md`; `src/command-line.md` composes its
passes. The EKore-to-Kore pipeline performs these transformations:

1. Parse the input as EKore.
2. Convert frontend definitions, modules, and imports into Kore-shaped data and
   place modules and declarations in configuration cells.
3. Flatten syntax alternatives and precedence groups into one production per
   declaration.
4. Mark productions without `function` as `functional`, `constructor`, and
   `injective`.
5. Derive Kore sort declarations from syntax productions, including searches
   through imported modules to avoid duplicates.
6. Derive Kore symbol declarations from production argument sorts, result
   sorts, `klabel`s, and attributes.
7. Translate rules headed by function symbols into equality axioms; translate
   other supported rules into rewrite axioms.
8. For the `kompile` command, discard residual frontend declarations before
   handing the result to the Haskell backend.

The implementation uses a K configuration as a transformation workspace. Each
module is represented by a `<mod>` cell with name, attributes, declarations,
and collected grammar. Passes repeatedly match and update these cells until no
applicable item remains. Helper functions query imports, declared sorts and
symbols, return sorts, function attributes, and attribute contents.

There are three command-level workflows:

- `ekore-to-kore` runs the lowering pipeline but retains frontend declarations
  that do not yet have a complete Kore translation. This form is also used for
  inspecting and testing intermediate results.
- `kompile` runs the same pipeline and then removes non-Kore declarations,
  producing input suitable for the historical Haskell backend.
- `kast <program>` parses an ordinary outer K definition, extracts its syntax
  productions into a temporary grammar, and parses a program with that grammar.
  This path does not lower the definition's rule bubbles into Kore.

That last limitation is important: the repository has machinery for parsing
ordinary K outer syntax, but the working semantic lowering begins with EKore,
where rule bodies are already expressed as abstract patterns. The planned
frontend stages—parsing bubbles, choosing labels, disambiguation, expanding
`require`, and fully interpreting configurations—were not completed.

## Tests and the fixed-point oracle

The test suite contains three deliberately small languages:

- `foobar`: constants plus a function rule;
- `peano`: natural-number constructors and recursive addition;
- `imp-simple`: a minimal cell-based Boolean language with rewrite rules.

For each language, the Ninja-based build defines four end-to-end checks:

1. transform a handwritten EKore definition and compare it with checked-in
   expected EKore/Kore;
2. run the same pipeline on that expected output and require the output to be
   unchanged;
3. extract the grammar from the ordinary `.k` definition and compare a parsed
   program with expected KAST; and
4. strip frontend declarations, execute the generated Kore with `kore-exec`,
   and compare the final term with the expected result.

The second check is the project's most reusable testing idea. It asserts that
the desugaring pipeline reaches a fixed point:

```text
lower(source) = expected
lower(expected) = expected
```

This catches passes that keep adding duplicate declarations, fail to consume
frontend constructs, or otherwise do not stabilize. It is an executable
metamorphic oracle, not a proof that the translation preserves K's meaning.
Semantic adequacy would additionally require relating source-language behavior
to the generated Matching Logic theory.

## What is incomplete

The repository's own milestones and TODOs identify substantial gaps:

- full parsing and disambiguation of K rule/configuration bubbles;
- expansion of `require` directives and inclusion of standard definitions;
- configuration concretization and context handling;
- translation of `requires` and `ensures` conditions;
- strictness, configuration initialization, and other generated axioms;
- complete functional, constructor, no-junk, and `mu` axioms;
- precedence attributes while flattening productions;
- module topological ordering and import-cycle checks;
- complete well-formedness and useful error reporting.

Some current transformations also accept only narrow syntactic shapes. For
example, rule translation expects an un-attributed rewrite whose left-hand side
is a direct symbol application. The examples demonstrate that this subset can
produce executable Kore, but they do not establish coverage of realistic K
definitions.

There is no stated or mechanized correctness/adequacy theorem connecting the
implemented transformation to the production K frontend. The expected-output,
fixed-point, parser, and execution tests provide useful regression evidence,
but only for the three toy languages.

## Historical implementation and maintenance status

The semantics is written as literate Markdown containing fenced K modules.
Pandoc tangling, a Python/Ninja build (`kninja`), and git submodules assemble a
toolchain consisting of K, K-light, and the Haskell backend. A small Python
launcher invokes `krun`; helper scripts extract serialized definitions or terms
from K configuration cells. CI originally built an Ubuntu 18.04 image with
Java 8, opam, Stack, and the other historical dependencies.

The first repository commit dates to September 2018 and the last commit on the
default branch to 16 January 2020. The checkout pins its dependencies as git
submodules rather than using the current K project conventions. In particular,
the build compiles K-in-K with the OCaml backend, which has since been removed
from K. Reproducing the historical build would require initializing the pinned
submodules and reconstructing that older toolchain; porting it would be a
substantial engineering task rather than a routine dependency update.

The code is released under the University of Illinois/NCSA Open Source License.

## Relationship to modern K projects

K-in-K should be treated as a conceptual and meta-verification reference. It
shows how to represent definitions as terms, express compiler passes as rewrite
rules, execute generated Kore, and test normalization for idempotence. These
ideas are directly relevant to projects that want specifications to test their
own transformations or to study meta-properties of a language definition.

It should not be copied as a current repository template. As of the accompanying
workspace assessment (1 August 2026), the K source tree is at K 7.1.337, while
maintained projects use Python packaging, `kdist`, `pyk`, `uv`, Nix flakes, and
the Haskell backend/booster workflow. The small `imp-semantics` repository is
the better modern skeleton; `wasm-semantics`, `evm-semantics`, and
`mir-semantics` are better examples of maintained real-language semantics; and
`kontrol` is the stronger model for turning K-backed symbolic execution into an
end-user prover product.

For a successor project, the parts worth preserving are the explicit staged
lowering, the separation between concrete and abstract meta-syntax, the
configuration-cell visitor pattern where it remains clear, and especially the
fixed-point oracle. The parser/build integration and backend assumptions should
be redesigned around current K and pyk APIs. Any claim of verification should
also go beyond idempotence by stating and proving an adequacy relation between
source K constructs and generated Kore.

## Sources inspected

- K-in-K: `README.md`, `src/kink.md`, `src/ekore.md`, `src/kore.md`,
  `src/command-line.md`, parser/file utilities, build scripts, git history, and
  all examples under `t/` in
  `/home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/kframework/k-in-k`.
- Modern-project comparison:
  `/home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/runtimeverification/good-k.md`.

