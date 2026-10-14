#!/usr/bin/env node
import { readFileSync, writeFileSync } from 'node:fs'
import { dirname, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

const siteRoot = resolve(dirname(fileURLToPath(import.meta.url)), '..')
const snippets = [
  { source: '../tests/tour-minimal/src/lib.rs', mirror: 'src/snippets/tour-minimal.rs' },
  { source: '../tests/tour-minimal/Cargo.toml', mirror: 'src/snippets/tour-minimal.Cargo.toml' },
  {
    source: '../tests/tour-imp/chapters/01-sorts.rs',
    mirror: 'src/snippets/imp-sorts.rs',
  },
  {
    source: '../tests/tour-imp/chapters/02-concrete-grammar.rs',
    mirror: 'src/snippets/imp-grammar.rs',
  },
  {
    source: '../tests/tour-imp/chapters/04-configuration-and-state.rs',
    mirror: 'src/snippets/imp-state.rs',
  },
  {
    source: '../tests/tour-imp/chapters/03-evaluation.rs',
    mirror: 'src/snippets/imp-evaluation.rs',
  },
  {
    source: '../tests/tour-imp/chapters/05-control-flow.rs',
    mirror: 'src/snippets/imp-control.rs',
  },
  {
    source: '../tests/tour-imp/chapters/06-machine-rules.rs',
    mirror: 'src/snippets/imp-machine-rules.rs',
  },
  {
    source: '../tests/tour-imp/src/lib.rs',
    mirror: 'src/snippets/tour-imp-capstone.rs',
  },
  {
    source: '../tests/tour-imp/generated/eval-add-readable.txt',
    mirror: 'src/snippets/eval-add-readable.rs',
  },
  {
    source: '../tests/tour-imp/generated/eval-add-expanded.txt',
    mirror: 'src/snippets/eval-add-expanded.rs',
  },
  {
    source: '../tests/tour-imp/generated/eval-add-descriptor.json',
    mirror: 'src/snippets/eval-add-descriptor.json',
  },
  {
    source: '../tests/tour-imp/generated/eval-add.k',
    mirror: 'src/snippets/eval-add.k',
  },
  {
    source: '../tests/imp/rust-definition/src/static_adjunct.rs',
    mirror: 'src/snippets/static-semantics.rs',
  },
  {
    source: '../tests/imp/rust-definition/src/verification.rs',
    mirror: 'src/snippets/simplifications.rs',
  },
  {
    source: '../tests/imp/rust-definition/src/claims.rs',
    mirror: 'src/snippets/claim-branching.rs',
    start: '#[k::claim(all_paths, label = "branching")]',
    end: '#[k::claim(all_paths, label = "branching-program")]',
  },
  {
    source: '../tests/imp/rust-definition/src/claims.rs',
    mirror: 'src/snippets/claim-circular.rs',
    start: '#[k::claim(all_paths, label = "sum-spec", circularity)]',
    end: '#[k::claim(all_paths, label = "two-sum-spec", circularity)]',
  },
  {
    source: '../crates/krs-macros/tests/fixtures/positive/src/main.rs',
    mirror: 'src/snippets/guarded-transition.rs',
    start: '#[language_host::rule]\n#[language_host::requires(language_host::builtin::int::gt(value, 0))]',
    end: '#[language_host::rule(label = "state-var")]',
  },
  {
    source: '../crates/krs-macros/tests/fixtures/positive/src/main.rs',
    mirror: 'src/snippets/typed-hook.rs',
    start: '#[language_host::function(\n    total,\n    sort = language_host::builtin::Bytes,\n    syntax = "Keccak256raw({value})"',
    end: '#[language_host::function(\n    total,\n    sort = language_host::builtin::Bytes,\n    syntax = "Sha256raw({value})"',
  },
  {
    source: '../tests/grammar-lexing/packages/tokens/src/lib.rs',
    mirror: 'src/snippets/token.rs',
    start: 'k::sorts! {',
    end: '/// Double-quoted text',
  },
  {
    source: '../tests/grammar-lexing/packages/layout/src/lib.rs',
    mirror: 'src/snippets/layout.rs',
    start: 'k::lexical! {',
    end: '#[k::constructors',
  },
  {
    source: '../tests/grammar-lexing/packages/lists/src/lib.rs',
    mirror: 'src/snippets/lists.rs',
    start: '/// A comma-separated list of integers',
    end: '#[k::function(partial, sort = Int, syntax = "count',
  },
  {
    source: '../tests/grammar-lexing/packages/strict-lists/src/lib.rs',
    mirror: 'src/snippets/strict-lists.rs',
    start: 'k::sorts! {',
    end: '/// Reads a list of digits',
  },
  {
    source: '../semantics/kevm/src/lib.rs',
    mirror: 'src/snippets/kevm-accounts.rs',
    start: '#[k::cell]\npub struct Account {',
    end: '#[k::configuration]',
  },
  {
    source: '../tests/tour-composition/packages/base-semantics/Cargo.toml',
    mirror: 'src/snippets/composition-base.Cargo.toml',
  },
  {
    source: '../tests/tour-composition/packages/root-semantics/Cargo.toml',
    mirror: 'src/snippets/composition-root.Cargo.toml',
  },
  {
    source: '../tests/tour-composition/packages/root-semantics/src/lib.rs',
    mirror: 'src/snippets/composition-rule.rs',
    start: '#[k::rule]\npub fn cross_package(',
    end: '#[must_use]',
  },
  {
    source: '../tests/tour-composition/packages/root-semantics/src/lib.rs',
    mirror: 'src/snippets/composition-symbol.rs',
    start: '#[k::symbol("tour::RootCommon")]',
    end: '#[k::constructor(sort = Expr, syntax = "pair({first},{second})")]',
  },
  {
    source: '../tests/tour-negatives/src/lib.rs',
    mirror: 'src/snippets/overlapping-rules.rs',
    start: 'k::rules! {',
  },
]

for (const snippet of snippets) {
  const sourcePath = resolve(siteRoot, snippet.source)
  const mirrorPath = resolve(siteRoot, snippet.mirror)
  const completeSource = readFileSync(sourcePath, 'utf8')
  const start = snippet.start ? completeSource.indexOf(snippet.start) : 0
  if (start < 0) throw new Error(`${snippet.source}: missing start anchor ${snippet.start}`)
  const end = snippet.end ? completeSource.indexOf(snippet.end, start) : completeSource.length
  if (end < 0) throw new Error(`${snippet.source}: missing end anchor ${snippet.end}`)
  const source = completeSource.slice(start, end).trimEnd().concat('\n')
  if (process.argv.includes('--write')) {
    writeFileSync(mirrorPath, source)
    console.log(`updated ${mirrorPath}`)
  } else if (readFileSync(mirrorPath, 'utf8') !== source) {
    throw new Error(`${snippet.mirror} is stale; run \`node scripts/sync-snippets.mjs --write\``)
  } else {
    console.log(`${snippet.mirror} is current`)
  }
}
