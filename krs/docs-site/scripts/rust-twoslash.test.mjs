import assert from 'node:assert/strict'
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { test } from 'node:test'
import { tmpdir } from 'node:os'
import { join } from 'node:path'

import { materializeManifest, parseTwoslashOutput, runChecked } from './rust-twoslash-lib.mjs'

const valid = JSON.stringify({ code: 'fn main() {}', staticQuickInfos: [], queries: [], errors: [] })

test('accepts a complete diagnostic-free protocol result', () => {
  assert.equal(parseTwoslashOutput(valid, 'example').code, 'fn main() {}')
})

test('rejects invalid output', () => {
  assert.throws(() => parseTwoslashOutput('not JSON', 'example'), /invalid JSON/)
  assert.throws(() => parseTwoslashOutput('{}', 'example'), /invalid code field/)
})

test('rejects analyzer diagnostics', () => {
  const output = JSON.stringify({
    code: 'broken',
    staticQuickInfos: [],
    queries: [],
    errors: [{ renderedMessage: 'cannot find value `broken`' }],
  })
  assert.throws(() => parseTwoslashOutput(output, 'negative control'), /cannot find value/)
})

test('rejects missing tools and nonzero subprocesses', () => {
  assert.throws(() => runChecked('/definitely/missing/twoslash-rust', []), /ENOENT/)
  assert.throws(
    () => runChecked(process.execPath, ['--eval', 'process.exit(7)']),
    /status 7/,
  )
})

test('compiler negative control rejects an erroneous Rust source', () => {
  const directory = mkdtempSync(join(tmpdir(), 'krs-docs-negative-control-'))
  try {
    mkdirSync(join(directory, 'src'))
    writeFileSync(
      join(directory, 'Cargo.toml'),
      '[package]\nname = "negative-control"\nversion = "0.0.0"\nedition = "2024"\n\n[workspace]\n',
    )
    writeFileSync(join(directory, 'src/lib.rs'), 'fn broken() { missing_symbol(); }\n')
    assert.throws(
      () => runChecked('cargo', ['check', '--manifest-path', join(directory, 'Cargo.toml')]),
      /status 101/,
    )
  } finally {
    rmSync(directory, { recursive: true, force: true })
  }
})

test('materializes relative path dependencies as absolute paths', () => {
  const manifest = materializeManifest(
    {
      packages: [
        {
          name: 'tour',
          version: '0.0.0',
          edition: '2024',
          dependencies: [
            {
              name: 'krs',
              rename: 'k',
              kind: null,
              path: '/checkout/crates/krs',
              source: null,
              req: '*',
              uses_default_features: true,
              features: [],
            },
          ],
        },
      ],
    },
    'tour',
  )
  assert.match(manifest, /"k" = \{ package = "krs", path = "\/checkout\/crates\/krs" \}/)
})
