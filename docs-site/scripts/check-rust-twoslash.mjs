#!/usr/bin/env node
import { copyFileSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

import { materializeManifest, parseTwoslashOutput, runChecked } from './rust-twoslash-lib.mjs'

const siteRoot = resolve(dirname(fileURLToPath(import.meta.url)), '..')
const repoRoot = resolve(siteRoot, '..')
const fixtureManifest = join(repoRoot, 'tests/tour-minimal/Cargo.toml')
const fixtureLock = join(repoRoot, 'tests/tour-minimal/Cargo.lock')
const fixtureSource = join(repoRoot, 'tests/tour-minimal/src/lib.rs')

if (process.argv.includes('--if-enabled') && process.env.KRS_RUST_TWOSLASH !== '1') {
  console.log('Rust Twoslash is disabled; compiler-backed snippet checks remain active')
  process.exit(0)
}

const temporary = mkdtempSync(join(tmpdir(), 'krs-rust-twoslash-'))

try {
  let binary
  try {
    const twoslashRust = await import('@vocs/twoslash-rust')
    binary = twoslashRust.getBinaryPath()
  } catch (error) {
    throw new Error(`could not resolve the Vocs Rust-Twoslash binary: ${error.message}`)
  }

  // The fixture compiler gate is authoritative. Twoslash is additional editor information.
  runChecked('cargo', ['check', '--locked', '--manifest-path', fixtureManifest])

  const metadata = JSON.parse(
    runChecked('cargo', [
      'metadata',
      '--format-version',
      '1',
      '--no-deps',
      '--manifest-path',
      fixtureManifest,
    ]),
  )
  const manifest = materializeManifest(metadata, 'krs-tour-minimal')
  const materializedManifest = join(temporary, 'Cargo.toml')
  mkdirSync(join(temporary, 'src'))
  writeFileSync(materializedManifest, manifest)
  copyFileSync(fixtureLock, join(temporary, 'Cargo.lock'))

  // Vocs receives this exact absolute-path manifest after the preflight succeeds.
  // It is build state, not a checked-in machine-specific source file.
  const vocsManifest = join(siteRoot, '.vocs/twoslash-Cargo.toml')
  mkdirSync(dirname(vocsManifest), { recursive: true })
  writeFileSync(vocsManifest, manifest)

  const source = `${readFileSync(fixtureSource, 'utf8')}\n\n#[allow(dead_code)]\nfn __twoslash_generated_symbol_probe(_: M2Obj) {}\n`
  writeFileSync(join(temporary, 'src/lib.rs'), source)
  runChecked('cargo', [
    'check',
    '--locked',
    '--offline',
    '--manifest-path',
    materializedManifest,
  ])

  const stdout = runChecked(binary, ['--cargo-toml', materializedManifest], {
    input: source,
    timeout: 300_000,
  })
  const result = parseTwoslashOutput(stdout, 'tour-minimal generated-symbol probe')
  if (!result.staticQuickInfos.some((hover) => hover.targetString === 'M2Obj'))
    throw new Error('tour-minimal generated-symbol probe: M2Obj has no rust-analyzer hover')

  console.log('Rust Twoslash gate passed: compiler, protocol, diagnostics, and generated symbols')
} finally {
  rmSync(temporary, { recursive: true, force: true })
}
