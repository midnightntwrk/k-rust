import { mkdtempSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'

import { defineConfig, Twoslash } from 'vocs/config'

const rustTwoslashEnabled = process.env.KRS_RUST_TWOSLASH === '1'

export default defineConfig({
  title: 'k-rust and KRS',
  titleTemplate: '%s – k-rust and KRS',
  description: 'k-rust, a Rust implementation of the K Framework, and KRS, a Rust-shaped language for K semantics.',
  checkDeadlinks: true,
  sidebar: [
    {
      text: 'Start here',
      collapsed: false,
      items: [
        { text: 'What KRS defines', link: '/start/what-krs-defines' },
        { text: 'Definition package', link: '/start/definition-package' },
      ],
    },
    {
      text: 'Build IMP',
      collapsed: false,
      items: [
        { text: 'Sorts and values', link: '/imp/sorts-and-values' },
        { text: 'Concrete grammar', link: '/imp/concrete-grammar' },
        { text: 'Evaluation', link: '/imp/evaluation' },
        { text: 'Configuration and state', link: '/imp/configuration-and-state' },
        { text: 'Machine rules', link: '/imp/machine-rules' },
        { text: 'Control flow', link: '/imp/control-flow' },
      ],
    },
    {
      text: 'Understand the semantics',
      collapsed: false,
      items: [
        { text: 'Applicability and failure', link: '/semantics/applicability-and-failure' },
        { text: 'Inspect the lowering', link: '/semantics/lowering' },
        { text: 'Static semantics', link: '/semantics/static-semantics' },
      ],
    },
    {
      text: 'Verify semantics',
      collapsed: false,
      items: [
        { text: 'Reachability claims', link: '/verification/reachability-claims' },
      ],
    },
    {
      text: 'Scale and compose',
      collapsed: false,
      items: [
        { text: 'Language-scale state', link: '/advanced/language-scale' },
        { text: 'Compose definitions', link: '/advanced/composition' },
      ],
    },
    {
      text: 'Reference',
      collapsed: false,
      items: [
        { text: 'Daily workflow', link: '/reference/workflow' },
        { text: 'Language surface', link: '/reference/language' },
        { text: 'Boundaries and open questions', link: '/reference/boundaries' },
      ],
    },
    {
      text: 'Synthesis',
      collapsed: false,
      items: [{ text: 'Five-minute theory', link: '/start/five-minute-theory' }],
    },
    {
      text: 'Try it',
      collapsed: false,
      items: [{ text: 'Compile in the browser', link: '/lessons/tour-minimal' }],
    },
    {
      text: 'k-rust',
      collapsed: false,
      items: [
        { text: 'Overview', link: '/k-rust' },
        { text: 'Compatibility contract', link: '/k-rust/compatibility' },
      ],
    },
  ],
  twoslash: rustTwoslashEnabled
    ? {
        transformers: [
          Twoslash.experimental_rust({
            cargoToml: './.vocs/twoslash-Cargo.toml',
            // The upstream cache key omits the manifest and toolchain. A fresh directory
            // prevents a stale success from bypassing the fail-closed preflight gate.
            cacheDir: mkdtempSync(join(tmpdir(), 'krs-vocs-rust-twoslash-')),
            throws: true,
            verbose: true,
          }),
        ],
      }
    : undefined,
})
