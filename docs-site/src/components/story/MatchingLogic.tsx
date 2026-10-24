'use client'

import { Stage, usePlayer } from './player'
import visual from './SpecificationTools.module.css'

const specifications = [
  { name: 'Rust MIR', short: 'MIR', project: 'KMIR', href: 'https://github.com/runtimeverification/mir-semantics',
    caption: 'Rust’s MIR is the compiler’s intermediate representation. KMIR specifies its execution using the same patterns-and-rules approach as our addition example.' },
  { name: 'WebAssembly', short: 'Wasm', project: 'KWasm', href: 'https://github.com/runtimeverification/wasm-semantics',
    caption: 'KWasm specifies WebAssembly: instructions, values, memory, and execution rules. Matching logic lets a virtual machine’s behavior be written down as one executable specification.' },
  { name: 'Ethereum VM', short: 'EVM', project: 'KEVM', href: 'https://github.com/runtimeverification/evm-semantics',
    caption: 'KEVM specifies the Ethereum Virtual Machine. The same foundation handles its stack, storage, gas, and instruction rules. Open any specification to explore its source.' },
]

const captions = [
  'The same foundation scales from two rules for addition to specifications of real languages and virtual machines. Each language links to its K specification.',
  ...specifications.map((specification) => specification.caption),
]

export function MatchingLogic() {
  const player = usePlayer(captions.length, 4000)
  return (
    <Stage player={player} caption={captions[player.at]}>
      <div className={visual.specificationTree}>
        <strong className={visual.root}>Matching logic</strong>
        <svg className={visual.connectors} viewBox="0 0 600 50" preserveAspectRatio="none" aria-hidden="true">
          <path d="M300 0V18H100V50 M300 18V50 M300 18H500V50" />
        </svg>
        <div className={visual.specifications}>
          {specifications.map((specification, index) => (
            <a key={specification.project} href={specification.href} target="_blank" rel="noreferrer" className={visual.specification} data-active={player.at === index + 1}>
              <span className={visual.specificationSymbol}>{specification.short}</span>
              <strong>{specification.name}</strong>
              <span>{specification.project} on GitHub ↗</span>
            </a>
          ))}
        </div>
      </div>
    </Stage>
  )
}
