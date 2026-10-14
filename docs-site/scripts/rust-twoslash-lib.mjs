import { spawnSync } from 'node:child_process'

export function runChecked(command, args, options = {}) {
  const result = spawnSync(command, args, {
    encoding: 'utf8',
    ...options,
  })
  if (result.error) throw new Error(`${command}: ${result.error.message}`)
  if (result.status !== 0) {
    const detail = (result.stderr || result.stdout || '').trim()
    throw new Error(`${command} exited with status ${result.status}${detail ? `\n${detail}` : ''}`)
  }
  return result.stdout
}

export function parseTwoslashOutput(stdout, label) {
  let result
  try {
    result = JSON.parse(stdout)
  } catch (error) {
    throw new Error(`${label}: invalid JSON: ${error.message}`)
  }
  if (!result || typeof result !== 'object' || Array.isArray(result))
    throw new Error(`${label}: output must be a JSON object`)
  for (const field of ['code', 'staticQuickInfos', 'queries', 'errors']) {
    if (field === 'code' ? typeof result[field] !== 'string' : !Array.isArray(result[field]))
      throw new Error(`${label}: output has an invalid ${field} field`)
  }
  if (result.errors.length > 0) {
    const diagnostics = result.errors
      .map((error) => error.renderedMessage ?? error.message ?? JSON.stringify(error))
      .join('\n')
    throw new Error(`${label}: rust-analyzer returned diagnostics\n${diagnostics}`)
  }
  return result
}

export function tomlString(value) {
  return JSON.stringify(value)
}

export function materializeManifest(metadata, packageName) {
  const pkg = metadata.packages.find((candidate) => candidate.name === packageName)
  if (!pkg) throw new Error(`cargo metadata did not contain package ${packageName}`)

  const lines = [
    '[package]',
    `name = ${tomlString(pkg.name)}`,
    `version = ${tomlString(pkg.version)}`,
    `edition = ${tomlString(pkg.edition)}`,
    'publish = false',
    '',
    '[lib]',
    'path = "src/lib.rs"',
    '',
    '[dependencies]',
  ]
  for (const dependency of pkg.dependencies.filter((item) => item.kind === null)) {
    const key = dependency.rename ?? dependency.name
    const fields = []
    if (dependency.rename) fields.push(`package = ${tomlString(dependency.name)}`)
    if (dependency.path) fields.push(`path = ${tomlString(dependency.path)}`)
    else if (dependency.source?.startsWith('registry+'))
      fields.push(`version = ${tomlString(dependency.req)}`)
    else throw new Error(`unsupported dependency source for ${key}: ${dependency.source}`)
    if (!dependency.uses_default_features) fields.push('default-features = false')
    if (dependency.features.length > 0)
      fields.push(`features = [${dependency.features.map(tomlString).join(', ')}]`)
    lines.push(`${tomlString(key)} = { ${fields.join(', ')} }`)
  }
  lines.push('', '[workspace]', 'resolver = "3"', '')
  return lines.join('\n')
}
