import { rmSync } from 'node:fs'

for (const filename of ['package.json', 'README.md', 'LICENSE', '.gitignore']) {
  rmSync(new URL(`../generated/${filename}`, import.meta.url), { force: true })
}
