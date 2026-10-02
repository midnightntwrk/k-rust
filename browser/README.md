# Browser lesson

`browser/` holds the in-browser KRS compiler for lessons and its release tooling:

- `worker/` is the compiler pipeline in a module worker (`src/`) and its tests (`test/`, `scripts/`);
- `pack/` builds the dependency pack with the native twin of the wasip1-hosted rustc fork;
- `release/` assembles, serves, and fetches content-addressed releases (`release.py`) and runs the local site (`serve-local.py`).

The backend compatibility suite lives in `tests/browser-backend/`, and the regression runner over one pack in `tests/browser-pack/`.

## Test harness

Every browser test drives its browsers and serves its pages through `worker/test/harness/`:

- `browsers.ts` is the one driver.
  `launch` starts headless Chromium under ChromeDriver (WebDriver classic, or WebDriver BiDi when `bidi` is set) or headless Firefox over WebDriver BiDi, with a fresh profile under the scratch root and a process-tree memory sampler.
  `openSite` serves a site directory, launches a browser on it, and waits until the page reports ready.
- `server.ts` is the static server (Bun.serve, `cache-control: no-store`, request log).
- `site.ts` builds a static site from browser bundles, copied files, and links.
- `memory.ts` samples the browser process tree through `/proc`.
- `environment.ts` resolves the scratch root, the checkout, and the Firefox binary, and waits while the load average is high.

Two servers stay outside the harness on purpose.
The cache test (`worker/test/cache/run.ts`) keeps a `node:http` asset host, because its truncated-transfer fault must send a `Content-Length` header and close the connection mid-body, which Bun.serve does not allow.
Tests that exercise the release host run `release/release.py serve`, which applies `release/hosting.toml`; `serve-local.py` runs that same host.

The worker's JSON-over-linear-memory calls (`worker/src/modules.ts`) stay separate from the Node parity runner's `crates/krs-wasm-abi/abi.mjs`: the worker must bundle for the browser without `node:fs`, and any edit under `crates/` changes the crates tree that every pack and oracle is pinned to.

## Runner convention

A runner is one file, run directly: `bun <file>.ts` for TypeScript and `python3 <file>.py` for Python gates.
It takes its inputs and output directories as options, writes its evidence under `--out`, and exits nonzero when a check fails.
Every default location derives from the scratch root, `KRS_GATE_SCRATCH` (default `/var/tmp`), as for the other gates; `tests/browser-pack/run.py` passes explicit locations under its `--out` to every step.
The staging script finds its two Wasm modules under `krs-<checkout>-<key>/browser-pack-target/<pkg>/wasm32-unknown-unknown/release/` within that scratch root, matching the browser pack runner's default Cargo targets.
`KRS_STAGE_POLICY` and `KRS_STAGE_EXPANDER` override the module paths.
Heavy runners wait while the 1-minute load average exceeds `--load-max` (default 40).
`worker/package.json` defines only the two checks that need no pack: `bun run test` (unit tests) and `bun run typecheck` (the worker and the backend suite page); CI runs both.

```toml
# Runners, from the directory given in `cwd`.

[[runner]]
cwd = "browser/worker"
run = "bun test test/unit"
what = "unit tests over recorded fixtures; the Wasm-module tests read KRS_BROWSER_ASSETS (default SCRATCH/krs-browser-assets) and skip without it"

[[runner]]
cwd = "browser/worker"
run = "bun scripts/stage-assets.ts --pack PACK --out DIR"
what = "stage a pack and the policy and expander modules as worker assets"

[[runner]]
cwd = "browser/worker"
run = "bun test/verify.ts --oracle FILE"
what = "worker gate: unit tests, pipeline under Bun and Node, controller, and the scenario plan in Chromium and Firefox (test/browser/run-browser.ts); FILE is the native collector stdout bundle"

[[runner]]
cwd = "browser/worker"
run = "bun test/parity/tour-minimal.ts"
what = "tour-minimal bundle parity with the native oracle (test/parity/regenerate-oracle.sh)"

[[runner]]
cwd = "browser/worker"
run = "bun test/parity/diagnostics.ts"
what = "diagnostic parity with the native baseline (test/parity/native-diagnostics.sh)"

[[runner]]
cwd = "browser/worker"
run = "bun test/cache/run.ts --staged DIR --oracle ORACLE_TOML"
what = "release cache and corruption tests"

[[runner]]
cwd = "browser/worker"
run = "bun test/lesson/docs-lesson.ts --site DOCS_SITE --assets PUBLISH --out DIR"
what = "the built docs site's lesson page through its own controls (docs-site/README.md)"

[[runner]]
cwd = "."
run = "python3 tests/browser-backend/verify.py --host all"
what = "backend compatibility suite in Node WASI, Chromium, and Firefox"

[[runner]]
cwd = "."
run = "python3 tests/browser-pack/run.py --pack PACK --fork-build FORK_BUILD --fork-source FORK_SOURCE --out DIR"
what = "every browser gate above, in order, against one pack (the release regression run)"
```

A successful scenario must produce the native oracle bundle byte for byte, so no runner pins a bundle digest.
`test/run-pipeline.ts`, `test/run-controller.ts`, `test/browser/run-browser.ts`, and `test/verify.ts` take that bundle as `--oracle FILE` (default `SCRATCH/krs-browser-parity/oracle/native/collector-stdout.json`, written by `test/parity/regenerate-oracle.sh`), and a missing file is an error.
`tests/browser-pack/run.py` regenerates the oracle before the pipeline step and passes its own.

Each browser runner listens on fixed local ports, and its driver takes the next port:

```toml
[ports]
"test/browser/run-browser.ts" = "4315 (Chromium), 4325 (Firefox)"
"test/parity/tour-minimal.ts" = "4335, +2 per session"
"test/parity/diagnostics.ts" = "4355, +2 per browser"
"test/cache/run.ts" = "4371 (Chromium), 4381 (Firefox), asset host 4391"
"tests/browser-backend/runner/browser.ts" = "4616 (Chromium), 4626 (Firefox)"
"test/lesson/docs-lesson.ts" = "5310 and 5310 + 1, 50, 60, 70"
"tests/browser-pack/run.py fetch" = "8741"
```

Runs from two checkouts at once therefore collide on ports even though their outputs do not; serialize them.
