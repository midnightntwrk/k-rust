# Sort injection fixtures

`arguments` records K v7.1.337 `kast --output kore` for a constructor with a declared subsort argument and an argument already at the required sort.
The Rust test calls `SortInjector` directly and compares the resulting KORE structurally with these committed artifacts.
`arguments/reference.toml` records commands, pins, and digests; no reference installation is needed to run the test.
