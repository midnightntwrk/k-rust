import KRustBridge

/-!
`lake exe krust-bridge`: the model conformance bridge that
`crates/k-rust-backend/src/tests/lean_bridge/driver.rs` runs. It reads one JSON request per
standard-input line, `{"id": n, "model": m, "input": x}`, and prints one answer line per request
in input order (`KRust.Bridge.answer`). It reads to end of input, so a caller sends a whole batch
through one process.
-/

open KRust.Bridge

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  unless line.all Char.isWhitespace do
    stdout.putStrLn (answer line).compress
  loop stdin stdout

def main : IO Unit := do
  let stdout ← IO.getStdout
  loop (← IO.getStdin) stdout
  stdout.flush
