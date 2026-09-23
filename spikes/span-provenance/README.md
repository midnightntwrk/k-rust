# Stable proc-macro source-provenance spike

This standalone workspace probes rustc/rust-analyzer 1.97.1 without editing or
depending on the production workspace. It covers an attribute path, refutable
parameter pattern and type, nested body path, function-like payload path,
invocation-local rejection, unavailable stable Span APIs, and three expansion
span-mapping strategies.

Run every gate with:

```sh
python3 tools/verify.py
```

The accepted test turns stable one-based `(line, Unicode-scalar column)`
endpoints back into byte ranges using the exact source snapshot, including a
non-ASCII prefix before the nested path. The rejected fixtures are expected to
fail and are checked through Cargo JSON diagnostics.

Conclusion: stable `proc_macro` exposes enough file and endpoint information to
anchor every probed authored token, but no stable byte-range, span-join, or
expansion-parent API, and raw spans cannot leave the proc-macro process. KRS
therefore snapshots stable line/column anchors at expansion time and derives
content-addressed byte ranges in a separate shared-parser provenance pass.
