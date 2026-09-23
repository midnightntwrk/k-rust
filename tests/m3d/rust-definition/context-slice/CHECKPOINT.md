# M3D context-alias slice checkpoint

This fixture is the executable vertical gate for one source-level context
alias selected by one named `seqstrict` production. It deliberately copies the
frozen M3C definition byte-for-byte and adds only `m3d_eval` and `M3dTwice`.

The executable asserts registration-order determinism through descriptor,
semantic, Definition, and emitted-K artifacts; exact authored/generated source
ranges and native origin roles; one pre-expansion native context alias with no
KRS-generated contexts or heat/cool rules; and successful public native
preparation, strictness resolution, context resolution, and KORE compilation.
It also rejects a dangling `using` identity, an unknown selected field, and
mismatched or lost K-tail/configuration-remainder bindings through mutations
of the collected stable descriptor bundle.

The focused parser suite additionally rejects missing, duplicate, or
structural HERE selections and any return-valued or nonempty post-state body.
Existing grammar parser tests retain empty, duplicate, qualified, and unknown
strictness-field coverage.

Run the focused Rust gates with:

```bash
CARGO_TARGET_DIR=/dev/shm/krs-m3d-target cargo test --locked -p krs-syntax --test fixed_state
CARGO_TARGET_DIR=/dev/shm/krs-m3d-target cargo test --locked -p krs-ir --test protocol_v7 --test fixed_state_ir
CARGO_TARGET_DIR=/dev/shm/krs-m3d-target cargo test --locked -p krs-compiler --test fixed_state_lowering
```

Run the permanent public native gate with:

```bash
CARGO_TARGET_DIR=/dev/shm/krs-m3d-target cargo run --locked --manifest-path tests/m3d/rust-definition/context-slice/Cargo.toml
```

Do not advance simplification or claims from this checkpoint. Same-name
multi-declaration context-alias groups and non-default named-alias result
semantics remain follow-on work. The fixture does not pin generated freezer
names and KRS does not generate source-level heat/cool/freezer sentences.
