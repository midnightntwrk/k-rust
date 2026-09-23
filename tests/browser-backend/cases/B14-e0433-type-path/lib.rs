// IR-15 finding 1: an unresolved module in a type path. The native twin
// reports E0433; rustc.wasm (195111dff) traps with no diagnostic.
pub fn f(_: missing::T) {}
