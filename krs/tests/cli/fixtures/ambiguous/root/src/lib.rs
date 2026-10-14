//! Root used to place two same-named packages in one resolved Cargo graph.

pub fn retain_dependencies() {
    duplicate_a::retain();
    duplicate_b::retain();
}

