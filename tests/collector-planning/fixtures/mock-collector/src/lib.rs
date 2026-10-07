//! Mock for the Wave 1A collector entry point.

use std::io::{self, Write};

/// Write one deterministic protocol record to the supplied stdout handle.
pub fn collect(
    output: &mut dyn Write,
    selected_facets: &[(&str, &str)],
) -> io::Result<()> {
    writeln!(
        output,
        "{{\"protocol\":2,\"selected_facets\":{}}}",
        selected_facets.len()
    )
}

