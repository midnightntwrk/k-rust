//! Wasm exports of the expander module (`krs_wasm_abi`).

use crate::protocol::{lookup_json, protocol_error_json, run_json};

fn unallocated() -> Vec<u8> {
    protocol_error_json(krs_wasm_abi::UNALLOCATED)
}

krs_wasm_abi::export! {
    alloc: krs_expand_alloc,
    dealloc: krs_expand_dealloc,
    unallocated: unallocated,
    /// Runs the expansion request at `request_ptr`.
    krs_expand_run => run_json,
    /// Runs the lookup request at `request_ptr`.
    krs_expand_lookup => lookup_json,
}

#[cfg(test)]
mod tests {
    use krs_wasm_abi::{call, dealloc, read};

    use crate::protocol::run_json;

    #[test]
    fn unknown_buffer_is_a_protocol_error() {
        let (response, len) = call(1, 4, run_json, super::unallocated);
        let value: serde_json::Value =
            serde_json::from_slice(&read(response, len).unwrap()).unwrap();
        assert_eq!(value["ok"], false);
        assert_eq!(value["diagnostics"][0]["code"], "krs::expand::protocol");
        assert_eq!(
            value["diagnostics"][0]["message"],
            krs_wasm_abi::UNALLOCATED
        );
        dealloc(response);
    }
}
