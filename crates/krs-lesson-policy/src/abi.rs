//! Wasm exports of the policy module (`krs_wasm_abi`).

use crate::protocol::{protocol_error, run_json};

fn unallocated() -> Vec<u8> {
    serde_json::to_vec(&protocol_error(krs_wasm_abi::UNALLOCATED.to_owned()))
        .expect("policy responses always serialize")
}

krs_wasm_abi::export! {
    alloc: krs_lesson_policy_alloc,
    dealloc: krs_lesson_policy_dealloc,
    unallocated: unallocated,
    /// Runs the policy request at `request_ptr`.
    krs_lesson_policy_run => run_json,
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
        assert_eq!(value["diagnostics"][0]["code"], "krs::policy::protocol");
        assert_eq!(
            value["diagnostics"][0]["message"],
            krs_wasm_abi::UNALLOCATED
        );
        dealloc(response);
    }
}
