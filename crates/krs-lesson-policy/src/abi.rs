//! Wasm ABI, in the shape of the IR-11 expander module.
//!
//! ```text
//! krs_lesson_policy_alloc(len: u32) -> ptr: u32
//! krs_lesson_policy_run(request_ptr: u32, request_len: u32) -> u64   // (response_len << 32) | response_ptr
//! krs_lesson_policy_dealloc(ptr: u32, len: u32)
//! memory
//! ```
//!
//! The host allocates a request buffer, writes the UTF-8 JSON request into
//! linear memory at the returned pointer, calls `run`, reads the response,
//! and deallocates both buffers. Buffers are owned by a registry keyed by
//! address, so the module needs no `unsafe` block: `run` reads the request
//! from the registered buffer rather than from a raw pointer. An unknown
//! pointer or an oversized length yields a `krs::policy::protocol` response.
//! Each `run` ends by invalidating `proc_macro2`'s thread-local span map, so
//! a reused instance does not accumulate fallback source-map state.

use std::collections::BTreeMap;
use std::sync::Mutex;

use serde_json::json;

use crate::protocol::{PROTOCOL_ERROR, SCHEMA, run_json};

struct Buffer {
    bytes: Box<[u8]>,
    len: usize,
}

/// Every live buffer, keyed by the address handed to the host.
static BUFFERS: Mutex<BTreeMap<usize, Buffer>> = Mutex::new(BTreeMap::new());

fn register(bytes: Vec<u8>) -> usize {
    let len = bytes.len();
    // A zero-length boxed slice has a dangling, possibly shared address, so
    // every buffer owns at least one byte.
    let mut bytes = if len == 0 { vec![0] } else { bytes }.into_boxed_slice();
    let address = bytes.as_mut_ptr() as usize;
    BUFFERS
        .lock()
        .expect("the buffer registry is not poisoned")
        .insert(address, Buffer { bytes, len });
    address
}

fn alloc(len: usize) -> usize {
    register(vec![0; len])
}

fn run(address: usize, len: usize) -> (usize, usize) {
    let request = {
        let buffers = BUFFERS.lock().expect("the buffer registry is not poisoned");
        buffers
            .get(&address)
            .filter(|buffer| len <= buffer.len)
            .map(|buffer| buffer.bytes[..len].to_vec())
    };
    let response = match request {
        Some(request) => run_json(&request),
        None => serde_json::to_vec(&json!({
            "schema": SCHEMA,
            "ok": false,
            "policy_version": null,
            "diagnostics": [{
                "code": PROTOCOL_ERROR,
                "message": "request pointer and length do not name an allocated buffer",
                "file": "",
                "authored": null,
                "class": crate::CLASS_UNMAPPABLE,
            }],
        }))
        .expect("the protocol error always serializes"),
    };
    proc_macro2::extra::invalidate_current_thread_spans();
    let response_len = response.len();
    (register(response), response_len)
}

fn dealloc(address: usize) {
    BUFFERS
        .lock()
        .expect("the buffer registry is not poisoned")
        .remove(&address);
}

fn to_u32(value: usize) -> u32 {
    u32::try_from(value).expect("wasm32 addresses and lengths fit in u32")
}

/// Allocates a zeroed buffer of `len` bytes and returns its address.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn krs_lesson_policy_alloc(len: u32) -> u32 {
    to_u32(alloc(len as usize))
}

/// Runs the policy request at `request_ptr` and returns
/// `(response_len << 32) | response_ptr`.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn krs_lesson_policy_run(request_ptr: u32, request_len: u32) -> u64 {
    let (address, len) = run(request_ptr as usize, request_len as usize);
    (u64::from(to_u32(len)) << 32) | u64::from(to_u32(address))
}

/// Releases a buffer returned by `alloc` or `run`.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn krs_lesson_policy_dealloc(ptr: u32, _len: u32) {
    dealloc(ptr as usize);
}

#[cfg(test)]
mod tests {
    use super::{BUFFERS, alloc, dealloc, run};

    fn write(address: usize, bytes: &[u8]) {
        let mut buffers = BUFFERS.lock().unwrap();
        buffers.get_mut(&address).unwrap().bytes[..bytes.len()].copy_from_slice(bytes);
    }

    fn read(address: usize, len: usize) -> Vec<u8> {
        BUFFERS.lock().unwrap()[&address].bytes[..len].to_vec()
    }

    #[test]
    fn registry_round_trips_a_request() {
        let request = br#"{"schema":1,"policy":{"version":1,"editable_files":["src/lib.rs"],"facade_alias":"k"},"files":{"src/lib.rs":"extern crate std;"}}"#;
        let address = alloc(request.len());
        write(address, request);
        let (response, len) = run(address, request.len());
        let value: serde_json::Value = serde_json::from_slice(&read(response, len)).unwrap();
        assert_eq!(value["ok"], false);
        assert_eq!(value["diagnostics"][0]["code"], "krs::policy::extern-crate");
        assert_eq!(
            value["diagnostics"][0]["authored"],
            serde_json::json!([0, 17])
        );
        dealloc(address);
        dealloc(response);
        let buffers = BUFFERS.lock().unwrap();
        assert!(!buffers.contains_key(&address) && !buffers.contains_key(&response));
    }

    #[test]
    fn unknown_buffer_is_a_protocol_error() {
        let (response, len) = run(1, 4);
        let value: serde_json::Value = serde_json::from_slice(&read(response, len)).unwrap();
        assert_eq!(value["diagnostics"][0]["code"], "krs::policy::protocol");
        dealloc(response);
    }

    #[test]
    fn zero_length_buffers_have_distinct_addresses() {
        let first = alloc(0);
        let second = alloc(0);
        assert_ne!(first, second);
        dealloc(first);
        dealloc(second);
    }
}
