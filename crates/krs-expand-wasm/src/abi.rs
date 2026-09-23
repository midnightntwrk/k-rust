//! Wasm ABI, in the shape of the `krs-lesson-policy` module.
//!
//! The host allocates a request buffer, writes the UTF-8 JSON request into
//! linear memory at the returned pointer, calls `run` (or `lookup`), reads
//! the response, and deallocates both buffers. Buffers are owned by a
//! registry keyed by address, so the module needs no `unsafe` block: a call
//! reads the request from the registered buffer rather than from a raw
//! pointer. An unknown pointer or an oversized length yields a
//! `krs::expand::protocol` response. Each call ends by invalidating
//! `proc_macro2`'s thread-local span map, so a reused instance does not
//! accumulate fallback source-map state.

use std::collections::BTreeMap;
use std::sync::Mutex;

use crate::protocol::{PROTOCOL_ERROR, SCHEMA, lookup_json, run_json, sha256};

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

fn call(address: usize, len: usize, handler: fn(&[u8]) -> Vec<u8>) -> (usize, usize) {
    let request = {
        let buffers = BUFFERS.lock().expect("the buffer registry is not poisoned");
        buffers
            .get(&address)
            .filter(|buffer| len <= buffer.len)
            .map(|buffer| buffer.bytes[..len].to_vec())
    };
    let response = match request {
        Some(request) => handler(&request),
        None => serde_json::to_vec(&serde_json::json!({
            "schema": SCHEMA,
            "ok": false,
            "diagnostics": [{
                "origin": "protocol",
                "code": PROTOCOL_ERROR,
                "severity": "error",
                "message": "request pointer and length do not name an allocated buffer",
                "class": "unmappable",
                "file": "",
                "authored": null,
                "invocation": null,
                "notes": [],
            }],
            "evidence": { "request_sha256": sha256(&[]) },
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

fn pack((address, len): (usize, usize)) -> u64 {
    (u64::from(to_u32(len)) << 32) | u64::from(to_u32(address))
}

/// Allocates a zeroed buffer of `len` bytes and returns its address.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn krs_expand_alloc(len: u32) -> u32 {
    to_u32(alloc(len as usize))
}

/// Runs the expansion request at `request_ptr` and returns
/// `(response_len << 32) | response_ptr`.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn krs_expand_run(request_ptr: u32, request_len: u32) -> u64 {
    pack(call(request_ptr as usize, request_len as usize, run_json))
}

/// Runs the lookup request at `request_ptr` and returns
/// `(response_len << 32) | response_ptr`.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn krs_expand_lookup(request_ptr: u32, request_len: u32) -> u64 {
    pack(call(
        request_ptr as usize,
        request_len as usize,
        lookup_json,
    ))
}

/// Releases a buffer returned by `alloc`, `run`, or `lookup`.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn krs_expand_dealloc(ptr: u32, _len: u32) {
    dealloc(ptr as usize);
}

#[cfg(test)]
mod tests {
    use super::{BUFFERS, alloc, call, dealloc};
    use crate::protocol::run_json;

    fn write(address: usize, bytes: &[u8]) {
        let mut buffers = BUFFERS.lock().unwrap();
        buffers.get_mut(&address).unwrap().bytes[..bytes.len()].copy_from_slice(bytes);
    }

    fn read(address: usize, len: usize) -> Vec<u8> {
        BUFFERS.lock().unwrap()[&address].bytes[..len].to_vec()
    }

    #[test]
    fn registry_round_trips_a_request() {
        let request = br#"{"schema":2}"#;
        let address = alloc(request.len());
        write(address, request);
        let (response, len) = call(address, request.len(), run_json);
        let value: serde_json::Value = serde_json::from_slice(&read(response, len)).unwrap();
        assert_eq!(value["ok"], false);
        assert_eq!(value["diagnostics"][0]["code"], "krs::expand::protocol");
        dealloc(address);
        dealloc(response);
        let buffers = BUFFERS.lock().unwrap();
        assert!(!buffers.contains_key(&address) && !buffers.contains_key(&response));
    }

    #[test]
    fn unknown_buffer_is_a_protocol_error() {
        let (response, len) = call(1, 4, run_json);
        let value: serde_json::Value = serde_json::from_slice(&read(response, len)).unwrap();
        assert_eq!(value["diagnostics"][0]["code"], "krs::expand::protocol");
        dealloc(response);
    }
}
