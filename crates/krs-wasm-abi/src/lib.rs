//! JSON-over-linear-memory Wasm ABI shared by the KRS browser modules.
//!
//! A module built with this crate exports, for its own export prefix:
//!
//! ```text
//! <prefix>_alloc(len: u32) -> ptr: u32
//! <prefix>_<entry>(request_ptr: u32, request_len: u32) -> u64   // (response_len << 32) | response_ptr
//! <prefix>_dealloc(ptr: u32, len: u32)
//! memory
//! ```
//!
//! and has no imports. The host allocates a request buffer, writes the UTF-8
//! JSON request into linear memory at the returned pointer, calls an entry,
//! reads the response, and deallocates both buffers.
//!
//! Buffers are owned by a registry keyed by address, so the module needs no
//! `unsafe` block: an entry reads the request from the registered buffer
//! rather than from a raw pointer. A pointer that names no buffer, or a
//! length beyond the buffer, yields the module's `unallocated` response
//! instead of a handler call. Each entry call ends by invalidating
//! `proc_macro2`'s thread-local span map, so a reused instance does not
//! accumulate fallback source-map state.
//!
//! [`export!`] declares the exports; the functions below are what they call.

use std::collections::BTreeMap;
use std::sync::Mutex;

/// Message of the protocol error an entry returns when its request pointer
/// and length do not name an allocated buffer.
pub const UNALLOCATED: &str = "request pointer and length do not name an allocated buffer";

struct Buffer {
    bytes: Box<[u8]>,
    len: usize,
}

/// Every live buffer, keyed by the address handed to the host.
static BUFFERS: Mutex<BTreeMap<usize, Buffer>> = Mutex::new(BTreeMap::new());

fn buffers() -> std::sync::MutexGuard<'static, BTreeMap<usize, Buffer>> {
    BUFFERS.lock().expect("the buffer registry is not poisoned")
}

fn register(bytes: Vec<u8>) -> usize {
    let len = bytes.len();
    // A zero-length boxed slice has a dangling, possibly shared address, so
    // every buffer owns at least one byte.
    let mut bytes = if len == 0 { vec![0] } else { bytes }.into_boxed_slice();
    let address = bytes.as_mut_ptr() as usize;
    buffers().insert(address, Buffer { bytes, len });
    address
}

/// Allocates a zeroed buffer of `len` bytes and returns its address.
#[must_use]
pub fn alloc(len: usize) -> usize {
    register(vec![0; len])
}

/// Releases the buffer at `address`; an unknown address is ignored.
pub fn dealloc(address: usize) {
    buffers().remove(&address);
}

/// Returns the first `len` bytes of the buffer at `address`, or `None` when
/// `address` names no buffer or `len` exceeds its length.
#[must_use]
pub fn read(address: usize, len: usize) -> Option<Vec<u8>> {
    buffers()
        .get(&address)
        .filter(|buffer| len <= buffer.len)
        .map(|buffer| buffer.bytes[..len].to_vec())
}

/// Copies `bytes` to the start of the buffer at `address`, as a host writes
/// linear memory. Returns false, writing nothing, when `address` names no
/// buffer or `bytes` is longer than it.
#[must_use]
pub fn write(address: usize, bytes: &[u8]) -> bool {
    match buffers().get_mut(&address) {
        Some(buffer) if bytes.len() <= buffer.len => {
            buffer.bytes[..bytes.len()].copy_from_slice(bytes);
            true
        }
        _ => false,
    }
}

/// Runs `handler` on the request in the buffer at `address` (or returns
/// `unallocated()` when there is none), registers the response, and returns
/// its address and length.
pub fn call(
    address: usize,
    len: usize,
    handler: fn(&[u8]) -> Vec<u8>,
    unallocated: fn() -> Vec<u8>,
) -> (usize, usize) {
    let response = match read(address, len) {
        Some(request) => handler(&request),
        None => unallocated(),
    };
    proc_macro2::extra::invalidate_current_thread_spans();
    let response_len = response.len();
    (register(response), response_len)
}

fn to_u32(value: usize) -> u32 {
    u32::try_from(value).expect("wasm32 addresses and lengths fit in u32")
}

/// [`alloc`] at the `u32` export boundary.
///
/// # Panics
///
/// When the address does not fit in `u32`, which cannot happen on wasm32.
#[must_use]
pub fn export_alloc(len: u32) -> u32 {
    to_u32(alloc(len as usize))
}

/// [`call`] at the `u32` export boundary, returning
/// `(response_len << 32) | response_ptr`.
///
/// # Panics
///
/// When the response address or length does not fit in `u32`, which cannot
/// happen on wasm32.
#[must_use]
pub fn export_call(
    request_ptr: u32,
    request_len: u32,
    handler: fn(&[u8]) -> Vec<u8>,
    unallocated: fn() -> Vec<u8>,
) -> u64 {
    let (address, len) = call(
        request_ptr as usize,
        request_len as usize,
        handler,
        unallocated,
    );
    (u64::from(to_u32(len)) << 32) | u64::from(to_u32(address))
}

/// [`dealloc`] at the `u32` export boundary.
pub fn export_dealloc(ptr: u32) {
    dealloc(ptr as usize);
}

/// Declares a module's Wasm exports.
///
/// ```ignore
/// krs_wasm_abi::export! {
///     alloc: krs_expand_alloc,
///     dealloc: krs_expand_dealloc,
///     unallocated: unallocated,
///     /// Runs the expansion request.
///     krs_expand_run => crate::protocol::run_json,
/// }
/// ```
///
/// `unallocated` is a `fn() -> Vec<u8>` returning the module's protocol
/// error response for [`UNALLOCATED`]; each entry names a
/// `fn(&[u8]) -> Vec<u8>` handler from request bytes to response bytes. The
/// invoking crate must allow `unsafe_code` (the exports carry
/// `#[unsafe(no_mangle)]`), for example by denying it instead of forbidding
/// it.
#[macro_export]
macro_rules! export {
    (
        alloc: $alloc:ident,
        dealloc: $dealloc:ident,
        unallocated: $unallocated:path,
        $( $(#[$entry_attr:meta])* $entry:ident => $handler:path ),+ $(,)?
    ) => {
        /// Allocates a zeroed buffer of `len` bytes and returns its address.
        #[allow(unsafe_code)]
        #[unsafe(no_mangle)]
        pub extern "C" fn $alloc(len: u32) -> u32 {
            $crate::export_alloc(len)
        }

        $(
            $(#[$entry_attr])*
            ///
            /// Returns `(response_len << 32) | response_ptr`.
            #[allow(unsafe_code)]
            #[unsafe(no_mangle)]
            pub extern "C" fn $entry(request_ptr: u32, request_len: u32) -> u64 {
                $crate::export_call(request_ptr, request_len, $handler, $unallocated)
            }
        )+

        /// Releases a buffer returned by the allocator or an entry.
        #[allow(unsafe_code)]
        #[unsafe(no_mangle)]
        pub extern "C" fn $dealloc(ptr: u32, _len: u32) {
            $crate::export_dealloc(ptr);
        }
    };
}

#[cfg(test)]
mod tests {
    use super::{alloc, buffers, call, dealloc, read, write};

    fn echo(request: &[u8]) -> Vec<u8> {
        [b"echo:", request].concat()
    }

    fn unallocated() -> Vec<u8> {
        b"unallocated".to_vec()
    }

    #[test]
    fn registry_round_trips_a_request() {
        let request = b"hello";
        let address = alloc(request.len());
        assert!(write(address, request));
        let (response, len) = call(address, request.len(), echo, unallocated);
        assert_eq!(read(response, len).unwrap(), b"echo:hello");
        dealloc(address);
        dealloc(response);
        let buffers = buffers();
        assert!(!buffers.contains_key(&address) && !buffers.contains_key(&response));
    }

    #[test]
    fn unknown_buffer_or_oversized_length_is_unallocated() {
        let (response, len) = call(1, 4, echo, unallocated);
        assert_eq!(read(response, len).unwrap(), b"unallocated");
        dealloc(response);

        let address = alloc(2);
        let (response, len) = call(address, 3, echo, unallocated);
        assert_eq!(read(response, len).unwrap(), b"unallocated");
        assert!(!write(address, b"abc"));
        dealloc(address);
        dealloc(response);
    }

    #[test]
    fn zero_length_buffers_have_distinct_addresses() {
        let first = alloc(0);
        let second = alloc(0);
        assert_ne!(first, second);
        let (response, len) = call(first, 0, echo, unallocated);
        assert_eq!(read(response, len).unwrap(), b"echo:");
        dealloc(first);
        dealloc(second);
        dealloc(response);
    }
}
