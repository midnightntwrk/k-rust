//! The memory this process is allowed, read once per run.
//!
//! A hook whose result size an argument's value sets (`padRightBytes`, `padLeftBytes`,
//! `Int2Bytes`, `makeList`; `^Int` and `<<Int` keep their own bound, `MAX_INT_RESULT_BITS`) may
//! be asked for a result no allocation can hold. The allowance is the line against which such a
//! result is judged: the smallest of the limits the operating system enforces on this process,
//! each of which turns an allocation above it into a failed allocation or a killed process.
//!
//! - **cgroup v2 `memory.max`** of the process's cgroup and of every ancestor up to the cgroup2
//!   mount (Linux). The kernel charges a cgroup's memory to each of its ancestors and reclaims or
//!   kills when any of them is over its `memory.max`, so an ancestor binds as much as the leaf.
//!   `memory.high` is a reclaim target, not a refusal line, and swap is not counted: a result
//!   that fits only in swap pays disk I/O on every use. cgroup v1 controllers are not read.
//! - **`RLIMIT_AS` and `RLIMIT_DATA` soft limits** (Unix): an allocation that would take the
//!   address space or the data segment past them fails.
//! - **Physical memory** (Linux, macOS): with no smaller limit, what does not fit in RAM does not
//!   fit at all.
//! - **The target's address space**: 4 GiB on a 32-bit target such as wasm32, where none of the
//!   limits above is visible to the module; the largest allocation and rendering peak there are
//!   also bounded per result where the hooks check their sizes. On a 64-bit target it never
//!   binds.
//!
//! The allowance is not reduced by the memory already in use. Whether a result is computed or
//! refused then depends only on the input and the limits, not on what the run has allocated so
//! far, on the timing of parallel branches, or on other processes sharing the cgroup; a result
//! that fits the allowance but not what is left fails as any other allocation does.
//!
//! [`Allowance::of_process`] reads the limits once and keeps them for the run. Tests give an
//! allowance of their own with [`Allowance::given`] and pass it to the hooks, so that whether a
//! result is refused does not depend on the host.

use std::fmt;
#[cfg(target_os = "linux")]
use std::path::Path;
use std::sync::OnceLock;

/// The memory this process may use, in bytes, and which limit sets it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Allowance {
    bytes: u64,
    source: AllowanceSource,
}

/// The limit that sets an [`Allowance`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AllowanceSource {
    /// The `memory.max` of a cgroup v2 cgroup containing the process: its own or an ancestor,
    /// named by its path in the cgroup hierarchy (`/user.slice/run-1.scope`).
    CgroupMemoryMax { cgroup: String },
    /// The soft `RLIMIT_AS` limit on the process's address space.
    AddressSpaceLimit,
    /// The soft `RLIMIT_DATA` limit on the process's data segment.
    DataLimit,
    /// The physical memory of the machine.
    PhysicalMemory,
    /// The address space of the target the backend is built for.
    TargetAddressSpace,
    /// An allowance a test gave ([`Allowance::given`]).
    Given,
}

impl Allowance {
    /// An allowance of `bytes`, given by the caller instead of read from the system.
    pub const fn given(bytes: u64) -> Self {
        Self {
            bytes,
            source: AllowanceSource::Given,
        }
    }

    /// The allowance of this process: the smallest limit present when it is first asked for,
    /// kept for the rest of the run.
    pub fn of_process() -> &'static Self {
        static ALLOWANCE: OnceLock<Allowance> = OnceLock::new();
        ALLOWANCE.get_or_init(|| smallest(probe()))
    }

    /// The memory the process may use, in bytes.
    pub const fn bytes(&self) -> u64 {
        self.bytes
    }

    /// The limit that sets it.
    pub const fn source(&self) -> &AllowanceSource {
        &self.source
    }
}

impl fmt::Display for AllowanceSource {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CgroupMemoryMax { cgroup } => write!(formatter, "cgroup memory.max of {cgroup}"),
            Self::AddressSpaceLimit => formatter.write_str("RLIMIT_AS"),
            Self::DataLimit => formatter.write_str("RLIMIT_DATA"),
            Self::PhysicalMemory => formatter.write_str("physical memory"),
            Self::TargetAddressSpace => formatter.write_str("the target's address space"),
            Self::Given => formatter.write_str("given by the caller"),
        }
    }
}

/// The smallest of the limits `candidates` and the target's address space; among equal limits,
/// the first one named.
fn smallest(candidates: Vec<(u64, AllowanceSource)>) -> Allowance {
    candidates
        .into_iter()
        .chain([(target_address_space(), AllowanceSource::TargetAddressSpace)])
        .min_by_key(|(bytes, _)| *bytes)
        .map(|(bytes, source)| Allowance { bytes, source })
        .expect("the target's address space is always a candidate")
}

/// The size of this target's address space in bytes, saturated at `u64::MAX` on a 64-bit target.
const fn target_address_space() -> u64 {
    (usize::MAX as u64).saturating_add(1)
}

/// Every limit present on this process, in the order of the module documentation.
fn probe() -> Vec<(u64, AllowanceSource)> {
    #[cfg(target_os = "linux")]
    let cgroup = cgroup::memory_max(&|path: &Path| std::fs::read_to_string(path).ok());
    #[cfg(not(target_os = "linux"))]
    let cgroup = None;
    #[cfg(unix)]
    let (address_space, data) = (system::address_space_limit(), system::data_limit());
    #[cfg(not(unix))]
    let (address_space, data) = (None, None);
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    let physical = system::physical_memory();
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    let physical = None;
    [
        cgroup.map(|(bytes, cgroup)| (bytes, AllowanceSource::CgroupMemoryMax { cgroup })),
        address_space.map(|bytes| (bytes, AllowanceSource::AddressSpaceLimit)),
        data.map(|bytes| (bytes, AllowanceSource::DataLimit)),
        physical.map(|bytes| (bytes, AllowanceSource::PhysicalMemory)),
    ]
    .into_iter()
    .flatten()
    .collect()
}

/// Reading the cgroup v2 hierarchy (Linux).
#[cfg(any(target_os = "linux", test))]
mod cgroup {
    use std::path::{Path, PathBuf};

    /// The smallest cgroup v2 `memory.max` over the process's cgroup and its ancestors visible
    /// under the cgroup2 mount, with the cgroup path that sets it; `None` when no cgroup on the
    /// chain has a limit (`max`) or the hierarchy is not visible. `read` returns a file's
    /// contents, `None` when it cannot be read.
    ///
    /// The process's cgroup is the `0::<path>` line of `/proc/self/cgroup` (the other lines are
    /// v1 hierarchies). `/proc/self/mountinfo` names the cgroup2 mount and the cgroup its root
    /// shows, which is `/` unless the mount shows a subtree: the cgroup's directory is the mount
    /// point joined with the path below that root, and a cgroup outside the root has no directory
    /// to read.
    pub(super) fn memory_max(read: &dyn Fn(&Path) -> Option<String>) -> Option<(u64, String)> {
        let membership = read(Path::new("/proc/self/cgroup"))?;
        let cgroup = membership
            .lines()
            .find_map(|line| line.strip_prefix("0::"))?;
        // A cgroup removed while the process is in it is shown with this suffix and has no
        // directory.
        if cgroup.ends_with(" (deleted)") {
            return None;
        }
        let cgroup = Path::new(cgroup);
        let mounts = read(Path::new("/proc/self/mountinfo"))?;
        let (root, mount_point, below_root) = mounts.lines().find_map(|line| {
            let (root, mount_point) = cgroup2_mount(line)?;
            let below_root = cgroup.strip_prefix(&root).ok()?.to_path_buf();
            Some((root, mount_point, below_root))
        })?;
        below_root
            .ancestors()
            .filter_map(|below| {
                let bytes = memory_max_text(&read(&mount_point.join(below).join("memory.max"))?)?;
                let name = if below.as_os_str().is_empty() {
                    root.clone()
                } else {
                    root.join(below)
                };
                Some((bytes, name.to_string_lossy().into_owned()))
            })
            .min_by_key(|(bytes, _)| *bytes)
    }

    /// The root and mount point of a `/proc/self/mountinfo` line that mounts a cgroup2 file system.
    ///
    /// A line is `id parent major:minor root mount-point options [optional fields] - type source
    /// super-options`, with a space, tab, newline or backslash in a path written as `\ooo` octal.
    fn cgroup2_mount(line: &str) -> Option<(PathBuf, PathBuf)> {
        let (fields, after_separator) = line.split_once(" - ")?;
        if after_separator.split(' ').next()? != "cgroup2" {
            return None;
        }
        let mut fields = fields.split(' ').skip(3);
        let root = unescape(fields.next()?)?;
        let mount_point = unescape(fields.next()?)?;
        Some((root, mount_point))
    }

    /// A mountinfo path with its `\ooo` escapes replaced by the bytes they stand for; `None` for a
    /// malformed escape.
    fn unescape(field: &str) -> Option<PathBuf> {
        let mut bytes = Vec::with_capacity(field.len());
        let mut rest = field.as_bytes();
        while let Some((&byte, after)) = rest.split_first() {
            if byte == b'\\' {
                let digits = std::str::from_utf8(after.get(..3)?).ok()?;
                bytes.push(u8::from_str_radix(digits, 8).ok()?);
                rest = &after[3..];
            } else {
                bytes.push(byte);
                rest = after;
            }
        }
        Some(PathBuf::from(String::from_utf8(bytes).ok()?))
    }

    /// The limit a `memory.max` file states, in bytes: `None` for `max` (no limit) and for anything
    /// that is not a byte count.
    fn memory_max_text(text: &str) -> Option<u64> {
        match text.trim() {
            "max" => None,
            bytes => bytes.parse().ok(),
        }
    }
}

#[cfg(unix)]
mod system {
    /// The soft `RLIMIT_AS` limit in bytes, `None` when it is unlimited or cannot be read.
    pub(super) fn address_space_limit() -> Option<u64> {
        // SAFETY: `getrlimit` writes one `rlimit` through a pointer to a live, exclusive one.
        soft_limit(|limit| unsafe { libc::getrlimit(libc::RLIMIT_AS, limit) })
    }

    /// The soft `RLIMIT_DATA` limit in bytes, `None` when it is unlimited or cannot be read.
    pub(super) fn data_limit() -> Option<u64> {
        // SAFETY: as above.
        soft_limit(|limit| unsafe { libc::getrlimit(libc::RLIMIT_DATA, limit) })
    }

    /// The soft limit `getrlimit` reads, `None` when it is unlimited or the call fails.
    fn soft_limit(getrlimit: impl FnOnce(&mut libc::rlimit) -> libc::c_int) -> Option<u64> {
        let mut limit = libc::rlimit {
            rlim_cur: 0,
            rlim_max: 0,
        };
        if getrlimit(&mut limit) != 0 || limit.rlim_cur == libc::RLIM_INFINITY {
            return None;
        }
        // `rlim_t` is `u64` on Linux and macOS and signed on some other Unix systems.
        #[allow(clippy::useless_conversion)]
        u64::try_from(limit.rlim_cur).ok()
    }

    /// The machine's physical memory in bytes, `None` when the system does not report it.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) fn physical_memory() -> Option<u64> {
        // SAFETY: `sysconf` only reads a system constant.
        let pages = unsafe { libc::sysconf(libc::_SC_PHYS_PAGES) };
        // SAFETY: as above.
        let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        let pages = u64::try_from(pages).ok().filter(|pages| *pages > 0)?;
        let page_size = u64::try_from(page_size).ok().filter(|size| *size > 0)?;
        Some(pages.saturating_mul(page_size))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::path::Path;

    use super::cgroup::memory_max as cgroup_memory_max;
    use super::{Allowance, AllowanceSource, smallest, target_address_space};

    const GIB: u64 = 1 << 30;

    const MOUNTINFO: &str = "\
22 1 259:2 / / rw,relatime shared:1 - ext4 /dev/nvme0n1p2 rw
45 43 0:29 / /sys/fs/cgroup rw,nosuid,nodev,noexec,relatime shared:7 - cgroup2 cgroup2 rw,nsdelegate
";

    /// `cgroup_memory_max` over the files `files` (path, contents), every other file unreadable.
    fn cgroup_limit(files: &[(&str, &str)]) -> Option<(u64, String)> {
        let files: BTreeMap<&Path, &str> = files
            .iter()
            .map(|(path, text)| (Path::new(*path), *text))
            .collect();
        cgroup_memory_max(&|path: &Path| files.get(path).map(|text| (*text).to_owned()))
    }

    #[test]
    fn an_ancestor_binds_as_much_as_the_leaf() {
        let leaf = "/sys/fs/cgroup/user.slice/agents.slice/run-1.scope/memory.max";
        let files = [
            (
                "/proc/self/cgroup",
                "1:net_cls:/\n0::/user.slice/agents.slice/run-1.scope\n",
            ),
            ("/proc/self/mountinfo", MOUNTINFO),
            ("/sys/fs/cgroup/user.slice/memory.max", "max\n"),
            (
                "/sys/fs/cgroup/user.slice/agents.slice/memory.max",
                "17179869184\n",
            ),
            (leaf, "68719476736\n"),
        ];
        assert_eq!(
            cgroup_limit(&files),
            Some((16 * GIB, "/user.slice/agents.slice".to_owned()))
        );

        let files = [
            files[0],
            files[1],
            files[2],
            ("/sys/fs/cgroup/user.slice/agents.slice/memory.max", "max\n"),
            (leaf, "1073741824\n"),
        ];
        assert_eq!(
            cgroup_limit(&files),
            Some((GIB, "/user.slice/agents.slice/run-1.scope".to_owned()))
        );
    }

    #[test]
    fn no_cgroup_limit_without_a_v2_membership_a_mount_or_a_bound() {
        let unlimited = [
            ("/proc/self/cgroup", "0::/run-1.scope\n"),
            ("/proc/self/mountinfo", MOUNTINFO),
            ("/sys/fs/cgroup/run-1.scope/memory.max", "max\n"),
        ];
        assert_eq!(cgroup_limit(&unlimited), None);
        // Only v1 hierarchies: the v1 memory controller's limit is not read.
        let v1_only = [
            ("/proc/self/cgroup", "4:memory:/run-1.scope\n"),
            ("/proc/self/mountinfo", MOUNTINFO),
            ("/sys/fs/cgroup/run-1.scope/memory.max", "1073741824\n"),
        ];
        assert_eq!(cgroup_limit(&v1_only), None);
        let unmounted = [
            ("/proc/self/cgroup", "0::/run-1.scope\n"),
            (
                "/proc/self/mountinfo",
                "22 1 259:2 / / rw shared:1 - ext4 /dev/nvme0n1p2 rw\n",
            ),
            ("/sys/fs/cgroup/run-1.scope/memory.max", "1073741824\n"),
        ];
        assert_eq!(cgroup_limit(&unmounted), None);
        let deleted = [
            ("/proc/self/cgroup", "0::/run-1.scope (deleted)\n"),
            ("/proc/self/mountinfo", MOUNTINFO),
            ("/sys/fs/cgroup/run-1.scope/memory.max", "1073741824\n"),
        ];
        assert_eq!(cgroup_limit(&deleted), None);
    }

    #[test]
    fn a_mount_of_a_subtree_shows_the_cgroups_below_its_root() {
        // The mount shows the subtree `/outer`, at an escaped mount point with a space.
        let mountinfo = "50 40 0:29 /outer /run/my\\040cgroup rw shared:9 - cgroup2 cgroup2 rw\n";
        let files = [
            ("/proc/self/cgroup", "0::/outer/inner\n"),
            ("/proc/self/mountinfo", mountinfo),
            ("/run/my cgroup/memory.max", "2147483648\n"),
            ("/run/my cgroup/inner/memory.max", "max\n"),
        ];
        assert_eq!(cgroup_limit(&files), Some((2 * GIB, "/outer".to_owned())));
        // A cgroup outside the mount's root has no directory there.
        let outside = [("/proc/self/cgroup", "0::/elsewhere\n"), files[1], files[2]];
        assert_eq!(cgroup_limit(&outside), None);
    }

    #[test]
    fn the_allowance_is_the_smallest_limit_present() {
        let allowance = smallest(vec![
            (
                16 * GIB,
                AllowanceSource::CgroupMemoryMax {
                    cgroup: "/a".to_owned(),
                },
            ),
            (24 * GIB, AllowanceSource::AddressSpaceLimit),
            (64 * GIB, AllowanceSource::PhysicalMemory),
        ]);
        assert_eq!(allowance.bytes(), 16 * GIB);
        assert_eq!(allowance.source().to_string(), "cgroup memory.max of /a");

        let allowance = smallest(vec![
            (24 * GIB, AllowanceSource::AddressSpaceLimit),
            (24 * GIB, AllowanceSource::DataLimit),
        ]);
        assert_eq!(
            (allowance.bytes(), allowance.source()),
            (24 * GIB, &AllowanceSource::AddressSpaceLimit)
        );

        let allowance = smallest(Vec::new());
        assert_eq!(allowance.bytes(), target_address_space());
        assert_eq!(allowance.source(), &AllowanceSource::TargetAddressSpace);
    }

    #[test]
    fn a_given_allowance_is_kept_as_given() {
        let allowance = Allowance::given(5 * GIB);
        assert_eq!(
            (allowance.bytes(), allowance.source()),
            (5 * GIB, &AllowanceSource::Given)
        );
    }

    #[test]
    fn the_process_allowance_is_read_once_and_bounded_by_the_address_space() {
        let first = Allowance::of_process();
        assert!(std::ptr::eq(first, Allowance::of_process()));
        assert!(first.bytes() > 0 && first.bytes() <= target_address_space());
    }
}
