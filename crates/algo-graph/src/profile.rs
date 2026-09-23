//! Sampled cost: CPU samples of an untraced run attributed to algorithm cards.
//!
//! A `samply record` profile holds, per sample, the stack of instruction addresses. [`fold_samply`]
//! resolves the addresses of the profiled binary to source frames, expanding inlined calls from
//! the binary's DWARF line tables, and folds identical stacks into [`Stacks`], the compact form a
//! receipt keeps. [`attribute`] then maps every workspace frame to the algorithm whose card names
//! a site item containing the frame's line, by [`OWNERSHIP_RULE`], and writes a
//! [`SampledProfile`]: sampled self and total shares by algorithm, and the hottest code that no
//! card names.

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt::Write as _,
    fs,
    io::Read as _,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};

use crate::{
    Error, Graph,
    cards::{ItemSpan, item_spans},
    coverage::is_workspace_source,
};

/// The schema of the stacks file [`fold_samply`] writes.
pub const STACKS_SCHEMA_VERSION: u32 = 1;

/// The schema of the `profile.toml` [`attribute`] writes.
pub const PROFILE_SCHEMA_VERSION: u32 = 1;

/// How a sample is attributed to algorithms.
pub const OWNERSHIP_RULE: &str = "a frame is a workspace frame when its source file is `crates/<crate>/src/**.rs`; inlined calls are frames of their own, each at its own file and line. A workspace frame belongs to an algorithm when its line lies inside the lines of an item that one of the algorithm's card sites names (a function, a method, an `impl` block, or, for a type site, the type and its `impl` blocks in the site's file); when several site items contain the line, the smallest item owns it, and among equal items the first algorithm id. A sample's owning algorithm is the innermost owned frame on its stack: the sample is that algorithm's self sample and a total sample of every distinct algorithm owning a frame on the stack. An uncarded function is the innermost enclosing item (function or method; for a line inside a type, as derived code is, the type and the frame's function) of a workspace frame that no algorithm owns. The uncarded tail of a sample is its workspace frames inside its innermost owned frame, or all of them without one: the sample is an uncarded leaf sample of the tail's innermost function, and an inclusive sample of every distinct function of the tail, each filed under the sample's owning algorithm, so a recursive or non-leaf walk counts once per sample and a driver function counts only the samples in which no algorithm runs inside it. A sample without an owned frame is filed under `(no algorithm)`, or under `(truncated stack)` when its stack does not reach the thread's start, since its owner may be among the missing outer frames. Frames outside the workspace (the standard library, dependencies, other libraries) belong to no algorithm and are never uncarded functions, so their samples count toward the innermost workspace frame. Shares divide by every sample of the profiled binary's process, which is CPU time on all threads";

/// The `under` label of samples without an owning algorithm on a complete stack.
pub const NO_ALGORITHM: &str = "(no algorithm)";

/// The `under` label of samples without an owning algorithm on a truncated stack, whose owner
/// may be among the missing outer frames.
pub const TRUNCATED_STACK: &str = "(truncated stack)";

/// The most rows of each uncarded table a `profile.toml` keeps.
const KEPT_ROWS: usize = 100;

/// One resolved frame.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct StackFrame {
    /// The function name from the debug information, without generic arguments.
    pub function: String,
    /// Workspace-relative for workspace sources, else shortened (`library/core/src/..`, a
    /// registry crate's `name-version/src/..`), or a library name for unsymbolicated frames.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub file: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub line: Option<u32>,
}

/// One folded stack: frame indices from the outermost to the innermost, and its sample weight.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct SampledStack {
    pub samples: u64,
    pub frames: Vec<u32>,
    /// The unwinder stopped before the thread's start: outer frames are missing.
    #[serde(default, skip_serializing_if = "is_false")]
    pub truncated: bool,
}

fn is_false(value: &bool) -> bool {
    !value
}

/// The symbolicated, folded samples of one profile.
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct Stacks {
    pub schema: u32,
    /// The sampling interval in milliseconds, from the profile.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub interval_ms: Option<f64>,
    /// The profiled binary's file name.
    pub binary: String,
    /// Samples whose outermost frame is neither the binary's `_start` nor a frame of another
    /// library (a thread start): the unwinder stopped early, so outer frames are missing.
    pub truncated_samples: u64,
    pub frames: Vec<StackFrame>,
    pub stacks: Vec<SampledStack>,
}

impl Stacks {
    /// The sum of the stacks' samples.
    pub fn samples(&self) -> u64 {
        self.stacks.iter().map(|stack| stack.samples).sum()
    }

    /// Sort the frames and the stacks, so that equal profiles serialize identically.
    fn canonicalize(&mut self) {
        let mut order = (0..self.frames.len()).collect::<Vec<_>>();
        order.sort_by(|left, right| self.frames[*left].cmp(&self.frames[*right]));
        let mut renumber = vec![0u32; self.frames.len()];
        for (new, old) in order.iter().enumerate() {
            renumber[*old] = new as u32;
        }
        self.frames = order
            .iter()
            .map(|index| self.frames[*index].clone())
            .collect();
        let mut merged = BTreeMap::<(Vec<u32>, bool), u64>::new();
        for stack in &self.stacks {
            let frames = stack
                .frames
                .iter()
                .map(|frame| renumber[*frame as usize])
                .collect();
            *merged.entry((frames, stack.truncated)).or_default() += stack.samples;
        }
        self.stacks = merged
            .into_iter()
            .map(|((frames, truncated), samples)| SampledStack {
                samples,
                frames,
                truncated,
            })
            .collect();
    }

    /// The stacks as JSON with one frame or stack per line.
    pub fn json(&self) -> Result<String, Error> {
        let mut out = String::new();
        let _ = writeln!(out, "{{\"schema\": {},", self.schema);
        if let Some(interval) = self.interval_ms {
            let _ = writeln!(
                out,
                "\"interval_ms\": {},",
                serde_json::to_string(&interval)?
            );
        }
        let _ = writeln!(out, "\"binary\": {},", serde_json::to_string(&self.binary)?);
        let _ = writeln!(out, "\"truncated_samples\": {},", self.truncated_samples);
        let _ = writeln!(out, "\"frames\": [");
        for (index, frame) in self.frames.iter().enumerate() {
            let comma = if index + 1 < self.frames.len() {
                ","
            } else {
                ""
            };
            let _ = writeln!(out, "{}{comma}", serde_json::to_string(frame)?);
        }
        let _ = writeln!(out, "],\n\"stacks\": [");
        for (index, stack) in self.stacks.iter().enumerate() {
            let comma = if index + 1 < self.stacks.len() {
                ","
            } else {
                ""
            };
            let _ = writeln!(out, "{}{comma}", serde_json::to_string(stack)?);
        }
        let _ = writeln!(out, "]}}");
        Ok(out)
    }
}

/// Write `stacks` as [`Stacks::json`], gzip-compressed when `path` ends in `.gz`.
pub fn write_stacks(path: &Path, stacks: &Stacks) -> Result<(), Error> {
    use std::io::Write as _;
    let json = stacks.json()?;
    if let Some(parent) = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent)?;
    }
    if path.extension().is_some_and(|extension| extension == "gz") {
        let mut encoder =
            flate2::write::GzEncoder::new(fs::File::create(path)?, flate2::Compression::default());
        encoder.write_all(json.as_bytes())?;
        encoder.finish()?;
    } else {
        fs::write(path, json)?;
    }
    Ok(())
}

/// A file's text, decompressed when it starts with the gzip magic bytes.
fn read_text(path: &Path) -> Result<String, Error> {
    let at = |error: &dyn std::fmt::Display| Error::Invalid(format!("{}: {error}", path.display()));
    let bytes = fs::read(path).map_err(|error| at(&error))?;
    if bytes.starts_with(&[0x1f, 0x8b]) {
        let mut text = String::new();
        flate2::read::GzDecoder::new(bytes.as_slice())
            .read_to_string(&mut text)
            .map_err(|error| at(&error))?;
        Ok(text)
    } else {
        String::from_utf8(bytes).map_err(|error| at(&error))
    }
}

/// Read a stacks file written by [`write_stacks`], plain or gzip-compressed.
pub fn read_stacks(path: &Path) -> Result<Stacks, Error> {
    let at = |error: &dyn std::fmt::Display| Error::Invalid(format!("{}: {error}", path.display()));
    let stacks: Stacks = serde_json::from_str(&read_text(path)?).map_err(|error| at(&error))?;
    if stacks.schema != STACKS_SCHEMA_VERSION {
        return Err(at(&format!(
            "stacks schema {}, but this tool reads schema {STACKS_SCHEMA_VERSION}",
            stacks.schema
        )));
    }
    let frames = stacks.frames.len();
    if let Some(stack) = stacks
        .stacks
        .iter()
        .find(|stack| stack.frames.iter().any(|frame| *frame as usize >= frames))
    {
        return Err(at(&format!(
            "a stack names frame {:?} of {frames}",
            stack.frames
        )));
    }
    Ok(stacks)
}

// The fields of the Firefox profiler's processed format (as `samply record` writes it) that the
// fold reads.

#[derive(Deserialize)]
struct SamplyProfile {
    meta: SamplyMeta,
    libs: Vec<SamplyLib>,
    threads: Vec<SamplyThread>,
}

#[derive(Deserialize)]
struct SamplyMeta {
    #[serde(default)]
    interval: Option<f64>,
}

#[derive(Deserialize)]
struct SamplyLib {
    name: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct SamplyThread {
    samples: SamplySamples,
    stack_table: SamplyStackTable,
    frame_table: SamplyFrameTable,
    func_table: SamplyFuncTable,
    resource_table: SamplyResourceTable,
}

#[derive(Deserialize)]
struct SamplySamples {
    stack: Vec<Option<usize>>,
    #[serde(default)]
    weight: Option<Vec<Option<f64>>>,
}

#[derive(Deserialize)]
struct SamplyStackTable {
    prefix: Vec<Option<usize>>,
    frame: Vec<usize>,
}

#[derive(Deserialize)]
struct SamplyFrameTable {
    address: Vec<Option<i64>>,
    func: Vec<usize>,
}

#[derive(Deserialize)]
struct SamplyFuncTable {
    /// -1 or null for a function without a resource (kernel or unknown code).
    resource: Vec<Option<i64>>,
}

#[derive(Deserialize)]
struct SamplyResourceTable {
    lib: Vec<Option<i64>>,
}

/// Resolves the addresses of one binary to frames, innermost first.
pub trait Symbolizer {
    /// The frames at `address`, a relative address as `samply` records it (a return address is
    /// already reduced by one), innermost inlined frame first.
    fn frames(&mut self, address: u64) -> Result<Vec<StackFrame>, Error>;
}

/// A [`Symbolizer`] over the DWARF line tables of an executable.
pub struct DwarfSymbolizer {
    loader: addr2line::Loader,
    roots: Vec<PathBuf>,
}

impl DwarfSymbolizer {
    /// Load `binary`; workspace files are made relative to `root`.
    pub fn new(binary: &Path, root: &Path) -> Result<Self, Error> {
        let loader = addr2line::Loader::new(binary)
            .map_err(|error| Error::Invalid(format!("{}: {error}", binary.display())))?;
        Ok(Self {
            loader,
            roots: roots_of(root),
        })
    }
}

impl Symbolizer for DwarfSymbolizer {
    fn frames(&mut self, address: u64) -> Result<Vec<StackFrame>, Error> {
        let probe = address + self.loader.relative_address_base();
        let mut frames = Vec::new();
        let mut iterator = self
            .loader
            .find_frames(probe)
            .map_err(|error| Error::Invalid(format!("symbolizing {address:#x}: {error}")))?;
        while let Some(frame) = iterator
            .next()
            .map_err(|error| Error::Invalid(format!("symbolizing {address:#x}: {error}")))?
        {
            let function = frame
                .function
                .as_ref()
                .and_then(|function| function.raw_name().ok())
                .map(|name| plain_name(&format!("{:#}", rustc_demangle::demangle(&name))));
            let (file, line) = frame.location.as_ref().map_or((None, None), |location| {
                (
                    location.file.map(|file| source_name(file, &self.roots)),
                    location.line,
                )
            });
            frames.push(StackFrame {
                function: function.unwrap_or_else(|| "?".to_owned()),
                file,
                line,
            });
        }
        if frames.is_empty() {
            let symbol = self
                .loader
                .find_symbol(probe)
                .map(|name| plain_name(&format!("{:#}", rustc_demangle::demangle(name))));
            frames.push(StackFrame {
                function: symbol.unwrap_or_else(|| format!("{address:#x}")),
                file: None,
                line: None,
            });
        }
        Ok(frames)
    }
}

fn roots_of(root: &Path) -> Vec<PathBuf> {
    let mut roots = vec![root.to_owned()];
    if let Ok(canonical) = fs::canonicalize(root)
        && canonical != root
    {
        roots.push(canonical);
    }
    roots
}

/// A source path as a frame records it: workspace-relative when the file is a workspace source
/// below one of `roots`, or, for a binary built in another checkout, when its suffix from a
/// `crates/` component is a workspace source that exists below the first root.
fn source_name(path: &str, roots: &[PathBuf]) -> String {
    let absolute = Path::new(path);
    for root in roots {
        if let Ok(relative) = absolute.strip_prefix(root) {
            let relative = relative.to_string_lossy().replace('\\', "/");
            if is_workspace_source(&relative) {
                return relative;
            }
        }
    }
    let mut offset = 0;
    while let Some(found) = path[offset..].find("crates/") {
        let start = offset + found;
        let suffix = &path[start..];
        if (start == 0 || path.as_bytes()[start - 1] == b'/')
            && is_workspace_source(suffix)
            && roots
                .first()
                .is_some_and(|root| root.join(suffix).is_file())
        {
            return suffix.to_owned();
        }
        offset = start + 1;
    }
    for marker in ["/rustlib/src/rust/", "/rustc/"] {
        if let Some(found) = path.find(marker) {
            let rest = &path[found + marker.len()..];
            // `/rustc/<hash>/library/..` keeps the part from `library/`.
            return match rest.find("library/") {
                Some(library) => rest[library..].to_owned(),
                None => rest.to_owned(),
            };
        }
    }
    if let Some(found) = path.find("/registry/src/") {
        let rest = &path[found + "/registry/src/".len()..];
        if let Some(slash) = rest.find('/') {
            return rest[slash + 1..].to_owned();
        }
    }
    path.to_owned()
}

/// A function name without generic argument lists and crate hashes: every `<..>` group that
/// follows an identifier or `::` is removed; qualified paths such as `<T as Trait>::f` keep
/// their leading group.
pub(crate) fn plain_name(name: &str) -> String {
    let mut output = String::with_capacity(name.len());
    let mut depth = 0usize;
    let mut previous = None::<char>;
    let mut characters = name.chars().peekable();
    while let Some(character) = characters.next() {
        if depth > 0 {
            match character {
                '<' => depth += 1,
                '>' if previous == Some('-') => {}
                '>' => depth -= 1,
                _ => {}
            }
            previous = Some(character);
            continue;
        }
        if character == '<'
            && previous.is_some_and(|previous| previous.is_alphanumeric() || previous == '_')
        {
            depth = 1;
            previous = Some(character);
            continue;
        }
        if character == ':' && characters.peek() == Some(&':') {
            let mut lookahead = characters.clone();
            lookahead.next();
            if lookahead.peek() == Some(&'<') {
                characters.next();
                characters.next();
                depth = 1;
                previous = Some('<');
                continue;
            }
        }
        output.push(character);
        previous = Some(character);
    }
    output
}

/// Fold a `samply record` profile (`.json` or `.json.gz`) of `binary_name` into [`Stacks`].
///
/// Only the samples of threads with a frame in `binary_name` are kept, which drops the profiler's
/// own launcher thread. Frames of the binary are resolved by `symbolizer`; a run of consecutive
/// frames in another library is one frame named after the library.
pub fn fold_samply(
    profile: &Path,
    binary_name: &str,
    symbolizer: &mut dyn Symbolizer,
) -> Result<Stacks, Error> {
    let text = read_text(profile)?;
    fold_samply_json(&text, binary_name, symbolizer)
        .map_err(|error| Error::Invalid(format!("{}: {error}", profile.display())))
}

/// [`fold_samply`] over the profile's JSON text.
pub fn fold_samply_json(
    text: &str,
    binary_name: &str,
    symbolizer: &mut dyn Symbolizer,
) -> Result<Stacks, Error> {
    let profile: SamplyProfile = serde_json::from_str(text)?;
    let binary_lib = profile
        .libs
        .iter()
        .enumerate()
        .filter(|(_, lib)| lib.name == binary_name)
        .map(|(index, _)| index)
        .collect::<BTreeSet<_>>();
    if binary_lib.is_empty() {
        return Err(Error::Invalid(format!(
            "the profile has no library named {binary_name}; its libraries are {}",
            profile
                .libs
                .iter()
                .map(|lib| lib.name.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        )));
    }
    let mut frame_ids = HashMap::<StackFrame, u32>::new();
    let mut frames = Vec::<StackFrame>::new();
    let mut resolved = HashMap::<u64, Vec<u32>>::new();
    let mut folded = HashMap::<(Vec<u32>, bool), u64>::new();
    let mut truncated = 0u64;
    let mut intern = |frame: StackFrame, frames: &mut Vec<StackFrame>| -> u32 {
        *frame_ids.entry(frame.clone()).or_insert_with(|| {
            frames.push(frame);
            (frames.len() - 1) as u32
        })
    };
    for thread in &profile.threads {
        let lib_of_frame = |frame: usize| -> Option<usize> {
            let func = *thread.frame_table.func.get(frame)?;
            let resource = usize::try_from((*thread.func_table.resource.get(func)?)?).ok()?;
            usize::try_from((*thread.resource_table.lib.get(resource)?)?).ok()
        };
        // A stack's frames, outermost first, as symbolic frame ids, with whether it has a frame
        // of the binary and whether it is rooted; memoized per stack index.
        let mut by_stack = HashMap::<usize, (Vec<u32>, bool, bool)>::new();
        for (sample, stack) in thread.samples.stack.iter().enumerate() {
            let Some(stack) = *stack else { continue };
            let weight = thread
                .samples
                .weight
                .as_ref()
                .and_then(|weights| weights.get(sample).copied().flatten())
                .unwrap_or(1.0);
            let (symbolic, in_binary, rooted) = match by_stack.entry(stack) {
                std::collections::hash_map::Entry::Occupied(entry) => entry.into_mut(),
                std::collections::hash_map::Entry::Vacant(entry) => {
                    let mut chain = Vec::new();
                    let mut cursor = Some(stack);
                    while let Some(index) = cursor {
                        chain.push(thread.stack_table.frame[index]);
                        cursor = thread.stack_table.prefix[index];
                    }
                    chain.reverse();
                    let mut symbolic = Vec::new();
                    let mut in_binary = false;
                    let mut previous_lib = None;
                    for frame in &chain {
                        let lib = lib_of_frame(*frame);
                        if lib.is_some_and(|lib| binary_lib.contains(&lib)) {
                            in_binary = true;
                            previous_lib = None;
                            let address =
                                thread.frame_table.address[*frame].unwrap_or(0).max(0) as u64;
                            let ids = match resolved.get(&address) {
                                Some(ids) => ids.clone(),
                                None => {
                                    let mut ids = symbolizer
                                        .frames(address)?
                                        .into_iter()
                                        .map(|frame| intern(frame, &mut frames))
                                        .collect::<Vec<_>>();
                                    ids.reverse();
                                    resolved.insert(address, ids.clone());
                                    ids
                                }
                            };
                            symbolic.extend(ids);
                        } else {
                            if previous_lib == Some(lib) {
                                continue;
                            }
                            previous_lib = Some(lib);
                            let name = lib
                                .and_then(|lib| profile.libs.get(lib))
                                .map_or_else(|| "(unknown)".to_owned(), |lib| lib.name.clone());
                            symbolic.push(intern(
                                StackFrame {
                                    function: name.clone(),
                                    file: Some(name),
                                    line: None,
                                },
                                &mut frames,
                            ));
                        }
                    }
                    let rooted = chain.first().is_some_and(|frame| {
                        let lib = lib_of_frame(*frame);
                        !lib.is_some_and(|lib| binary_lib.contains(&lib))
                    }) || symbolic
                        .first()
                        .is_some_and(|frame| frames[*frame as usize].function == "_start");
                    entry.insert((symbolic, in_binary, rooted))
                }
            };
            if !*in_binary {
                continue;
            }
            let weight = weight.round().max(0.0) as u64;
            if !*rooted {
                truncated += weight;
            }
            *folded.entry((symbolic.clone(), !*rooted)).or_default() += weight;
        }
    }
    let mut stacks = Stacks {
        schema: STACKS_SCHEMA_VERSION,
        interval_ms: profile.meta.interval,
        binary: binary_name.to_owned(),
        truncated_samples: truncated,
        frames,
        stacks: folded
            .into_iter()
            .map(|((frames, truncated), samples)| SampledStack {
                samples,
                frames,
                truncated,
            })
            .collect(),
    };
    stacks.canonicalize();
    Ok(stacks)
}

/// Sampled shares of one algorithm.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct SampledAlgorithm {
    pub id: String,
    /// Samples whose innermost owned frame is the algorithm's.
    pub self_samples: u64,
    /// Samples with a frame the algorithm owns.
    pub total_samples: u64,
}

/// Samples of an uncarded function filed under one algorithm.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Under {
    /// The algorithm id, or [`NO_ALGORITHM`].
    pub id: String,
    pub samples: u64,
}

/// One uncarded function and its samples.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct UncardedFunction {
    /// `file::Type::method` or `file::function`.
    pub function: String,
    pub samples: u64,
    /// The algorithms its samples are filed under, most samples first.
    pub under: Vec<Under>,
}

/// The attribution of one profile, as `profile.toml` holds it.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct SampledProfile {
    pub schema: u32,
    pub rule: String,
    /// The stacks file the attribution read, relative to this file.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stacks: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub interval_ms: Option<f64>,
    pub samples: u64,
    pub truncated_samples: u64,
    /// Samples with an owning algorithm.
    pub owned_samples: u64,
    /// Samples whose innermost workspace frame no algorithm owns.
    pub uncarded_leaf_samples: u64,
    /// Samples without a workspace frame.
    pub outside_workspace_samples: u64,
    /// Samples whose owner was chosen among equal items of several algorithms.
    pub tied_samples: u64,
    /// Samples of truncated stacks without an owned frame.
    #[serde(default)]
    pub truncated_unowned_samples: u64,
    #[serde(rename = "algorithm", default)]
    pub algorithms: Vec<SampledAlgorithm>,
    /// Uncarded leaf functions by samples; at most 100, each with at least 0.1 % of the samples.
    #[serde(rename = "leaf", default)]
    pub leaves: Vec<UncardedFunction>,
    /// Uncarded functions by inclusive samples, cut like `leaf`.
    #[serde(rename = "inclusive", default)]
    pub inclusive: Vec<UncardedFunction>,
}

impl SampledProfile {
    /// `part` of the profile's samples, or 0 without samples.
    pub fn share(&self, part: u64) -> f64 {
        if self.samples == 0 {
            0.0
        } else {
            part as f64 / self.samples as f64
        }
    }

    /// The profile as TOML.
    pub fn toml(&self) -> Result<String, Error> {
        Ok(toml::to_string_pretty(self)?)
    }

    /// A compact text summary: the algorithm shares and the top `limit` rows of each table.
    pub fn text(&self, limit: usize) -> String {
        let percent = |samples: u64| format!("{:.1} %", 100.0 * self.share(samples));
        let mut out = String::new();
        let _ = writeln!(
            out,
            "{} samples{}; owned by an algorithm {}, uncarded leaf {}, outside the workspace {}, truncated stacks {} ({} without an owned frame)",
            self.samples,
            self.interval_ms
                .map(|interval| format!(" at {:.0} Hz", 1000.0 / interval))
                .unwrap_or_default(),
            percent(self.owned_samples),
            percent(self.uncarded_leaf_samples),
            percent(self.outside_workspace_samples),
            percent(self.truncated_samples),
            percent(self.truncated_unowned_samples)
        );
        let _ = writeln!(out, "\nalgorithm: self, total");
        let mut algorithms = self.algorithms.iter().collect::<Vec<_>>();
        algorithms.sort_by(|left, right| {
            right
                .self_samples
                .cmp(&left.self_samples)
                .then_with(|| left.id.cmp(&right.id))
        });
        for algorithm in algorithms.iter().take(limit) {
            let _ = writeln!(
                out,
                "  {}: {}, {}",
                algorithm.id,
                percent(algorithm.self_samples),
                percent(algorithm.total_samples)
            );
        }
        for (title, rows) in [
            ("uncarded leaf functions", &self.leaves),
            ("uncarded functions, inclusive", &self.inclusive),
        ] {
            let _ = writeln!(out, "\n{title}:");
            for row in rows.iter().take(limit) {
                let _ = writeln!(
                    out,
                    "  {} {} under {}",
                    percent(row.samples),
                    row.function,
                    under_text(row)
                );
            }
        }
        out
    }
}

/// `id (x %)` for the leading algorithms an uncarded function is filed under.
pub fn under_text(row: &UncardedFunction) -> String {
    let mut parts = row
        .under
        .iter()
        .take(2)
        .map(|under| {
            if row.under.len() == 1 {
                under.id.clone()
            } else {
                format!(
                    "{} ({:.0} %)",
                    under.id,
                    100.0 * under.samples as f64 / row.samples.max(1) as f64
                )
            }
        })
        .collect::<Vec<_>>();
    if row.under.len() > 2 {
        parts.push(format!("+{}", row.under.len() - 2));
    }
    parts.join(", ")
}

/// Read a `profile.toml` at the current schema.
pub fn read_profile(path: &Path) -> Result<SampledProfile, Error> {
    let at = |error: &dyn std::fmt::Display| Error::Invalid(format!("{}: {error}", path.display()));
    let profile: SampledProfile =
        toml::from_str(&fs::read_to_string(path).map_err(|error| at(&error))?)
            .map_err(|error| at(&error))?;
    if profile.schema != PROFILE_SCHEMA_VERSION {
        return Err(at(&format!(
            "profile schema {}, but this tool reads schema {PROFILE_SCHEMA_VERSION}; rerun `algo-graph profile`",
            profile.schema
        )));
    }
    Ok(profile)
}

/// Where a workspace frame falls: its owning algorithm and its enclosing item.
#[derive(Clone, Debug, Default)]
struct Placement {
    owner: Option<String>,
    tied: bool,
    /// `file::symbol` of the smallest code item containing the line.
    function: String,
}

/// The item spans of workspace files, read on first use.
struct Sources<'a> {
    root: &'a Path,
    spans: BTreeMap<String, Option<BTreeMap<String, Vec<ItemSpan>>>>,
}

impl Sources<'_> {
    fn spans(&mut self, file: &str) -> Option<&BTreeMap<String, Vec<ItemSpan>>> {
        self.spans
            .entry(file.to_owned())
            .or_insert_with(|| {
                let source = fs::read_to_string(self.root.join(file)).ok()?;
                item_spans(&source).ok()
            })
            .as_ref()
    }
}

/// Attribute `stacks` to the algorithms of `graph` by [`OWNERSHIP_RULE`], reading item spans from
/// the sources below `root`, which must be the sources the profiled binary was built from.
pub fn attribute(stacks: &Stacks, graph: &Graph, root: &Path) -> Result<SampledProfile, Error> {
    let mut sources = Sources {
        root,
        spans: BTreeMap::new(),
    };
    // Site ranges per file: (start, end, algorithm).
    let mut ranges = BTreeMap::<String, Vec<(usize, usize, String)>>::new();
    for node in graph.nodes.iter().filter(|node| node.kind == "algorithm") {
        let mut seen = BTreeSet::new();
        for site in &node.sites {
            if !seen.insert((&site.file, &site.symbol)) {
                continue;
            }
            let Some(spans) = sources.spans(&site.file) else {
                continue;
            };
            let items = spans.get(&site.symbol).cloned().unwrap_or_default();
            let code = items
                .iter()
                .filter(|item| item.code)
                .copied()
                .collect::<Vec<_>>();
            let chosen = if code.is_empty() {
                items
                    .iter()
                    .chain(
                        spans
                            .get(&format!("impl {}", site.symbol))
                            .map(Vec::as_slice)
                            .unwrap_or_default(),
                    )
                    .copied()
                    .collect()
            } else {
                code
            };
            let file_ranges = ranges.entry(site.file.clone()).or_default();
            for item in chosen {
                file_ranges.push((item.start, item.end, node.id.clone()));
            }
        }
    }
    for file_ranges in ranges.values_mut() {
        file_ranges.sort();
        file_ranges.dedup();
    }

    let mut placements = Vec::<Option<Placement>>::with_capacity(stacks.frames.len());
    for frame in &stacks.frames {
        let Some(file) = frame
            .file
            .as_deref()
            .filter(|file| is_workspace_source(file))
        else {
            placements.push(None);
            continue;
        };
        let line = frame.line.map(|line| line as usize);
        let mut placement = Placement {
            function: format!("{file}::{}", frame.function),
            ..Placement::default()
        };
        if let Some(line) = line {
            if let Some(file_ranges) = ranges.get(file) {
                let containing = file_ranges
                    .iter()
                    .filter(|(start, end, _)| *start <= line && line <= *end)
                    .collect::<Vec<_>>();
                if let Some(smallest) = containing.iter().map(|(start, end, _)| end - start).min() {
                    let owners = containing
                        .iter()
                        .filter(|(start, end, _)| end - start == smallest)
                        .map(|(_, _, id)| id)
                        .collect::<BTreeSet<_>>();
                    placement.tied = owners.len() > 1;
                    placement.owner = owners.first().map(|id| (*id).clone());
                }
            }
            if let Some(spans) = sources.spans(file) {
                // The smallest code item containing the line; else the smallest type, whose
                // lines hold derived code, with the frame's function.
                if let Some((symbol, item)) = spans
                    .iter()
                    .flat_map(|(symbol, items)| items.iter().map(move |item| (symbol, item)))
                    .filter(|(_, item)| item.start <= line && line <= item.end)
                    .min_by_key(|(symbol, item)| {
                        (!item.code, item.end - item.start, (*symbol).clone())
                    })
                {
                    placement.function = if item.code {
                        format!("{file}::{symbol}")
                    } else {
                        format!("{file}::{symbol}::{}", frame.function)
                    };
                }
            }
        }
        placements.push(Some(placement));
    }

    let mut self_samples = BTreeMap::<String, u64>::new();
    let mut total_samples = BTreeMap::<String, u64>::new();
    let mut leaves = BTreeMap::<String, BTreeMap<String, u64>>::new();
    let mut inclusive = BTreeMap::<String, BTreeMap<String, u64>>::new();
    let mut owned = 0;
    let mut uncarded_leaf = 0;
    let mut outside = 0;
    let mut tied = 0;
    let mut truncated_unowned = 0;
    for stack in &stacks.stacks {
        let weight = stack.samples;
        let workspace = stack
            .frames
            .iter()
            .filter_map(|frame| placements[*frame as usize].as_ref())
            .collect::<Vec<_>>();
        let Some(innermost) = workspace.last() else {
            outside += weight;
            continue;
        };
        let owner = workspace.iter().rev().find(|frame| frame.owner.is_some());
        let owner_id = owner.and_then(|frame| frame.owner.clone());
        if let Some(frame) = owner {
            owned += weight;
            if frame.tied {
                tied += weight;
            }
        }
        if let Some(id) = &owner_id {
            *self_samples.entry(id.clone()).or_default() += weight;
        }
        for id in workspace
            .iter()
            .filter_map(|frame| frame.owner.as_ref())
            .collect::<BTreeSet<_>>()
        {
            *total_samples.entry(id.clone()).or_default() += weight;
        }
        if owner_id.is_none() && stack.truncated {
            truncated_unowned += weight;
        }
        let under = owner_id.unwrap_or_else(|| {
            if stack.truncated {
                TRUNCATED_STACK
            } else {
                NO_ALGORITHM
            }
            .to_owned()
        });
        if innermost.owner.is_none() {
            uncarded_leaf += weight;
            *leaves
                .entry(innermost.function.clone())
                .or_default()
                .entry(under.clone())
                .or_default() += weight;
        }
        // The uncarded tail: the workspace frames inside the innermost owned frame, each
        // function once.
        let tail = workspace
            .iter()
            .rposition(|frame| frame.owner.is_some())
            .map_or(0, |position| position + 1);
        for function in workspace[tail..]
            .iter()
            .map(|frame| frame.function.as_str())
            .collect::<BTreeSet<_>>()
        {
            *inclusive
                .entry(function.to_owned())
                .or_default()
                .entry(under.clone())
                .or_default() += weight;
        }
    }
    let samples = stacks.samples();
    let rows = |table: BTreeMap<String, BTreeMap<String, u64>>| {
        let mut rows = table
            .into_iter()
            .map(|(function, under)| {
                let mut under = under
                    .into_iter()
                    .map(|(id, samples)| Under { id, samples })
                    .collect::<Vec<_>>();
                under.sort_by(|left, right| {
                    right
                        .samples
                        .cmp(&left.samples)
                        .then_with(|| left.id.cmp(&right.id))
                });
                UncardedFunction {
                    samples: under.iter().map(|under| under.samples).sum(),
                    function,
                    under,
                }
            })
            .filter(|row| row.samples * 1000 >= samples && row.samples > 0)
            .collect::<Vec<_>>();
        rows.sort_by(|left, right| {
            right
                .samples
                .cmp(&left.samples)
                .then_with(|| left.function.cmp(&right.function))
        });
        rows.truncate(KEPT_ROWS);
        rows
    };
    Ok(SampledProfile {
        schema: PROFILE_SCHEMA_VERSION,
        rule: OWNERSHIP_RULE.to_owned(),
        stacks: None,
        interval_ms: stacks.interval_ms,
        samples,
        truncated_samples: stacks.truncated_samples,
        owned_samples: owned,
        uncarded_leaf_samples: uncarded_leaf,
        outside_workspace_samples: outside,
        tied_samples: tied,
        truncated_unowned_samples: truncated_unowned,
        algorithms: total_samples
            .into_iter()
            .map(|(id, total)| SampledAlgorithm {
                self_samples: self_samples.get(&id).copied().unwrap_or(0),
                total_samples: total,
                id,
            })
            .collect(),
        leaves: rows(leaves),
        inclusive: rows(inclusive),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Anchor, Node};

    /// A two-file workspace: `alg.rs` holds the carded `run` and `Walker::step`, `helper.rs`
    /// holds the uncarded `walk` (recursive) and `leaf`.
    fn workspace() -> PathBuf {
        let root = std::env::temp_dir().join(format!(
            "algo-graph-profile-test-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let source = root.join("crates/demo/src");
        fs::create_dir_all(&source).unwrap();
        fs::write(
            source.join("alg.rs"),
            "pub fn run() {\n    walk();\n}\n\npub struct Walker;\n\nimpl Walker {\n    pub fn step(&self) {\n        leaf();\n    }\n}\n",
        )
        .unwrap();
        fs::write(
            source.join("helper.rs"),
            "pub fn walk() {\n    walk();\n    leaf();\n}\n\npub fn leaf() {\n    let _ = 1;\n}\n",
        )
        .unwrap();
        root
    }

    fn algorithm(id: &str, sites: &[(&str, &str)]) -> Node {
        let anchor = |file: &str, symbol: &str| Anchor {
            crate_name: "demo".to_owned(),
            file: file.to_owned(),
            symbol: symbol.to_owned(),
        };
        Node {
            kind: "algorithm".to_owned(),
            id: id.to_owned(),
            provenance: "declared".to_owned(),
            anchor: anchor(sites[0].0, sites[0].1),
            area: None,
            name: None,
            sites: sites
                .iter()
                .map(|(file, symbol)| anchor(file, symbol))
                .collect(),
            cost: Vec::new(),
            variable: None,
            invariant: None,
            no_counter: None,
            span: None,
            table: None,
            call: None,
            behavior: None,
            generating_passes: Vec::new(),
            type_path: None,
            role: None,
            registry_name: None,
            sequence: None,
        }
    }

    fn frame(function: &str, file: &str, line: u32) -> StackFrame {
        StackFrame {
            function: function.to_owned(),
            file: Some(file.to_owned()),
            line: Some(line),
        }
    }

    /// The fixture profile: frames 0..=5 and four stacks.
    fn fixture() -> Stacks {
        let alg = "crates/demo/src/alg.rs";
        let helper = "crates/demo/src/helper.rs";
        Stacks {
            schema: STACKS_SCHEMA_VERSION,
            interval_ms: Some(1.0),
            binary: "demo".to_owned(),
            truncated_samples: 0,
            frames: vec![
                frame("_start", "library/std/src/rt.rs", 1),
                frame("run", alg, 2),
                frame("walk", helper, 2),
                frame("walk", helper, 3),
                frame("leaf", helper, 7),
                frame("step", alg, 9),
                StackFrame {
                    function: "memcpy".to_owned(),
                    file: Some("libc.so.6".to_owned()),
                    line: None,
                },
            ],
            stacks: vec![
                // run -> walk -> walk -> leaf: uncarded leaf `leaf` under a.run, walk inclusive.
                SampledStack {
                    samples: 5,
                    frames: vec![0, 1, 2, 3, 4],
                    truncated: false,
                },
                // run -> walk (self in walk).
                SampledStack {
                    samples: 3,
                    frames: vec![0, 1, 2],
                    truncated: false,
                },
                // run -> Walker::step -> leaf -> memcpy: leaf under b.step.
                SampledStack {
                    samples: 2,
                    frames: vec![0, 1, 5, 4, 6],
                    truncated: false,
                },
                // No workspace frame.
                SampledStack {
                    samples: 1,
                    frames: vec![0, 6],
                    truncated: false,
                },
                // run itself.
                SampledStack {
                    samples: 4,
                    frames: vec![0, 1],
                    truncated: false,
                },
            ],
        }
    }

    fn graph() -> Graph {
        Graph {
            nodes: vec![
                algorithm("a.run", &[("crates/demo/src/alg.rs", "run")]),
                algorithm("b.step", &[("crates/demo/src/alg.rs", "Walker")]),
            ],
            edges: Vec::new(),
        }
    }

    #[test]
    fn attribution_follows_the_ownership_rule() {
        let root = workspace();
        let profile = attribute(&fixture(), &graph(), &root).unwrap();
        fs::remove_dir_all(&root).unwrap();
        assert_eq!(profile.samples, 15);
        assert_eq!(profile.owned_samples, 14);
        assert_eq!(profile.outside_workspace_samples, 1);
        assert_eq!(profile.uncarded_leaf_samples, 10);
        let algorithms = profile
            .algorithms
            .iter()
            .map(|row| (row.id.as_str(), row.self_samples, row.total_samples))
            .collect::<Vec<_>>();
        // b.step names the type Walker, so the impl block's method is its code.
        assert_eq!(algorithms, vec![("a.run", 12, 14), ("b.step", 2, 2)]);
        let leaves = profile
            .leaves
            .iter()
            .map(|row| (row.function.as_str(), row.samples, under_text(row)))
            .collect::<Vec<_>>();
        assert_eq!(
            leaves,
            vec![
                (
                    "crates/demo/src/helper.rs::leaf",
                    7,
                    "a.run (71 %), b.step (29 %)".to_owned()
                ),
                ("crates/demo/src/helper.rs::walk", 3, "a.run".to_owned()),
            ]
        );
        // The recursive walk counts once per sample.
        let inclusive = profile
            .inclusive
            .iter()
            .map(|row| (row.function.as_str(), row.samples))
            .collect::<Vec<_>>();
        assert_eq!(
            inclusive,
            vec![
                ("crates/demo/src/helper.rs::walk", 8),
                ("crates/demo/src/helper.rs::leaf", 7),
            ]
        );
    }

    #[test]
    fn a_driver_counts_only_samples_without_an_algorithm_inside() {
        let root = workspace();
        let mut stacks = fixture();
        // helper.rs::walk calls the carded run: walk -> run (a.run inside), and walk alone.
        stacks.stacks = vec![
            SampledStack {
                samples: 6,
                frames: vec![0, 2, 1],
                truncated: false,
            },
            SampledStack {
                samples: 2,
                frames: vec![0, 2],
                truncated: false,
            },
            // A truncated stack without an owned frame: its owner may be missing.
            SampledStack {
                samples: 2,
                frames: vec![2],
                truncated: true,
            },
        ];
        let profile = attribute(&stacks, &graph(), &root).unwrap();
        fs::remove_dir_all(&root).unwrap();
        let inclusive = profile
            .inclusive
            .iter()
            .map(|row| (row.function.as_str(), row.samples, under_text(row)))
            .collect::<Vec<_>>();
        assert_eq!(
            inclusive,
            vec![(
                "crates/demo/src/helper.rs::walk",
                4,
                format!("{NO_ALGORITHM} (50 %), {TRUNCATED_STACK} (50 %)")
            )]
        );
        assert_eq!(profile.truncated_unowned_samples, 2);
        assert_eq!(profile.algorithms[0].self_samples, 6);
    }

    #[test]
    fn stacks_round_trip_through_json() {
        let mut stacks = fixture();
        stacks.canonicalize();
        for extension in ["json", "json.gz"] {
            let path = std::env::temp_dir().join(format!(
                "algo-graph-stacks-{}-{:?}.{extension}",
                std::process::id(),
                std::thread::current().id()
            ));
            write_stacks(&path, &stacks).unwrap();
            let read = read_stacks(&path).unwrap();
            fs::remove_file(&path).unwrap();
            assert_eq!(read, stacks);
        }
        let read = stacks.clone();
        assert_eq!(read.samples(), 15);
    }

    struct Table(BTreeMap<u64, Vec<StackFrame>>);

    impl Symbolizer for Table {
        fn frames(&mut self, address: u64) -> Result<Vec<StackFrame>, Error> {
            Ok(self.0.get(&address).cloned().unwrap_or_default())
        }
    }

    #[test]
    fn samply_stacks_expand_inlined_frames_and_fold() {
        // Thread 0 is the launcher (libc only); thread 1 runs the binary. Stack 2 is
        // libc -> 0x10 -> 0x20, and 0x20 holds an inlined call.
        let profile = r#"{
          "meta": {"interval": 0.5},
          "libs": [{"name": "libc.so.6"}, {"name": "demo"}],
          "threads": [
            {"samples": {"stack": [0], "weight": [1]},
             "stackTable": {"prefix": [null], "frame": [0]},
             "frameTable": {"address": [7], "func": [0]},
             "funcTable": {"resource": [0]},
             "resourceTable": {"lib": [0]}},
            {"samples": {"stack": [2, 2, 1, null, 3], "weight": null},
             "stackTable": {"prefix": [null, 0, 1, null], "frame": [0, 1, 2, 3]},
             "frameTable": {"address": [7, 16, 32, 48], "func": [0, 1, 1, 1]},
             "funcTable": {"resource": [0, 1]},
             "resourceTable": {"lib": [0, 1]}}
          ]
        }"#;
        let mut table = Table(BTreeMap::from([
            (16, vec![frame("run", "crates/demo/src/alg.rs", 2)]),
            (
                32,
                vec![
                    frame("leaf", "crates/demo/src/helper.rs", 7),
                    frame("walk", "crates/demo/src/helper.rs", 3),
                ],
            ),
            (48, vec![frame("walk", "crates/demo/src/helper.rs", 2)]),
        ]));
        let stacks = fold_samply_json(profile, "demo", &mut table).unwrap();
        let named = stacks
            .stacks
            .iter()
            .map(|stack| {
                (
                    stack
                        .frames
                        .iter()
                        .map(|frame| stacks.frames[*frame as usize].function.as_str())
                        .collect::<Vec<_>>(),
                    stack.samples,
                    stack.truncated,
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            named,
            vec![
                (vec!["libc.so.6", "run"], 1, false),
                (vec!["libc.so.6", "run", "walk", "leaf"], 2, false),
                (vec!["walk"], 1, true),
            ]
        );
        // The lone `walk` stack starts inside the binary without `_start`: truncated.
        assert_eq!(stacks.truncated_samples, 1);
        assert_eq!(stacks.interval_ms, Some(0.5));
    }

    #[test]
    fn names_lose_generic_arguments() {
        assert_eq!(
            plain_name("drop_in_place<[k_rust::Sentence]>"),
            "drop_in_place"
        );
        assert_eq!(
            plain_name("core::ptr::drop_glue::<k_rust::Definition>"),
            "core::ptr::drop_glue"
        );
        assert_eq!(
            plain_name("<k_rust::Sentence as core::cmp::PartialEq>::eq"),
            "<k_rust::Sentence as core::cmp::PartialEq>::eq"
        );
        assert_eq!(plain_name("map<u8, fn() -> u8>"), "map");
    }

    #[test]
    fn source_names_are_workspace_relative_or_shortened() {
        let roots = vec![PathBuf::from("/work/k-rust")];
        assert_eq!(
            source_name("/work/k-rust/crates/demo/src/alg.rs", &roots),
            "crates/demo/src/alg.rs"
        );
        assert_eq!(
            source_name(
                "/home/u/.rustup/toolchains/stable/lib/rustlib/src/rust/library/core/src/ptr/mod.rs",
                &roots
            ),
            "library/core/src/ptr/mod.rs"
        );
        assert_eq!(
            source_name(
                "/home/u/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/hashbrown-0.15.2/src/raw/mod.rs",
                &roots
            ),
            "hashbrown-0.15.2/src/raw/mod.rs"
        );
        // Another checkout's path is kept when its workspace suffix is not below the root.
        assert_eq!(
            source_name("/elsewhere/crates/demo/src/alg.rs", &roots),
            "/elsewhere/crates/demo/src/alg.rs"
        );
    }
}
