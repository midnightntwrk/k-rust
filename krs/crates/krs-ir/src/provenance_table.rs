//! The provenance tables of a serialized KRS artifact.
//!
//! Every node of a descriptor bundle, a Semantic IR, a Definition IR and a
//! source map carries an [`OriginStack`], and nearly every frame of a stack
//! repeats a frame of another node: the item's macro-invocation frame, the
//! transformation frame of a role, the file's identity in each range. An
//! artifact root therefore writes its provenance once, in a `provenance`
//! object placed after its version field and before its body:
//!
//! - `packages`: each [`crate::PackageId`] a file or item names;
//! - `files`: each [`crate::SourceFileId`], its package as an index;
//! - `items`: each [`crate::StableItemId`] a frame names, its package as an index;
//! - `labels`: each frame label;
//! - `frames`: each distinct [`OriginFrame`], as a tuple whose first element is
//!   the frame's kind code: `[code, file, start, end, item, label]` for a
//!   ranged frame (codes 0-3), `[code, item, label]` for a transformation
//!   (codes 4-6), and `[7, kind]` or `[7, kind, file, start, end]` for an
//!   inserted frame without or with its anchor. `item` and `label` are an
//!   index or `null`.
//!
//! Within the body an origin stack is the array of its frames' indexes. Each
//! table lists its rows in the order the body first reaches them, so the
//! encoding of a canonical value is canonical, and every artifact is
//! self-contained: a reader needs no other file. Nothing is dropped: decoding
//! yields the same in-memory value, which keeps every frame of every stack.
//!
//! The tables belong to the artifact root. An [`OriginStack`] serialized on
//! its own, outside any root, has no table to refer to and is written as the
//! array of its frames.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::io;
use std::marker::PhantomData;
use std::rc::Rc;

use serde::de::value::MapAccessDeserializer;
use serde::de::{
    DeserializeSeed, Error as _, IgnoredAny, IntoDeserializer, MapAccess, SeqAccess, Visitor,
};
use serde::ser::{Error as _, SerializeStruct, SerializeTuple};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::provenance::{FrameKind, INSERTED_FRAME_CODE};
use crate::{
    InsertedNode, ItemKind, OriginFrame, PackageId, Sha256Digest, SourceFileId, SourceRange,
    SourceRangeError, StableItemId,
};

/// The field of an artifact root that holds its provenance tables.
pub const PROVENANCE_FIELD: &str = "provenance";

/// A serialized KRS artifact whose origin stacks refer to its provenance tables.
pub trait ArtifactRoot {
    /// The root's serde name.
    const NAME: &'static str;
    /// The field that holds the root's version, written first.
    const VERSION_FIELD: &'static str;
    /// The number of fields [`Self::serialize_body`] writes or skips.
    const BODY_FIELDS: usize;
    /// The type of the version field.
    type Version: Serialize + ?Sized;

    /// Returns the root's version.
    fn version(&self) -> &Self::Version;

    /// Writes every field of the root after its version and its tables, in order.
    ///
    /// # Errors
    ///
    /// Returns the serializer's error.
    fn serialize_body<M: SerializeStruct>(&self, fields: &mut M) -> Result<(), M::Error>;

    /// Rejects a version this release does not read, before the rest of the
    /// document is decoded.
    ///
    /// # Errors
    ///
    /// Returns the root's own message for an unsupported version.
    fn check_version(version: &serde_json::Value) -> Result<(), String>;
}

/// Writes `root` as `{version, provenance, body...}`.
///
/// The body is serialized twice: once into a sink, which interns every frame
/// in the order the body reaches it, and once into `serializer`, after the
/// tables, with each stack written as its frames' indexes.
///
/// # Errors
///
/// Returns the serializer's error, or an error if a frame of the second pass
/// is missing from the tables the first pass built.
pub fn serialize_root<R: ArtifactRoot + ?Sized, S: Serializer>(
    root: &R,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    #[cfg(any(test, feature = "test-support"))]
    if matches!(current(), Some(Scope::Inline)) {
        let mut fields = serializer.serialize_struct(R::NAME, 1 + R::BODY_FIELDS)?;
        fields.serialize_field(R::VERSION_FIELD, root.version())?;
        root.serialize_body(&mut fields)?;
        return fields.end();
    }
    let collecting = Rc::new(RefCell::new(Interner::default()));
    {
        let _scope = enter(Some(Scope::Collect(Rc::clone(&collecting))));
        serde_json::to_writer(io::sink(), &Body(root)).map_err(S::Error::custom)?;
    }
    let interned = Rc::new(
        Rc::into_inner(collecting)
            .ok_or_else(|| S::Error::custom("provenance interner is still shared"))?
            .into_inner(),
    );
    let mut fields = serializer.serialize_struct(R::NAME, 2 + R::BODY_FIELDS)?;
    fields.serialize_field(R::VERSION_FIELD, root.version())?;
    fields.serialize_field(PROVENANCE_FIELD, &TablesRef::new(&interned.frames))?;
    let _scope = enter(Some(Scope::Write(interned)));
    root.serialize_body(&mut fields)?;
    fields.end()
}

/// Reads an artifact root into `W`, the root's field-for-field wire form.
///
/// The version field is checked before anything is decoded against the
/// tables, and the tables are installed once both are read; every field
/// after them is decoded against them. A field read before that point,
/// the tables among them, is buffered and decoded afterwards, so a document
/// whose keys were reordered (a `serde_json::Value` orders its keys) reads
/// the same, and an unsupported version is refused as such however the
/// tables of that version are shaped.
///
/// # Errors
///
/// Returns an error for an unsupported version, a missing or invalid table, a
/// frame index outside the table, or an invalid body.
pub fn deserialize_root<'de, R, W, D>(deserializer: D) -> Result<W, D::Error>
where
    R: ArtifactRoot + ?Sized,
    W: Deserialize<'de>,
    D: Deserializer<'de>,
{
    deserializer.deserialize_map(RootVisitor::<R, W>(PhantomData, PhantomData))
}

/// Runs `body` with artifact roots read and written without provenance
/// tables, their stacks as arrays of frames. Tests use it to state an artifact
/// by hand and to compare a decoded artifact with an encoding that inlines
/// its frames. The mode belongs to the calling thread, so it does not reach
/// [`crate::json::from_slice`], which decodes on a thread of its own.
#[cfg(any(test, feature = "test-support"))]
pub fn with_inline_provenance<T>(body: impl FnOnce() -> T) -> T {
    let _scope = enter(Some(Scope::Inline));
    body()
}

pub(crate) fn serialize_stack<S: Serializer>(
    frames: &[OriginFrame],
    serializer: S,
) -> Result<S::Ok, S::Error> {
    match current() {
        Some(Scope::Collect(interner)) => {
            let mut interner = interner.borrow_mut();
            let indexes = frames
                .iter()
                .map(|frame| interner.intern(frame))
                .collect::<Result<Vec<_>, _>>()
                .map_err(S::Error::custom)?;
            indexes.serialize(serializer)
        }
        Some(Scope::Write(interned)) => frames
            .iter()
            .map(|frame| {
                interned.indexes.get(frame).copied().ok_or_else(|| {
                    S::Error::custom("origin frame is missing from the artifact's frame table")
                })
            })
            .collect::<Result<Vec<_>, _>>()?
            .serialize(serializer),
        _ => frames.serialize(serializer),
    }
}

pub(crate) fn deserialize_stack<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Vec<OriginFrame>, D::Error> {
    if let Some(Scope::Read(table)) = current() {
        Vec::<u32>::deserialize(deserializer)?
            .into_iter()
            .map(|index| {
                table
                    .get(index as usize)
                    .cloned()
                    .ok_or_else(|| D::Error::custom(format!("invalid frame index {index}")))
            })
            .collect()
    } else {
        Vec::<OriginFrame>::deserialize(deserializer)
    }
}

#[derive(Clone)]
enum Scope {
    Collect(Rc<RefCell<Interner>>),
    Write(Rc<Interner>),
    Read(Rc<Vec<OriginFrame>>),
    #[cfg(any(test, feature = "test-support"))]
    Inline,
}

thread_local! {
    static SCOPE: RefCell<Option<Scope>> = const { RefCell::new(None) };
}

/// Restores the enclosing scope when dropped.
struct Entered(Option<Scope>);

fn enter(scope: Option<Scope>) -> Entered {
    Entered(SCOPE.with(|cell| cell.replace(scope)))
}

impl Drop for Entered {
    fn drop(&mut self) {
        let enclosing = self.0.take();
        SCOPE.with(|cell| *cell.borrow_mut() = enclosing);
    }
}

fn current() -> Option<Scope> {
    SCOPE.with(|cell| cell.borrow().clone())
}

#[derive(Default)]
struct Interner {
    frames: Vec<OriginFrame>,
    indexes: HashMap<OriginFrame, u32>,
}

impl Interner {
    /// Interns `frame`, refusing a reversed range, which the reader refuses:
    /// a written artifact is always one the reader reads back.
    fn intern(&mut self, frame: &OriginFrame) -> Result<u32, String> {
        if let Some(index) = self.indexes.get(frame) {
            return Ok(*index);
        }
        let range = match frame {
            OriginFrame::Ranged { range, .. } => Some(range),
            OriginFrame::Inserted { anchor, .. } => anchor.as_ref(),
            OriginFrame::Transformation { .. } => None,
        };
        if let Some(range) = range
            && range.start_byte > range.end_byte
        {
            return Err(SourceRangeError {
                start_byte: range.start_byte,
                end_byte: range.end_byte,
            }
            .to_string());
        }
        let index = u32::try_from(self.frames.len()).map_err(|_| {
            "an artifact holds more distinct origin frames than u32 indexes".to_owned()
        })?;
        self.frames.push(frame.clone());
        self.indexes.insert(frame.clone(), index);
        Ok(index)
    }
}

/// A root's body fields alone, which the first pass interns from.
struct Body<'a, R: ?Sized>(&'a R);

impl<R: ArtifactRoot + ?Sized> Serialize for Body<'_, R> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut fields = serializer.serialize_struct(R::NAME, R::BODY_FIELDS)?;
        self.0.serialize_body(&mut fields)?;
        fields.end()
    }
}

/// Interns borrowed rows in first-reached order.
struct Rows<'a, T: ?Sized> {
    rows: Vec<&'a T>,
    indexes: HashMap<&'a T, u32>,
}

impl<'a, T: ?Sized + Eq + std::hash::Hash> Rows<'a, T> {
    fn new() -> Self {
        Self {
            rows: Vec::new(),
            indexes: HashMap::new(),
        }
    }

    fn intern(&mut self, row: &'a T) -> u32 {
        if let Some(index) = self.indexes.get(row) {
            return *index;
        }
        // The frame table is bounded by `u32`, and each frame adds at most one row here.
        let index = u32::try_from(self.rows.len()).expect("table rows are bounded by frames");
        self.rows.push(row);
        self.indexes.insert(row, index);
        index
    }
}

#[derive(Serialize)]
struct FileRow<'a> {
    package: u32,
    package_relative_path: &'a str,
    content_sha256: &'a Sha256Digest,
}

#[derive(Serialize)]
struct ItemRow<'a> {
    package: u32,
    module_path: &'a [String],
    item_name: &'a str,
    item_kind: ItemKind,
    disambiguator: &'a str,
}

enum FrameRow<'a> {
    Ranged([Option<u32>; 6]),
    Transformation([Option<u32>; 3]),
    Inserted(&'a InsertedNode, Option<[u32; 3]>),
}

impl Serialize for FrameRow<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Ranged(fields) => fields.serialize(serializer),
            Self::Transformation(fields) => fields.serialize(serializer),
            Self::Inserted(kind, anchor) => {
                let mut tuple = serializer.serialize_tuple(if anchor.is_some() { 5 } else { 2 })?;
                tuple.serialize_element(&INSERTED_FRAME_CODE)?;
                tuple.serialize_element(kind)?;
                if let Some(anchor) = anchor {
                    for field in anchor {
                        tuple.serialize_element(field)?;
                    }
                }
                tuple.end()
            }
        }
    }
}

/// The tables of one artifact, borrowed from its interned frames.
#[derive(Serialize)]
#[serde(rename = "ProvenanceTables")]
struct TablesRef<'a> {
    packages: Vec<&'a PackageId>,
    files: Vec<FileRow<'a>>,
    items: Vec<ItemRow<'a>>,
    labels: Vec<&'a str>,
    frames: Vec<FrameRow<'a>>,
}

/// Builds the identity tables while walking the frame table.
struct TableBuilder<'a> {
    packages: Rows<'a, PackageId>,
    files: Rows<'a, SourceFileId>,
    items: Rows<'a, StableItemId>,
    labels: Rows<'a, str>,
    file_rows: Vec<FileRow<'a>>,
    item_rows: Vec<ItemRow<'a>>,
}

impl<'a> TableBuilder<'a> {
    fn file(&mut self, file: &'a SourceFileId) -> u32 {
        let known = self.files.rows.len();
        let index = self.files.intern(file);
        if self.files.rows.len() > known {
            self.file_rows.push(FileRow {
                package: self.packages.intern(file.package()),
                package_relative_path: file.package_relative_path(),
                content_sha256: file.content_sha256(),
            });
        }
        index
    }

    fn item(&mut self, item: &'a StableItemId) -> u32 {
        let known = self.items.rows.len();
        let index = self.items.intern(item);
        if self.items.rows.len() > known {
            self.item_rows.push(ItemRow {
                package: self.packages.intern(item.package()),
                module_path: item.module_path(),
                item_name: item.item_name(),
                item_kind: item.item_kind(),
                disambiguator: item.disambiguator(),
            });
        }
        index
    }

    fn label(&mut self, label: Option<&'a String>) -> Option<u32> {
        label.map(|label| self.labels.intern(label.as_str()))
    }
}

impl<'a> TablesRef<'a> {
    fn new(frames: &'a [OriginFrame]) -> Self {
        let mut tables = TableBuilder {
            packages: Rows::new(),
            files: Rows::new(),
            items: Rows::new(),
            labels: Rows::new(),
            file_rows: Vec::new(),
            item_rows: Vec::new(),
        };
        let rows = frames
            .iter()
            .map(|frame| match frame {
                OriginFrame::Ranged {
                    kind,
                    range,
                    item,
                    label,
                } => FrameRow::Ranged([
                    Some(u32::from(kind.code())),
                    Some(tables.file(&range.file)),
                    Some(range.start_byte),
                    Some(range.end_byte),
                    item.as_ref().map(|item| tables.item(item)),
                    tables.label(label.as_ref()),
                ]),
                OriginFrame::Transformation { kind, item, label } => FrameRow::Transformation([
                    Some(u32::from(kind.code())),
                    item.as_ref().map(|item| tables.item(item)),
                    tables.label(label.as_ref()),
                ]),
                OriginFrame::Inserted { kind, anchor } => FrameRow::Inserted(
                    kind,
                    anchor
                        .as_ref()
                        .map(|range| [tables.file(&range.file), range.start_byte, range.end_byte]),
                ),
            })
            .collect();
        Self {
            packages: tables.packages.rows,
            files: tables.file_rows,
            items: tables.item_rows,
            labels: tables.labels.rows,
            frames: rows,
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct FileWire {
    package: u32,
    package_relative_path: String,
    content_sha256: Sha256Digest,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ItemWire {
    package: u32,
    module_path: Vec<String>,
    item_name: String,
    item_kind: ItemKind,
    disambiguator: String,
}

enum FrameWire {
    Ranged(u8, u32, u32, u32, Option<u32>, Option<u32>),
    Transformation(u8, Option<u32>, Option<u32>),
    Inserted(InsertedNode, Option<(u32, u32, u32)>),
}

impl<'de> Deserialize<'de> for FrameWire {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct FrameVisitor;

        fn next<'de, T: Deserialize<'de>, A: SeqAccess<'de>>(
            sequence: &mut A,
            position: usize,
        ) -> Result<T, A::Error> {
            sequence
                .next_element()?
                .ok_or_else(|| A::Error::invalid_length(position, &FrameVisitor))
        }

        impl<'de> Visitor<'de> for FrameVisitor {
            type Value = FrameWire;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a provenance frame array")
            }

            fn visit_seq<A: SeqAccess<'de>>(
                self,
                mut sequence: A,
            ) -> Result<Self::Value, A::Error> {
                let code: u8 = next(&mut sequence, 0)?;
                let frame = if code == INSERTED_FRAME_CODE {
                    let kind = next(&mut sequence, 1)?;
                    let anchor = match sequence.next_element::<u32>()? {
                        None => None,
                        Some(file) => {
                            Some((file, next(&mut sequence, 3)?, next(&mut sequence, 4)?))
                        }
                    };
                    FrameWire::Inserted(kind, anchor)
                } else {
                    match FrameKind::from_code(code) {
                        Some(FrameKind::Ranged(_)) => FrameWire::Ranged(
                            code,
                            next(&mut sequence, 1)?,
                            next(&mut sequence, 2)?,
                            next(&mut sequence, 3)?,
                            next(&mut sequence, 4)?,
                            next(&mut sequence, 5)?,
                        ),
                        Some(FrameKind::Transformation(_)) => FrameWire::Transformation(
                            code,
                            next(&mut sequence, 1)?,
                            next(&mut sequence, 2)?,
                        ),
                        None => {
                            return Err(A::Error::custom(format!(
                                "unknown provenance frame code {code}"
                            )));
                        }
                    }
                };
                if sequence.next_element::<IgnoredAny>()?.is_some() {
                    return Err(A::Error::custom("provenance frame has extra fields"));
                }
                Ok(frame)
            }
        }

        deserializer.deserialize_seq(FrameVisitor)
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TablesWire {
    packages: Vec<PackageId>,
    files: Vec<FileWire>,
    items: Vec<ItemWire>,
    labels: Vec<String>,
    frames: Vec<FrameWire>,
}

/// The frame table of one artifact, each frame resolved against the identity tables.
struct ReadTables(Vec<OriginFrame>);

fn at<'t, T>(table: &'t [T], index: u32, what: &str) -> Result<&'t T, String> {
    table
        .get(index as usize)
        .ok_or_else(|| format!("invalid {what} index {index}"))
}

impl TablesWire {
    fn resolve(self) -> Result<ReadTables, String> {
        let files = self
            .files
            .into_iter()
            .map(|file| {
                SourceFileId::new(
                    at(&self.packages, file.package, "package")?.clone(),
                    file.package_relative_path,
                    file.content_sha256,
                )
                .map_err(|error| error.to_string())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let items = self
            .items
            .into_iter()
            .map(|item| {
                StableItemId::new(
                    at(&self.packages, item.package, "package")?.clone(),
                    item.module_path,
                    item.item_name,
                    item.item_kind,
                    item.disambiguator,
                )
                .map_err(|error| error.to_string())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let item = |index: Option<u32>| {
            index
                .map(|index| at(&items, index, "item").cloned())
                .transpose()
        };
        let label = |index: Option<u32>| {
            index
                .map(|index| at(&self.labels, index, "label").cloned())
                .transpose()
        };
        let range = |file: u32, start: u32, end: u32| {
            SourceRange::new(at(&files, file, "file")?.clone(), start, end)
                .map_err(|error| error.to_string())
        };
        let frames = self
            .frames
            .into_iter()
            .map(|frame| {
                Ok(match frame {
                    FrameWire::Ranged(code, file, start, end, item_index, label_index) => {
                        let Some(FrameKind::Ranged(kind)) = FrameKind::from_code(code) else {
                            unreachable!("the frame visitor read a ranged code")
                        };
                        OriginFrame::Ranged {
                            kind,
                            range: range(file, start, end)?,
                            item: item(item_index)?,
                            label: label(label_index)?,
                        }
                    }
                    FrameWire::Transformation(code, item_index, label_index) => {
                        let Some(FrameKind::Transformation(kind)) = FrameKind::from_code(code)
                        else {
                            unreachable!("the frame visitor read a transformation code")
                        };
                        OriginFrame::Transformation {
                            kind,
                            item: item(item_index)?,
                            label: label(label_index)?,
                        }
                    }
                    FrameWire::Inserted(kind, anchor) => OriginFrame::Inserted {
                        kind,
                        anchor: anchor
                            .map(|(file, start, end)| range(file, start, end))
                            .transpose()?,
                    },
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        Ok(ReadTables(frames))
    }
}

impl<'de> Deserialize<'de> for ReadTables {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        TablesWire::deserialize(deserializer)?
            .resolve()
            .map_err(D::Error::custom)
    }
}

struct RootVisitor<R: ?Sized, W>(PhantomData<fn() -> W>, PhantomData<fn(&R)>);

impl<'de, R: ArtifactRoot + ?Sized, W: Deserialize<'de>> Visitor<'de> for RootVisitor<R, W> {
    type Value = W;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "a {} object", R::NAME)
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<W, A::Error> {
        let install = |frames: Vec<OriginFrame>| enter(Some(Scope::Read(Rc::new(frames))));
        let mut buffered = Vec::new();
        let mut versioned = false;
        // Tables read before the version, buffered until the version is checked.
        let mut early_tables = None;
        let mut scope = None;
        while let Some(key) = map.next_key::<String>()? {
            if key == PROVENANCE_FIELD {
                if versioned {
                    let ReadTables(frames) = map.next_value()?;
                    scope = Some(install(frames));
                    break;
                }
                early_tables = Some(map.next_value::<serde_json::Value>()?);
                continue;
            }
            let value = map.next_value::<serde_json::Value>()?;
            let version = key == R::VERSION_FIELD;
            if version {
                R::check_version(&value).map_err(A::Error::custom)?;
                versioned = true;
            }
            buffered.push((key, value));
            if version && let Some(tables) = early_tables.take() {
                let ReadTables(frames) =
                    ReadTables::deserialize(tables).map_err(A::Error::custom)?;
                scope = Some(install(frames));
                break;
            }
        }
        if early_tables.is_some() {
            return Err(A::Error::missing_field(R::VERSION_FIELD));
        }
        #[cfg(any(test, feature = "test-support"))]
        let inline = matches!(current(), Some(Scope::Inline));
        #[cfg(not(any(test, feature = "test-support")))]
        let inline = false;
        if scope.is_none() && !inline {
            return Err(A::Error::missing_field(PROVENANCE_FIELD));
        }
        let body = W::deserialize(MapAccessDeserializer::new(Remaining {
            buffered: buffered.into_iter(),
            pending: None,
            map,
        }));
        drop(scope);
        body
    }
}

/// The fields of a root after its tables: those read before them, then the rest.
struct Remaining<A> {
    buffered: std::vec::IntoIter<(String, serde_json::Value)>,
    pending: Option<serde_json::Value>,
    map: A,
}

impl<'de, A: MapAccess<'de>> MapAccess<'de> for Remaining<A> {
    type Error = A::Error;

    fn next_key_seed<K: DeserializeSeed<'de>>(
        &mut self,
        seed: K,
    ) -> Result<Option<K::Value>, Self::Error> {
        if let Some((key, value)) = self.buffered.next() {
            self.pending = Some(value);
            return seed
                .deserialize(IntoDeserializer::<'de, A::Error>::into_deserializer(key))
                .map(Some);
        }
        self.map.next_key_seed(seed)
    }

    fn next_value_seed<V: DeserializeSeed<'de>>(
        &mut self,
        seed: V,
    ) -> Result<V::Value, Self::Error> {
        if let Some(value) = self.pending.take() {
            return seed.deserialize(value).map_err(A::Error::custom);
        }
        self.map.next_value_seed(seed)
    }
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};

    use super::{ArtifactRoot, deserialize_root, serialize_root, with_inline_provenance};
    use crate::testing;
    use crate::{
        InsertedNode, ItemKind, OriginFrame, OriginStack, RangedOriginKind, SourceRange,
        TransformationOriginKind,
    };

    /// A root holding bare stacks, so every frame kind, inserted frames among them, is reachable.
    #[derive(Debug, PartialEq)]
    struct Root {
        version: u32,
        stacks: Vec<OriginStack>,
    }

    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct RootWire {
        version: u32,
        stacks: Vec<OriginStack>,
    }

    impl ArtifactRoot for Root {
        const NAME: &'static str = "Root";
        const VERSION_FIELD: &'static str = "version";
        const BODY_FIELDS: usize = 1;
        type Version = u32;

        fn version(&self) -> &u32 {
            &self.version
        }

        fn serialize_body<M: serde::ser::SerializeStruct>(
            &self,
            fields: &mut M,
        ) -> Result<(), M::Error> {
            fields.serialize_field("stacks", &self.stacks)
        }

        fn check_version(version: &serde_json::Value) -> Result<(), String> {
            if version == 1 {
                Ok(())
            } else {
                Err(format!("unsupported test root {version}"))
            }
        }
    }

    impl Serialize for Root {
        fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serialize_root(self, serializer)
        }
    }

    impl<'de> Deserialize<'de> for Root {
        fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            let wire = deserialize_root::<Self, RootWire, D>(deserializer)?;
            Ok(Self {
                version: wire.version,
                stacks: wire.stacks,
            })
        }
    }

    fn range(stack: &OriginStack) -> SourceRange {
        stack.exact_authored_range().unwrap()
    }

    /// Two stacks sharing a file, an item, a label and two frames, with every frame kind.
    fn root() -> Root {
        let item = testing::item("syntax", "Value", ItemKind::Sort);
        let mut first = testing::authored(3, 8);
        let anchor = range(&testing::authored(10, 14));
        first.push(OriginFrame::Ranged {
            kind: RangedOriginKind::MacroInvocation,
            range: range(&testing::authored(0, 20)),
            item: Some(item.clone()),
            label: None,
        });
        first.push(OriginFrame::inserted(
            InsertedNode::DefinednessTest,
            Some(anchor),
        ));
        first.push(OriginFrame::Transformation {
            kind: TransformationOriginKind::DefinitionIr,
            item: Some(item.clone()),
            label: Some("rule".to_owned()),
        });
        let mut second = testing::authored_in(
            testing::package("ORG-EXAMPLE-OTHER", "other"),
            "src/other.rs",
            testing::digest_with("ab".repeat(32)),
            1,
            2,
        );
        second.push(OriginFrame::inserted(InsertedNode::GeneratedBinder, None));
        second.push(first.frames()[3].clone());
        Root {
            version: 1,
            stacks: vec![first.clone(), second, first],
        }
    }

    /// Every frame, file, item and label is written once, the stacks are index
    /// lists, the tables precede the body, and decoding yields the same value.
    #[test]
    fn tables_hold_each_row_once_and_round_trip() {
        let root = root();
        let text = crate::json::to_canonical_string(&root).unwrap();
        assert!(
            text.starts_with(r#"{"version":1,"provenance":{"packages":["#),
            "{text}"
        );
        let json: serde_json::Value = serde_json::from_str(&text).unwrap();
        let tables = &json["provenance"];
        assert_eq!(tables["packages"].as_array().unwrap().len(), 2);
        assert_eq!(tables["files"].as_array().unwrap().len(), 2);
        assert_eq!(tables["items"].as_array().unwrap().len(), 1);
        assert_eq!(tables["labels"], serde_json::json!(["rule"]));
        assert_eq!(
            tables["frames"],
            serde_json::json!([
                [0, 0, 3, 8, null, null],
                [1, 0, 0, 20, 0, null],
                [7, "definedness_test", 0, 10, 14],
                [6, 0, 0],
                [0, 1, 1, 2, null, null],
                [7, "generated_binder"],
            ])
        );
        assert_eq!(
            json["stacks"],
            serde_json::json!([[0, 1, 2, 3], [4, 5, 3], [0, 1, 2, 3]])
        );
        assert_eq!(tables["files"][1]["package"], 1);
        assert_eq!(serde_json::from_str::<Root>(&text).unwrap(), root);
        assert_eq!(
            crate::json::from_slice::<Root>(text.as_bytes()).unwrap(),
            root
        );
        // A `Value` orders its keys, so the tables follow the body; the reader buffers it.
        let reordered = serde_json::to_value(&root).unwrap();
        assert_eq!(
            reordered.as_object().unwrap().keys().collect::<Vec<_>>(),
            ["provenance", "stacks", "version"]
        );
        assert_eq!(serde_json::from_value::<Root>(reordered).unwrap(), root);
        let late = format!(
            r#"{{"stacks":{},"version":1,"provenance":{}}}"#,
            json["stacks"], json["provenance"]
        );
        assert_eq!(serde_json::from_str::<Root>(&late).unwrap(), root);
    }

    /// Outside a root, and inside a root in the inline test mode, a stack is its frames.
    #[test]
    fn a_stack_outside_a_root_is_written_as_its_frames() {
        let root = root();
        let alone = serde_json::to_value(&root.stacks[0]).unwrap();
        assert_eq!(alone[0]["frame_type"], "ranged");
        let inline = with_inline_provenance(|| serde_json::to_value(&root).unwrap());
        assert!(inline.get("provenance").is_none());
        assert_eq!(inline["stacks"][0], alone);
        assert_eq!(
            with_inline_provenance(|| serde_json::from_value::<Root>(inline.clone())).unwrap(),
            root
        );
        let error = serde_json::from_value::<Root>(inline).unwrap_err();
        assert!(
            error.to_string().contains("missing field `provenance`"),
            "{error}"
        );
    }

    #[test]
    fn readers_refuse_invalid_tables_and_versions() {
        let json = serde_json::to_value(root()).unwrap();
        let refused = |edit: &dyn Fn(&mut serde_json::Value), expected: &str| {
            let mut changed = json.clone();
            edit(&mut changed);
            let error = serde_json::from_value::<Root>(changed)
                .unwrap_err()
                .to_string();
            assert!(error.contains(expected), "{expected}: {error}");
        };
        refused(
            &|json| json["stacks"][0][0] = 99.into(),
            "invalid frame index 99",
        );
        refused(
            &|json| json["provenance"]["frames"][0][1] = 9.into(),
            "invalid file index 9",
        );
        refused(
            &|json| json["provenance"]["frames"][1][4] = 9.into(),
            "invalid item index 9",
        );
        refused(
            &|json| json["provenance"]["frames"][3][2] = 9.into(),
            "invalid label index 9",
        );
        refused(
            &|json| json["provenance"]["files"][0]["package"] = 9.into(),
            "invalid package index 9",
        );
        refused(
            &|json| json["provenance"]["frames"][0] = serde_json::json!([0, 0, 8, 3, null, null]),
            "starts at 8 but ends at 3",
        );
        refused(
            &|json| json["provenance"]["frames"][0] = serde_json::json!([8, 0]),
            "unknown provenance frame code 8",
        );
        refused(
            &|json| json["provenance"]["frames"][3] = serde_json::json!([6, 0, 0, 0]),
            "provenance frame has extra fields",
        );
        refused(
            &|json| json["provenance"]["frames"][2] = serde_json::json!([7, "definedness_test", 0]),
            "invalid length 3",
        );
        refused(
            &|json| json["stacks"][1] = serde_json::json!([5]),
            "must begin with an authored frame",
        );
        refused(
            &|json| json["provenance"]["extra"] = serde_json::json!([]),
            "unknown field `extra`",
        );
        let early = r#"{"version":2,"provenance":{"unread":true}}"#;
        let error = serde_json::from_str::<Root>(early).unwrap_err().to_string();
        assert!(error.contains("unsupported test root 2"), "{error}");
        // A `Value` puts the tables before the version, which is still checked first.
        refused(
            &|json| {
                json["version"] = 2.into();
                json["provenance"]["frames"][0] = serde_json::json!([8, 0]);
            },
            "unsupported test root 2",
        );
        refused(
            &|json| {
                json.as_object_mut().unwrap().remove("version");
            },
            "missing field `version`",
        );
    }

    /// The writer refuses a reversed range, which the reader would refuse.
    #[test]
    fn writers_refuse_a_reversed_range() {
        let mut stack = testing::authored(0, 20);
        let mut reversed = range(&testing::authored(3, 8));
        reversed.start_byte = 8;
        reversed.end_byte = 3;
        stack.push(OriginFrame::Ranged {
            kind: RangedOriginKind::MacroInvocation,
            range: reversed,
            item: None,
            label: None,
        });
        let root = Root {
            version: 1,
            stacks: vec![stack],
        };
        let error = crate::json::to_canonical_string(&root)
            .unwrap_err()
            .to_string();
        assert!(error.contains("starts at 8 but ends at 3"), "{error}");
    }
}
