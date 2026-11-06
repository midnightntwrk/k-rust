//! Joining backend rule identities to authored KRS sources.

use std::collections::BTreeMap;

use krs_ir::{
    LineIndex, NodeOrigin, OriginFrame, PackageCrateName, PackageId, SourceFileId, SourceRange,
};
use krs_k_rust::{Author, EmittedProvenance, InputSentenceKind};

use crate::{SourceText, report::SourceSpan, report::StepOrigin};

/// Positions authored ranges in source text supplied by the caller, caching one line index per file.
///
/// It is the one positioning of an authored origin: `krs run --trace` and the claims of a report
/// place a step's rule by it, and `krs kink` places every rule a document names by it, so the
/// two cannot place a sentence differently.
pub struct Origins {
    sources: Option<SourceText>,
    lines: BTreeMap<SourceFileId, Option<LineIndex>>,
}

impl Origins {
    /// Origins positioned in the text `sources` returns, or only named by file without it.
    #[must_use]
    pub fn new(sources: Option<SourceText>) -> Self {
        Self {
            sources,
            lines: BTreeMap::new(),
        }
    }

    /// The authored span of a KRS origin (its first authored frame), positioned at the range's
    /// start when its source text is available; `None` when no frame is authored.
    pub fn span(&mut self, origin: &NodeOrigin) -> Option<SourceSpan> {
        let range = authored_range(origin)?;
        let (line, column) = self.position(range).unzip();
        Some(SourceSpan {
            file: range.file.package_relative_path().to_owned(),
            line,
            column,
        })
    }

    fn position(&mut self, range: &SourceRange) -> Option<(u32, u32)> {
        let sources = self.sources.as_ref()?;
        let index = self
            .lines
            .entry(range.file.clone())
            .or_insert_with(|| sources(&range.file).map(|text| LineIndex::new(&text)))
            .as_ref()?;
        let position = index
            .byte_to_position(usize::try_from(range.start_byte).ok()?)
            .ok()?;
        Some((position.line(), position.scalar_column()))
    }

    /// Classify the provenance of one emitted rule identity.
    ///
    /// A rule authored as a KRS rule is `Authored`. A rule the native frontend derived from another
    /// KRS sentence (a strict production's heating and cooling rules, a context) is `Generated` from
    /// that sentence. A rule of K's builtin closure is `Builtin`.
    pub(crate) fn step_origin(&mut self, provenance: Option<&EmittedProvenance>) -> StepOrigin {
        let Some(provenance) = provenance else {
            return StepOrigin::Generated {
                pass: "unknown".to_owned(),
                from: None,
            };
        };
        if let Some(pass) = provenance.generated_by() {
            return StepOrigin::Generated {
                pass: pass.as_str().to_owned(),
                from: None,
            };
        }
        match provenance.authors().first() {
            Some(Author::Krs { kind, origin, .. }) => {
                let span = self.span(origin);
                match kind {
                    InputSentenceKind::Rule | InputSentenceKind::Claim => match span {
                        Some(span) => StepOrigin::Authored {
                            file: span.file,
                            line: span.line,
                            column: span.column,
                        },
                        None => StepOrigin::Generated {
                            pass: "unknown".to_owned(),
                            from: None,
                        },
                    },
                    other => StepOrigin::Generated {
                        pass: generating_kind(*other).to_owned(),
                        from: span,
                    },
                }
            }
            Some(Author::Builtin { module, .. }) => StepOrigin::Builtin {
                module: module.clone(),
            },
            None => StepOrigin::Generated {
                pass: "unknown".to_owned(),
                from: None,
            },
        }
    }
}

/// The KRS item that wrote an emitted rule identity, with the package that declares it.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct ItemPath {
    /// The declaring package's K namespace, which tells the definition's packages apart.
    pub(crate) namespace: String,
    /// The name a stop gives the declaring package's crate: the crate name of its library, as
    /// the definition records it ([`krs_ir_levels::DefinitionIr::crate_name`]), which the
    /// package itself sets, so that every reader of the definition names the item alike. It is
    /// never a name a depending package's manifest renames the dependency to.
    pub(crate) krate: String,
    /// The item's Rust path below its crate root (`interrupt::boundary_fetch`, `Arith::Add`
    /// for a variant of the enum family `Arith`), in the source `krs expand` prints: a function's
    /// equation is the item the expansion names after the function and its branch (`clamp_2`
    /// for the second branch of `fn Clamp`).
    pub(crate) path: String,
}

impl ItemPath {
    /// The name of the item that a stop reads as it whatever else the definition declares
    /// ([`crate::rules::Rules::resolve_item`]), in the definition whose main module is `root` (the
    /// root package's K namespace): `crate::` and its path for an item of the root package, its
    /// crate name and its path otherwise. It names the item alone except where two packages of
    /// one crate name each have an item at its path, or the root package has an item at the whole
    /// of a dependency item's spelling.
    pub(crate) fn spelling(&self, root: &str) -> String {
        let krate = if self.namespace == root {
            "crate"
        } else {
            &self.krate
        };
        format!("{krate}::{}", self.path)
    }
}

/// The KRS item that wrote an emitted rule identity ([`ItemPath`]), from its first KRS author's
/// origin ([`origin_item_path`]), with its package's crate name as `crate_names` records it;
/// `None` for a rule of K's builtin closure.
pub(crate) fn item_path(
    provenance: Option<&EmittedProvenance>,
    crate_names: &[PackageCrateName],
) -> Option<ItemPath> {
    let Some(Author::Krs { origin, .. }) = provenance?.authors().first() else {
        return None;
    };
    origin_item_path(origin, crate_names)
}

/// The KRS item a sentence's origin names ([`ItemPath`]): the item the first frame of the origin
/// that names an authored item names. An item whose name holds KRS's reserved marker (`__krs_`)
/// is one the expansion generated, such as a production's grammar registration, which no author
/// writes and no Rust path of the source names; the origin names the authored item it serves in
/// a later frame (a strict variant's heat and cool rules name the variant once the production is
/// lowered). Its package's crate name is the one `crate_names` records for it (a definition's
/// [`krs_ir_levels::DefinitionIr::crate_names`]), or the package's default crate name where
/// `crate_names` records none. `None` for an origin that names no authored item.
pub(crate) fn origin_item_path(
    origin: &NodeOrigin,
    crate_names: &[PackageCrateName],
) -> Option<ItemPath> {
    let item = origin
        .origin()
        .frames()
        .iter()
        .find_map(|frame| match frame {
            OriginFrame::Ranged { item, .. } | OriginFrame::Transformation { item, .. } => item
                .as_ref()
                .filter(|item| !item.item_name().starts_with(krs_ir::ir::RESERVED_MARKER)),
            OriginFrame::Inserted { .. } => None,
        })?;
    // A variant of a constructor family is named in Rust through its enum, which its identity
    // holds as its disambiguator, never in its module path.
    let family = item
        .disambiguator()
        .strip_prefix(krs_ir::ENUM_VARIANT_DISAMBIGUATOR_PREFIX);
    let path = item
        .module_path()
        .iter()
        .map(String::as_str)
        .chain(family)
        .chain([item.item_name()])
        .collect::<Vec<_>>()
        .join("::");
    let package = item.package();
    Some(ItemPath {
        namespace: package.k_namespace().to_owned(),
        krate: krs_ir::crate_name_in(crate_names, package),
        path,
    })
}

/// The names of one package of a definition that a stop's first segment may be.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PackageNames {
    /// The crate name of its library, by which a stop names it ([`ItemPath::krate`]).
    pub(crate) krate: String,
    /// Its Cargo package name with `-` written `_`, which names no crate where its `[lib]`
    /// section names its library otherwise, and which a refusal then points at `krate` from.
    pub(crate) package: String,
}

/// The packages of `definition` by K namespace, each with its names ([`PackageNames`]): the
/// package of each module's and each sentence's origin ([`packages_of`]). KRS generates a
/// package's module from the items it declares, with the origin of one of them, so every package
/// of the definition is found here, whether or not any of its items writes a rule or an
/// equation.
pub(crate) fn packages(definition: &krs_ir_levels::DefinitionIr) -> BTreeMap<String, PackageNames> {
    packages_of(
        definition.modules().iter().flat_map(|module| {
            std::iter::once(module.origin()).chain(
                module
                    .sentences()
                    .iter()
                    .map(krs_ir_levels::DefinitionSentence::origin),
            )
        }),
        |package| definition.crate_name(package),
    )
}

/// The packages `origins` name by K namespace, each with its names, its crate name as
/// `crate_name` gives it: of each origin, the package of the first frame that names one, the
/// package of its item, or else the package of the source its range is in.
fn packages_of<'o>(
    origins: impl Iterator<Item = &'o NodeOrigin>,
    crate_name: impl Fn(&PackageId) -> String,
) -> BTreeMap<String, PackageNames> {
    let mut packages = BTreeMap::new();
    for origin in origins {
        let package = origin
            .origin()
            .frames()
            .iter()
            .find_map(|frame| match frame {
                OriginFrame::Ranged { item, range, .. } => Some(
                    item.as_ref()
                        .map_or_else(|| range.file.package(), |item| item.package()),
                ),
                OriginFrame::Transformation { item, .. } => {
                    item.as_ref().map(krs_ir::StableItemId::package)
                }
                OriginFrame::Inserted { .. } => None,
            });
        if let Some(package) = package {
            packages
                .entry(package.k_namespace().to_owned())
                .or_insert_with(|| PackageNames {
                    krate: crate_name(package),
                    package: package.default_crate_name(),
                });
        }
    }
    packages
}

/// The name of the KRS item that wrote a sentence of `definition`, from the sentence's origin, as a run's report names it (a coverage row's and a
/// stop rule's `item`) and as a stop reads it (`krs run --stop-before`): `crate::` and the item's
/// Rust path below its crate root for an item of the root package (`crate::plus_succ`), the
/// crate name of the package that declares it, as the definition records it, and its path
/// otherwise (`lang::step`). `None` for an origin that names no authored item.
///
/// The name is the item's, not the sentence's: an item that lowers to several sentences (a
/// context's heat and cool rules) gives each of them the one name. It names the item alone
/// except where two packages of one crate name each have an item at its path, or the root
/// package has an item at the whole of a dependency item's spelling; a reader that must name
/// the sentence there names it by its K label.
#[must_use]
pub fn item_spelling(
    definition: &krs_ir_levels::DefinitionIr,
    origin: &NodeOrigin,
) -> Option<String> {
    origin_item_path(origin, definition.crate_names())
        .map(|item| item.spelling(definition.main_module().as_str()))
}

/// The pass that turns a non-rule input sentence into rules.
const fn generating_kind(kind: InputSentenceKind) -> &'static str {
    match kind {
        InputSentenceKind::Production => "strict",
        InputSentenceKind::Context => "context",
        InputSentenceKind::ContextAlias => "context-alias",
        InputSentenceKind::Configuration => "configuration",
        InputSentenceKind::SyntaxSort
        | InputSentenceKind::SortSynonym
        | InputSentenceKind::SyntaxLexical
        | InputSentenceKind::SyntaxAssociativity
        | InputSentenceKind::SyntaxPriority
        | InputSentenceKind::Rule
        | InputSentenceKind::Claim
        | InputSentenceKind::Bubble => "frontend",
    }
}

/// The first authored frame of an origin stack.
pub(crate) fn authored_range(origin: &NodeOrigin) -> Option<&SourceRange> {
    origin
        .origin()
        .frames()
        .iter()
        .find_map(|frame| match frame {
            OriginFrame::Ranged { range, .. } if frame.is_authored() => Some(range),
            _ => None,
        })
}

#[cfg(test)]
mod tests {
    use krs_ir::testing::{digest, origin_in, package};

    use super::{PackageNames, packages_of};

    /// Every package an origin is in is a package, by K namespace, with its crate name as a stop
    /// names it and its package name with `-` written `_`, whatever else the origins say of it.
    #[test]
    fn the_packages_are_those_the_origins_are_in() {
        let core = package("ORG-CORE", "gb-sm83-core");
        let types = package("ORG-TYPES", "sm83-types");
        let origins = [
            origin_in("a", core.clone(), "src/lib.rs", digest(), 0, 3),
            origin_in("b", types, "src/lib.rs", digest(), 0, 3),
            origin_in("c", core, "src/ops.rs", digest(), 4, 9),
        ];
        // `sm83-types` names its library `sm83_isa` in its `[lib]` section.
        let crate_name = |package: &krs_ir::PackageId| {
            if package.cargo_name() == "sm83-types" {
                "sm83_isa".to_owned()
            } else {
                package.default_crate_name()
            }
        };
        let names = |krate: &str, package: &str| PackageNames {
            krate: krate.to_owned(),
            package: package.to_owned(),
        };
        assert_eq!(
            packages_of(origins.iter(), crate_name)
                .into_iter()
                .collect::<Vec<_>>(),
            [
                ("ORG-CORE".to_owned(), names("gb_sm83_core", "gb_sm83_core")),
                ("ORG-TYPES".to_owned(), names("sm83_isa", "sm83_types")),
            ]
        );
    }
}
