//! Deterministic readable-to-reference Rust projection.

use krs_diagnostic::{Diagnostic, Location, ToDiagnostic, codes};
use krs_syntax::KrsSyntax;
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinOperator, BuiltinSort, CollectionMethod, Descriptor,
    DescriptorApplicationRef, DescriptorApplicationReference, DescriptorBundle, DescriptorHeadRule,
    DescriptorIndex, DescriptorPayload, DescriptorStage, DescriptorTerm,
    ENUM_VARIANT_DISAMBIGUATOR_PREFIX, FacadeMarker, ListNotation, OriginFrame, PackageId,
    ProtocolHeadRuleExtra, ProtocolHeadRuleResult, ProvenanceRole, RangedOriginKind, RefMap,
    SourceFileId, SourceMapKey, StableItemId, Stage, TermMapOperation,
};
use krs_ir_levels::{
    IrTermKind, RuleBodyRef, SemanticRule, SemanticSortRef, SemanticTerm, SemanticTheory,
};
use krs_syntax::surface::{self, FacadeScope, FunctionMacro, InvocationKind, Scope};
use proc_macro2::{Ident, Span, TokenStream, TokenTree};
use quote::{ToTokens, format_ident, quote};
use syn::ext::IdentExt;
use syn::spanned::Spanned;

mod modules;

use modules::ModuleTree;

/// One printed module file of a package.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpandedFile {
    /// The file's normalized `/`-separated path relative to the package root.
    pub path: String,
    /// The printed file.
    pub text: String,
}

/// A package's printed source: the module files expansion changes, each printed at its own path
/// with the crate's module structure kept, and the crate root printed whether or not it changes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageExpansion {
    /// The module files whose printed items differ from the authored ones, in path order.
    pub changed: Vec<ExpandedFile>,
    /// The crate root, printed.
    pub root: ExpandedFile,
}

/// Expands every module file of a package's library crate.
///
/// The files are the crate's module tree, read from `crate_root` (the library target's root
/// file) as rustc reads it ([`ModuleTree::read`]). Each file is printed at its own path, so a
/// path an item resolves, `#[path]` and `include!` included, resolves in the printed file as in
/// the authored one; only the readable forms are replaced by their long forms. A file every
/// readable form of which is already long is printed unchanged and left out of
/// [`PackageExpansion::changed`].
///
/// Every authored file a descriptor of the package names must be one of the tree's files and
/// still have its collected content digest.
/// `facade` is the package's facade scope before file and inline-module bindings, and
/// `crates` the crate name its source gives each dependency package it names
/// ([`expand_reference_source_naming`]).
///
/// # Errors
///
/// Returns a typed failure when a descriptor's file is not in the module tree, a file cannot be
/// read, has changed since collection, or is not UTF-8, or when a file's expansion fails as
/// [`expand_reference_source`]'s does.
pub fn expand_package_reference_source(
    bundle: &DescriptorBundle,
    semantic: &SemanticTheory,
    package: &PackageId,
    crates: &BTreeMap<PackageId, String>,
    manifest_path: &Path,
    crate_root: &Path,
    facade: &FacadeScope,
) -> Result<PackageExpansion, ReferenceExpansionError> {
    let source_error = ReferenceExpansionError::Source;
    let package_root = manifest_path.parent().ok_or_else(|| {
        source_error(ReferenceSourceError::ManifestDirectory(
            manifest_path.to_path_buf(),
        ))
    })?;
    let in_package = bundle
        .descriptors()
        .iter()
        .filter(|descriptor| descriptor.id().package() == package)
        .collect::<Vec<_>>();
    // A descriptor collected from `file` in the module `module` or one it holds inline.
    let named = |file: &str, module: &[String]| {
        in_package.iter().any(|descriptor| {
            descriptor.id().module_path().starts_with(module)
                && authored_source_file(descriptor)
                    .is_some_and(|named| named.package_relative_path() == file)
        })
    };
    let tree = ModuleTree::read(crate_root, package_root, &named, facade)?;
    reaches_descriptor_files(&tree, &in_package)?;
    let authored = authored_paths(tree.files.iter().map(|file| &file.parsed), crates, facade);
    let none = WrittenPaths::default();
    let expansion = Expansion::new(
        facade,
        PathScope {
            package,
            crates,
            authored: &authored,
            written: &none,
            at: None,
            module: &[],
            tree: Some(&tree),
        },
        bundle,
        semantic,
    );
    // Each file by its package-relative path: its printed text and whether it changed.
    let mut printed = BTreeMap::<&str, (String, bool)>::new();
    for file in &tree.files {
        let (text, file_changed) = expansion.file(
            &file.source,
            file.parsed.clone(),
            file.relative.as_deref(),
            &file.module_path,
        )?;
        let Some(path) = file.relative.as_deref() else {
            if file_changed || file.module_path.is_empty() {
                return Err(source_error(ReferenceSourceError::OutsidePackage(
                    file.path.clone(),
                )));
            }
            continue;
        };
        // A file two modules read (`#[path]`) is printed once, so both must print it alike.
        match printed.get_mut(path) {
            Some((earlier, _)) if *earlier != text => {
                return Err(source_error(ReferenceSourceError::SharedFile(
                    file.path.clone(),
                )));
            }
            Some((_, changed)) => *changed |= file_changed,
            None => {
                printed.insert(path, (text, file_changed));
            }
        }
    }
    let root = tree
        .files
        .iter()
        .find(|file| file.module_path.is_empty())
        .and_then(|file| file.relative.as_deref())
        .and_then(|path| Some((path, printed.get(path)?)))
        .map(|(path, (text, _))| ExpandedFile {
            path: path.to_owned(),
            text: text.clone(),
        })
        .ok_or_else(|| {
            source_error(ReferenceSourceError::OutsidePackage(
                crate_root.to_path_buf(),
            ))
        })?;
    let changed = printed
        .into_iter()
        .filter(|(_, (_, changed))| *changed)
        .map(|(path, (text, _))| ExpandedFile {
            path: path.to_owned(),
            text,
        })
        .collect();
    Ok(PackageExpansion { changed, root })
}

/// Checks that every authored file a descriptor of `in_package` names is a file of `tree` with
/// the content the descriptor was collected from.
fn reaches_descriptor_files(
    tree: &ModuleTree,
    in_package: &[&Descriptor],
) -> Result<(), ReferenceExpansionError> {
    let source_error = ReferenceExpansionError::Source;
    let mut unreached = BTreeSet::new();
    for file in in_package.iter().copied().filter_map(authored_source_file) {
        let walked = tree
            .files
            .iter()
            .find(|walked| walked.relative.as_deref() == Some(file.package_relative_path()));
        match walked {
            None => {
                unreached.insert(file.clone());
            }
            Some(walked) if walked.digest != *file.content_sha256() => {
                return Err(source_error(ReferenceSourceError::Changed(
                    walked.path.clone(),
                )));
            }
            Some(_) => {}
        }
    }
    if !unreached.is_empty() {
        return Err(source_error(ReferenceSourceError::Selection(
            unreached.into_iter().collect(),
        )));
    }
    Ok(())
}

fn authored_source_file(descriptor: &Descriptor) -> Option<&SourceFileId> {
    descriptor
        .origin()
        .frames()
        .iter()
        .find_map(|frame| match frame {
            OriginFrame::Ranged {
                kind: RangedOriginKind::Authored,
                range,
                ..
            } => Some(&range.file),
            OriginFrame::Ranged { .. }
            | OriginFrame::Transformation { .. }
            | OriginFrame::Inserted { .. } => None,
        })
}

/// Expands the readable constructs in one Rust module to the deterministic
/// layer-2 reference surface.
///
/// Rules use whole-definition sort inference and fixed-configuration
/// completion. Readable sorts, direct memberships, constructor families,
/// syntax metadata, strictness, precedence, and explicit associativity are
/// projected through deterministic identity-preserving layer-2 carriers;
/// unrelated Rust items remain AST-equivalent.
/// Readable macros are recognized under `facade`,
/// the package's facade scope before file and inline-module bindings.
///
/// # Errors
///
/// Returns a typed failure for invalid Rust/KRS syntax, absent or ambiguous
/// collected rules, missing inferred sorts, or an external declaration whose
/// Cargo dependency alias is not recoverable from the stable protocol.
pub fn expand_reference_source(
    source: &str,
    facade: &FacadeScope,
    package: &PackageId,
    module_path: &[String],
    bundle: &DescriptorBundle,
    semantic: &SemanticTheory,
) -> Result<String, ReferenceExpansionError> {
    expand_reference_source_naming(
        source,
        facade,
        package,
        &BTreeMap::new(),
        module_path,
        bundle,
        semantic,
    )
}

/// [`expand_reference_source`], where the source names each package of `crates` (a dependency
/// it declares) by its crate name there.
///
/// Another package's item prints by the path the printed clause writes to it ([`WrittenPaths`]),
/// which the long form, standing in the clause's module, resolves as the clause does; elsewhere a
/// dependency's item prints by its declaring path in that crate (`::semantic_base::Unit`) where
/// that path is known to compile ([`dependency_path`]), and an item of a package the source does
/// not depend on directly has no path the source can print.
///
/// # Errors
///
/// As [`expand_reference_source`].
pub fn expand_reference_source_naming(
    source: &str,
    facade: &FacadeScope,
    package: &PackageId,
    crates: &BTreeMap<PackageId, String>,
    module_path: &[String],
    bundle: &DescriptorBundle,
    semantic: &SemanticTheory,
) -> Result<String, ReferenceExpansionError> {
    let file = syn::parse_file(source).map_err(ReferenceExpansionError::RustSyntax)?;
    let authored = authored_paths(std::iter::once(&file), crates, facade);
    let none = WrittenPaths::default();
    let expansion = Expansion::new(
        facade,
        PathScope {
            package,
            crates,
            authored: &authored,
            written: &none,
            at: None,
            module: &[],
            tree: None,
        },
        bundle,
        semantic,
    );
    Ok(expansion.file(source, file, None, module_path)?.0)
}

/// What the expansion of a package's files shares.
struct Expansion<'a> {
    facade: &'a FacadeScope,
    package: PathScope<'a>,
    bundle: &'a DescriptorBundle,
    descriptor_index: DescriptorIndex<'a>,
    semantic_rules: BTreeMap<&'a StableItemId, &'a SemanticRule>,
    /// The module paths of the package's descriptors.
    descriptor_modules: BTreeSet<&'a [String]>,
    /// The module paths of the package's author spec modules (KF-041): inline `mod`s whose
    /// attribute consumes their items, which are printed with the module, unchanged.
    spec_modules: Vec<&'a [String]>,
}

/// The modules of a file whose printing marks more than their expanded items.
#[derive(Default)]
struct Touched {
    /// The modules whose items changed.
    changed: BTreeSet<Vec<String>>,
    /// The modules whose printed rules write `map![..]`.
    maps: BTreeSet<Vec<String>>,
}

/// One file being expanded.
struct SourceFile<'a> {
    source: &'a str,
    lines: krs_ir::LineIndex,
    /// The file's package-relative path, which the descriptors of its clauses name; `None` where
    /// the file is not known (a lone source), so that any descriptor's file matches.
    relative: Option<&'a str>,
    /// The readable macro of each item that is one, by the indices of the inline modules that
    /// hold it and its own.
    entries: BTreeMap<Vec<usize>, FunctionMacro>,
}

impl<'a> Expansion<'a> {
    fn new(
        facade: &'a FacadeScope,
        package: PathScope<'a>,
        bundle: &'a DescriptorBundle,
        semantic: &'a SemanticTheory,
    ) -> Self {
        let in_package = || {
            bundle
                .descriptors()
                .iter()
                .filter(|descriptor| descriptor.id().package() == package.package)
        };
        Self {
            facade,
            package,
            bundle,
            descriptor_index: DescriptorIndex::new(bundle),
            semantic_rules: semantic
                .modules()
                .iter()
                .flat_map(krs_ir_levels::SemanticModule::rules)
                .map(|rule| (rule.id(), rule))
                .collect(),
            descriptor_modules: in_package()
                .map(|descriptor| descriptor.id().module_path())
                .collect(),
            spec_modules: in_package()
                .filter(|descriptor| {
                    matches!(
                        descriptor.payload(),
                        DescriptorPayload::Grammar(grammar)
                            if matches!(grammar.as_ref(), krs_ir::GrammarDescriptor::SpecModule { .. })
                    )
                })
                .map(|descriptor| descriptor.id().module_path())
                .collect(),
        }
    }

    /// Whether the inline module `module` is expanded: it holds a descriptor of the package, at
    /// or below it, and is no author spec module. Any other inline module is printed as written.
    fn expands(&self, module: &[String]) -> bool {
        self.descriptor_modules
            .iter()
            .any(|path| path.starts_with(module))
            && !self
                .spec_modules
                .iter()
                .any(|spec| module.starts_with(spec))
    }

    /// Whether the inline module `module`, of path `path` in `file`, holds a collected descriptor
    /// where it stands: one under `#[cfg]` does only where its condition held, which a
    /// descriptor that originates in its bytes shows (two modules of one name may stand under
    /// exclusive conditions); one without is the module of its path.
    fn collected_in(&self, file: &SourceFile<'_>, module: &syn::ItemMod, path: &[String]) -> bool {
        if !module
            .attrs
            .iter()
            .any(|attribute| attribute.path().is_ident("cfg"))
        {
            return true;
        }
        let Some(bytes) = krs_syntax::TokenRange::for_tokens(module)
            .ok()
            .and_then(|range| authored_bytes(&file.lines, range))
        else {
            return false;
        };
        self.bundle.descriptors().iter().any(|descriptor| {
            descriptor.id().package() == self.package.package
                && descriptor.id().module_path().starts_with(path)
                && originates_in(descriptor, file.relative, Some(&bytes))
        })
    }

    /// `file`, the module `module_path`'s file, printed, and whether its items changed.
    fn file(
        &self,
        source: &str,
        mut file: syn::File,
        relative: Option<&str>,
        module_path: &[String],
    ) -> Result<(String, bool), ReferenceExpansionError> {
        let authored = file
            .items
            .iter()
            .map(ToTokens::to_token_stream)
            .collect::<TokenStream>();
        let context = SourceFile {
            source,
            lines: krs_ir::LineIndex::new(source),
            relative,
            entries: reference_macro_entries(&file, self.facade),
        };
        let mut touched = Touched::default();
        let mut items = self.items(
            &context,
            std::mem::take(&mut file.items),
            module_path,
            &[],
            &mut touched,
        )?;
        let changed = items
            .iter()
            .map(ToTokens::to_token_stream)
            .collect::<TokenStream>()
            .to_string()
            != authored.to_string();
        // The file's own `use` items are always marked, as they were when a file was printed
        // whole; an inline module's only where its items changed.
        touched.changed.insert(module_path.to_vec());
        self.decorate(&context, &mut items, module_path, &touched);
        file.items = items;
        let mut output = String::from(
            "// @generated by `krs expand`; deterministic layer-2 reference surface.\n\n",
        );
        output.push_str(&unparse_keeping_attribute_operators(file));
        Ok((output, changed))
    }

    /// The `use` items of a changed module allow being unused, since a long form may no
    /// longer use what a readable form did; a module whose printed rules write `map![..]`
    /// imports `k::map`.
    fn decorate(
        &self,
        file: &SourceFile<'_>,
        items: &mut Vec<syn::Item>,
        module_path: &[String],
        touched: &Touched,
    ) {
        let changed = touched.changed.contains(module_path);
        for item in items.iter_mut() {
            match item {
                syn::Item::Use(item_use) if changed => item_use
                    .attrs
                    .push(syn::parse_quote!(#[allow(unused_imports)])),
                syn::Item::Mod(module) => {
                    let mut path = module_path.to_vec();
                    path.push(module.ident.unraw().to_string());
                    if self.expands(&path)
                        && self.collected_in(file, module, &path)
                        && let Some((_, inner)) = &mut module.content
                    {
                        self.decorate(file, inner, &path, touched);
                    }
                }
                _ => {}
            }
        }
        if !touched.maps.contains(module_path) {
            return;
        }
        let map_use: syn::ItemUse = syn::parse_quote!(
            #[allow(unused_imports)]
            use k::map;
        );
        let map_key = map_use.tree.to_token_stream().to_string();
        if contains_use_tree(items, &map_key) {
            return;
        }
        let insertion = items
            .iter()
            .position(|item| {
                !matches!(item, syn::Item::Use(item_use) if item_use.tree.to_token_stream().to_string() < map_key)
            })
            .unwrap_or(items.len());
        items.insert(insertion, syn::Item::Use(map_use));
    }

    /// The items of the module `module_path`, `chain` the indices of the inline modules of the
    /// file that hold them, with each readable form replaced by its long form. Each inline module
    /// whose items change, and each module whose printed rules write `map![..]`, is recorded in
    /// `touched`.
    #[expect(
        clippy::too_many_lines,
        reason = "The source-order traversal keeps projected items deterministic."
    )]
    fn items(
        &self,
        file: &SourceFile<'_>,
        authored: Vec<syn::Item>,
        module_path: &[String],
        chain: &[usize],
        touched: &mut Touched,
    ) -> Result<Vec<syn::Item>, ReferenceExpansionError> {
        let package = PathScope {
            module: module_path,
            ..self.package
        };
        let bundle = self.bundle;
        let descriptor_index = &self.descriptor_index;
        let semantic_rules = &self.semantic_rules;
        let source = file.source;
        let module_uses = Bindings::of_items(&authored);
        let mut rendered_names = BTreeSet::new();
        let mut needs_map_macro = false;
        let mut items = Vec::new();
        for (index, mut item) in authored.into_iter().enumerate() {
            if let syn::Item::Mod(module) = &mut item
                && module.content.is_some()
            {
                let mut path = module_path.to_vec();
                path.push(module.ident.unraw().to_string());
                if self.expands(&path)
                    && self.collected_in(file, module, &path)
                    && let Some((_, inner)) = &mut module.content
                {
                    let mut chain = chain.to_vec();
                    chain.push(index);
                    let authored = inner
                        .iter()
                        .map(ToTokens::to_token_stream)
                        .collect::<TokenStream>()
                        .to_string();
                    *inner = self.items(file, std::mem::take(inner), &path, &chain, touched)?;
                    if inner
                        .iter()
                        .map(ToTokens::to_token_stream)
                        .collect::<TokenStream>()
                        .to_string()
                        != authored
                    {
                        touched.changed.insert(path);
                    }
                }
                items.push(item);
                continue;
            }
            if let Some(long_form) = materialize_function_shorthand(&item)? {
                for mut long_item in long_form {
                    if let syn::Item::Fn(item_fn) = &mut long_item
                        && requires_holds_equality(item_fn)
                    {
                        restate_requires(
                            item_fn,
                            package,
                            module_path,
                            bundle,
                            descriptor_index,
                            semantic_rules,
                        )?;
                    }
                    items.push(long_item);
                }
                continue;
            }
            // A rule or equation fn whose subject holds `k::bits!` templates
            // is written as its long form, its condition restated from the
            // descriptor as a table row's is.
            // So is a fn whose `requires` holds `==`, which the printer would
            // not write back as Rust (see [`requires_holds_equality`]).
            if let syn::Item::Fn(item_fn) = &mut item
                && (krs_syntax::desugar_bit_templates(item_fn)
                    .map_err(ReferenceExpansionError::KrsSyntax)?
                    .is_some()
                    || requires_holds_equality(item_fn))
            {
                restate_requires(
                    item_fn,
                    package,
                    module_path,
                    bundle,
                    descriptor_index,
                    semantic_rules,
                )?;
            }
            if let syn::Item::Struct(item_struct) = &mut item {
                materialize_configuration_wrappers(item_struct)?;
                materialize_constructor_flags(item_struct);
                materialize_function_syntax(item_struct)?;
            }
            let trailing_enum_grammar = if let syn::Item::Enum(item_enum) = &mut item {
                materialize_syntax_list(item_enum, package, module_path, bundle, descriptor_index)?;
                materialize_enum_productions(
                    item_enum,
                    package,
                    module_path,
                    bundle,
                    descriptor_index,
                )?
            } else {
                Vec::new()
            };
            if let syn::Item::Impl(item_impl) = &mut item {
                materialize_initializers(item_impl)?;
            }
            let syn::Item::Macro(invocation) = &item else {
                // The grammar an enum's family declares stands under the enum's conditions.
                let conditions = item_attributes(&item)
                    .iter()
                    .filter(|attribute| is_condition(attribute))
                    .cloned()
                    .collect::<Vec<_>>();
                items.push(item);
                items.extend(
                    trailing_enum_grammar
                        .into_iter()
                        .map(|grammar| with_attributes(grammar, &conditions)),
                );
                continue;
            };
            let mut key = chain.to_vec();
            key.push(index);
            let entry = file.entries.get(&key);
            // What a readable macro declares stands under the invocation's attributes: rustc
            // applies its `cfg` before the macro runs, and its lint attributes to what the macro
            // generates.
            let invocation_attributes = &invocation.attrs;
            if matches!(
                entry,
                Some(FunctionMacro::Sorts | FunctionMacro::FrameworkSorts)
            ) {
                items.extend(
                    materialize_readable_sorts(invocation)?
                        .into_iter()
                        .map(|sort| with_attributes(sort, invocation_attributes)),
                );
                continue;
            }
            if entry == Some(&FunctionMacro::Equations) {
                let table = krs_syntax::EquationTable::parse_tokens(invocation.mac.tokens.clone())
                    .map_err(ReferenceExpansionError::KrsSyntax)?;
                for row in table.rows() {
                    let name = row.label().unraw().to_string();
                    let authored = authored_bytes(&file.lines, row.source_range());
                    let descriptors = descriptor_index
                        .values()
                        .filter_map(|descriptor| match descriptor.payload() {
                            krs_ir::DescriptorPayload::StructuredRule(rule)
                                if descriptor.id().package() == package.package
                                    && descriptor.id().module_path() == module_path
                                    && descriptor.id().item_name() == name
                                    && descriptor.id().item_kind()
                                        == krs_ir::ItemKind::Equation
                                    && originates_in(
                                        descriptor,
                                        file.relative,
                                        authored.as_ref(),
                                    ) =>
                            {
                                Some((descriptor, rule.as_ref()))
                            }
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    if descriptors.is_empty()
                        && (configured_out(&row.rule().item().attrs)
                            || configured_out(invocation_attributes))
                    {
                        continue;
                    }
                    let [(descriptor, rule)] = descriptors.as_slice() else {
                        return Err(ReferenceExpansionError::RuleCoverage {
                            name,
                            found: descriptors.len(),
                        });
                    };
                    let semantic_rule = semantic_rules.get(descriptor.id()).ok_or_else(|| {
                        ReferenceExpansionError::MissingSemanticRule(Box::new(
                            descriptor.id().clone(),
                        ))
                    })?;
                    let written = WrittenPaths::of(
                        descriptor,
                        ReferencedItems::of_equation(rule),
                        source,
                        Some(&Bindings::of_uses(table.imports())),
                        &module_uses,
                    );
                    // A record update is written in full, as its fields (F5).
                    let rule = crate::semantic::structured_rule_long_form(descriptor, rule, bundle)
                        .map_err(|error| ReferenceExpansionError::Lowering(Box::new(error)))?
                        .try_map_refs(&mut OperatorCalls::new(
                            descriptor,
                            semantic_rule,
                            semantic_rules,
                        ))?;
                    items.push(with_attributes(
                        syn::Item::Fn(render_equation_row(
                            row,
                            &rule,
                            package.writing(&written),
                            bundle,
                        )?),
                        invocation_attributes,
                    ));
                    if !rendered_names.insert(name.clone()) {
                        return Err(ReferenceExpansionError::DuplicateRule(name));
                    }
                }
                continue;
            }
            // A claim block's clauses are readable records too, whose
            // descriptors are claims (F7).
            let (block, kind) = match entry {
                Some(FunctionMacro::Rules) => (
                    krs_syntax::RuleBlock::parse_tokens(invocation.mac.tokens.clone())
                        .map_err(ReferenceExpansionError::KrsSyntax)?,
                    krs_ir::ItemKind::Rule,
                ),
                Some(FunctionMacro::Claims) => (
                    krs_syntax::ClaimBlock::parse_tokens(invocation.mac.tokens.clone())
                        .map_err(ReferenceExpansionError::KrsSyntax)?
                        .block()
                        .clone(),
                    krs_ir::ItemKind::Claim,
                ),
                _ => {
                    items.push(item);
                    items.extend(trailing_enum_grammar);
                    continue;
                }
            };
            for clause in block.clauses() {
                let name = clause.rule().item().sig.ident.unraw().to_string();
                let authored = authored_bytes(&file.lines, clause.source_range());
                let descriptors = descriptor_index
                    .head_rules()
                    .filter(|(descriptor, _)| {
                        descriptor.id().package() == package.package
                            && descriptor.id().module_path() == module_path
                            && descriptor.id().item_name() == name
                            && descriptor.id().item_kind() == kind
                            && originates_in(descriptor, file.relative, authored.as_ref())
                    })
                    .collect::<Vec<_>>();
                if descriptors.is_empty()
                    && (configured_out(&clause.rule().item().attrs)
                        || configured_out(invocation_attributes))
                {
                    continue;
                }
                let [(descriptor, rule)] = descriptors.as_slice() else {
                    return Err(ReferenceExpansionError::RuleCoverage {
                        name,
                        found: descriptors.len(),
                    });
                };
                needs_map_macro |= !rule.extras.is_empty();
                let semantic_rule = semantic_rules.get(descriptor.id()).ok_or_else(|| {
                    ReferenceExpansionError::MissingSemanticRule(Box::new(descriptor.id().clone()))
                })?;
                let written = WrittenPaths::of(
                    descriptor,
                    ReferencedItems::of_head_rule(rule),
                    source,
                    Some(&Bindings::of_uses(block.imports())),
                    &module_uses,
                );
                // A record update is written in full, as its fields (F5).
                let rule = crate::semantic::head_rule_long_form(descriptor, rule, bundle)
                    .map_err(|error| ReferenceExpansionError::Lowering(Box::new(error)))?
                    .try_map_refs(&mut OperatorCalls::new(
                        descriptor,
                        semantic_rule,
                        semantic_rules,
                    ))?;
                items.push(with_attributes(
                    syn::Item::Fn(render_rule(
                        clause,
                        &rule,
                        semantic_rule,
                        package.writing(&written),
                        bundle,
                        descriptor_index,
                    )?),
                    invocation_attributes,
                ));
                if !rendered_names.insert(name.clone()) {
                    return Err(ReferenceExpansionError::DuplicateRule(name));
                }
            }
        }
        if needs_map_macro {
            touched.maps.insert(module_path.to_vec());
        }
        for item in &mut items {
            if !matches!(item, syn::Item::Mod(_)) {
                rename_hidden_binders(item)?;
            }
        }
        Ok(items)
    }
}

/// The byte range of the source that `range` spans, measured as the
/// collector measures a descriptor's origin: through the line and column of
/// each end.
fn authored_bytes(
    lines: &krs_ir::LineIndex,
    range: krs_syntax::TokenRange,
) -> Option<std::ops::Range<usize>> {
    let start = lines.line_column_to_byte(range.start()).ok()?;
    let end = lines.line_column_to_byte(range.end()).ok()?;
    Some(start..end)
}

/// Whether `descriptor`'s authored origin lies in `authored`, the bytes of a
/// readable clause or table row of the file `file` (package-relative; any file where `None`).
///
/// A clause's descriptor is the one that originates in the clause, not one of
/// its name: two blocks may each hold a clause of one name under exclusive
/// `cfg`s, and only the clause whose `cfg` holds has a descriptor. A file the
/// module tree reads twice (`#[path]`) holds the same bytes in two modules,
/// and the same bytes of two files are two clauses.
fn originates_in(
    descriptor: &Descriptor,
    file: Option<&str>,
    authored: Option<&std::ops::Range<usize>>,
) -> bool {
    let (Some(authored), Some(origin)) = (authored, descriptor.origin().exact_authored_range())
    else {
        return false;
    };
    file.is_none_or(|file| origin.file.package_relative_path() == file)
        && authored.start <= origin.start_byte as usize
        && origin.end_byte as usize <= authored.end
}

/// Whether a readable clause or table row in which no collected sentence
/// originates was configured out: it, or the macro invocation that holds it, carries a
/// `#[cfg(..)]`, which the macro writes on what it generates for the clause (rustc removes the
/// invocation itself), so the clause's sentence was collected exactly when its condition held.
/// A clause whose condition does not hold denotes nothing, as an item Rust
/// removes before any macro sees it, so its expanded surface is its absence.
fn configured_out(attributes: &[syn::Attribute]) -> bool {
    attributes
        .iter()
        .any(|attribute| attribute.path().is_ident("cfg"))
}

/// Whether `attribute` is a condition on its item: `cfg`, or a `cfg_attr` that may apply one.
fn is_condition(attribute: &syn::Attribute) -> bool {
    attribute.path().is_ident("cfg") || attribute.path().is_ident("cfg_attr")
}

/// `item` with `attributes` written before its own: an item a readable form declares, under the
/// attributes of the form it stands for.
fn with_attributes(mut item: syn::Item, attributes: &[syn::Attribute]) -> syn::Item {
    if let Some(own) = item_attributes_mut(&mut item) {
        own.splice(0..0, attributes.iter().cloned());
    }
    item
}

/// `file` printed by prettyplease, with each attribute argument that holds
/// a comparison or a connective printed as the Rust expression it is.
///
/// prettyplease prints a list attribute's arguments token by token, with a
/// space after every `=` and none before an operator, so
/// `#[k::ensures(m == n + 1)]` would come out as `m = = n + 1`, which no
/// longer parses, and `a != b && c <= d` as `a!= b&&c<= d`. Such an
/// attribute's arguments are replaced by a placeholder before printing, and
/// the placeholder by the arguments printed as expressions after it.
fn unparse_keeping_attribute_operators(mut file: syn::File) -> String {
    let mut arguments = Vec::new();
    for item in &mut file.items {
        let tokens = protect_attribute_operators(item.to_token_stream(), &mut arguments);
        if let Ok(protected) = syn::parse2(tokens) {
            *item = protected;
        }
    }
    let mut output = prettyplease::unparse(&file);
    for (index, text) in arguments.iter().enumerate().rev() {
        output = output.replace(&format!("{ATTRIBUTE_PLACEHOLDER}{index}"), text);
    }
    output
}

/// The identifier that stands for one attribute's arguments while
/// prettyplease prints the file, followed by the arguments' index.
const ATTRIBUTE_PLACEHOLDER: &str = "__krs_attribute_arguments_";

/// `tokens` with the arguments of each attribute `#[path(args)]` whose
/// arguments hold `==`, `!=`, `<=`, `>=`, `=>`, `&&`, or `||` and are
/// expressions replaced by a placeholder; `arguments` receives their printed
/// text, in placeholder order.
fn protect_attribute_operators(tokens: TokenStream, arguments: &mut Vec<String>) -> TokenStream {
    fn holds_operator(tokens: &TokenStream) -> bool {
        let mut joint = None;
        for tree in tokens.clone() {
            match tree {
                TokenTree::Punct(punct) => {
                    let pair = joint.map(|first| [first, punct.as_char()]);
                    if matches!(
                        pair,
                        Some(['=' | '!' | '<' | '>', '='] | ['=', '>'] | ['&', '&'] | ['|', '|'])
                    ) {
                        return true;
                    }
                    joint =
                        (punct.spacing() == proc_macro2::Spacing::Joint).then(|| punct.as_char());
                }
                TokenTree::Group(group) => {
                    if holds_operator(&group.stream()) {
                        return true;
                    }
                    joint = None;
                }
                _ => joint = None,
            }
        }
        false
    }
    fn printed(tokens: TokenStream) -> Option<String> {
        use syn::parse::Parser;
        let expressions =
            syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated
                .parse2(tokens)
                .ok()?;
        let printed = expressions
            .iter()
            .map(|expression| {
                let text = prettyplease::unparse(&syn::parse_quote!(const _: () = #expression;));
                text.trim_end()
                    .strip_prefix("const _: () = ")
                    .and_then(|text| text.strip_suffix(';'))
                    .map(str::to_owned)
            })
            .collect::<Option<Vec<_>>>()?;
        Some(printed.join(", "))
    }
    let mut output = Vec::new();
    let mut trees = tokens.into_iter().peekable();
    while let Some(tree) = trees.next() {
        match tree {
            TokenTree::Punct(punct) if punct.as_char() == '#' => {
                output.push(TokenTree::Punct(punct));
                let Some(TokenTree::Group(attribute)) = trees.peek().cloned() else {
                    continue;
                };
                if attribute.delimiter() != proc_macro2::Delimiter::Bracket {
                    continue;
                }
                trees.next();
                let mut inner = attribute.stream().into_iter().collect::<Vec<_>>();
                if let Some(TokenTree::Group(list)) = inner.last()
                    && list.delimiter() == proc_macro2::Delimiter::Parenthesis
                    && holds_operator(&list.stream())
                    && let Some(text) = printed(list.stream())
                {
                    let placeholder = format_ident!("{ATTRIBUTE_PLACEHOLDER}{}", arguments.len());
                    arguments.push(text);
                    let mut group = proc_macro2::Group::new(
                        proc_macro2::Delimiter::Parenthesis,
                        quote!(#placeholder),
                    );
                    group.set_span(list.span());
                    *inner.last_mut().expect("the list was matched above") =
                        TokenTree::Group(group);
                }
                let mut group = proc_macro2::Group::new(
                    proc_macro2::Delimiter::Bracket,
                    inner.into_iter().collect(),
                );
                group.set_span(attribute.span());
                output.push(TokenTree::Group(group));
            }
            TokenTree::Group(group) => {
                let mut protected = proc_macro2::Group::new(
                    group.delimiter(),
                    protect_attribute_operators(group.stream(), arguments),
                );
                protected.set_span(group.span());
                output.push(TokenTree::Group(protected));
            }
            other => output.push(other),
        }
    }
    output.into_iter().collect()
}

fn reference_macro_entries(
    file: &syn::File,
    facade: &FacadeScope,
) -> BTreeMap<Vec<usize>, FunctionMacro> {
    /// Each item's indices, those of the inline modules that hold it and its own, by address.
    fn index(
        items: &[syn::Item],
        chain: &mut Vec<usize>,
        found: &mut BTreeMap<*const syn::Item, Vec<usize>>,
    ) {
        for (at, item) in items.iter().enumerate() {
            chain.push(at);
            found.insert(std::ptr::from_ref(item), chain.clone());
            if let syn::Item::Mod(syn::ItemMod {
                content: Some((_, inner)),
                ..
            }) = item
            {
                index(inner, chain, found);
            }
            chain.pop();
        }
    }
    let mut item_indices = BTreeMap::new();
    index(&file.items, &mut Vec::new(), &mut item_indices);
    let discovered = surface::invocations(file, facade);
    surface::item_owners(&discovered)
        .into_iter()
        .filter_map(|(item, invocation)| {
            if !matches!(&invocation.scope, Scope::Module(_)) {
                return None;
            }
            let InvocationKind::Function { entry, .. } = &invocation.kind else {
                return None;
            };
            Some((item_indices.get(&item)?.clone(), *entry))
        })
        .collect()
}

fn contains_use_tree(items: &[syn::Item], expected: &str) -> bool {
    items.iter().any(|item| {
        matches!(item, syn::Item::Use(item_use) if item_use.tree.to_token_stream().to_string() == expected)
    })
}

fn materialize_enum_productions(
    item: &mut syn::ItemEnum,
    package: PathScope<'_>,
    module_path: &[String],
    bundle: &DescriptorBundle,
    descriptor_index: &DescriptorIndex<'_>,
) -> Result<Vec<syn::Item>, ReferenceExpansionError> {
    if !has_attribute(&item.attrs, "constructors") {
        return Ok(Vec::new());
    }
    let declaration = krs_syntax::EnumConstructorDeclaration::from_attributed_item(item.clone())
        .map_err(ReferenceExpansionError::KrsSyntax)?;
    // A family already written in the reference form, such as the KItem
    // freezers of hand-written heating rules (KF-014), is its own expansion.
    if declaration.is_reference_family() {
        return Ok(Vec::new());
    }
    materialize_reference_family_attribute(item, &declaration)?;
    for output_variant in &mut item.variants {
        let variant = declaration
            .variants()
            .iter()
            .find(|variant| variant.name() == &output_variant.ident)
            .ok_or_else(|| {
                ReferenceExpansionError::GeneratedRust(syn::Error::new(
                    output_variant.ident.span(),
                    "enum variant disappeared during reference projection",
                ))
            })?;
        let Some(syntax) = variant.syntax() else {
            continue;
        };
        // A family without a chain has no groups, and its reference form
        // names none.
        let group = variant.precedence_group().map(|group_ordinal| {
            let group = declaration
                .precedence_groups()
                .nth(group_ordinal)
                .expect("enum precedence ordinal identifies a parsed group")
                .emitted_name(declaration.enum_name(), group_ordinal);
            let group = syn::LitStr::new(&group, Span::call_site());
            quote!(group = #group,)
        });
        let template = syntax.syntax();
        let format = syntax.format().ok_or_else(|| {
            ReferenceExpansionError::GeneratedRust(syn::Error::new(
                template.span(),
                "readable enum syntax has no derived reference format",
            ))
        })?;
        // Keys in the canonical order of decision X2.
        let avoid = syntax.avoid().then(|| quote!(avoid = true,));
        let prefer = syntax.prefer().then(|| quote!(prefer = true,));
        let placement = syntax.placement().map(|flag| {
            let key = format_ident!("{}", flag.as_str());
            quote!(#key = true,)
        });
        let overload = syntax.overload().map(|target| quote!(overload = #target,));
        let color = syntax.color().map(|color| quote!(color = #color,));
        let colors = syntax
            .colors()
            .map(|colors| quote!(colors = [#(#colors),*],));
        let materialized: syn::Attribute = syn::parse_quote!(#[k::syntax(
            #template,
            #group
            #avoid
            #prefer
            #placement
            #overload
            #color
            #colors
            format = #format
        )]);
        let syntax_index = output_variant
            .attrs
            .iter()
            .position(|attribute| attribute_is(attribute, "syntax"))
            .ok_or_else(|| {
                ReferenceExpansionError::GeneratedRust(syn::Error::new(
                    output_variant.ident.span(),
                    "checked enum syntax helper disappeared during reference projection",
                ))
            })?;
        output_variant
            .attrs
            .retain(|attribute| !attribute_is(attribute, "format"));
        output_variant.attrs[syntax_index] = materialized;
        materialize_reference_variant_fields(
            output_variant,
            declaration.enum_name(),
            package,
            module_path,
            bundle,
            descriptor_index,
        )?;
        materialize_reference_strictness(output_variant, variant.strictness())?;
    }
    render_family_grammar(&declaration)
}

/// Writes the reference form of a readable `#[k::syntax_list]` enum (KF-020):
/// the `reference` marker, `k::Term<..>` field types, and the strictness
/// result on the cons variant's strictness attribute.
fn materialize_syntax_list(
    item: &mut syn::ItemEnum,
    package: PathScope<'_>,
    module_path: &[String],
    bundle: &DescriptorBundle,
    descriptor_index: &DescriptorIndex<'_>,
) -> Result<(), ReferenceExpansionError> {
    if !has_attribute(&item.attrs, "syntax_list") {
        return Ok(());
    }
    let declaration = krs_syntax::SyntaxListDeclaration::from_attributed_item(item.clone())
        .map_err(ReferenceExpansionError::KrsSyntax)?;
    if declaration.attribute().is_reference() {
        return Ok(());
    }
    let index = item
        .attrs
        .iter()
        .position(|attribute| attribute_is(attribute, "syntax_list"))
        .ok_or_else(|| {
            ReferenceExpansionError::GeneratedRust(syn::Error::new(
                item.ident.span(),
                "checked syntax-list attribute disappeared during projection",
            ))
        })?;
    // Keys in the canonical order of decision X2.
    let separator = declaration.attribute().separator();
    let non_empty = declaration
        .attribute()
        .non_empty()
        .map(|_| quote!(non_empty,));
    item.attrs[index] =
        syn::parse_quote!(#[k::syntax_list(separator = #separator, #non_empty reference)]);
    for output_variant in &mut item.variants {
        if output_variant.ident != *declaration.cons().name() {
            continue;
        }
        materialize_reference_variant_fields(
            output_variant,
            declaration.name(),
            package,
            module_path,
            bundle,
            descriptor_index,
        )?;
        materialize_reference_strictness(output_variant, declaration.cons().strictness())?;
    }
    Ok(())
}

/// Writes the reference spelling `internal = true` / `program = true` for a
/// bare placement flag in `#[k::constructor(..)]`; `#[k::function]` keeps its
/// bare flags in both layers (decision X2).
/// The `#[k::function(..)]` attribute of an item, by its last path segment.
fn function_attribute_index(attributes: &[syn::Attribute]) -> Option<usize> {
    attributes.iter().position(|attribute| {
        attribute.path().segments.len() >= 2 && attribute_is(attribute, "function")
    })
}

/// The attribute `#[prefix::name(tokens)]` beside `template`'s path.
fn sibling_attribute(
    template: &syn::Attribute,
    name: &str,
    tokens: &TokenStream,
) -> syn::Attribute {
    let mut path = template.path().clone();
    if let Some(last) = path.segments.last_mut() {
        last.ident = Ident::new(name, Span::call_site());
    }
    if tokens.is_empty() {
        syn::parse_quote!(#[#path])
    } else {
        syn::parse_quote!(#[#path(#tokens)])
    }
}

/// Writes the default syntax of a function struct that omits `syntax`, so
/// the reference surface states every key.
fn materialize_function_syntax(item: &mut syn::ItemStruct) -> Result<(), ReferenceExpansionError> {
    let Some(index) = function_attribute_index(&item.attrs) else {
        return Ok(());
    };
    let syn::Meta::List(list) = &item.attrs[index].meta else {
        return Ok(());
    };
    let mut attribute = krs_syntax::FunctionAttribute::parse_tokens(list.tokens.clone())
        .map_err(ReferenceExpansionError::KrsSyntax)?;
    if attribute.has_authored_syntax() {
        return Ok(());
    }
    let declaration = krs_syntax::ConstructorDeclaration::from_item(item.clone())
        .map_err(ReferenceExpansionError::KrsSyntax)?;
    attribute
        .complete_default_syntax(&declaration)
        .map_err(ReferenceExpansionError::KrsSyntax)?;
    let syntax = attribute.production().syntax.clone();
    let mut tokens = list.tokens.clone();
    tokens.extend(quote!(, syntax = #syntax));
    item.attrs[index] = sibling_attribute(&item.attrs[index], "function", &tokens);
    Ok(())
}

/// The long form of `#[k::function(..)]` on a `fn`: the struct with its
/// sort and syntax stated, and the `#[k::equation]` its body defines.
fn materialize_function_shorthand(
    item: &syn::Item,
) -> Result<Option<Vec<syn::Item>>, ReferenceExpansionError> {
    let Some(mut shorthand) = krs_syntax::ShorthandItem::from_item(item) else {
        return Ok(None);
    };
    let Some(index) = function_attribute_index(&shorthand.attrs) else {
        return Ok(None);
    };
    let function = shorthand.attrs.remove(index);
    let tokens = match &function.meta {
        syn::Meta::List(list) => list.tokens.clone(),
        _ => TokenStream::new(),
    };
    let lowered = krs_syntax::FunctionShorthand::lower(tokens.clone(), shorthand)
        .map_err(ReferenceExpansionError::KrsSyntax)?;
    let production = lowered.attribute().production();
    let sort = lowered.sort_type();
    // A label names the equation the body defines, which the long form writes on that equation.
    let (mut keys, _) =
        krs_syntax::take_shorthand_label(tokens).map_err(ReferenceExpansionError::KrsSyntax)?;
    if !keys.is_empty() {
        keys.extend(quote!(,));
    }
    keys.extend(quote!(sort = #sort));
    if !lowered.attribute().has_authored_syntax() {
        let syntax = &production.syntax;
        keys.extend(quote!(, syntax = #syntax));
    }
    let mut structure = lowered.structure().clone();
    structure
        .attrs
        .push(sibling_attribute(&function, "function", &keys));
    let mut items = vec![syn::Item::Struct(structure)];
    for equation in lowered.equations() {
        let mut item = equation.item().clone();
        // A branch's guard tests a term with `k::matches!`; write it with the
        // author's facade path.
        for attribute in &mut item.attrs {
            if let syn::Meta::List(list) = &mut attribute.meta {
                list.tokens = with_facade_matches(list.tokens.clone(), function.path());
                // The guard the lowering writes for an unguarded fn names
                // `k::requires`; write it with the facade path too.
                let synthesized = list.path.segments.len() == 2
                    && list.path.segments[0].ident == "k"
                    && list.path.segments[1].ident == "requires";
                if synthesized {
                    *attribute = sibling_attribute(&function, "requires", &list.tokens);
                }
            }
        }
        let keys = equation.equation_keys();
        item.attrs
            .insert(0, sibling_attribute(&function, "equation", &keys));
        // The subject reads as a hand-written equation's, `k::term![F(x)]`.
        let mut term_path = function.path().clone();
        if let Some(last) = term_path.segments.last_mut() {
            last.ident = Ident::new("term", Span::call_site());
        }
        if let Some(syn::FnArg::Typed(subject)) = item.sig.inputs.first_mut() {
            let pattern = &subject.pat;
            *subject.pat = syn::parse_quote!(#term_path![#pattern]);
        }
        items.push(syn::Item::Fn(item));
    }
    Ok(Some(items))
}

/// Rewrites `k::matches!` in `tokens` to the facade path of `template`, an
/// attribute path such as `facade::function`.
fn with_facade_matches(tokens: TokenStream, template: &syn::Path) -> TokenStream {
    let facade = template
        .segments
        .iter()
        .take(template.segments.len().saturating_sub(1))
        .map(|segment| segment.ident.clone())
        .collect::<Vec<_>>();
    let tokens = tokens.into_iter().collect::<Vec<_>>();
    let mut output = TokenStream::new();
    let mut index = 0;
    while index < tokens.len() {
        let is_matches = matches!(
            &tokens[index..],
            [
                proc_macro2::TokenTree::Ident(k),
                proc_macro2::TokenTree::Punct(first),
                proc_macro2::TokenTree::Punct(second),
                proc_macro2::TokenTree::Ident(name),
                proc_macro2::TokenTree::Punct(bang),
                ..
            ] if k == "k" && first.as_char() == ':' && second.as_char() == ':' && name == "matches" && bang.as_char() == '!'
        );
        if is_matches && !facade.is_empty() {
            output.extend(quote!(#(#facade::)*matches!));
            index += 5;
            continue;
        }
        match &tokens[index] {
            proc_macro2::TokenTree::Group(group) => {
                let mut inner = proc_macro2::Group::new(
                    group.delimiter(),
                    with_facade_matches(group.stream(), template),
                );
                inner.set_span(group.span());
                output.extend([proc_macro2::TokenTree::Group(inner)]);
            }
            other => output.extend([other.clone()]),
        }
        index += 1;
    }
    output
}

fn materialize_constructor_flags(item: &mut syn::ItemStruct) {
    for attribute in &mut item.attrs {
        if !attribute_is(attribute, "constructor") {
            continue;
        }
        let syn::Meta::List(list) = &mut attribute.meta else {
            continue;
        };
        let tokens = list.tokens.clone().into_iter().collect::<Vec<_>>();
        let mut rewritten = TokenStream::new();
        for (index, token) in tokens.iter().enumerate() {
            rewritten.extend(std::iter::once(token.clone()));
            let bare_flag = matches!(token, proc_macro2::TokenTree::Ident(ident) if ident == "internal" || ident == "program")
                && (index == 0
                    || matches!(&tokens[index - 1], proc_macro2::TokenTree::Punct(punct) if punct.as_char() == ','))
                && tokens.get(index + 1).is_none_or(|next| {
                    matches!(next, proc_macro2::TokenTree::Punct(punct) if punct.as_char() == ',')
                });
            if bare_flag {
                rewritten.extend(quote!(= true));
            }
        }
        list.tokens = rewritten;
    }
}

fn materialize_reference_family_attribute(
    item: &mut syn::ItemEnum,
    declaration: &krs_syntax::EnumConstructorDeclaration,
) -> Result<(), ReferenceExpansionError> {
    let sort = declaration.sort();
    let constructors = item
        .attrs
        .iter()
        .position(|attribute| attribute_is(attribute, "constructors"))
        .ok_or_else(|| {
            ReferenceExpansionError::GeneratedRust(syn::Error::new(
                item.ident.span(),
                "checked constructor-family attribute disappeared during projection",
            ))
        })?;
    item.attrs[constructors] = syn::parse_quote!(#[k::constructors(sort = #sort, reference)]);
    item.attrs
        .retain(|attribute| !attribute_is(attribute, "precedence"));
    Ok(())
}

fn materialize_reference_variant_fields(
    output: &mut syn::Variant,
    family: &Ident,
    package: PathScope<'_>,
    module_path: &[String],
    bundle: &DescriptorBundle,
    descriptor_index: &DescriptorIndex<'_>,
) -> Result<(), ReferenceExpansionError> {
    let disambiguator = format!("{ENUM_VARIANT_DISAMBIGUATOR_PREFIX}{family}");
    let descriptors = descriptor_index
        .constructors()
        .filter(|(descriptor, _)| {
            descriptor.id().package() == package.package
                && descriptor.id().module_path() == module_path
                && output.ident == descriptor.id().item_name()
                && descriptor.id().disambiguator() == disambiguator
        })
        .collect::<Vec<_>>();
    let [(_, constructor)] = descriptors.as_slice() else {
        return Err(ReferenceExpansionError::ConstructorCoverage {
            family: family.to_string(),
            variant: output.ident.to_string(),
            found: descriptors.len(),
        });
    };
    match &mut output.fields {
        syn::Fields::Named(fields) => {
            if fields.named.len() != constructor.fields.len() {
                return Err(ReferenceExpansionError::ConstructorFieldCoverage {
                    family: family.to_string(),
                    variant: output.ident.to_string(),
                    expected: constructor.fields.len(),
                    found: fields.named.len(),
                });
            }
            for field in &mut fields.named {
                let name = field.ident.as_ref().ok_or_else(|| {
                    ReferenceExpansionError::GeneratedRust(syn::Error::new(
                        field.span(),
                        "a checked enum record field lost its name",
                    ))
                })?;
                let descriptor_field = constructor
                    .fields
                    .iter()
                    .find(|candidate| *name == candidate.name)
                    .ok_or_else(|| ReferenceExpansionError::MissingConstructorField {
                        family: family.to_string(),
                        variant: output.ident.to_string(),
                        field: name.to_string(),
                    })?;
                let sort = &descriptor_field.sort.sort;
                let ty = if descriptor_field.arguments.is_empty() {
                    render_reference_term_type(sort, package, module_path, bundle)?
                } else {
                    let sort = render_reference_collection(
                        sort,
                        &descriptor_field.arguments,
                        package,
                        module_path,
                        bundle,
                    )?;
                    quote!(k::Term<#sort>)
                };
                field.ty = syn::parse2(ty).map_err(ReferenceExpansionError::GeneratedRust)?;
            }
        }
        syn::Fields::Unnamed(fields) if fields.unnamed.is_empty() => {
            if !constructor.fields.is_empty() {
                return Err(ReferenceExpansionError::ConstructorFieldCoverage {
                    family: family.to_string(),
                    variant: output.ident.to_string(),
                    expected: constructor.fields.len(),
                    found: 0,
                });
            }
        }
        syn::Fields::Unit => {
            if !constructor.fields.is_empty() {
                return Err(ReferenceExpansionError::ConstructorFieldCoverage {
                    family: family.to_string(),
                    variant: output.ident.to_string(),
                    expected: constructor.fields.len(),
                    found: 0,
                });
            }
        }
        syn::Fields::Unnamed(fields) => {
            return Err(ReferenceExpansionError::ConstructorFieldCoverage {
                family: family.to_string(),
                variant: output.ident.to_string(),
                expected: constructor.fields.len(),
                found: fields.unnamed.len(),
            });
        }
    }
    Ok(())
}

/// A typed collection sort with its element types, `k::builtin::Set<..>`:
/// a builtin argument by its marker, a nested collection likewise, and any
/// other sort as the `k::Term<..>` a field of that sort has.
fn render_reference_collection(
    sort: &krs_ir::DescriptorSortRef,
    arguments: &[krs_ir::ConstructorSortArgumentDescriptor],
    package: PathScope<'_>,
    module_path: &[String],
    bundle: &krs_ir::DescriptorBundle,
) -> Result<TokenStream, ReferenceExpansionError> {
    let krs_ir::DescriptorSortRef::Builtin(builtin) = sort else {
        return render_reference_term_type(sort, package, module_path, bundle);
    };
    let marker = render_builtin_sort(*builtin);
    if arguments.is_empty() {
        return Ok(marker);
    }
    let arguments = arguments
        .iter()
        .map(|argument| {
            render_reference_collection(
                &argument.sort.sort,
                &argument.arguments,
                package,
                module_path,
                bundle,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(quote!(#marker<#(#arguments),*>))
}

fn render_reference_term_type(
    sort: &krs_ir::DescriptorSortRef,
    package: PathScope<'_>,
    module_path: &[String],
    bundle: &krs_ir::DescriptorBundle,
) -> Result<TokenStream, ReferenceExpansionError> {
    match sort {
        krs_ir::DescriptorSortRef::Builtin(sort) => {
            let sort = render_builtin_sort(*sort);
            Ok(quote!(k::Term<#sort>))
        }
        // A framework sort's marker is the facade's `k::KItemSort` or `k::KResultSort`.
        krs_ir::DescriptorSortRef::Declared(id)
            if id.package().k_namespace() == crate::partition::FRAMEWORK_NAMESPACE =>
        {
            let marker = rust_ident(&format!("{}Sort", id.item_name()))?;
            Ok(quote!(k::Term<dyn k::#marker>))
        }
        // A sort of the printed module by its marker's name; one of another module or package
        // by the marker's path, as a turbofish marker prints it ([`render_sort_marker`]).
        krs_ir::DescriptorSortRef::Declared(id) => {
            if is_token_sort(id, bundle) || is_list_sort(id, bundle) {
                return render_reference_token_term_type(id, package);
            }
            let marker = rust_ident(&format!("{}Sort", id.item_name()))?;
            if id.package() == package.package && id.module_path() == module_path {
                return Ok(quote!(k::Term<dyn #marker>));
            }
            let path = render_local_path(id, package, &[marker])?;
            Ok(quote!(k::Term<dyn #path>))
        }
        krs_ir::DescriptorSortRef::Cell(id) => render_declared_path(id, package),
        krs_ir::DescriptorSortRef::Parameter(name) => {
            let name = rust_ident(name)?;
            Ok(quote!(k::Term<#name>))
        }
    }
}

fn render_reference_token_term_type(
    id: &StableItemId,
    package: PathScope<'_>,
) -> Result<TokenStream, ReferenceExpansionError> {
    let token = render_declared_path(id, package)?;
    Ok(quote!(k::Term<#token>))
}

/// The collected declaration of `cell`, as its owner's declaration holds it.
fn declared_cell<'a>(
    cell: &krs_ir::DescriptorCellIdentity,
    index: &DescriptorIndex<'a>,
) -> Option<&'a krs_ir::DescriptorCellField> {
    index
        .cell_owner(&cell.owner)
        .ok()?
        .fields
        .iter()
        .find(|field| field.rust_field == cell.field)
}

/// Whether `cell` is a fixed nested (group) cell, whose `cells!` entry is
/// written without a wrapper because it mirrors the expanded struct (KF-016):
/// its declared kind's content is a group.
fn is_group_cell(cell: &krs_ir::DescriptorCellIdentity, index: &DescriptorIndex<'_>) -> bool {
    declared_cell(cell, index).is_some_and(|field| {
        krs_ir::cell_kind::DescriptorCell::new(field, index)
            .kind()
            .group()
            .is_some()
    })
}

/// Whether `cell` is a fixed optional (`?`) cell, whose `cells!` entry is `Some(..)` or `None`:
/// its declared kind's multiplicity is presence.
fn is_optional_cell(cell: &krs_ir::DescriptorCellIdentity, index: &DescriptorIndex<'_>) -> bool {
    declared_cell(cell, index).is_some_and(|field| {
        krs_ir::cell_kind::CellView::multiplicity(&krs_ir::cell_kind::DescriptorCell::new(
            field, index,
        )) == krs_ir::cell_kind::Multiplicity::Optional
    })
}

/// The constructors of the cons list a list cell holds (F6).
struct CellConsList {
    sort: StableItemId,
    cons: StableItemId,
    empty: StableItemId,
}

/// The cons list the leaf cell `cell` holds, when its sort is one.
fn cell_cons_list(
    cell: &krs_ir::DescriptorCellIdentity,
    bundle: &krs_ir::DescriptorBundle,
) -> Option<CellConsList> {
    let sort = bundle.descriptors().iter().find_map(|descriptor| {
        if descriptor.id() != &cell.owner {
            return None;
        }
        let declaration = match descriptor.payload() {
            DescriptorPayload::Cell(declaration) => declaration.as_ref(),
            DescriptorPayload::FixedConfiguration(configuration) => &configuration.declaration,
            _ => return None,
        };
        declaration
            .fields
            .iter()
            .find_map(|field| match &field.content {
                krs_ir::ProtocolCellContent::Leaf { sort, .. }
                    if field.rust_field == cell.field =>
                {
                    match &sort.sort {
                        krs_ir::DescriptorSortRef::Declared(id) => Some(id.clone()),
                        _ => None,
                    }
                }
                _ => None,
            })
    })?;
    bundle.descriptors().iter().find_map(|descriptor| {
        let DescriptorPayload::Grammar(grammar) = descriptor.payload() else {
            return None;
        };
        let krs_ir::GrammarDescriptor::Production(production) = grammar.as_ref() else {
            return None;
        };
        if production.result_sort.sort != krs_ir::DescriptorSortRef::Declared(sort.clone()) {
            return None;
        }
        let empty = production
            .attributes
            .iter()
            .find_map(|attribute| match attribute {
                krs_ir::DescriptorProductionAttribute::ListCons {
                    terminator: empty, ..
                }
                | krs_ir::DescriptorProductionAttribute::ConsList { empty, .. } => {
                    match &empty.application {
                        DescriptorApplicationRef::Declared(id) => Some(id.clone()),
                        _ => None,
                    }
                }
                _ => None,
            })?;
        let krs_ir::DescriptorProductionOwner::Constructor { constructor } = &production.owner
        else {
            return None;
        };
        let DescriptorApplicationRef::Declared(cons) = &constructor.application else {
            return None;
        };
        Some(CellConsList {
            sort: sort.clone(),
            cons: cons.clone(),
            empty,
        })
    })
}

/// Renders one side of a list cell as the constructor term it denotes:
/// `Cons(a, Cons(b, rest))`.
fn render_list(
    list: &krs_ir::ProtocolHeadRuleList<DescriptorTerm>,
    constructors: &CellConsList,
    shared: Option<&Ident>,
    pattern: bool,
    package: PathScope<'_>,
    bundle: &krs_ir::DescriptorBundle,
) -> Result<TokenStream, ReferenceExpansionError> {
    let mut rendered = match &list.rest {
        krs_ir::ProtocolHeadRuleListRest::Exact => {
            let empty = render_declared_application(&constructors.empty, package)?;
            quote!(#empty())
        }
        krs_ir::ProtocolHeadRuleListRest::Shared(_) => {
            let rest = shared.ok_or(ReferenceExpansionError::UnresolvedListNotation)?;
            quote!(#rest)
        }
        krs_ir::ProtocolHeadRuleListRest::Term(rest) => {
            render_term(rest, pattern, package, bundle)?
        }
    };
    let cons = render_declared_application(&constructors.cons, package)?;
    for item in list.items.iter().rev() {
        let item = render_term(item, pattern, package, bundle)?;
        rendered = quote!(#cons(#item, #rendered));
    }
    Ok(rendered)
}

/// Renders one side of a builtin `List` cell as the term its brackets
/// denote: `list::concat(list::item(a), rest)`, nested as
/// [`render_builtin_list_level`] nests a term's brackets.
fn render_builtin_list(
    list: &krs_ir::ProtocolHeadRuleList<DescriptorTerm>,
    shared: Option<&Ident>,
    pattern: bool,
    package: PathScope<'_>,
    bundle: &krs_ir::DescriptorBundle,
) -> Result<TokenStream, ReferenceExpansionError> {
    let item = render_facade_marker(krs_ir::ListOperation::Item.facade_marker());
    let concat = render_facade_marker(krs_ir::ListOperation::Concat.facade_marker());
    let mut rendered = match &list.rest {
        krs_ir::ProtocolHeadRuleListRest::Exact => None,
        krs_ir::ProtocolHeadRuleListRest::Shared(_) => {
            let rest = shared.ok_or(ReferenceExpansionError::UnresolvedListNotation)?;
            Some(quote!(#rest))
        }
        krs_ir::ProtocolHeadRuleListRest::Term(rest) => {
            Some(render_term(rest, pattern, package, bundle)?)
        }
    };
    for element in &list.back {
        let element = render_term(element, pattern, package, bundle)?;
        rendered = Some(rendered.map_or_else(
            || quote!(#item(#element)),
            |init| quote!(#concat(#init, #item(#element))),
        ));
    }
    for element in list.items.iter().rev() {
        let element = render_term(element, pattern, package, bundle)?;
        rendered = Some(rendered.map_or_else(
            || quote!(#item(#element)),
            |tail| quote!(#concat(#item(#element), #tail)),
        ));
    }
    Ok(rendered.unwrap_or_else(|| {
        let empty = render_facade_marker(krs_ir::ListOperation::Empty.facade_marker());
        quote!(#empty())
    }))
}

/// Renders one level of brackets at the builtin `List` as the term it
/// denotes: `[a, ..tail]` is `list::concat(list::item(a), tail)`, or
/// `list::item(a)` when the tail is the empty list, and `[..init, z]` is
/// `list::concat(init, list::item(z))`.
fn render_builtin_list_level(
    notation: ListNotation,
    arguments: &krs_ir::Arguments<DescriptorStage>,
    pattern: bool,
    package: PathScope<'_>,
    bundle: &krs_ir::DescriptorBundle,
) -> Result<TokenStream, ReferenceExpansionError> {
    let krs_ir::Arguments::Positional(operands) = arguments else {
        return Err(ReferenceExpansionError::UnresolvedListNotation);
    };
    let [first, second] = operands.as_slice() else {
        return Err(ReferenceExpansionError::UnresolvedListNotation);
    };
    let item = render_facade_marker(krs_ir::ListOperation::Item.facade_marker());
    let concat = render_facade_marker(krs_ir::ListOperation::Concat.facade_marker());
    let is_empty = |term: &DescriptorTerm| {
        matches!(
            term,
            DescriptorTerm::Application { reference, .. }
                if reference.application
                    == DescriptorApplicationRef::ListNotation(ListNotation::Empty)
        )
    };
    let render = |term| render_term(term, pattern, package, bundle);
    Ok(match notation {
        ListNotation::Cons if is_empty(second) => {
            let head = render(first)?;
            quote!(#item(#head))
        }
        ListNotation::Cons => {
            let (head, tail) = (render(first)?, render(second)?);
            quote!(#concat(#item(#head), #tail))
        }
        ListNotation::Snoc => {
            let (init, last) = (render(first)?, render(second)?);
            quote!(#concat(#init, #item(#last)))
        }
        ListNotation::Empty => return Err(ReferenceExpansionError::UnresolvedListNotation),
    })
}

/// Whether `id` is the closed sort of a `#[k::syntax_list]` enum, whose
/// reference type is the enum itself.
fn is_list_sort(id: &StableItemId, bundle: &krs_ir::DescriptorBundle) -> bool {
    bundle.descriptors().iter().any(|descriptor| {
        let DescriptorPayload::Grammar(grammar) = descriptor.payload() else {
            return false;
        };
        let krs_ir::GrammarDescriptor::Production(production) = grammar.as_ref() else {
            return false;
        };
        production.result_sort.sort == krs_ir::DescriptorSortRef::Declared(id.clone())
            && production.attributes.iter().any(|attribute| {
                matches!(
                    attribute,
                    krs_ir::DescriptorProductionAttribute::ListCons { .. }
                )
            })
    })
}

fn is_token_sort(id: &StableItemId, bundle: &krs_ir::DescriptorBundle) -> bool {
    bundle.descriptors().iter().any(|descriptor| {
        let DescriptorPayload::Grammar(grammar) = descriptor.payload() else {
            return false;
        };
        let krs_ir::GrammarDescriptor::Tokens { productions } = grammar.as_ref() else {
            return false;
        };
        productions.iter().any(|production| {
            matches!(
                &production.owner,
                krs_ir::DescriptorProductionOwner::TokenSort { sort }
                    if sort.sort == krs_ir::DescriptorSortRef::Declared(id.clone())
            )
        })
    })
}

fn materialize_reference_strictness(
    output: &mut syn::Variant,
    strictness: Option<&krs_syntax::StrictnessAttribute>,
) -> Result<(), ReferenceExpansionError> {
    let Some(strictness) = strictness else {
        return Ok(());
    };
    let indices = output
        .attrs
        .iter()
        .enumerate()
        .filter(|(_, attribute)| {
            attribute_is(attribute, "strict") || attribute_is(attribute, "seqstrict")
        })
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    let [index] = indices.as_slice() else {
        return Err(ReferenceExpansionError::GeneratedRust(syn::Error::new(
            output.ident.span(),
            "checked enum strictness helper disappeared or was duplicated during projection",
        )));
    };
    let fields = strictness.fields();
    let authored_result = strictness.result_sort();
    let result: syn::Path = if authored_result
        .segments
        .last()
        .is_some_and(|segment| segment.ident == "KResult")
    {
        syn::parse_quote!(k::KResult)
    } else {
        authored_result.clone()
    };
    // The context alias a strictness names decides which context its heating uses, so the long
    // form names it too.
    let using = strictness.using().map(|alias| quote!(using = #alias,));
    output.attrs[*index] = match strictness.kind() {
        krs_syntax::StrictnessKind::Strict => {
            syn::parse_quote!(#[k::strict(#using sequence = [#(#fields),*], result = #result)])
        }
        krs_syntax::StrictnessKind::SeqStrict => {
            syn::parse_quote!(#[k::seqstrict(#using sequence = [#(#fields),*], result = #result)])
        }
    };
    Ok(())
}

fn render_family_grammar(
    declaration: &krs_syntax::EnumConstructorDeclaration,
) -> Result<Vec<syn::Item>, ReferenceExpansionError> {
    let owner = declaration.enum_name();
    let groups = declaration
        .precedence_groups()
        .enumerate()
        .map(|(ordinal, group)| {
            syn::parse_str::<Ident>(&group.emitted_name(owner, ordinal)).map_err(|error| {
                ReferenceExpansionError::GeneratedRust(syn::Error::new(
                    group.range().first(),
                    error,
                ))
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut items = Vec::new();
    if groups.len() >= 2 {
        let mut chain = TokenStream::new();
        for (ordinal, group) in groups.iter().enumerate() {
            if ordinal != 0 {
                chain.extend(quote!(>));
            }
            group.to_tokens(&mut chain);
        }
        let item: syn::ItemMacro = syn::parse2(quote! {
            k::precedence! { for #owner; #chain }
        })
        .map_err(ReferenceExpansionError::GeneratedRust)?;
        items.push(syn::Item::Macro(item));
    }

    let mut sentences = TokenStream::new();
    for (ordinal, group) in declaration.precedence_groups().enumerate() {
        let Some(associativity) = group.associativity() else {
            continue;
        };
        let name = &groups[ordinal];
        match associativity {
            krs_syntax::GroupAssociativity::Left => {
                sentences.extend(quote!(left: #name;));
            }
            krs_syntax::GroupAssociativity::Right => {
                sentences.extend(quote!(right: #name;));
            }
            krs_syntax::GroupAssociativity::NonAssociative => {
                sentences.extend(quote!(non_associative: #name;));
            }
        }
    }
    if !sentences.is_empty() {
        let item: syn::ItemMacro = syn::parse2(quote! {
            k::associativity! { for #owner; #sentences }
        })
        .map_err(ReferenceExpansionError::GeneratedRust)?;
        items.push(syn::Item::Macro(item));
    }
    Ok(items)
}

#[expect(
    clippy::too_many_lines,
    reason = "Trait aliases and direct/ancestor impls are one graph projection."
)]
fn materialize_readable_sorts(
    invocation: &syn::ItemMacro,
) -> Result<Vec<syn::Item>, ReferenceExpansionError> {
    let declaration = krs_syntax::SortsDeclaration::parse_tokens(invocation.mac.tokens.clone())
        .map_err(ReferenceExpansionError::KrsSyntax)?;
    let local_parents = declaration
        .entries()
        .iter()
        .filter_map(|entry| match entry {
            krs_syntax::SortsEntry::Sort(sort) => {
                Some((sort.name().to_string(), sort.parents().to_vec()))
            }
            krs_syntax::SortsEntry::Membership(_) => None,
        })
        .collect::<BTreeMap<_, _>>();
    let mut items = Vec::new();
    for entry in declaration.entries() {
        let krs_syntax::SortsEntry::Sort(sort) = entry else {
            continue;
        };
        let name = sort.name();
        let marker = format_ident!("{name}Sort");
        let semantic_parents = sort
            .parents()
            .iter()
            .map(reference_semantic_sort_path)
            .collect::<Vec<_>>();
        let marker_parents = sort
            .parents()
            .iter()
            .map(reference_marker_path)
            .collect::<Result<Vec<_>, _>>()?;
        let brackets = sort
            .brackets()
            .iter()
            .map(|bracket| {
                let template = bracket.template().literal();
                syn::parse_quote!(#[k::bracket(#template)])
            })
            .collect::<Vec<syn::Attribute>>();
        let item_trait: syn::ItemTrait = if semantic_parents.is_empty() {
            syn::parse2(quote! {
                #[k::sort(alias = #name)]
                #(#brackets)*
                pub trait #marker {}
            })
        } else {
            syn::parse2(quote! {
                #[k::sort(alias = #name, parents = [#(#semantic_parents),*])]
                #(#brackets)*
                pub trait #marker: #(#marker_parents)+* {}
            })
        }
        .map_err(ReferenceExpansionError::GeneratedRust)?;
        let item_alias: syn::ItemType = syn::parse2(quote! {
            pub type #name = k::Term<dyn #marker>;
        })
        .map_err(ReferenceExpansionError::GeneratedRust)?;
        items.push(syn::Item::Trait(item_trait));
        items.push(syn::Item::Type(item_alias));
    }

    let mut emitted_impls = BTreeSet::new();
    for entry in declaration.entries() {
        let krs_syntax::SortsEntry::Membership(membership) = entry else {
            continue;
        };
        for member in membership.members() {
            let direct_sort = membership.supersort();
            let direct_marker = reference_marker_path(direct_sort)?;
            let direct_key = (
                direct_marker.to_token_stream().to_string(),
                member.to_token_stream().to_string(),
            );
            if emitted_impls.insert(direct_key) {
                let direct: syn::ItemImpl = syn::parse2(quote! {
                    #[k::subsort(sort = #direct_sort)]
                    impl #direct_marker for #member {}
                })
                .map_err(ReferenceExpansionError::GeneratedRust)?;
                items.push(syn::Item::Impl(direct));
            }

            let mut ancestors = Vec::new();
            push_reference_sort_ancestors(
                direct_sort,
                &local_parents,
                &mut BTreeSet::new(),
                &mut ancestors,
            );
            for ancestor in ancestors {
                let marker = reference_marker_path(&ancestor)?;
                let key = (
                    marker.to_token_stream().to_string(),
                    member.to_token_stream().to_string(),
                );
                if emitted_impls.insert(key) {
                    let implementation: syn::ItemImpl = syn::parse2(quote! {
                        impl #marker for #member {}
                    })
                    .map_err(ReferenceExpansionError::GeneratedRust)?;
                    items.push(syn::Item::Impl(implementation));
                }
            }
        }
    }
    Ok(items)
}

fn push_reference_sort_ancestors(
    sort: &syn::Path,
    local_parents: &BTreeMap<String, Vec<syn::Path>>,
    visited: &mut BTreeSet<String>,
    output: &mut Vec<syn::Path>,
) {
    let Some(name) = local_reference_sort_name(sort) else {
        return;
    };
    if !visited.insert(name.clone()) {
        return;
    }
    let Some(parents) = local_parents.get(&name) else {
        return;
    };
    for parent in parents {
        if local_reference_sort_name(parent).is_some_and(|name| local_parents.contains_key(&name)) {
            output.push(parent.clone());
            push_reference_sort_ancestors(parent, local_parents, visited, output);
        }
    }
}

fn local_reference_sort_name(path: &syn::Path) -> Option<String> {
    (path.leading_colon.is_none() && path.segments.len() == 1)
        .then(|| path.segments[0].ident.to_string())
}

fn reference_semantic_sort_path(path: &syn::Path) -> syn::Path {
    if is_framework_sort_path(path) {
        let name = &path
            .segments
            .last()
            .expect("a framework sort path has a final segment")
            .ident;
        syn::parse_quote!(k::#name)
    } else {
        path.clone()
    }
}

fn reference_marker_path(path: &syn::Path) -> Result<syn::Path, ReferenceExpansionError> {
    if is_framework_sort_path(path) {
        let name = &path
            .segments
            .last()
            .expect("a framework sort path has a final segment")
            .ident;
        let marker = format_ident!("{name}Sort");
        return Ok(syn::parse_quote!(k::#marker));
    }
    let mut marker = path.clone();
    let Some(last) = marker.segments.last_mut() else {
        return Err(ReferenceExpansionError::GeneratedRust(syn::Error::new(
            path.span(),
            "sort path has no final segment",
        )));
    };
    last.ident = format_ident!("{}Sort", last.ident);
    Ok(marker)
}

fn is_framework_sort_path(path: &syn::Path) -> bool {
    path.segments
        .last()
        .is_some_and(|segment| matches!(segment.ident.to_string().as_str(), "KItem" | "KResult"))
}

fn materialize_configuration_wrappers(
    item: &mut syn::ItemStruct,
) -> Result<(), ReferenceExpansionError> {
    if !has_attribute(&item.attrs, "configuration") && !has_attribute(&item.attrs, "cell") {
        return Ok(());
    }
    let declaration = krs_syntax::ConfigurationDeclaration::parse_tokens(item.to_token_stream())
        .map_err(ReferenceExpansionError::KrsSyntax)?;
    let syn::Fields::Named(fields) = &mut item.fields else {
        return Err(ReferenceExpansionError::GeneratedRust(syn::Error::new(
            item.fields.span(),
            "a fixed configuration must be a named-field struct",
        )));
    };
    for field in &mut fields.named {
        let Some(name) = &field.ident else {
            continue;
        };
        let cell = declaration
            .cells()
            .iter()
            .find(|cell| cell.name() == name)
            .ok_or_else(|| {
                ReferenceExpansionError::GeneratedRust(syn::Error::new(
                    name.span(),
                    "configuration field disappeared during reference projection",
                ))
            })?;
        if !cell.has_inferred_wrapper() {
            continue;
        }
        // An optional cell's wrapper goes inside its `Option` (KF-023, R7).
        let content = krs_syntax::option_content(&field.ty)
            .filter(|_| cell.is_optional())
            .unwrap_or(&field.ty)
            .clone();
        let wrapped: syn::Type = if cell.is_computation_cell() {
            syn::parse_quote!(k::configuration::KCell<#content>)
        } else {
            syn::parse_quote!(k::configuration::Cell<#content>)
        };
        field.ty = if cell.is_optional() {
            syn::parse_quote!(Option<#wrapped>)
        } else {
            wrapped
        };
    }
    Ok(())
}

fn materialize_initializers(item: &mut syn::ItemImpl) -> Result<(), ReferenceExpansionError> {
    let mut contains_initializer = false;
    for impl_item in &mut item.items {
        let syn::ImplItem::Fn(method) = impl_item else {
            continue;
        };
        if !has_attribute(&method.attrs, "init") {
            continue;
        }
        contains_initializer = true;
        let mut parsed_method = method.clone();
        parsed_method
            .attrs
            .retain(|attribute| !attribute_is(attribute, "init"));
        let initializer =
            krs_syntax::InitializerFunction::parse_tokens(parsed_method.to_token_stream())
                .map_err(ReferenceExpansionError::KrsSyntax)?;
        for (input, variable) in method.sig.inputs.iter_mut().zip(initializer.variables()) {
            let syn::FnArg::Typed(parameter) = input else {
                continue;
            };
            if parameter
                .attrs
                .iter()
                .any(|attribute| attribute_is(attribute, "config_var"))
            {
                continue;
            }
            let name = variable.attribute().name();
            let attribute: syn::Attribute = if variable.attribute().is_main() {
                syn::parse_quote!(#[k::config_var(name = #name, main)])
            } else {
                syn::parse_quote!(#[k::config_var(name = #name)])
            };
            parameter.attrs.push(attribute);
        }
        let [syn::Stmt::Expr(syn::Expr::Struct(body), None)] = method.block.stmts.as_mut_slice()
        else {
            return Err(ReferenceExpansionError::GeneratedRust(syn::Error::new(
                method.block.span(),
                "a fixed initializer must contain exactly one struct expression",
            )));
        };
        materialize_initializer_cells(body, initializer.cells())?;
    }
    if contains_initializer && !item.attrs.iter().any(is_initializer_lint_allow) {
        item.attrs.push(syn::parse_quote!(
            #[allow(clippy::must_use_candidate, clippy::needless_pass_by_value)]
        ));
    }
    Ok(())
}

fn materialize_initializer_cells(
    body: &mut syn::ExprStruct,
    cells: &[krs_syntax::FixedCellInitializer],
) -> Result<(), ReferenceExpansionError> {
    for cell in cells {
        let field = body
            .fields
            .iter_mut()
            .find(|field| matches!(&field.member, syn::Member::Named(name) if name == cell.name()))
            .ok_or_else(|| {
                ReferenceExpansionError::GeneratedRust(syn::Error::new(
                    cell.name().span(),
                    "initializer field disappeared during reference projection",
                ))
            })?;
        // An optional cell's value is `Some(value)` or `k::absent!(template)` (KF-023, R7); the
        // template is materialized as a value is, and written back as `k::absent!`'s.
        let has_colon = field.colon_token.is_some();
        let mut absent_template = cell.absent().map(|_| cell.field().expr.clone());
        let expression = match (&mut absent_template, &mut field.expr, cell.is_optional()) {
            (Some(template), _, _) => template,
            (None, syn::Expr::Call(call), true) if call.args.len() == 1 => {
                call.args.first_mut().expect("`Some(..)` has one argument")
            }
            (None, expression, _) => expression,
        };
        qualify_reference_initializer_state_macro(expression)?;
        match cell.content() {
            krs_syntax::InitializerCellContent::Leaf {
                computation,
                inferred_constructor: true,
                ..
            } => {
                let value = expression.clone();
                *expression = if *computation {
                    syn::parse_quote!(k::configuration::KCell::new(#value))
                } else {
                    syn::parse_quote!(k::configuration::Cell::new(#value))
                };
                if !has_colon {
                    field.colon_token = Some(syn::token::Colon::default());
                }
            }
            krs_syntax::InitializerCellContent::Leaf {
                inferred_constructor: false,
                ..
            } => {}
            krs_syntax::InitializerCellContent::Nested { children, .. } => {
                let syn::Expr::Struct(nested) = expression else {
                    return Err(ReferenceExpansionError::GeneratedRust(syn::Error::new(
                        expression.span(),
                        "a nested fixed-cell initializer must be a struct expression",
                    )));
                };
                materialize_initializer_cells(nested, children)?;
            }
        }
        if let Some(template) = absent_template {
            field.expr = syn::parse_quote!(k::absent!(#template));
            if !has_colon {
                field.colon_token = Some(syn::token::Colon::default());
            }
        }
    }
    Ok(())
}

fn qualify_reference_initializer_state_macro(
    expression: &mut syn::Expr,
) -> Result<(), ReferenceExpansionError> {
    let macro_expression = match expression {
        syn::Expr::Macro(expression) => Some(expression),
        syn::Expr::Call(call) => call.args.first_mut().and_then(|argument| match argument {
            syn::Expr::Macro(expression) => Some(expression),
            _ => None,
        }),
        _ => None,
    };
    let Some(expression) = macro_expression else {
        return Ok(());
    };
    if expression.mac.path.leading_colon.is_some() || expression.mac.path.segments.len() != 1 {
        return Ok(());
    }
    let name = expression.mac.path.segments[0].ident.clone();
    if !matches!(name.to_string().as_str(), "k" | "map") {
        return Ok(());
    }
    expression.mac.path =
        syn::parse2(quote!(k::#name)).map_err(ReferenceExpansionError::GeneratedRust)?;
    Ok(())
}

fn has_attribute(attributes: &[syn::Attribute], name: &str) -> bool {
    attributes
        .iter()
        .any(|attribute| attribute_is(attribute, name))
}

fn attribute_is(attribute: &syn::Attribute, name: &str) -> bool {
    attribute
        .path()
        .segments
        .last()
        .is_some_and(|segment| segment.ident == name)
}

fn is_initializer_lint_allow(attribute: &syn::Attribute) -> bool {
    attribute_is(attribute, "allow")
        && attribute
            .meta
            .to_token_stream()
            .to_string()
            .contains("clippy :: must_use_candidate")
}

#[expect(
    clippy::too_many_lines,
    reason = "One rule projection keeps its two sides visibly paired."
)]
fn render_rule(
    clause: &krs_syntax::RuleClause,
    rule: &DescriptorHeadRule,
    semantic: &SemanticRule,
    package: PathScope<'_>,
    bundle: &krs_ir::DescriptorBundle,
    descriptor_index: &DescriptorIndex<'_>,
) -> Result<syn::ItemFn, ReferenceExpansionError> {
    let variable_sorts = semantic
        .variables()
        .iter()
        .map(|variable| (variable.id().as_str(), variable.sort()))
        .collect::<BTreeMap<_, _>>();
    let mut reserved = rule
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<BTreeSet<_>>();
    // An open pattern that rewrites the cell names its tail; one that only
    // reads it keeps the tail anonymous.
    let tail = rule
        .head
        .as_ref()
        .filter(|head| !head.exact && head.result.is_some())
        .map(|_| fresh_ident("tail", &mut reserved))
        .transpose()?;
    let state = fresh_ident("state", &mut reserved)?;
    // A map entry's `x -> _` value is recorded as a binding named `_`, used
    // once and at the sort a narrowing `_: S` gives it, so it denotes what
    // a fresh binder of that sort used once does; it prints as one, since
    // `_` is no Rust binder a typed parameter can name.
    let wildcard = rule
        .bindings
        .iter()
        .any(|binding| binding.name == "_")
        .then(|| fresh_ident("value", &mut reserved))
        .transpose()?;
    let binder = |name: &str| match &wildcard {
        Some(fresh) if name == "_" => Ok(fresh.clone()),
        _ => rust_ident(name),
    };
    let mut parameters = Vec::new();
    for binding in &rule.bindings {
        let name = binder(&binding.name)?;
        let sort = variable_sorts.get(binding.name.as_str()).ok_or_else(|| {
            ReferenceExpansionError::MissingBindingSort {
                rule: clause.rule().item().sig.ident.unraw().to_string(),
                binding: binding.name.clone(),
            }
        })?;
        let ty = render_sort_type(sort, package)?;
        parameters.push((name.unraw().to_string(), quote!(#name: #ty)));
    }

    let mut left_cells = Vec::new();
    let mut right_cells = Vec::new();
    // A clause without the computation cell leaves it out of both sides (E7).
    if let (Some(head), Some(computation)) = (&rule.head, &rule.computation_cell) {
        let computation = render_rule_cell_field(&computation.cell, &rule.configuration, package)?;
        let subject = head
            .items
            .iter()
            .map(|item| render_term(item, true, package, bundle))
            .collect::<Result<Vec<_>, _>>()?;
        let rest = match (&tail, head.exact) {
            (_, true) => Vec::new(),
            (Some(tail), false) => vec![quote!(#tail @ ..)],
            (None, false) => vec![quote!(..)],
        };
        left_cells.push(quote! {
            #computation: k::configuration::KCell(#(#subject),* #(, #rest)*)
        });
        if let Some(result) = &head.result {
            let result_items = match result {
                ProtocolHeadRuleResult::Replace(term) => {
                    vec![render_term(term, false, package, bundle)?]
                }
                ProtocolHeadRuleResult::Splice(splice) => splice
                    .terms()
                    .map(|term| render_term(term, false, package, bundle))
                    .collect::<Result<Vec<_>, _>>()?,
                ProtocolHeadRuleResult::Erase => Vec::new(),
            };
            right_cells.push(if let Some(tail) = &tail {
                quote! {
                    #computation: k::configuration::KCell(#(#result_items,)* ..#tail)
                }
            } else {
                quote! {
                    #computation: k::configuration::KCell(#(#result_items),*)
                }
            });
        }
    }

    let mut instance_tails = 0_usize;
    for (ordinal, extra) in rule.extras.iter().enumerate() {
        match extra {
            ProtocolHeadRuleExtra::RewriteState {
                cell,
                before,
                after,
                ..
            } => {
                let (left, right) = render_readable_state(
                    cell,
                    before,
                    after.as_ref(),
                    &rule.configuration,
                    &mut StateRendering {
                        package,
                        bundle,
                        descriptor_index,
                        reserved: &mut reserved,
                        tails: &mut instance_tails,
                        rests: ordinal,
                    },
                )?;
                left_cells.push(left);
                right_cells.extend(right);
            }
            ProtocolHeadRuleExtra::HaveMap { cell, entries, .. } => {
                let cell = render_rule_cell_field(&cell.cell, &rule.configuration, package)?;
                let entries = entries
                    .iter()
                    .map(|entry| {
                        let key = render_term(&entry.key, true, package, bundle)?;
                        let value = binder(&entry.value_binding)?;
                        Ok(quote!(#key -> #value))
                    })
                    .collect::<Result<Vec<_>, ReferenceExpansionError>>()?;
                let rest = fresh_ident(&format!("rest{ordinal}"), &mut reserved)?;
                left_cells.push(quote! {
                    #cell: k::configuration::Cell(map![#(#entries,)* #rest @ ..])
                });
            }
            ProtocolHeadRuleExtra::UpdateMap {
                cell,
                base_binding,
                update,
            } => {
                let cell = render_rule_cell_field(&cell.cell, &rule.configuration, package)?;
                let base = rust_ident(base_binding)?;
                let update = render_term(update, false, package, bundle)?;
                left_cells.push(quote!(#cell: k::configuration::Cell(#base)));
                right_cells.push(quote! {
                    #cell: k::configuration::Cell(#update)
                });
            }
            ProtocolHeadRuleExtra::RewriteList {
                cell,
                before,
                after,
                ..
            } => {
                // A cell of the builtin `List` is the `list::item` and
                // `list::concat` term its brackets denote; its anonymous
                // `..` is a parameter both sides name.
                let Some(list) = cell_cons_list(&cell.cell, bundle) else {
                    let shared = matches!(before.rest, krs_ir::ProtocolHeadRuleListRest::Shared(_))
                        .then(|| {
                            let rest = fresh_ident("rest", &mut reserved)?;
                            let ty = render_sort_type(
                                &SemanticSortRef::Builtin(krs_ir::BuiltinSort::List),
                                package,
                            )?;
                            parameters.push((rest.to_string(), quote!(#rest: #ty)));
                            Ok::<_, ReferenceExpansionError>(rest)
                        })
                        .transpose()?;
                    let field = render_rule_cell_field(&cell.cell, &rule.configuration, package)?;
                    let before =
                        render_builtin_list(before, shared.as_ref(), true, package, bundle)?;
                    left_cells.push(quote! {
                        #field: k::configuration::Cell(#before)
                    });
                    if let Some(after) = after {
                        let after =
                            render_builtin_list(after, shared.as_ref(), false, package, bundle)?;
                        right_cells.push(quote! {
                            #field: k::configuration::Cell(#after)
                        });
                    }
                    continue;
                };
                // A list cell is the constructor term it denotes (F6); its
                // anonymous `..` is a parameter both sides name.
                let shared = matches!(before.rest, krs_ir::ProtocolHeadRuleListRest::Shared(_))
                    .then(|| {
                        let rest = fresh_ident("rest", &mut reserved)?;
                        let ty = render_sort_type(
                            &SemanticSortRef::Declared(list.sort.clone()),
                            package,
                        )?;
                        parameters.push((rest.to_string(), quote!(#rest: #ty)));
                        Ok::<_, ReferenceExpansionError>(rest)
                    })
                    .transpose()?;
                let field = render_rule_cell_field(&cell.cell, &rule.configuration, package)?;
                let before = render_list(before, &list, shared.as_ref(), true, package, bundle)?;
                left_cells.push(quote! {
                    #field: k::configuration::Cell(#before)
                });
                if let Some(after) = after {
                    let after = render_list(after, &list, shared.as_ref(), false, package, bundle)?;
                    right_cells.push(quote! {
                        #field: k::configuration::Cell(#after)
                    });
                }
            }
            ProtocolHeadRuleExtra::RewriteCell {
                cell,
                before,
                after,
                ..
            } => {
                let group = is_group_cell(&cell.cell, descriptor_index);
                let optional = is_optional_cell(&cell.cell, descriptor_index);
                let cell = render_rule_cell_field(&cell.cell, &rule.configuration, package)?;
                let before = render_term(before, true, package, bundle)?;
                let after = after
                    .as_ref()
                    .map(|after| render_term(after, false, package, bundle))
                    .transpose()?;
                // A nested field's entry has no wrapper (KF-016); a leaf's is `Cell(..)`. A
                // value written on an optional cell matches or writes the cell present, which
                // `cells!` spells `Some(..)` (KF-023).
                let entry = |term: TokenStream| {
                    let entry = if group {
                        term
                    } else {
                        quote!(k::configuration::Cell(#term))
                    };
                    if optional {
                        quote!(Some(#entry))
                    } else {
                        entry
                    }
                };
                // A read-only cell is a subject entry without a result entry.
                let before = entry(before);
                left_cells.push(quote!(#cell: #before));
                right_cells.extend(after.map(|after| {
                    let after = entry(after);
                    quote!(#cell: #after)
                }));
            }
        }
    }
    let configuration = render_declared_path(&rule.configuration, package)?;
    let name = &clause.rule().item().sig.ident;
    let label = syn::LitStr::new(
        rule.label
            .as_ref()
            .map_or_else(
                || name.unraw().to_string().replace('_', "-"),
                |label| label.name.clone(),
            )
            .as_str(),
        Span::call_site(),
    );
    let attrs = &clause.rule().item().attrs;
    // The clause's `#[k::exists]` and `#[k::ensures]` helpers are retained
    // verbatim and placed before `#[k::rule(..)]` (KF-040).
    let existential_helpers = clause.rule().existentials().attributes();
    // The clause's `#[k::requires]` helper is consumed by the readable parser;
    // the reference form restates it from the descriptor, after `#[k::rule]`.
    let requires = rule
        .requires
        .as_ref()
        .map(|condition| {
            render_term(&condition.term, false, package, bundle)
                .map(|term| quote!(#[k::requires(#term)]))
        })
        .transpose()?;
    let evaluation = semantic
        .evaluation()
        .map(|step| {
            let marker = format_ident!("{}", step.kind().as_str());
            let hole = rust_ident(step.hole().as_str())?;
            let mut keys = vec![quote!(#marker), quote!(hole = #hole)];
            if let Some(result) = step.result() {
                let sort = render_result_sort(result.sort(), package)?;
                keys.push(quote!(result = #sort));
            }
            Ok::<_, ReferenceExpansionError>(keys)
        })
        .transpose()?
        .unwrap_or_default();
    // A claim clause is the `#[k::claim]` fn its records stand for (F7).
    let rule_attribute = match &rule.claim {
        Some(claim) => reference_claim_attribute(claim, &label),
        None => reference_rule_attribute(
            rule.priority.as_ref(),
            &evaluation,
            rule.nondet.as_ref(),
            &label,
        )?,
    };
    // A `cells!` rule declares its typed binders in their first-occurrence
    // order in the subject, which lists the cells in another order than
    // the readable record (map reads first), so the order is read back from
    // the rendered subject.
    let subject = quote!(#(#left_cells,)* #state @ ..);
    // A `k::bits!` template's hidden binder is no authored binder, so the
    // subject is read back with it renamed, and the names mapped back.
    let (readable, renamed) = rename_hidden_tokens(subject.clone())?;
    let order = krs_syntax::parse_cells_pattern(readable)
        .and_then(|cells| krs_syntax::cells_pattern_term_binders(&cells))
        .map_err(ReferenceExpansionError::KrsSyntax)?
        .into_iter()
        .map(|binder| {
            renamed
                .iter()
                .find(|(_, fresh)| **fresh == binder)
                .map_or(binder, |(hidden, fresh)| Ident::new(hidden, fresh.span()))
        })
        .collect::<Vec<_>>();
    let position = |name: &str| {
        order
            .iter()
            .position(|binder| binder.unraw() == name)
            .unwrap_or(usize::MAX)
    };
    parameters.sort_by_key(|(name, _)| position(name));
    let parameters = parameters.into_iter().map(|(_, parameter)| parameter);
    // A `#[k::claim]` fn takes its helpers after the claim attribute, which
    // reads them; a rule fn's `#[k::exists]` and `#[k::ensures]` precede it.
    let (before, after) = if rule.claim.is_some() {
        (Vec::new(), existential_helpers.to_vec())
    } else {
        (existential_helpers.to_vec(), Vec::new())
    };
    syn::parse2(quote! {
        #(#attrs)*
        #(#before)*
        #rule_attribute
        #(#after)*
        #requires
        pub fn #name(
            #(#parameters,)*
            k::cells! { #subject }: #configuration,
        ) -> #configuration {
            k::cells! {
                #(#right_cells,)*
                ..#state
            }
        }
    })
    .map_err(ReferenceExpansionError::GeneratedRust)
}

/// Whether a `#[k::requires]` of `item` holds the operator `==`.
///
/// prettyplease writes a list attribute's arguments as `key = value` pairs,
/// with a space after every `=`, so it would print `a == b` as `a = = b`,
/// which no longer parses as the condition; such a condition is restated in
/// its call spelling instead.
fn requires_holds_equality(item: &syn::ItemFn) -> bool {
    fn holds(tokens: TokenStream) -> bool {
        let mut previous_joint_eq = false;
        for tree in tokens {
            match tree {
                proc_macro2::TokenTree::Punct(punct) if punct.as_char() == '=' => {
                    if previous_joint_eq {
                        return true;
                    }
                    previous_joint_eq = punct.spacing() == proc_macro2::Spacing::Joint;
                }
                proc_macro2::TokenTree::Group(group) => {
                    if holds(group.stream()) {
                        return true;
                    }
                    previous_joint_eq = false;
                }
                _ => previous_joint_eq = false,
            }
        }
        false
    }
    item.attrs.iter().any(|attribute| {
        attribute
            .path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "requires")
            && matches!(&attribute.meta, syn::Meta::List(list) if holds(list.tokens.clone()))
    })
}

/// Restates the `requires` of a rule or equation fn from its descriptor, in
/// the function-call spelling of a table row's or a readable clause's
/// condition; the fn's attribute path and position are kept.
fn restate_requires(
    item: &mut syn::ItemFn,
    package: PathScope<'_>,
    module_path: &[String],
    bundle: &krs_ir::DescriptorBundle,
    descriptor_index: &DescriptorIndex<'_>,
    semantic_rules: &BTreeMap<&StableItemId, &SemanticRule>,
) -> Result<(), ReferenceExpansionError> {
    let name = item.sig.ident.unraw().to_string();
    let condition = descriptor_index
        .values()
        .find_map(|descriptor| match descriptor.payload() {
            krs_ir::DescriptorPayload::StructuredRule(rule)
                if descriptor.id().package() == package.package
                    && descriptor.id().module_path() == module_path
                    && descriptor.id().item_name() == name =>
            {
                rule.requires
                    .as_ref()
                    .map(|condition| (descriptor, condition))
            }
            _ => None,
        });
    let Some((descriptor, condition)) = condition else {
        return Ok(());
    };
    let semantic_rule = semantic_rules.get(descriptor.id()).ok_or_else(|| {
        ReferenceExpansionError::MissingSemanticRule(Box::new(descriptor.id().clone()))
    })?;
    let condition = condition
        .term
        .clone()
        .try_map_refs(&mut OperatorCalls::new(
            descriptor,
            semantic_rule,
            semantic_rules,
        ))?;
    let term = render_term(&condition, false, package, bundle)?;
    // Several `#[k::requires]` state one condition, their conjunction: the first is restated as
    // the whole condition and the others are dropped.
    let mut restated = false;
    item.attrs.retain_mut(|attribute| {
        let requires = attribute.path().segments.len() > 1
            && attribute
                .path()
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "requires");
        if !requires {
            return true;
        }
        if restated {
            return false;
        }
        if let syn::Meta::List(list) = &mut attribute.meta {
            list.tokens = term.clone();
            restated = true;
        }
        true
    });
    Ok(())
}

/// The `#[k::equation]` fn one `k::equations!` row stands for, with its
/// paths qualified, since the table's `use` items do not reach it.
fn render_equation_row(
    row: &krs_syntax::EquationRow,
    rule: &krs_ir::StructuredRuleDescriptor,
    package: PathScope<'_>,
    bundle: &krs_ir::DescriptorBundle,
) -> Result<syn::ItemFn, ReferenceExpansionError> {
    let sort = match &rule.subject_sort.sort {
        krs_ir::DescriptorSortRef::Builtin(sort) => {
            let sort = render_builtin_sort(*sort);
            quote!(k::Term<#sort>)
        }
        other => {
            let sort = render_descriptor_sort(other, package)?;
            quote!(k::Term<#sort>)
        }
    };
    let subject = render_term(&rule.subject, true, package, bundle)?;
    let result = rule
        .result
        .as_ref()
        .map(|result| render_term(result, false, package, bundle))
        .transpose()?;
    let requires = rule
        .requires
        .as_ref()
        .map(|condition| {
            render_term(&condition.term, false, package, bundle)
                .map(|term| quote!(#[k::requires(#term)]))
        })
        .transpose()?;
    let keys = row.equation_keys().map(|keys| quote!((#keys)));
    let attrs = &row.rule().item().attrs;
    let name = row.label();
    syn::parse2(quote! {
        #(#attrs)*
        #[k::equation #keys]
        #requires
        fn #name(k::term![#subject]: #sort) -> #sort {
            #result
        }
    })
    .map_err(ReferenceExpansionError::GeneratedRust)
}

/// Fresh names and lookups for rendering readable optional and collection
/// states in the reference spelling (KF-023).
struct StateRendering<'a> {
    package: PathScope<'a>,
    bundle: &'a krs_ir::DescriptorBundle,
    /// The bundle's index, built once per expansion.
    descriptor_index: &'a DescriptorIndex<'a>,
    reserved: &'a mut BTreeSet<String>,
    /// Instance `k` tails named so far (`tail0`, `tail1`, ..).
    tails: &'a mut usize,
    /// The extra's ordinal, which numbers its collection rest.
    rests: usize,
}

/// Renders one readable optional or collection entry as its `cells!`
/// subject and result entries.
fn render_readable_state(
    cell: &krs_ir::DescriptorCellReference,
    before: &krs_ir::ProtocolRuleStateTerm<krs_ir::DescriptorTerm>,
    after: Option<&krs_ir::ProtocolRuleStateTerm<krs_ir::DescriptorTerm>>,
    configuration: &StableItemId,
    rendering: &mut StateRendering<'_>,
) -> Result<(TokenStream, Option<TokenStream>), ReferenceExpansionError> {
    use krs_ir::ProtocolRuleStateTerm as State;
    let field = render_rule_cell_field(&cell.cell, configuration, rendering.package)?;
    let group = is_group_cell(&cell.cell, rendering.descriptor_index);
    let optional = |state: &State<krs_ir::DescriptorTerm>,
                    pattern: bool|
     -> Result<TokenStream, ReferenceExpansionError> {
        Ok(match state {
            State::Absent => quote!(None),
            State::Present { value } => {
                let term = match &**value {
                    State::Term(term) | State::Group(term) => {
                        render_term(term, pattern, rendering.package, rendering.bundle)?
                    }
                    _ => return Err(ReferenceExpansionError::UnsupportedState),
                };
                if group {
                    quote!(Some(#term))
                } else {
                    quote!(Some(k::configuration::Cell(#term)))
                }
            }
            _ => return Err(ReferenceExpansionError::UnsupportedState),
        })
    };
    match (before, after) {
        (State::Instances(before), after) => {
            let rest = fresh_ident(&format!("instances{}", rendering.rests), rendering.reserved)?;
            let declaration = collection_declaration(&cell.cell, rendering.descriptor_index)
                .ok_or(ReferenceExpansionError::UnsupportedState)?;
            let owner = render_declared_path(&declaration, rendering.package)?;
            // Each matched instance's `k` tail, by label, reused by the
            // instance that updates it.
            let mut tails = BTreeMap::new();
            let left = render_instances(before, true, &rest, &owner, &mut tails, rendering)?;
            let right = after
                .map(|after| {
                    let State::Instances(after) = after else {
                        return Err(ReferenceExpansionError::UnsupportedState);
                    };
                    render_instances(after, false, &rest, &owner, &mut tails, rendering)
                })
                .transpose()?;
            Ok((
                quote!(#field: #left),
                right.map(|right| quote!(#field: #right)),
            ))
        }
        (before, after) => {
            let left = optional(before, true)?;
            let right = after.map(|after| optional(after, false)).transpose()?;
            Ok((
                quote!(#field: #left),
                right.map(|right| quote!(#field: #right)),
            ))
        }
    }
}

/// The instance declaration of a collection cell.
fn collection_declaration(
    cell: &krs_ir::DescriptorCellIdentity,
    index: &DescriptorIndex<'_>,
) -> Option<StableItemId> {
    let owner = index.cell_owner(&cell.owner).ok()?;
    let field = owner
        .fields
        .iter()
        .find(|field| field.reference.cell == *cell)?;
    match &field.content {
        krs_ir::ProtocolCellContent::Nested { declaration } => {
            Some(declaration.declaration.clone())
        }
        krs_ir::ProtocolCellContent::Leaf { .. } => None,
    }
}

fn render_instances(
    instances: &krs_ir::ProtocolRuleInstances<krs_ir::DescriptorTerm>,
    pattern: bool,
    rest: &Ident,
    owner: &TokenStream,
    tails: &mut BTreeMap<String, Ident>,
    rendering: &mut StateRendering<'_>,
) -> Result<TokenStream, ReferenceExpansionError> {
    let mut items = Vec::new();
    for instance in &instances.front {
        items.push(render_instance(instance, pattern, owner, tails, rendering)?);
    }
    if !matches!(instances.rest, krs_ir::ProtocolRuleFrame::Exact) {
        items.push(if pattern {
            quote!(#rest @ ..)
        } else {
            quote!(..#rest)
        });
    }
    for instance in &instances.back {
        items.push(render_instance(instance, pattern, owner, tails, rendering)?);
    }
    Ok(match instances.delimiter {
        krs_ir::InstanceDelimiter::Brace => quote!({ #(#items),* }),
        krs_ir::InstanceDelimiter::Bracket => quote!([ #(#items),* ]),
    })
}

fn render_instance(
    instance: &krs_ir::ProtocolRuleInstance<krs_ir::DescriptorTerm>,
    pattern: bool,
    owner: &TokenStream,
    tails: &mut BTreeMap<String, Ident>,
    rendering: &mut StateRendering<'_>,
) -> Result<TokenStream, ReferenceExpansionError> {
    use krs_ir::ProtocolRuleStateTerm as State;
    let mut fields = Vec::new();
    // The tail of a matched instance's `k`, which its update reuses.
    let reused = match &instance.rest {
        krs_ir::ProtocolInstanceRest::Update { label } => tails.get(label).cloned(),
        _ => None,
    };
    for field in &instance.fields {
        let name = rust_ident(&field.field)?;
        let value = match &field.value {
            State::Term(term) | State::Group(term) => {
                render_term(term, pattern, rendering.package, rendering.bundle)?
            }
            State::KSequence(sequence) => {
                let items = sequence
                    .items
                    .iter()
                    .map(|item| {
                        render_term(&item.value, pattern, rendering.package, rendering.bundle)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let tail = match (&sequence.tail, pattern) {
                    (krs_ir::ProtocolRuleFrame::Exact, _) => None,
                    (_, true) => {
                        let tail =
                            fresh_ident(&format!("tail{}", *rendering.tails), rendering.reserved)?;
                        *rendering.tails += 1;
                        if let Some(label) = &instance.label {
                            tails.insert(label.clone(), tail.clone());
                        }
                        Some(quote!(#tail @ ..))
                    }
                    (_, false) => {
                        let tail = reused
                            .clone()
                            .ok_or(ReferenceExpansionError::UnsupportedState)?;
                        Some(quote!(..#tail))
                    }
                };
                let items = items.into_iter().chain(tail);
                quote!(k::k![#(#items),*])
            }
            // A map cell's entries, its other entries open where the record leaves them so.
            State::Map(krs_ir::ProtocolRuleMap {
                body: krs_ir::ProtocolRuleMapBody::Items { items, remainder },
                ..
            }) => {
                let entries = items
                    .iter()
                    .map(|item| {
                        let key =
                            render_term(&item.key, pattern, rendering.package, rendering.bundle)?;
                        let value =
                            render_term(&item.value, pattern, rendering.package, rendering.bundle)?;
                        Ok(quote!(#key -> #value))
                    })
                    .collect::<Result<Vec<_>, ReferenceExpansionError>>()?;
                let rest = match remainder {
                    krs_ir::ProtocolRuleFrame::Exact => None,
                    krs_ir::ProtocolRuleFrame::Anonymous { .. } => Some(quote!(..)),
                    _ => return Err(ReferenceExpansionError::UnsupportedState),
                };
                let parts = entries.into_iter().chain(rest);
                quote!(k::map![#(#parts),*])
            }
            _ => return Err(ReferenceExpansionError::UnsupportedState),
        };
        fields.push(quote!(#name: #value));
    }
    match &instance.rest {
        krs_ir::ProtocolInstanceRest::Exact => {}
        krs_ir::ProtocolInstanceRest::Open => fields.push(quote!(..)),
        krs_ir::ProtocolInstanceRest::Update { label } => {
            let label = rust_ident(label)?;
            fields.push(quote!(..#label));
        }
    }
    let record = quote!(k::fragment![#owner { #(#fields),* }]);
    Ok(match &instance.label {
        Some(label) => {
            let label = rust_ident(label)?;
            quote!(#label @ #record)
        }
        None => record,
    })
}

/// Renders `#[k::rule(..)]` with its keys in the canonical order
/// (`owise | priority = N`, then `heat | cool, hole = x, result = S`, then
/// `nondet = g`, then `label`).
fn reference_rule_attribute(
    priority: Option<&krs_ir::DescriptorRulePriority>,
    evaluation: &[TokenStream],
    nondet: Option<&krs_ir::DescriptorNondetGroup>,
    label: &syn::LitStr,
) -> Result<TokenStream, ReferenceExpansionError> {
    let mut keys = Vec::new();
    if let Some(priority) = priority {
        if priority.key.role() == ProvenanceRole::RuleOwise {
            keys.push(quote!(owise));
        } else {
            let value = proc_macro2::Literal::u32_unsuffixed(priority.value);
            keys.push(quote!(priority = #value));
        }
    }
    keys.extend(evaluation.iter().cloned());
    if let Some(nondet) = nondet {
        let group = rust_ident(&nondet.name)?;
        keys.push(quote!(nondet = #group));
    }
    keys.push(quote!(label = #label));
    Ok(quote!(#[k::rule(#(#keys),*)]))
}

/// The `#[k::claim(..)]` of a readable claim: its modality, label, and flags.
fn reference_claim_attribute(claim: &krs_ir::HeadRuleClaim, label: &syn::LitStr) -> TokenStream {
    let mut keys = vec![match claim.modality {
        krs_ir::ClaimModality::AllPaths => quote!(all_paths),
        krs_ir::ClaimModality::OnePath => quote!(one_path),
    }];
    keys.push(quote!(label = #label));
    if claim.circularity_key.is_some() {
        keys.push(quote!(circularity));
    }
    if claim.trusted_key.is_some() {
        keys.push(quote!(trusted));
    }
    quote!(#[k::claim(#(#keys),*)])
}

fn render_rule_cell_field(
    cell: &krs_ir::DescriptorCellIdentity,
    configuration: &StableItemId,
    package: PathScope<'_>,
) -> Result<TokenStream, ReferenceExpansionError> {
    let field = rust_ident(&cell.field)?;
    if &cell.owner == configuration {
        return Ok(quote!(#field));
    }
    let owner = render_declared_path(&cell.owner, package)?;
    Ok(quote!(#owner::#field))
}

/// The Rust spelling that reads back as the canonical Float `token`: one literal
/// token (so `-0.0` stays signed) or an `f32::`/`f64::` constant path.
fn float_literal(token: &str) -> Result<TokenStream, ReferenceExpansionError> {
    let invalid = || ReferenceExpansionError::InvalidLiteral(token.to_owned());
    match krs_ir::float_token::rust_spelling(token).map_err(|_| invalid())? {
        krs_ir::float_token::RustFloat::Literal(literal) => literal
            .parse::<proc_macro2::Literal>()
            .map(|literal| TokenTree::Literal(literal).into())
            .map_err(|_| invalid()),
        krs_ir::float_token::RustFloat::Constant(width, constant) => {
            let width = syn::Ident::new(width.name(), Span::call_site());
            let constant = syn::Ident::new(constant.name(), Span::call_site());
            Ok(quote!(#width::#constant))
        }
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "Exhaustive rendering mirrors the closed descriptor term sum."
)]
fn render_term(
    term: &DescriptorTerm,
    pattern: bool,
    package: PathScope<'_>,
    bundle: &krs_ir::DescriptorBundle,
) -> Result<TokenStream, ReferenceExpansionError> {
    match term {
        DescriptorTerm::Variable { name, .. } => {
            let name = rust_ident(name)?;
            Ok(quote!(#name))
        }
        DescriptorTerm::Application {
            reference,
            head_class,
            arguments,
            instance,
            open,
            ..
        } => {
            let head = match &reference.application {
                // A turbofish renders its sort markers, the types inside
                // `k::Term<..>`: a readable `Choose::<Exp>` is
                // `Choose::<dyn crate::ExpSort>` (KF-027).
                DescriptorApplicationRef::Declared(id) if !instance.is_empty() => {
                    let head = render_declared_application(id, package.at(&reference.key))?;
                    let markers = instance
                        .iter()
                        .map(|sort| render_sort_marker(&sort.sort, package))
                        .collect::<Result<Vec<_>, _>>()?;
                    quote!(#head::<#(#markers),*>)
                }
                DescriptorApplicationRef::Declared(id) => {
                    render_declared_application(id, package.at(&reference.key))?
                }
                DescriptorApplicationRef::Builtin(operation) => {
                    render_builtin_operation(*operation)
                }
                DescriptorApplicationRef::Map(operation) => {
                    render_facade_marker(operation.facade_marker())
                }
                DescriptorApplicationRef::List(operation) => {
                    render_facade_marker(operation.facade_marker())
                }
                DescriptorApplicationRef::Set(operation) => {
                    render_facade_marker(operation.facade_marker())
                }
                DescriptorApplicationRef::Ml(connective) => {
                    let name = format_ident!("{}", connective.facade_marker().name);
                    quote!(k::ml::#name)
                }
                // [`OperatorCalls`] leaves only `-x` on `Int` an operator:
                // K has no unary minus on `Int`, so it is `int::sub(0, x)`.
                DescriptorApplicationRef::Operator(BuiltinOperator::Neg) => {
                    let krs_ir::Arguments::Positional(operands) = arguments else {
                        return Err(ReferenceExpansionError::UnresolvedOperator("-"));
                    };
                    let [operand] = operands.as_slice() else {
                        return Err(ReferenceExpansionError::UnresolvedOperator("-"));
                    };
                    let operand = render_term(operand, pattern, package, bundle)?;
                    let sub = render_builtin_operation(BuiltinOperation::IntSub);
                    return Ok(quote!(#sub(0, #operand)));
                }
                DescriptorApplicationRef::Operator(operator) => {
                    return Err(ReferenceExpansionError::UnresolvedOperator(
                        operator.symbol(),
                    ));
                }
                // [`OperatorCalls`] replaces every index and collection method
                // by the call it denotes.
                DescriptorApplicationRef::CollectionMethod(method) => {
                    return Err(ReferenceExpansionError::UnresolvedCollectionMethod(*method));
                }
                // [`OperatorCalls`] leaves a level a notation only where it
                // builds the builtin `List`.
                DescriptorApplicationRef::ListNotation(notation) => {
                    return render_builtin_list_level(
                        *notation, arguments, pattern, package, bundle,
                    );
                }
            };
            if arguments.is_empty()
                && matches!(
                    head_class,
                    krs_ir::DescriptorApplicationHeadClass::BareReference
                )
            {
                return Ok(head);
            }
            // A pattern `Ctor { .. }` names no field: every field is `_`.
            let fieldless = *open && pattern;
            if arguments.is_empty() && !fieldless {
                return Ok(quote!(#head()));
            }
            let arguments = match arguments {
                krs_ir::Arguments::Positional(values) if !fieldless => {
                    let values = values
                        .iter()
                        .map(|value| render_term(value, pattern, package, bundle))
                        .collect::<Result<Vec<_>, _>>()?;
                    return Ok(quote!(#head(#(#values),*)));
                }
                krs_ir::Arguments::Positional(_) => Vec::new(),
                krs_ir::Arguments::Named(values) => values.iter().collect(),
            };
            let DescriptorApplicationRef::Declared(id) = &reference.application else {
                return Err(ReferenceExpansionError::NamedBuiltinApplication);
            };
            let descriptor = bundle
                .descriptors()
                .iter()
                .find(|descriptor| descriptor.id() == id)
                .ok_or_else(|| ReferenceExpansionError::MissingDeclaration(Box::new(id.clone())))?;
            let DescriptorPayload::Constructor(constructor) = descriptor.payload() else {
                return Err(ReferenceExpansionError::NamedNonConstructor(Box::new(
                    id.clone(),
                )));
            };
            let mut supplied = BTreeMap::new();
            for argument in arguments {
                let field = &argument.field;
                let value = argument.value.as_ref();
                if supplied.insert(field.as_str(), value).is_some() {
                    return Err(ReferenceExpansionError::DuplicateApplicationField {
                        id: Box::new(id.clone()),
                        field: field.as_str().to_owned(),
                    });
                }
            }
            let mut values = Vec::with_capacity(constructor.fields.len());
            for field in &constructor.fields {
                if let Some(value) = supplied.remove(field.name.as_str()) {
                    values.push(render_term(value, pattern, package, bundle)?);
                } else if pattern {
                    values.push(quote!(_));
                } else {
                    return Err(ReferenceExpansionError::MissingApplicationField {
                        id: Box::new(id.clone()),
                        field: field.name.clone(),
                    });
                }
            }
            if let Some(field) = supplied.keys().next() {
                return Err(ReferenceExpansionError::UnknownApplicationField {
                    id: Box::new(id.clone()),
                    field: (*field).to_owned(),
                });
            }
            Ok(quote!(#head(#(#values),*)))
        }
        DescriptorTerm::Literal { literal, .. } => match literal {
            // One literal token, so a negative value prints as `-1`, not `- 1`.
            krs_ir::DescriptorLiteral::Int(value) => value
                .parse::<proc_macro2::Literal>()
                .map(|literal| TokenTree::Literal(literal).into())
                .map_err(|_| ReferenceExpansionError::InvalidLiteral(value.clone())),
            krs_ir::DescriptorLiteral::Bool(value) => Ok(quote!(#value)),
            krs_ir::DescriptorLiteral::String(value) => {
                let value = syn::LitStr::new(value, Span::call_site());
                Ok(quote!(#value))
            }
            krs_ir::DescriptorLiteral::Float(token) => float_literal(token),
        },
        DescriptorTerm::Wildcard { .. } => Ok(quote!(_)),
        DescriptorTerm::BuiltinToken { sort, value, .. } => match sort {
            BuiltinSort::Id => {
                let value = syn::LitStr::new(value, Span::call_site());
                Ok(quote!(k::id!(#value)))
            }
            BuiltinSort::Bytes => {
                let value = krs_ir::bytes_token::decode(value)
                    .map_err(|_| ReferenceExpansionError::InvalidLiteral(value.clone()))?;
                let value = syn::LitByteStr::new(&value, Span::call_site());
                Ok(quote!(k::bytes!(#value)))
            }
            _ => Err(ReferenceExpansionError::UnsupportedBuiltinToken(*sort)),
        },
        DescriptorTerm::Anonymous { sort, spelling, .. } => {
            let sort = render_descriptor_sort(&sort.sort, package)?;
            let spelling = syn::LitStr::new(spelling, Span::call_site());
            Ok(quote!(k::anonymous!(#sort, #spelling)))
        }
        DescriptorTerm::Lexeme { sort, text, .. } => {
            let sort = render_descriptor_sort(&sort.sort, package)?;
            let text = syn::LitStr::new(text, Span::call_site());
            Ok(quote!(k::lexeme!(#sort, #text)))
        }
        DescriptorTerm::SortTest {
            kind,
            sort,
            operand,
            ..
        } => {
            let sort = render_descriptor_sort(&sort.sort, package)?;
            let operand = render_term(operand, pattern, package, bundle)?;
            Ok(match kind {
                krs_ir::SortTestKind::Predicate => quote!(k::is!(#sort, #operand)),
                krs_ir::SortTestKind::Projection => quote!(k::project!(#sort, #operand)),
            })
        }
        DescriptorTerm::As {
            name,
            pattern: aliased,
            ..
        } => {
            let name = rust_ident(name)?;
            let aliased = render_term(aliased, pattern, package, bundle)?;
            Ok(quote!(#name @ #aliased))
        }
        DescriptorTerm::Or { alternatives, .. } => {
            let alternatives = alternatives
                .iter()
                .map(|alternative| render_term(alternative, pattern, package, bundle))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(quote!((#(#alternatives)|*)))
        }
        DescriptorTerm::OrBool { arguments, .. } => {
            let arguments = arguments
                .iter()
                .map(|term| render_term(term, pattern, package, bundle))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(quote!(k::or_bool!(#(#arguments),*)))
        }
        DescriptorTerm::Matches {
            subject,
            pattern: matched,
            ..
        } => {
            let subject = render_term(subject, pattern, package, bundle)?;
            let matched = render_term(matched, true, package, bundle)?;
            Ok(quote!(k::matches!(#subject, #matched)))
        }
        // K's local rewrite (KF-011): `()` on the right is `.K`.
        DescriptorTerm::Rewrite { from, to, .. } => {
            let from = render_term(from, true, package, bundle)?;
            let to = to
                .as_ref()
                .map(|to| render_term(to, false, package, bundle))
                .transpose()?
                .unwrap_or_else(|| quote!(()));
            Ok(quote!(k::rewrite!(#from => #to)))
        }
        // A block's `let` statements nest to the right; they print as one
        // Rust block.
        DescriptorTerm::Let { .. } => {
            let mut statements = Vec::new();
            let mut current = term;
            while let DescriptorTerm::Let {
                pattern: bound,
                sort,
                value,
                body,
                ..
            } = current
            {
                let bound = render_term(bound, true, package, bundle)?;
                let value = render_term(value, pattern, package, bundle)?;
                statements.push(if let Some(sort) = sort {
                    let sort = render_descriptor_sort(&sort.sort, package)?;
                    quote!(let #bound: #sort = #value;)
                } else {
                    quote!(let #bound = #value;)
                });
                current = body;
            }
            let result = render_term(current, pattern, package, bundle)?;
            Ok(quote!({ #(#statements)* #result }))
        }
        DescriptorTerm::Closure {
            name, sort, body, ..
        } => {
            let name = rust_ident(name)?;
            let sort = render_descriptor_sort(&sort.sort, package)?;
            let body = render_term(body, pattern, package, bundle)?;
            Ok(quote!(|#name: #sort| #body))
        }
        DescriptorTerm::Cell {
            declaration,
            fields,
            ..
        } => {
            let owner = render_declared_path(declaration, package)?;
            let fields = fields
                .iter()
                .map(|field| {
                    let name = rust_ident(field.field.as_str())?;
                    let value = render_term(&field.value, pattern, package, bundle)?;
                    Ok(quote!(#name: #value))
                })
                .collect::<Result<Vec<_>, ReferenceExpansionError>>()?;
            Ok(quote!(k::fragment![#owner { #(#fields),* }]))
        }
    }
}

fn render_sort_type(
    sort: &SemanticSortRef,
    package: PathScope<'_>,
) -> Result<TokenStream, ReferenceExpansionError> {
    match sort {
        // A framework sort, such as a computation item's `KItem`, is the
        // facade's `k::KItem`.
        SemanticSortRef::Declared(id) => render_sort_path(id, package),
        // A whole-group binder is typed by its nested `#[k::cell]` struct (KF-016).
        SemanticSortRef::Cell(id) => render_declared_path(id, package),
        SemanticSortRef::Builtin(sort) => {
            let sort = render_builtin_sort(*sort);
            Ok(quote!(k::Term<#sort>))
        }
        SemanticSortRef::Parameter(name) => {
            let name = rust_ident(name.as_str())?;
            Ok(quote!(k::Term<#name>))
        }
    }
}

fn render_descriptor_sort(
    sort: &krs_ir::DescriptorSortRef,
    package: PathScope<'_>,
) -> Result<TokenStream, ReferenceExpansionError> {
    match sort {
        krs_ir::DescriptorSortRef::Declared(id) => render_sort_path(id, package),
        krs_ir::DescriptorSortRef::Cell(id) => render_declared_path(id, package),
        krs_ir::DescriptorSortRef::Builtin(sort) => Ok(render_builtin_sort(*sort)),
        krs_ir::DescriptorSortRef::Parameter(name) => {
            let name = rust_ident(name)?;
            Ok(quote!(#name))
        }
    }
}

/// Renders a sort path as an island or key argument names it: a local sort
/// by its `crate::` path, a framework sort as `k::KItem` or `k::KResult`.
fn render_sort_path(
    id: &StableItemId,
    package: PathScope<'_>,
) -> Result<TokenStream, ReferenceExpansionError> {
    if id.package().k_namespace() == crate::partition::FRAMEWORK_NAMESPACE {
        let name = rust_ident(id.item_name())?;
        return Ok(quote!(k::#name));
    }
    render_declared_path(id, package)
}

/// Renders the `result = S` sort of a heat or cool rule (KF-014).
fn render_result_sort(
    sort: &SemanticSortRef,
    package: PathScope<'_>,
) -> Result<TokenStream, ReferenceExpansionError> {
    match sort {
        SemanticSortRef::Declared(id) => render_sort_path(id, package),
        SemanticSortRef::Cell(id) => render_declared_path(id, package),
        SemanticSortRef::Builtin(sort) => Ok(render_builtin_sort(*sort)),
        SemanticSortRef::Parameter(name) => {
            let name = rust_ident(name.as_str())?;
            Ok(quote!(#name))
        }
    }
}

fn render_declared_application(
    id: &StableItemId,
    package: PathScope<'_>,
) -> Result<TokenStream, ReferenceExpansionError> {
    if let Some(path) = package.written_path(id) {
        return Ok(quote!(#path));
    }
    let Some(owner) = id
        .disambiguator()
        .strip_prefix(ENUM_VARIANT_DISAMBIGUATOR_PREFIX)
    else {
        return render_declared_path(id, package);
    };
    let owner = rust_ident(owner)?;
    let variant = rust_ident(id.item_name())?;
    let path = render_local_path(id, package, &[owner, variant])?;
    Ok(quote!(#path))
}

/// The path of the item `id`: the path the printed clause writes to it, where it is another
/// package's and the clause writes one ([`WrittenPaths`]), else [`render_local_path`]'s.
fn render_declared_path(
    id: &StableItemId,
    package: PathScope<'_>,
) -> Result<TokenStream, ReferenceExpansionError> {
    if let Some(path) = package.written_path(id) {
        return Ok(quote!(#path));
    }
    let item = rust_ident(id.item_name())?;
    let path = render_local_path(id, package, &[item])?;
    Ok(quote!(#path))
}

/// The path of `suffix` (an item and the segments below it) in the module `id` is declared in.
///
/// An item of the printed package prints by its `crate::` path, which names an item of any
/// module of the crate. A dependency's item prints by its declaring path where that is known to
/// compile ([`dependency_path`]).
fn render_local_path(
    id: &StableItemId,
    package: PathScope<'_>,
    suffix: &[Ident],
) -> Result<syn::Path, ReferenceExpansionError> {
    let mut path: syn::Path = if id.package() == package.package {
        let head = suffix.first().map(|head| head.unraw().to_string());
        if !package.reaches(id.module_path(), head.as_deref().unwrap_or_default()) {
            return Err(ReferenceExpansionError::PrivateModule {
                item: Box::new(id.clone()),
                from: crate_module_path(package.module),
            });
        }
        let mut path: syn::Path = syn::parse_quote!(crate);
        for segment in id.module_path() {
            path.segments
                .push(syn::PathSegment::from(rust_ident(segment)?));
        }
        path
    } else {
        let segments = dependency_path(id, package, suffix.first())?;
        let mut path: syn::Path = syn::parse_quote!(::placeholder);
        path.segments.clear();
        for segment in &segments {
            path.segments
                .push(syn::PathSegment::from(rust_ident(segment)?));
        }
        path
    };
    path.segments
        .extend(suffix.iter().cloned().map(syn::PathSegment::from));
    Ok(path)
}

/// The path, from the extern prelude (printed after `::`), to the module that holds `head`, an
/// item a dependency package declares in the module of `id`, for a reference the printed clause
/// writes no path to ([`WrittenPaths`]); `head` itself is not in it.
///
/// `::dep::m::Item` names the item the module `m` declares wherever it compiles, and it compiles
/// from another crate only where every module on it is public, which the collected declarations
/// do not record. So it is printed:
///
/// - for an item declared at the crate root, `dep::Item`: the source reaches the crate only by
///   its name, and the crate root's own items need no module to be public;
/// - where the source writes a path to the declaring module or through it (`use dep::m;`,
///   `dep::m::Other`, or `d::m::Item` in a module where `use dep as d;` stands,
///   [`authored_paths`]): rustc resolved every module on it from the printed crate, which sees
///   another crate's items alike from all its modules. The item itself is taken to be public,
///   as at the crate root.
///
/// Elsewhere printing is refused ([`ReferenceExpansionError::DependencyPath`]). No other path is
/// taken from what the source writes elsewhere: a path's last segment is the name a module
/// exports, which a renaming re-export (`pub use x::Same as Unit;`) gives another item, so a
/// path that ends in an item's name need not name that item. A package the source does not
/// depend on directly has no crate name there
/// ([`ReferenceExpansionError::ExternalDeclaration`]).
fn dependency_path(
    id: &StableItemId,
    scope: PathScope<'_>,
    head: Option<&Ident>,
) -> Result<Vec<String>, ReferenceExpansionError> {
    let crate_name = scope
        .crates
        .get(id.package())
        .ok_or_else(|| ReferenceExpansionError::ExternalDeclaration(Box::new(id.clone())))?;
    let mut declared = vec![crate_name.clone()];
    declared.extend(id.module_path().iter().cloned());
    let Some(head) = head else {
        return Ok(declared);
    };
    let head = head.unraw().to_string();
    // A path written to the declaring module itself, or through it, compiles only where every
    // module on it is public; another crate's item is visible from every module of the printed
    // crate alike, so a path the source writes anywhere is evidence everywhere. A module holds
    // one item of a name in the type namespace, so the written modules are the declaring ones.
    let module = declared.last().cloned().unwrap_or_default();
    let written = scope
        .authored
        .get(&(crate_name.clone(), module))
        .is_some_and(|paths| paths.contains(&declared));
    if id.module_path().is_empty() || written {
        return Ok(declared);
    }
    Err(ReferenceExpansionError::DependencyPath {
        item: Box::new(id.clone()),
        declared: format!("{}::{head}", declared.join("::")),
    })
}

/// The paths `files`, the module files of one crate, write to an item of a crate `crates` names,
/// by crate name and item name: each path, from the crate name, that ends in that item, through a
/// `use` (before its `as`) or in the tokens of a readable macro `facade` names (`k::rules!`,
/// `k::sorts!`, ..), whose paths the collector resolved through rustc.
///
/// Every file of the crate counts: another crate's items are visible alike from all the modules
/// of the crate, so a path that compiles in one module compiles in each. Only paths rustc
/// resolved from the crate name count:
/// - an item under `#[cfg]` (an inline module's inner `#![cfg]` included) does not, since its
///   condition may not have held, and then rustc resolved none of its paths (a file under
///   `#![cfg]` is one of `files` only where a descriptor shows its condition held,
///   [`ModuleTree::read`]);
/// - neither do the tokens of other items: a `macro_rules!` body is resolved only where it is
///   invoked, and a `#[cfg]` may stand on any statement, field or arm of an item;
/// - in a module that declares or imports an item of a crate's name (`mod dep {..}`,
///   `use x::y as dep;`), that name is the item, not the crate.
///
/// A path from a name that a `use` or an `extern crate` of the same module gives a path from a
/// crate name (`use dep as d;`, `use dep::m as mm;`) is that path: `d::Item` is `dep::Item`,
/// which the extern prelude names wherever the source stands. A module's `use` reaches only the
/// module's own items, not the modules it declares, so a rename applies to the paths of its
/// module alone ([`renamed_crates`]).
#[expect(
    clippy::too_many_lines,
    reason = "The path collectors share one scope of crate names and renames."
)]
fn authored_paths<'f>(
    files: impl IntoIterator<Item = &'f syn::File>,
    crates: &BTreeMap<PackageId, String>,
    facade: &FacadeScope,
) -> BTreeMap<(String, String), BTreeSet<Vec<String>>> {
    type Paths = BTreeMap<(String, String), BTreeSet<Vec<String>>>;
    /// The crate names, and the paths from them that a module's `use .. as` names stand for.
    struct Names<'a> {
        crates: &'a BTreeSet<&'a String>,
        renamed: BTreeMap<String, Vec<String>>,
    }
    fn record(path: &[String], names: &Names<'_>, paths: &mut Paths) {
        let path = match path.first().and_then(|first| names.renamed.get(first)) {
            Some(target) => target.iter().chain(&path[1..]).cloned().collect(),
            None => path.to_vec(),
        };
        let Some(first) = path.first().filter(|first| names.crates.contains(first)) else {
            return;
        };
        for end in 2..=path.len() {
            paths
                .entry((first.clone(), path[end - 1].clone()))
                .or_default()
                .insert(path[..end].to_vec());
        }
    }
    fn uses(tree: &syn::UseTree, prefix: &mut Vec<String>, names: &Names<'_>, paths: &mut Paths) {
        match tree {
            syn::UseTree::Path(path) => {
                prefix.push(path.ident.unraw().to_string());
                uses(&path.tree, prefix, names, paths);
                prefix.pop();
            }
            syn::UseTree::Name(name) => {
                prefix.push(name.ident.unraw().to_string());
                record(prefix, names, paths);
                prefix.pop();
            }
            syn::UseTree::Rename(rename) => {
                prefix.push(rename.ident.unraw().to_string());
                record(prefix, names, paths);
                prefix.pop();
            }
            syn::UseTree::Group(group) => {
                for tree in &group.items {
                    uses(tree, prefix, names, paths);
                }
            }
            syn::UseTree::Glob(_) => {}
        }
    }
    // Every maximal `ident (:: ident)*` run of `tokens`, groups searched too.
    fn runs(tokens: TokenStream, names: &Names<'_>, paths: &mut Paths) {
        let tokens = tokens.into_iter().collect::<Vec<_>>();
        let separator = |at: usize| {
            matches!((tokens.get(at), tokens.get(at + 1)),
                (Some(TokenTree::Punct(first)), Some(TokenTree::Punct(second)))
                    if first.as_char() == ':' && second.as_char() == ':'
                        && first.spacing() == proc_macro2::Spacing::Joint)
        };
        let mut at = 0;
        while at < tokens.len() {
            match &tokens[at] {
                TokenTree::Group(group) => {
                    runs(group.stream(), names, paths);
                    at += 1;
                }
                TokenTree::Ident(ident) if at < 2 || !separator(at - 2) => {
                    let mut path = vec![ident.unraw().to_string()];
                    at += 1;
                    while separator(at)
                        && let Some(TokenTree::Ident(next)) = tokens.get(at + 2)
                    {
                        path.push(next.unraw().to_string());
                        at += 3;
                    }
                    record(&path, names, paths);
                }
                _ => at += 1,
            }
        }
    }
    /// The paths of one module's items, at the indices `chain` of the inline modules of a file
    /// whose readable macros are `entries`, each inline module's with its own names.
    fn module(
        items: &[syn::Item],
        crates: &BTreeSet<&String>,
        entries: &BTreeMap<Vec<usize>, FunctionMacro>,
        chain: &mut Vec<usize>,
        paths: &mut Paths,
    ) {
        // A child module sees every crate name again, whatever its parent declares.
        let shadowed = local_names(items);
        let unshadowed = crates
            .iter()
            .copied()
            .filter(|name| !shadowed.contains(name.as_str()))
            .collect::<BTreeSet<_>>();
        let names = Names {
            crates: &unshadowed,
            renamed: renamed_crates(items, &unshadowed),
        };
        for (index, item) in items.iter().enumerate() {
            if item_attributes(item)
                .iter()
                .any(|attribute| attribute.path().is_ident("cfg"))
            {
                continue;
            }
            chain.push(index);
            match item {
                syn::Item::Mod(syn::ItemMod {
                    content: Some((_, items)),
                    ..
                }) => module(items, crates, entries, chain, paths),
                syn::Item::Use(item_use) => {
                    uses(&item_use.tree, &mut Vec::new(), &names, paths);
                }
                syn::Item::Macro(invocation) if entries.contains_key(chain.as_slice()) => {
                    runs(invocation.mac.tokens.clone(), &names, paths);
                }
                _ => {}
            }
            chain.pop();
        }
    }
    let crate_names = crates.values().collect::<BTreeSet<_>>();
    let mut paths = BTreeMap::new();
    if !crate_names.is_empty() {
        for file in files {
            let entries = reference_macro_entries(file, facade);
            module(
                &file.items,
                &crate_names,
                &entries,
                &mut Vec::new(),
                &mut paths,
            );
        }
    }
    paths
}

/// The names the items of one module declare or import, other than an import of a crate by its
/// own name (`use dep;`), in the namespace a path's first segment is resolved in.
fn local_names(items: &[syn::Item]) -> BTreeSet<String> {
    fn bound(tree: &syn::UseTree, depth: usize, names: &mut BTreeSet<String>) {
        match tree {
            syn::UseTree::Path(path) => bound(&path.tree, depth + 1, names),
            syn::UseTree::Name(name) => {
                // `use dep;` and `use dep::{self}` import the crate as itself.
                let name = name.ident.unraw().to_string();
                if depth > 0 && name != "self" {
                    names.insert(name);
                }
            }
            syn::UseTree::Rename(rename) => {
                names.insert(rename.rename.unraw().to_string());
            }
            syn::UseTree::Group(group) => {
                for tree in &group.items {
                    bound(tree, depth, names);
                }
            }
            syn::UseTree::Glob(_) => {}
        }
    }
    let mut names = BTreeSet::new();
    for item in items {
        let name = match item {
            syn::Item::Use(item) => {
                bound(&item.tree, 0, &mut names);
                continue;
            }
            syn::Item::ExternCrate(item) => match &item.rename {
                Some((_, rename)) => rename,
                None => continue,
            },
            syn::Item::Mod(item) => &item.ident,
            syn::Item::Struct(item) => &item.ident,
            syn::Item::Enum(item) => &item.ident,
            syn::Item::Union(item) => &item.ident,
            syn::Item::Type(item) => &item.ident,
            syn::Item::Trait(item) => &item.ident,
            syn::Item::TraitAlias(item) => &item.ident,
            syn::Item::Fn(item) => &item.sig.ident,
            syn::Item::Const(item) => &item.ident,
            syn::Item::Static(item) => &item.ident,
            _ => continue,
        };
        names.insert(name.unraw().to_string());
    }
    names
}

/// The path of the module `module` from `crate`.
fn crate_module_path(module: &[String]) -> String {
    std::iter::once("crate")
        .chain(module.iter().map(String::as_str))
        .collect::<Vec<_>>()
        .join("::")
}

/// The outer attributes of `item`.
fn item_attributes(item: &syn::Item) -> &[syn::Attribute] {
    match item {
        syn::Item::Const(item) => &item.attrs,
        syn::Item::Enum(item) => &item.attrs,
        syn::Item::ExternCrate(item) => &item.attrs,
        syn::Item::Fn(item) => &item.attrs,
        syn::Item::ForeignMod(item) => &item.attrs,
        syn::Item::Impl(item) => &item.attrs,
        syn::Item::Macro(item) => &item.attrs,
        syn::Item::Mod(item) => &item.attrs,
        syn::Item::Static(item) => &item.attrs,
        syn::Item::Struct(item) => &item.attrs,
        syn::Item::Trait(item) => &item.attrs,
        syn::Item::TraitAlias(item) => &item.attrs,
        syn::Item::Type(item) => &item.attrs,
        syn::Item::Union(item) => &item.attrs,
        syn::Item::Use(item) => &item.attrs,
        _ => &[],
    }
}

/// The outer attributes of `item`, to write.
fn item_attributes_mut(item: &mut syn::Item) -> Option<&mut Vec<syn::Attribute>> {
    match item {
        syn::Item::Const(item) => Some(&mut item.attrs),
        syn::Item::Enum(item) => Some(&mut item.attrs),
        syn::Item::ExternCrate(item) => Some(&mut item.attrs),
        syn::Item::Fn(item) => Some(&mut item.attrs),
        syn::Item::ForeignMod(item) => Some(&mut item.attrs),
        syn::Item::Impl(item) => Some(&mut item.attrs),
        syn::Item::Macro(item) => Some(&mut item.attrs),
        syn::Item::Mod(item) => Some(&mut item.attrs),
        syn::Item::Static(item) => Some(&mut item.attrs),
        syn::Item::Struct(item) => Some(&mut item.attrs),
        syn::Item::Trait(item) => Some(&mut item.attrs),
        syn::Item::TraitAlias(item) => Some(&mut item.attrs),
        syn::Item::Type(item) => Some(&mut item.attrs),
        syn::Item::Union(item) => Some(&mut item.attrs),
        syn::Item::Use(item) => Some(&mut item.attrs),
        _ => None,
    }
}

/// The names a `use` or an `extern crate` among `items` (one module's) gives a path from one of
/// `crate_names` (`use dep as d;`, `use dep::m as mm;`), each beside that path; a name given two
/// paths, or that is a crate name itself, is left out.
fn renamed_crates(
    items: &[syn::Item],
    crate_names: &BTreeSet<&String>,
) -> BTreeMap<String, Vec<String>> {
    /// The `as` names of `tree`'s renames, each beside the path it renames.
    fn renames(
        tree: &syn::UseTree,
        prefix: &mut Vec<String>,
        found: &mut Vec<(String, Vec<String>)>,
    ) {
        match tree {
            syn::UseTree::Path(path) => {
                prefix.push(path.ident.unraw().to_string());
                renames(&path.tree, prefix, found);
                prefix.pop();
            }
            syn::UseTree::Rename(rename) => {
                let mut path = prefix.clone();
                path.push(rename.ident.unraw().to_string());
                found.push((rename.rename.unraw().to_string(), path));
            }
            syn::UseTree::Group(group) => {
                for tree in &group.items {
                    renames(tree, prefix, found);
                }
            }
            syn::UseTree::Name(_) | syn::UseTree::Glob(_) => {}
        }
    }
    let mut found = Vec::new();
    for item in items {
        match item {
            syn::Item::Use(item) => renames(&item.tree, &mut Vec::new(), &mut found),
            syn::Item::ExternCrate(item) => {
                if let Some((_, rename)) = &item.rename {
                    found.push((
                        rename.unraw().to_string(),
                        vec![item.ident.unraw().to_string()],
                    ));
                }
            }
            _ => {}
        }
    }
    let mut renamed = BTreeMap::<String, Option<Vec<String>>>::new();
    for (name, path) in found {
        if crate_names.contains(&name)
            || !path
                .first()
                .is_some_and(|first| crate_names.contains(first))
        {
            continue;
        }
        renamed
            .entry(name)
            .and_modify(|target| {
                if target.as_ref() != Some(&path) {
                    *target = None;
                }
            })
            .or_insert(Some(path));
    }
    renamed
        .into_iter()
        .filter_map(|(name, path)| Some((name, path?)))
        .collect()
}

/// The paths a printed clause or table row writes to the items it references, each as the long
/// form that replaces it prints it ([`WrittenPaths::of`]), by item, in source order.
#[derive(Debug, Default)]
struct WrittenPaths(BTreeMap<StableItemId, Vec<(krs_ir::ProvenanceKey, syn::Path)>>);

impl WrittenPaths {
    /// The paths `descriptor`'s clause writes at `references`, the keys and items of its
    /// declared applications and sorts as collected ([`ReferencedItems`]).
    ///
    /// rustc resolved the tokens at each such key to the item the descriptor records, so the
    /// clause's path names that item where the clause stands. The long form replaces the clause
    /// in the same module, where a path of two or more segments, printed verbatim, resolves as
    /// the clause's did (`p::Unit`, whatever `p` re-exports under that name). Two scopes are not
    /// the module's:
    ///
    /// - `block`, the `use` items of the clause's block, which the long form does not keep: a
    ///   path whose first name one of them binds is printed through that `use`'s path, and one
    ///   whose first name a glob of the block may bind has no written path;
    /// - a path of one name (`Same`), which the long form prints as a path, as it prints its own
    ///   package's items (`crate::Same`): it is printed as the path of the one `use` of the module
    ///   that binds it, and has no written path where none does (a glob's name).
    ///
    /// A reference with no exact authored range in the file, or whose text is no path, has none
    /// either.
    fn of(
        descriptor: &Descriptor,
        references: Vec<(krs_ir::ProvenanceKey, StableItemId)>,
        source: &str,
        block: Option<&Bindings>,
        module: &Bindings,
    ) -> Self {
        let Some(file) = descriptor
            .origin()
            .exact_authored_range()
            .map(|range| range.file)
        else {
            return Self::default();
        };
        let mut found =
            BTreeMap::<StableItemId, Vec<(u32, krs_ir::ProvenanceKey, syn::Path)>>::new();
        for (key, id) in references {
            let Some(range) = descriptor
                .provenance()
                .origin_for(&key)
                .and_then(krs_ir::OriginStack::exact_authored_range)
                .filter(|range| range.file == file)
            else {
                continue;
            };
            let Some(path) = source
                .get(range.start_byte as usize..range.end_byte as usize)
                .and_then(|text| syn::parse_str::<syn::Path>(text).ok())
                .and_then(|path| written_path(path, block, module))
            else {
                continue;
            };
            found
                .entry(id)
                .or_default()
                .push((range.start_byte, key, path));
        }
        Self(
            found
                .into_iter()
                .map(|(id, mut paths)| {
                    paths.sort_by(|left, right| (left.0, &left.1).cmp(&(right.0, &right.1)));
                    let paths = paths
                        .into_iter()
                        .map(|(_, key, path)| (key, path))
                        .collect();
                    (id, paths)
                })
                .collect(),
        )
    }

    /// The path the clause writes to `id`: at the reference `at`, where it writes one there,
    /// else at its first reference to `id`.
    fn get(&self, id: &StableItemId, at: Option<&krs_ir::ProvenanceKey>) -> Option<&syn::Path> {
        let paths = self.0.get(id)?;
        at.and_then(|at| paths.iter().find(|(key, _)| key == at))
            .or_else(|| paths.first())
            .map(|(_, path)| path)
    }
}

/// `path`, written in a clause whose block's `use` items bind `block` and whose module's bind
/// `module`, as the long form prints it in that module ([`WrittenPaths::of`]); `None` where no
/// printed path is known to resolve as it does. Generic arguments are left out: the long form
/// prints an instance by itself.
fn written_path(
    mut path: syn::Path,
    block: Option<&Bindings>,
    module: &Bindings,
) -> Option<syn::Path> {
    for segment in &mut path.segments {
        segment.arguments = syn::PathArguments::None;
    }
    if path.leading_colon.is_some() {
        return Some(path);
    }
    let first = path.segments.first()?.ident.unraw().to_string();
    // `crate`, `self` and `super` name the crate and the module the long form stands in.
    if matches!(first.as_str(), "crate" | "self" | "super") {
        return (path.segments.len() > 1).then_some(path);
    }
    if let Some(block) = block {
        match block.binding(&first) {
            Binding::One(target) => {
                // The `use`'s own path resolves in the module, unless the block binds its first
                // name too.
                let head = target.segments.first()?.ident.unraw().to_string();
                if target.leading_colon.is_none()
                    && (block.glob || !matches!(block.binding(&head), Binding::Unbound))
                {
                    return None;
                }
                let mut joined = target.clone();
                joined.segments.extend(path.segments.into_iter().skip(1));
                return written_path(joined, None, module);
            }
            Binding::Unknown => return None,
            Binding::Unbound if block.glob => return None,
            Binding::Unbound => {}
        }
    }
    if path.segments.len() > 1 {
        return Some(path);
    }
    match module.binding(&first) {
        Binding::One(target) if target.leading_colon.is_some() || target.segments.len() > 1 => {
            Some(target.clone())
        }
        _ => None,
    }
}

/// The names one scope's `use` and `extern crate` items bind ([`written_path`]).
#[derive(Debug, Default)]
struct Bindings {
    /// Each name an item binds by name, beside the path of each such binding: `None` for one
    /// under an attribute (a `#[cfg]` that may not hold).
    explicit: BTreeMap<String, Vec<Option<syn::Path>>>,
    /// Whether a glob import binds names of its own.
    glob: bool,
}

/// How a scope binds a name ([`Bindings::binding`]).
enum Binding<'a> {
    /// No `use` of the scope binds it by name.
    Unbound,
    /// One unconditional `use` binds it, to this path.
    One(&'a syn::Path),
    /// Several do, or one under an attribute.
    Unknown,
}

impl Bindings {
    /// The bindings of one module's `items`.
    fn of_items(items: &[syn::Item]) -> Self {
        let mut bindings = Self::default();
        for item in items {
            match item {
                syn::Item::Use(item) => bindings.add_use(item),
                syn::Item::ExternCrate(item) => {
                    if let Some((_, rename)) = &item.rename {
                        let path = syn::Path {
                            leading_colon: Some(syn::Token![::](Span::call_site())),
                            segments: std::iter::once(syn::PathSegment::from(item.ident.clone()))
                                .collect(),
                        };
                        bindings.bind(rename, item.attrs.is_empty().then_some(path));
                    }
                }
                _ => {}
            }
        }
        bindings
    }

    /// The bindings of a block's `uses`.
    fn of_uses(uses: &[syn::ItemUse]) -> Self {
        let mut bindings = Self::default();
        for item in uses {
            bindings.add_use(item);
        }
        bindings
    }

    fn add_use(&mut self, item: &syn::ItemUse) {
        fn add(
            tree: &syn::UseTree,
            prefix: &mut syn::Path,
            conditional: bool,
            bindings: &mut Bindings,
        ) {
            let path = |prefix: &syn::Path, last: Option<&Ident>| {
                let mut path = prefix.clone();
                path.segments
                    .extend(last.cloned().map(syn::PathSegment::from));
                (!conditional).then_some(path)
            };
            match tree {
                syn::UseTree::Path(next) => {
                    prefix
                        .segments
                        .push(syn::PathSegment::from(next.ident.clone()));
                    add(&next.tree, prefix, conditional, bindings);
                    prefix.segments.pop();
                }
                syn::UseTree::Name(name) if name.ident == "self" => {
                    if let Some(last) = prefix.segments.last() {
                        let last = last.ident.clone();
                        bindings.bind(&last, path(prefix, None));
                    }
                }
                syn::UseTree::Name(name) => {
                    bindings.bind(&name.ident, path(prefix, Some(&name.ident)));
                }
                syn::UseTree::Rename(rename) if rename.rename == "_" => {}
                syn::UseTree::Rename(rename) => {
                    let last = (rename.ident != "self").then_some(&rename.ident);
                    bindings.bind(&rename.rename, path(prefix, last));
                }
                syn::UseTree::Glob(_) => bindings.glob = true,
                syn::UseTree::Group(group) => {
                    for tree in &group.items {
                        add(tree, prefix, conditional, bindings);
                    }
                }
            }
        }
        let mut prefix = syn::Path {
            leading_colon: item.leading_colon,
            segments: syn::punctuated::Punctuated::new(),
        };
        add(&item.tree, &mut prefix, !item.attrs.is_empty(), self);
    }

    fn bind(&mut self, name: &Ident, path: Option<syn::Path>) {
        self.explicit
            .entry(name.unraw().to_string())
            .or_default()
            .push(path.filter(|path| !path.segments.is_empty()));
    }

    fn binding(&self, name: &str) -> Binding<'_> {
        match self.explicit.get(name).map(Vec::as_slice) {
            None => Binding::Unbound,
            Some([Some(path)]) => Binding::One(path),
            Some(_) => Binding::Unknown,
        }
    }
}

/// The declared items a descriptor's applications and sorts reference, each beside the key of
/// the authored path rustc resolved to it ([`WrittenPaths::of`]).
#[derive(Default)]
struct ReferencedItems(Vec<(krs_ir::ProvenanceKey, StableItemId)>);

impl ReferencedItems {
    /// The references of a readable clause's rule, as collected.
    fn of_head_rule(rule: &DescriptorHeadRule) -> Vec<(krs_ir::ProvenanceKey, StableItemId)> {
        let mut referenced = Self::default();
        let Ok(_) = rule.clone().try_map_refs(&mut referenced);
        referenced.0
    }

    /// The references of a table row's equation, as collected.
    fn of_equation(
        rule: &krs_ir::StructuredRuleDescriptor,
    ) -> Vec<(krs_ir::ProvenanceKey, StableItemId)> {
        let mut referenced = Self::default();
        let Ok(_) = rule.clone().try_map_refs(&mut referenced);
        referenced.0
    }
}

/// The sort marker of a turbofish argument: a builtin's marker type, or a
/// declared sort's `dyn` marker trait (KF-027).
fn render_sort_marker(
    sort: &krs_ir::DescriptorSortRef,
    package: PathScope<'_>,
) -> Result<TokenStream, ReferenceExpansionError> {
    match sort {
        krs_ir::DescriptorSortRef::Builtin(sort) => Ok(render_builtin_sort(*sort)),
        // A framework sort's marker is the facade's: `KItem`'s is `dyn k::KItemSort`.
        krs_ir::DescriptorSortRef::Declared(id)
            if id.package().k_namespace() == crate::partition::FRAMEWORK_NAMESPACE =>
        {
            let marker = rust_ident(&format!("{}Sort", id.item_name()))?;
            Ok(quote!(dyn k::#marker))
        }
        krs_ir::DescriptorSortRef::Declared(id) => {
            let marker = rust_ident(&format!("{}Sort", id.item_name()))?;
            let path = render_local_path(id, package, &[marker])?;
            Ok(quote!(dyn #path))
        }
        krs_ir::DescriptorSortRef::Cell(_) | krs_ir::DescriptorSortRef::Parameter(_) => {
            render_descriptor_sort(sort, package)
        }
    }
}

fn render_builtin_sort(sort: BuiltinSort) -> TokenStream {
    let name = format_ident!("{}", sort.marker_name());
    quote!(k::builtin::#name)
}

/// The calls the operators, the list notation, and the indexes and
/// collection methods of one descriptor denote, read from the semantic rule
/// lowered from it: each operator head becomes the operation semantic
/// lowering applied at that head, each bracket level the constructor, and
/// each index or method the collection operation, found by the source-map
/// key lowering gives the application there. `-x` on `Int` applies
/// `int::sub` to an operand the descriptor does not hold, so it stays the
/// operator `-`, which [`render_term`] spells `int::sub(0, x)`. An index or a
/// method holds the denoted call's arguments in its order, so its call is
/// printed as the reader would write it, with the collection inference
/// chose: `krs expand` shows what the notation hides.
struct OperatorCalls<'a> {
    descriptor: &'a Descriptor,
    operations: BTreeMap<SourceMapKey, BuiltinOperation>,
    /// The Map, List and Set operations, by their terms' keys.
    collection_operations: BTreeMap<SourceMapKey, DescriptorApplicationRef>,
    constructors: BTreeMap<SourceMapKey, StableItemId>,
    /// The keys of `.List` terms: `[]` at a builtin `List` position.
    list_units: BTreeSet<SourceMapKey>,
    /// The keys of every builtin `List` term, among them the `list::item`
    /// of each bracket level at a builtin `List` position.
    list_terms: BTreeSet<SourceMapKey>,
}

impl<'a> OperatorCalls<'a> {
    /// The calls of `descriptor`, read from `rule`, the semantic rule lowered from it, and from the
    /// equations of the functions lifted out of it (NT-15), which `rules` holds: a `let` block or
    /// `k::matches!` of a claim or a static clause's result is an equation's term there, with the
    /// choices lowering made in it.
    fn new(
        descriptor: &'a Descriptor,
        rule: &SemanticRule,
        rules: &BTreeMap<&StableItemId, &SemanticRule>,
    ) -> Self {
        let mut operations = BTreeMap::new();
        let mut collection_operations = BTreeMap::new();
        let mut constructors = BTreeMap::new();
        let mut list_units = BTreeSet::new();
        let mut list_terms = BTreeSet::new();
        let mut pending = with_local_functions(rule, rules)
            .into_iter()
            .flat_map(semantic_rule_terms)
            .collect::<Vec<_>>();
        while let Some(term) = pending.pop() {
            match term.kind() {
                IrTermKind::Application {
                    application: ApplicationRef::Builtin(operation),
                    ..
                } => {
                    operations.insert(term.origin().key().clone(), *operation);
                }
                IrTermKind::Application {
                    application: ApplicationRef::Declared(id),
                    ..
                } => {
                    constructors.insert(term.origin().key().clone(), id.clone());
                }
                IrTermKind::List(operands) => {
                    if matches!(**operands, krs_ir_levels::ListOperands::Empty) {
                        list_units.insert(term.origin().key().clone());
                    }
                    list_terms.insert(term.origin().key().clone());
                    collection_operations.insert(
                        term.origin().key().clone(),
                        DescriptorApplicationRef::List(operands.operation()),
                    );
                }
                IrTermKind::Map(operands) => {
                    if let Ok(operation) = TermMapOperation::try_from(operands.operation()) {
                        collection_operations.insert(
                            term.origin().key().clone(),
                            DescriptorApplicationRef::Map(operation),
                        );
                    }
                }
                IrTermKind::Set(operands) => {
                    collection_operations.insert(
                        term.origin().key().clone(),
                        DescriptorApplicationRef::Set(operands.operation()),
                    );
                }
                _ => {}
            }
            pending.extend(term.children());
        }
        Self {
            descriptor,
            operations,
            collection_operations,
            constructors,
            list_units,
            list_terms,
        }
    }
}

/// `rule` and the equations of the functions lifted out of its `let` blocks and `k::matches!`
/// tests (NT-15), which `rules` holds under the identities [`krs_ir::local_function_ids`] derives
/// from `rule`'s and each function's place, from the first on: the lifting numbers them without a
/// gap, so the first place without an equation ends them.
fn with_local_functions<'r>(
    rule: &'r SemanticRule,
    rules: &BTreeMap<&StableItemId, &'r SemanticRule>,
) -> Vec<&'r SemanticRule> {
    let mut found = vec![rule];
    for index in 0.. {
        let Some(equation) = krs_ir::local_function_ids(rule.id(), index)
            .ok()
            .and_then(|ids| Some((rules.get(&ids.equation)?, rules.get(&ids.otherwise))))
        else {
            break;
        };
        found.push(equation.0);
        found.extend(equation.1.copied());
    }
    found
}

/// Every term of a semantic rule, equation, or claim.
fn semantic_rule_terms(rule: &SemanticRule) -> Vec<&SemanticTerm> {
    let mut terms = Vec::new();
    match rule.relational_body() {
        RuleBodyRef::Term(rewrite) => {
            terms.push(rewrite.from());
            terms.push(rewrite.to());
        }
        RuleBodyRef::Configuration { body, .. } => {
            for part in body.parts() {
                terms.extend(part.terms());
            }
        }
        RuleBodyRef::Predicate(body) => {
            terms.extend(body.lhs().terms());
            terms.extend(body.rhs().terms());
        }
    }
    if let Some(context) = rule.function_context() {
        terms.extend(
            context
                .cells()
                .cells()
                .iter()
                .map(krs_ir::FixedCellPattern::pattern),
        );
    }
    for condition in rule.requires().into_iter().chain(rule.ensures()) {
        terms.extend(condition.terms());
    }
    terms
}

impl RefMap<DescriptorStage, DescriptorStage> for OperatorCalls<'_> {
    type Error = ReferenceExpansionError;

    fn application(
        &mut self,
        reference: DescriptorApplicationReference,
    ) -> Result<DescriptorApplicationReference, Self::Error> {
        if let DescriptorApplicationRef::ListNotation(notation) = reference.application {
            let constructor =
                crate::semantic::application_source_key(self.descriptor, &reference.key)
                    .and_then(|key| self.constructors.get(&key).cloned());
            let unit = crate::semantic::list_operation_source_key(self.descriptor, &reference.key)
                .is_some_and(|key| self.list_units.contains(&key));
            // A level at the builtin `List` stays notation, which
            // [`render_term`] spells as the `list::item`/`list::concat` term
            // it lowered to; so does the `[]` that ends a closed one, which
            // lowered to nothing of its own.
            let builtin =
                crate::semantic::list_notation_source_key(self.descriptor, &reference.key)
                    .is_some_and(|key| self.list_terms.contains(&key));
            let application = if let Some(constructor) = constructor {
                DescriptorApplicationRef::Declared(constructor)
            } else if unit {
                DescriptorApplicationRef::List(krs_ir::ListOperation::Empty)
            } else if builtin || notation == ListNotation::Empty {
                DescriptorApplicationRef::ListNotation(notation)
            } else {
                return Err(ReferenceExpansionError::UnresolvedListNotation);
            };
            return Ok(DescriptorApplicationReference {
                key: reference.key,
                application,
            });
        }
        if let DescriptorApplicationRef::CollectionMethod(method) = reference.application {
            let application = [
                "term-map-operation",
                "term-list-operation",
                "term-set-operation",
            ]
            .into_iter()
            .find_map(|label| {
                let key =
                    crate::semantic::semantic_source_key(self.descriptor, &reference.key, label)?;
                self.collection_operations.get(&key).cloned()
            })
            .ok_or(ReferenceExpansionError::UnresolvedCollectionMethod(method))?;
            return Ok(DescriptorApplicationReference {
                key: reference.key,
                application,
            });
        }
        let DescriptorApplicationRef::Operator(operator) = reference.application else {
            return Ok(reference);
        };
        let operation = crate::semantic::application_source_key(self.descriptor, &reference.key)
            .and_then(|key| self.operations.get(&key).copied())
            .ok_or(ReferenceExpansionError::UnresolvedOperator(
                operator.symbol(),
            ))?;
        let application =
            if operator == BuiltinOperator::Neg && operation == BuiltinOperation::IntSub {
                DescriptorApplicationRef::Operator(operator)
            } else {
                DescriptorApplicationRef::Builtin(operation)
            };
        Ok(DescriptorApplicationReference {
            key: reference.key,
            application,
        })
    }

    fn sort(
        &mut self,
        reference: <DescriptorStage as Stage>::Sort,
    ) -> Result<<DescriptorStage as Stage>::Sort, Self::Error> {
        Ok(reference)
    }
    fn nominal(
        &mut self,
        reference: <DescriptorStage as Stage>::Nominal,
    ) -> Result<<DescriptorStage as Stage>::Nominal, Self::Error> {
        Ok(reference)
    }
    fn context_alias(
        &mut self,
        reference: <DescriptorStage as Stage>::ContextAlias,
    ) -> Result<<DescriptorStage as Stage>::ContextAlias, Self::Error> {
        Ok(reference)
    }
    fn configuration(
        &mut self,
        reference: <DescriptorStage as Stage>::Configuration,
    ) -> Result<<DescriptorStage as Stage>::Configuration, Self::Error> {
        Ok(reference)
    }
    fn cell(
        &mut self,
        reference: <DescriptorStage as Stage>::Cell,
    ) -> Result<<DescriptorStage as Stage>::Cell, Self::Error> {
        Ok(reference)
    }
    fn head_rule_cell(
        &mut self,
        reference: <DescriptorStage as Stage>::HeadRuleCell,
    ) -> Result<<DescriptorStage as Stage>::HeadRuleCell, Self::Error> {
        Ok(reference)
    }
    fn item(
        &mut self,
        reference: <DescriptorStage as Stage>::Item,
    ) -> Result<<DescriptorStage as Stage>::Item, Self::Error> {
        Ok(reference)
    }
    fn cell_declaration(
        &mut self,
        reference: <DescriptorStage as Stage>::CellDeclaration,
    ) -> Result<<DescriptorStage as Stage>::CellDeclaration, Self::Error> {
        Ok(reference)
    }
    fn initializer_owner(
        &mut self,
        reference: <DescriptorStage as Stage>::InitializerOwner,
    ) -> Result<<DescriptorStage as Stage>::InitializerOwner, Self::Error> {
        Ok(reference)
    }
    fn parent(
        &mut self,
        reference: <DescriptorStage as Stage>::Parent,
    ) -> Result<<DescriptorStage as Stage>::Parent, Self::Error> {
        Ok(reference)
    }
    fn constructor_sort(
        &mut self,
        reference: <DescriptorStage as Stage>::ConstructorSort,
    ) -> Result<<DescriptorStage as Stage>::ConstructorSort, Self::Error> {
        Ok(reference)
    }
    fn constructor_field_sort(
        &mut self,
        reference: <DescriptorStage as Stage>::ConstructorFieldSort,
    ) -> Result<<DescriptorStage as Stage>::ConstructorFieldSort, Self::Error> {
        Ok(reference)
    }
}

impl RefMap<DescriptorStage, DescriptorStage> for ReferencedItems {
    type Error = std::convert::Infallible;

    fn application(
        &mut self,
        reference: DescriptorApplicationReference,
    ) -> Result<DescriptorApplicationReference, Self::Error> {
        if let DescriptorApplicationRef::Declared(id) = &reference.application {
            self.0.push((reference.key.clone(), id.clone()));
        }
        Ok(reference)
    }

    fn sort(
        &mut self,
        reference: <DescriptorStage as Stage>::Sort,
    ) -> Result<<DescriptorStage as Stage>::Sort, Self::Error> {
        if let krs_ir::DescriptorSortRef::Declared(id) | krs_ir::DescriptorSortRef::Cell(id) =
            &reference.sort
        {
            self.0.push((reference.key.clone(), id.clone()));
        }
        Ok(reference)
    }
    fn nominal(
        &mut self,
        reference: <DescriptorStage as Stage>::Nominal,
    ) -> Result<<DescriptorStage as Stage>::Nominal, Self::Error> {
        Ok(reference)
    }
    fn context_alias(
        &mut self,
        reference: <DescriptorStage as Stage>::ContextAlias,
    ) -> Result<<DescriptorStage as Stage>::ContextAlias, Self::Error> {
        Ok(reference)
    }
    fn configuration(
        &mut self,
        reference: <DescriptorStage as Stage>::Configuration,
    ) -> Result<<DescriptorStage as Stage>::Configuration, Self::Error> {
        Ok(reference)
    }
    fn cell(
        &mut self,
        reference: <DescriptorStage as Stage>::Cell,
    ) -> Result<<DescriptorStage as Stage>::Cell, Self::Error> {
        Ok(reference)
    }
    fn head_rule_cell(
        &mut self,
        reference: <DescriptorStage as Stage>::HeadRuleCell,
    ) -> Result<<DescriptorStage as Stage>::HeadRuleCell, Self::Error> {
        Ok(reference)
    }
    fn item(
        &mut self,
        reference: <DescriptorStage as Stage>::Item,
    ) -> Result<<DescriptorStage as Stage>::Item, Self::Error> {
        Ok(reference)
    }
    fn cell_declaration(
        &mut self,
        reference: <DescriptorStage as Stage>::CellDeclaration,
    ) -> Result<<DescriptorStage as Stage>::CellDeclaration, Self::Error> {
        Ok(reference)
    }
    fn initializer_owner(
        &mut self,
        reference: <DescriptorStage as Stage>::InitializerOwner,
    ) -> Result<<DescriptorStage as Stage>::InitializerOwner, Self::Error> {
        Ok(reference)
    }
    fn parent(
        &mut self,
        reference: <DescriptorStage as Stage>::Parent,
    ) -> Result<<DescriptorStage as Stage>::Parent, Self::Error> {
        Ok(reference)
    }
    fn constructor_sort(
        &mut self,
        reference: <DescriptorStage as Stage>::ConstructorSort,
    ) -> Result<<DescriptorStage as Stage>::ConstructorSort, Self::Error> {
        Ok(reference)
    }
    fn constructor_field_sort(
        &mut self,
        reference: <DescriptorStage as Stage>::ConstructorFieldSort,
    ) -> Result<<DescriptorStage as Stage>::ConstructorFieldSort, Self::Error> {
        Ok(reference)
    }
}

fn render_builtin_operation(operation: BuiltinOperation) -> TokenStream {
    let spec = operation.spec();
    let module = format_ident!("{}", spec.rust_module);
    let name = format_ident!("{}", spec.rust_name);
    quote!(k::builtin::#module::#name)
}

fn render_facade_marker(marker: FacadeMarker) -> TokenStream {
    let module = format_ident!("{}", marker.module);
    let name = format_ident!("{}", marker.name);
    quote!(k::builtin::#module::#name)
}

/// Names the hidden binders of a `k::bits!` template's long form, which no
/// author may write, `bits`, `bits1`, .. in the order of their ordinals,
/// skipping every identifier the item already spells.
fn rename_hidden_binders(item: &mut syn::Item) -> Result<(), ReferenceExpansionError> {
    let (tokens, renamed) = rename_hidden_tokens(item.to_token_stream())?;
    if !renamed.is_empty() {
        *item = syn::parse2(tokens).map_err(ReferenceExpansionError::GeneratedRust)?;
    }
    Ok(())
}

/// Tokens with their hidden binders renamed, and the renaming.
type Renamed = (TokenStream, BTreeMap<String, Ident>);

/// `tokens` with each hidden template binder renamed as
/// [`rename_hidden_binders`] does, and the renaming.
fn rename_hidden_tokens(tokens: TokenStream) -> Result<Renamed, ReferenceExpansionError> {
    fn identifiers(tokens: TokenStream, names: &mut BTreeSet<String>) {
        for token in tokens {
            match token {
                // `r#bits` and `bits` are one identifier, so a fresh name
                // skips the identifier, not its spelling.
                proc_macro2::TokenTree::Ident(ident) => {
                    names.insert(ident.unraw().to_string());
                }
                proc_macro2::TokenTree::Group(group) => identifiers(group.stream(), names),
                _ => {}
            }
        }
    }
    fn rename(tokens: TokenStream, names: &BTreeMap<String, Ident>) -> TokenStream {
        tokens
            .into_iter()
            .map(|token| match token {
                proc_macro2::TokenTree::Ident(ident) => names
                    .get(&ident.to_string())
                    .map_or(proc_macro2::TokenTree::Ident(ident), |name| {
                        proc_macro2::TokenTree::Ident(name.clone())
                    }),
                proc_macro2::TokenTree::Group(group) => {
                    let mut renamed =
                        proc_macro2::Group::new(group.delimiter(), rename(group.stream(), names));
                    renamed.set_span(group.span());
                    proc_macro2::TokenTree::Group(renamed)
                }
                other => other,
            })
            .collect()
    }
    let mut spelled = BTreeSet::new();
    identifiers(tokens.clone(), &mut spelled);
    let mut hidden = spelled
        .iter()
        .filter(|name| krs_syntax::is_hidden_binder(name))
        .cloned()
        .collect::<Vec<_>>();
    // A record update's hidden binder (F5) is named after its alias and
    // field, `saved_gas` for the field `gas` of `saved`.
    let updates = spelled
        .iter()
        .filter_map(|name| {
            name.strip_prefix(RECORD_UPDATE_BINDER)
                .map(|readable| (name.clone(), readable.to_owned()))
        })
        .collect::<Vec<_>>();
    if hidden.is_empty() && updates.is_empty() {
        return Ok((tokens, BTreeMap::new()));
    }
    hidden.sort_by_key(|name| {
        name.trim_start_matches(|character: char| !character.is_ascii_digit())
            .parse::<u64>()
            .unwrap_or(u64::MAX)
    });
    let mut names = hidden
        .into_iter()
        .map(|name| Ok((name, fresh_ident("bits", &mut spelled)?)))
        .collect::<Result<BTreeMap<_, _>, ReferenceExpansionError>>()?;
    for (name, readable) in updates {
        let fresh = fresh_ident(&readable, &mut spelled)?;
        names.insert(name, fresh);
    }
    Ok((rename(tokens, &names), names))
}

/// The spelling prefix of a record update's hidden binder (F5).
const RECORD_UPDATE_BINDER: &str = "__krs_update_";

fn fresh_ident(
    base: &str,
    reserved: &mut BTreeSet<String>,
) -> Result<Ident, ReferenceExpansionError> {
    if !reserved.contains(base) {
        reserved.insert(base.to_owned());
        return rust_ident(base);
    }
    let mut ordinal = 1_u32;
    loop {
        let candidate = format!("{base}{ordinal}");
        if !reserved.contains(candidate.as_str()) {
            reserved.insert(candidate.clone());
            return rust_ident(&candidate);
        }
        ordinal += 1;
    }
}

/// The Rust identifier that names `value`: the identifier itself, or the raw
/// identifier of a name that is reserved in the edition KRS packages use
/// (`r#type`, `r#gen`).
///
/// Every name a descriptor holds was a Rust identifier where it was written,
/// so no authored name fails here; a name that is neither an identifier nor a
/// keyword a raw identifier can spell (`_`, `self`, `crate`, a name with a
/// character no identifier holds) is a failure of whatever produced it, typed
/// rather than a panic. `_` binds nothing and is no name: a readable `_`
/// binding prints as a fresh binder (see [`render_rule`]).
fn rust_ident(value: &str) -> Result<Ident, ReferenceExpansionError> {
    if !EDITION_RESERVED.contains(&value)
        && let Ok(ident) = syn::parse_str::<Ident>(value)
    {
        return Ok(ident);
    }
    // `Ident::new_raw` panics on what no raw identifier spells, so the raw
    // spelling is parsed instead.
    syn::parse_str::<Ident>(&format!("r#{value}")).map_err(|_| {
        ReferenceExpansionError::GeneratedRust(syn::Error::new(
            Span::call_site(),
            format!("`{value}` is not a Rust identifier"),
        ))
    })
}

/// The names reserved in the 2024 edition, which KRS packages use, that
/// `syn` parses as identifiers because no edition `syn` targets reserves
/// them. A raw identifier names them in every edition that has raw
/// identifiers.
const EDITION_RESERVED: &[&str] = &["gen"];

/// The package whose source is printed, with the crate names its source gives the packages it
/// depends on, by which it names their declarations.
#[derive(Clone, Copy, Debug)]
struct PathScope<'a> {
    package: &'a PackageId,
    crates: &'a BTreeMap<PackageId, String>,
    /// The paths the source writes to dependencies' items ([`authored_paths`]).
    authored: &'a BTreeMap<(String, String), BTreeSet<Vec<String>>>,
    /// The paths the clause being printed writes to the items it references.
    written: &'a WrittenPaths,
    /// The key of the reference being printed, whose own path is printed where the clause
    /// writes one there.
    at: Option<&'a krs_ir::ProvenanceKey>,
    /// The module the long form stands in.
    module: &'a [String],
    /// The crate's module tree, which says from where each of its modules is visible; `None`
    /// for a lone source, whose modules are all taken to be visible.
    tree: Option<&'a ModuleTree>,
}

impl<'a> PathScope<'a> {
    /// The scope for printing a clause that writes `written`.
    fn writing<'b>(self, written: &'b WrittenPaths) -> PathScope<'b>
    where
        'a: 'b,
    {
        PathScope {
            written,
            at: None,
            ..self
        }
    }

    /// The scope for printing the reference at `key`.
    fn at<'b>(self, key: &'b krs_ir::ProvenanceKey) -> PathScope<'b>
    where
        'a: 'b,
    {
        PathScope {
            at: Some(key),
            ..self
        }
    }

    /// The path the clause writes to `id` ([`WrittenPaths::get`]), where `id` is another
    /// package's item or one of this package whose `crate::` path does not reach it from the
    /// printed module ([`PathScope::reaches`]).
    fn written_path(self, id: &StableItemId) -> Option<&'a syn::Path> {
        // An enum variant's path passes through its enum, whose visibility is the variant's.
        let head = id
            .disambiguator()
            .strip_prefix(ENUM_VARIANT_DISAMBIGUATOR_PREFIX)
            .unwrap_or(id.item_name());
        if id.package() == self.package && self.reaches(id.module_path(), head) {
            return None;
        }
        self.written.get(id, self.at)
    }

    /// Whether `crate::m1::..::mk::item`, the path of the item `item` of this package's module
    /// `module`, names it from the module the long form stands in: each module on it and the item
    /// are visible there ([`ModuleTree::reaches_item`]).
    fn reaches(self, module: &[String], item: &str) -> bool {
        self.tree
            .is_none_or(|tree| tree.reaches_item(module, item, self.module))
    }
}

/// Failure to select or reread the one authored source of a package.
#[derive(Debug)]
pub enum ReferenceSourceError {
    /// Descriptors of the package come from authored files that the crate's module tree does
    /// not reach as module files (such as a file `include!` reads), so no printed file holds
    /// their forms.
    Selection(Vec<SourceFileId>),
    /// A module file of the crate is chosen by a `cfg_attr(.., path = ..)`, which the source
    /// alone does not resolve.
    ConditionalModulePath {
        /// The file declaring the module.
        file: PathBuf,
        /// The module's path from the crate root.
        module: String,
    },
    /// A module file of the crate lies outside the package directory, where no printed file
    /// can stand.
    OutsidePackage(PathBuf),
    /// A file two modules of the crate read (`#[path]`) prints differently in each, and one
    /// printed file must stand for both.
    SharedFile(PathBuf),
    /// The package manifest path has no parent directory.
    ManifestDirectory(PathBuf),
    /// The selected source file could not be read.
    Read {
        /// Source path under the manifest directory.
        path: PathBuf,
        /// Operating-system error.
        error: io::Error,
    },
    /// The selected source file no longer has its collected content digest.
    Changed(PathBuf),
    /// The selected source file is not UTF-8.
    Encoding {
        /// Source path under the manifest directory.
        path: PathBuf,
        /// Decoding error.
        error: std::str::Utf8Error,
    },
}

impl ToDiagnostic for ReferenceSourceError {
    fn to_diagnostic(&self) -> Diagnostic {
        let code = match self {
            Self::Selection(_) => codes::reference::SOURCE_SELECTION,
            Self::ConditionalModulePath { .. } => codes::reference::SOURCE_MODULE_PATH,
            Self::OutsidePackage(_) => codes::reference::SOURCE_OUTSIDE_PACKAGE,
            Self::SharedFile(_) => codes::reference::SOURCE_SHARED_FILE,
            Self::ManifestDirectory(_) => codes::reference::SOURCE_MANIFEST_DIRECTORY,
            Self::Read { .. } => codes::reference::SOURCE_READ,
            Self::Changed(_) => codes::reference::SOURCE_CHANGED,
            Self::Encoding { .. } => codes::reference::SOURCE_ENCODING,
        };
        Diagnostic::error(code, self.to_string(), Location::None)
    }
}

impl fmt::Display for ReferenceSourceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Selection(files) => {
                let paths = files
                    .iter()
                    .map(SourceFileId::package_relative_path)
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(
                    formatter,
                    "expand prints the crate's module files, and descriptors come from files its module tree does not reach as modules (such as a file `include!` reads): {paths}; declare their items in a module file"
                )
            }
            Self::ConditionalModulePath { file, module } => write!(
                formatter,
                "expand cannot tell which file or directory the module `{module}` declared in `{}` is read from: a `cfg_attr` may give its path; declare it with a plain `#[path]`, or as two modules under `#[cfg]`",
                file.display()
            ),
            Self::OutsidePackage(path) => write!(
                formatter,
                "expand prints each changed module file at its path in the package, and `{}` is outside the package directory",
                path.display()
            ),
            Self::SharedFile(path) => write!(
                formatter,
                "expand prints `{}` once, and the two modules that read it print it differently; give each module its own file",
                path.display()
            ),
            Self::ManifestDirectory(path) => write!(
                formatter,
                "manifest has no parent directory: `{}`",
                path.display()
            ),
            Self::Read { path, error } => {
                write!(formatter, "could not read `{}`: {error}", path.display())
            }
            Self::Changed(path) => write!(
                formatter,
                "expand source changed after collection: `{}`",
                path.display()
            ),
            Self::Encoding { path, error } => write!(
                formatter,
                "expand source is not UTF-8: `{}`: {error}",
                path.display()
            ),
        }
    }
}

impl Error for ReferenceSourceError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Read { error, .. } => Some(error),
            Self::Encoding { error, .. } => Some(error),
            Self::Selection(_)
            | Self::ConditionalModulePath { .. }
            | Self::OutsidePackage(_)
            | Self::SharedFile(_)
            | Self::ManifestDirectory(_)
            | Self::Changed(_) => None,
        }
    }
}

/// Typed deterministic-reference projection failure.
#[derive(Debug)]
pub enum ReferenceExpansionError {
    /// The package's authored source could not be selected or reread.
    Source(ReferenceSourceError),
    /// The selected source is not a Rust module.
    RustSyntax(syn::Error),
    /// One readable KRS island is malformed.
    KrsSyntax(krs_syntax::SyntaxError),
    /// A readable sentence's long form could not be read from its descriptor.
    Lowering(Box<crate::DescriptorLoweringError>),
    /// Generated Rust unexpectedly failed to parse.
    GeneratedRust(syn::Error),
    /// One rule name occurred in more than one readable table.
    DuplicateRule(String),
    /// A readable rule did not map one-to-one to a collected head rule.
    RuleCoverage {
        /// Readable clause name.
        name: String,
        /// Number of matching collected head rules.
        found: usize,
    },
    /// An authored enum variant did not map one-to-one to a constructor.
    ConstructorCoverage {
        /// Rust enum family.
        family: String,
        /// Rust variant.
        variant: String,
        /// Number of matching constructor descriptors.
        found: usize,
    },
    /// The projected Rust fields did not cover the collected constructor.
    ConstructorFieldCoverage {
        /// Rust enum family.
        family: String,
        /// Rust variant.
        variant: String,
        /// Collected field count.
        expected: usize,
        /// Rust field count.
        found: usize,
    },
    /// A projected Rust field was absent from the collected constructor.
    MissingConstructorField {
        /// Rust enum family.
        family: String,
        /// Rust variant.
        variant: String,
        /// Rust field.
        field: String,
    },
    /// Semantic lowering omitted a collected rule.
    MissingSemanticRule(Box<StableItemId>),
    /// Inference did not produce a type for a readable binder.
    MissingBindingSort {
        /// Readable clause name.
        rule: String,
        /// Binder whose inferred sort was absent.
        binding: String,
    },
    /// An item of a package the printed package does not depend on directly, to which the
    /// printed clause writes no path the long form can print ([`WrittenPaths`]).
    ExternalDeclaration(Box<StableItemId>),
    /// A dependency's item declared below its crate root, to which the printed clause writes no
    /// path the long form can print ([`WrittenPaths`]) and whose declaring path is not known to
    /// compile ([`dependency_path`]).
    DependencyPath {
        /// The item.
        item: Box<StableItemId>,
        /// Its declaring path from the crate name.
        declared: String,
    },
    /// An item of the printed package that is not visible, or is in a module that is not, from
    /// the module the long form stands in, to which the printed clause writes no path the long
    /// form can print ([`WrittenPaths`]).
    PrivateModule {
        /// The item.
        item: Box<StableItemId>,
        /// The module the long form stands in, as a path from `crate`.
        from: String,
    },
    /// One application mixed positional and named arguments.
    MixedApplicationArguments,
    /// A builtin operation unexpectedly used named arguments.
    NamedBuiltinApplication,
    /// A referenced declaration was absent from the collected bundle.
    MissingDeclaration(Box<StableItemId>),
    /// A named application did not reference a constructor declaration.
    NamedNonConstructor(Box<StableItemId>),
    /// One named constructor field occurred more than once.
    DuplicateApplicationField {
        /// Constructor identity.
        id: Box<StableItemId>,
        /// Duplicate Rust field name.
        field: String,
    },
    /// A constructor result omitted a required named field.
    MissingApplicationField {
        /// Constructor identity.
        id: Box<StableItemId>,
        /// Missing Rust field name.
        field: String,
    },
    /// A named argument did not belong to its constructor declaration.
    UnknownApplicationField {
        /// Constructor identity.
        id: Box<StableItemId>,
        /// Unknown Rust field name.
        field: String,
    },
    /// A canonical integer payload was not valid Rust tokens.
    InvalidLiteral(String),
    /// No reference-surface spelling exists for this builtin token sort.
    UnsupportedBuiltinToken(BuiltinSort),
    /// A readable optional or collection entry has no reference spelling.
    UnsupportedState,
    /// Semantic lowering chose no operation for an operator.
    UnresolvedOperator(&'static str),
    /// Semantic lowering recorded no constructor for bracket list notation.
    UnresolvedListNotation,
    /// Semantic lowering chose no collection operation for an index or a
    /// collection method.
    UnresolvedCollectionMethod(CollectionMethod),
}

impl ToDiagnostic for ReferenceExpansionError {
    fn to_diagnostic(&self) -> Diagnostic {
        let code = match self {
            Self::Source(error) => return error.to_diagnostic(),
            Self::RustSyntax(_) => codes::reference::RUST_SYNTAX,
            Self::KrsSyntax(error) => {
                let mut diagnostic = error.to_diagnostic();
                diagnostic.message = self.to_string();
                return diagnostic;
            }
            Self::Lowering(error) => return error.to_diagnostic(),
            Self::GeneratedRust(_) => codes::reference::GENERATED_RUST,
            Self::DuplicateRule(_) => codes::reference::DUPLICATE_RULE,
            Self::RuleCoverage { .. } => codes::reference::RULE_COVERAGE,
            Self::ConstructorCoverage { .. } => codes::reference::CONSTRUCTOR_COVERAGE,
            Self::ConstructorFieldCoverage { .. } => codes::reference::CONSTRUCTOR_FIELD_COVERAGE,
            Self::MissingConstructorField { .. } => codes::reference::MISSING_CONSTRUCTOR_FIELD,
            Self::MissingSemanticRule(_) => codes::reference::MISSING_SEMANTIC_RULE,
            Self::MissingBindingSort { .. } => codes::reference::MISSING_BINDING_SORT,
            Self::ExternalDeclaration(_) => codes::reference::EXTERNAL_DECLARATION,
            Self::DependencyPath { .. } => codes::reference::DEPENDENCY_PATH,
            Self::PrivateModule { .. } => codes::reference::PRIVATE_MODULE,
            Self::MixedApplicationArguments => codes::reference::MIXED_APPLICATION_ARGUMENTS,
            Self::NamedBuiltinApplication => codes::reference::NAMED_BUILTIN_APPLICATION,
            Self::MissingDeclaration(_) => codes::reference::MISSING_DECLARATION,
            Self::NamedNonConstructor(_) => codes::reference::NAMED_NON_CONSTRUCTOR,
            Self::DuplicateApplicationField { .. } => codes::reference::DUPLICATE_APPLICATION_FIELD,
            Self::MissingApplicationField { .. } => codes::reference::MISSING_APPLICATION_FIELD,
            Self::UnknownApplicationField { .. } => codes::reference::UNKNOWN_APPLICATION_FIELD,
            Self::InvalidLiteral(_) => codes::reference::INVALID_LITERAL,
            Self::UnsupportedBuiltinToken(_) => codes::reference::UNSUPPORTED_BUILTIN_TOKEN,
            Self::UnsupportedState => codes::reference::UNSUPPORTED_STATE,
            Self::UnresolvedOperator(_) | Self::UnresolvedCollectionMethod(_) => {
                codes::reference::UNRESOLVED_OPERATOR
            }
            Self::UnresolvedListNotation => codes::reference::UNRESOLVED_LIST_NOTATION,
        };
        Diagnostic::error(code, self.to_string(), Location::None)
    }
}

impl fmt::Display for ReferenceExpansionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Source(error) => error.fmt(formatter),
            Self::RustSyntax(error) => write!(formatter, "invalid Rust source: {error}"),
            Self::KrsSyntax(error) => write!(formatter, "invalid readable KRS source: {error}"),
            Self::Lowering(error) => write!(formatter, "{error}"),
            Self::GeneratedRust(error) => write!(formatter, "invalid generated Rust: {error}"),
            Self::DuplicateRule(name) => write!(formatter, "readable rule `{name}` occurs twice"),
            Self::RuleCoverage { name, found } => write!(
                formatter,
                "readable rule `{name}` maps to {found} collected head rules; expected one"
            ),
            Self::ConstructorCoverage {
                family,
                variant,
                found,
            } => write!(
                formatter,
                "readable enum variant `{family}::{variant}` maps to {found} constructors; expected one"
            ),
            Self::ConstructorFieldCoverage {
                family,
                variant,
                expected,
                found,
            } => write!(
                formatter,
                "readable enum variant `{family}::{variant}` has {found} Rust fields but {expected} collected fields"
            ),
            Self::MissingConstructorField {
                family,
                variant,
                field,
            } => write!(
                formatter,
                "readable enum field `{family}::{variant}.{field}` is absent from its collected constructor"
            ),
            Self::MissingSemanticRule(id) => {
                write!(formatter, "collected rule {id} is absent from semantic IR")
            }
            Self::MissingBindingSort { rule, binding } => {
                write!(
                    formatter,
                    "rule `{rule}` binding `{binding}` has no inferred sort"
                )
            }
            Self::ExternalDeclaration(item) => write!(
                formatter,
                "cannot print a path to {item}: its package is no direct dependency of the printed package, so the source has no crate name for it, and the clause writes no path to it that the long form can print (a path of one name that no one `use` of the module binds, or a path a glob of the block may reach); name it in the clause by a path through the dependency that re-exports it (`dep::Item`), or depend on its package"
            ),
            Self::DependencyPath { item, declared } => write!(
                formatter,
                "cannot print a path to {item}: the clause writes no path to it that the long form can print (a path of one name that no one `use` of the module binds, or a path a glob of the block may reach), and `{declared}` passes through modules whose publicity the collected declarations do not record; name it in the clause by a path that compiles there, such as its public re-export"
            ),
            Self::PrivateModule { item, from } => write!(
                formatter,
                "cannot print a path to {item} in `{from}`: the item or a module on `{}` is private to a module that does not contain `{from}`, and the clause writes no path to the item there that the long form can print; make it visible there (`pub(crate)`), or name the item in the clause by a path that compiles there, such as a re-export (a binder's sort by `where x: PATH`)",
                crate_module_path(item.module_path()),
            ),
            Self::MixedApplicationArguments => {
                formatter.write_str("application mixes positional and named arguments")
            }
            Self::NamedBuiltinApplication => {
                formatter.write_str("builtin application unexpectedly uses named arguments")
            }
            Self::MissingDeclaration(id) => {
                write!(formatter, "application declaration {id} is absent")
            }
            Self::NamedNonConstructor(id) => {
                write!(formatter, "named application {id} is not a constructor")
            }
            Self::DuplicateApplicationField { id, field } => {
                write!(formatter, "constructor {id} repeats field `{field}`")
            }
            Self::MissingApplicationField { id, field } => {
                write!(formatter, "constructor result {id} omits field `{field}`")
            }
            Self::UnknownApplicationField { id, field } => {
                write!(formatter, "constructor {id} has no field `{field}`")
            }
            Self::InvalidLiteral(value) => write!(formatter, "invalid integer literal `{value}`"),
            Self::UnsupportedBuiltinToken(sort) => {
                write!(formatter, "unsupported builtin token sort {sort}")
            }
            Self::UnsupportedState => formatter
                .write_str("a readable optional or collection entry has no reference spelling"),
            Self::UnresolvedOperator(operator) => write!(
                formatter,
                "semantic lowering chose no builtin operation for an operator `{operator}`"
            ),
            Self::UnresolvedListNotation => formatter
                .write_str("semantic lowering chose no constructor for bracket list notation"),
            Self::UnresolvedCollectionMethod(method) => write!(
                formatter,
                "semantic lowering chose no collection operation for `{}`",
                method.written()
            ),
        }
    }
}

impl Error for ReferenceExpansionError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Source(error) => error.source(),
            Self::RustSyntax(error) | Self::GeneratedRust(error) => Some(error),
            Self::KrsSyntax(error) => Some(error),
            Self::Lowering(error) => Some(error.as_ref()),
            Self::DuplicateRule(_)
            | Self::RuleCoverage { .. }
            | Self::ConstructorCoverage { .. }
            | Self::ConstructorFieldCoverage { .. }
            | Self::MissingConstructorField { .. }
            | Self::MissingSemanticRule(_)
            | Self::MissingBindingSort { .. }
            | Self::ExternalDeclaration(_)
            | Self::DependencyPath { .. }
            | Self::PrivateModule { .. }
            | Self::MixedApplicationArguments
            | Self::NamedBuiltinApplication
            | Self::MissingDeclaration(_)
            | Self::NamedNonConstructor(_)
            | Self::DuplicateApplicationField { .. }
            | Self::MissingApplicationField { .. }
            | Self::UnknownApplicationField { .. }
            | Self::InvalidLiteral(_)
            | Self::UnsupportedBuiltinToken(_)
            | Self::UnsupportedState
            | Self::UnresolvedOperator(_)
            | Self::UnresolvedListNotation
            | Self::UnresolvedCollectionMethod(_) => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Bindings, PathScope, ReferenceExpansionError, WrittenPaths, authored_paths, configured_out,
        contains_use_tree, fresh_ident, rename_hidden_tokens, render_declared_path,
        render_reference_token_term_type, render_sort_marker, render_term, rust_ident,
        written_path,
    };
    use krs_diagnostic::{ToDiagnostic, codes};
    use krs_ir::{
        BuiltinSort, DescriptorApplicationHeadClass, DescriptorApplicationRef,
        DescriptorApplicationReference, DescriptorBundle, DescriptorTerm, ItemKind, ListOperation,
        PackageId, ProvenanceKey, ProvenanceRole, StableItemId,
    };
    use quote::ToTokens;
    use std::collections::{BTreeMap, BTreeSet};

    #[test]
    fn facade_attributes_prevent_readable_item_macro_projection() {
        let facade = krs_syntax::surface::FacadeScope::new(["crate".to_owned()].into());
        let file = syn::parse_file(
            "use crate as k;\n#[k::sort] k::sorts! { A; }\n#[k::unknown] k::rules! { invalid }\n#[doc = \"x\"] k::sorts! { B; }\nk::rules! {}\n",
        )
        .unwrap();
        let entries = super::reference_macro_entries(&file, &facade);
        assert_eq!(
            entries,
            std::collections::BTreeMap::from([
                (vec![3], krs_syntax::surface::FunctionMacro::Sorts),
                (vec![4], krs_syntax::surface::FunctionMacro::Rules),
            ]),
        );
    }

    #[test]
    fn map_macro_import_detection_ignores_attributes_and_rejects_other_uses() {
        let file = syn::parse_file("#[allow(unused_imports)] use k::map; use k::builtin::map;")
            .expect("valid imports");
        let expected = syn::parse_str::<syn::ItemUse>("use k::map;")
            .expect("valid map import")
            .tree
            .to_token_stream()
            .to_string();
        assert!(contains_use_tree(&file.items, &expected));

        let other = syn::parse_str::<syn::ItemUse>("use k::cells;")
            .expect("valid cells import")
            .tree
            .to_token_stream()
            .to_string();
        assert!(!contains_use_tree(&file.items, &other));
    }

    #[test]
    fn a_strictness_long_form_names_its_context_alias() {
        let strictness = krs_syntax::parse_seqstrict_attribute(quote::quote!(
            using = operand_eval,
            sequence = [value],
            result = KResult
        ))
        .unwrap();
        let mut variant: syn::Variant = syn::parse_quote!(
            #[k::seqstrict(using = operand_eval)]
            Double { value: Expr }
        );
        super::materialize_reference_strictness(&mut variant, Some(&strictness)).unwrap();
        assert_eq!(
            variant.attrs[0].to_token_stream().to_string(),
            "# [k :: seqstrict (using = operand_eval , sequence = [value] , result = k :: KResult)]"
        );
    }

    #[test]
    fn readable_macros_of_inline_modules_are_found_by_their_module_indices() {
        let facade = krs_syntax::surface::FacadeScope::new(["k".to_owned()].into());
        let file = syn::parse_file(
            "mod a { use x::y; k::rules! {} mod b { k::sorts! { A; } } }\nfn f() { k::rules! {} }\nk::equations! {}\n",
        )
        .unwrap();
        assert_eq!(
            super::reference_macro_entries(&file, &facade),
            std::collections::BTreeMap::from([
                (vec![0, 1], krs_syntax::surface::FunctionMacro::Rules),
                (vec![0, 2, 0], krs_syntax::surface::FunctionMacro::Sorts),
                (vec![2], krs_syntax::surface::FunctionMacro::Equations),
            ]),
        );
    }

    #[test]
    fn canonical_bytes_token_expands_back_to_a_byte_string_macro() {
        let package = PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap();
        let token = DescriptorTerm::BuiltinToken {
            key: ProvenanceKey::new(ProvenanceRole::ClaimBytesToken, 0),
            sort: BuiltinSort::Bytes,
            value: r#"b"\x00\x41\xff""#.to_owned(),
        };
        let rendered = render_term(
            &token,
            false,
            local(&package),
            &DescriptorBundle::new(Vec::new()).unwrap(),
        )
        .unwrap()
        .to_string();
        assert_eq!(rendered, r#"k :: bytes ! (b"\0A\xFF")"#);
    }

    #[test]
    fn declared_token_reference_field_remains_a_symbolic_term() {
        let package = PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap();
        let token = StableItemId::new(
            package.clone(),
            std::iter::empty::<String>(),
            "String",
            ItemKind::Sort,
            "",
        )
        .unwrap();
        let rendered = render_reference_token_term_type(&token, local(&package))
            .unwrap()
            .to_string();

        assert_eq!(rendered, "k :: Term < crate :: String >");
    }

    #[test]
    fn list_lookup_expands_back_to_the_typed_builtin_marker() {
        let package = PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap();
        let variable = |name: &str, ordinal| DescriptorTerm::Variable {
            key: ProvenanceKey::new(ProvenanceRole::ClaimEnsuresReference, ordinal),
            path_key: ProvenanceKey::new(ProvenanceRole::ClaimEnsuresPath, ordinal),
            name: name.to_owned(),
        };
        let lookup = DescriptorTerm::Application {
            instance: Vec::new(),
            head_class: DescriptorApplicationHeadClass::Applied,
            reference: DescriptorApplicationReference {
                key: ProvenanceKey::new(ProvenanceRole::ClaimEnsuresApplicationHead, 0),
                application: DescriptorApplicationRef::List(ListOperation::Get),
            },
            path_key: ProvenanceKey::new(ProvenanceRole::ClaimEnsuresPath, 2),
            arguments: krs_ir::Arguments::Positional(vec![
                Box::new(variable("program", 0)),
                Box::new(variable("index", 1)),
            ]),
            update: None,
            open: false,
        };
        let rendered = render_term(
            &lookup,
            false,
            local(&package),
            &DescriptorBundle::new(Vec::new()).unwrap(),
        )
        .unwrap()
        .to_string();
        assert_eq!(rendered, "k :: builtin :: list :: get (program , index)");
    }
    /// Whether `result` is the typed failure of a name that no identifier spells.
    fn unprintable<T>(result: &Result<T, ReferenceExpansionError>) -> bool {
        matches!(result, Err(ReferenceExpansionError::GeneratedRust(_)))
    }

    #[test]
    fn a_name_prints_as_its_identifier_or_raw_keyword_and_no_name_panics() {
        for (name, printed) in [
            ("x", "x"),
            ("type", "r#type"),
            ("r#type", "r#type"),
            // Reserved in the 2024 edition, which `syn` does not reserve.
            ("gen", "r#gen"),
            ("r#gen", "r#gen"),
            ("try", "r#try"),
            ("async", "r#async"),
            ("await", "r#await"),
            ("dyn", "r#dyn"),
            ("union", "union"),
        ] {
            assert_eq!(rust_ident(name).unwrap().to_string(), printed);
        }
        // `Ident::new_raw` panics on each of these; the printer fails typed instead.
        for name in [
            "_", "self", "Self", "super", "crate", "", "1x", "a-b", "r#_",
        ] {
            assert!(unprintable(&rust_ident(name)), "{name:?}");
        }
    }

    #[test]
    fn a_fresh_name_from_an_authored_base_that_is_no_identifier_fails_typed() {
        let mut reserved = std::collections::BTreeSet::from(["tail".to_owned()]);
        assert_eq!(
            fresh_ident("tail", &mut reserved).unwrap().to_string(),
            "tail1"
        );
        assert!(unprintable(&fresh_ident("", &mut reserved)));
        // A record update's hidden binder is named after what follows its prefix, which an
        // authored identifier may leave empty.
        assert!(unprintable(&rename_hidden_tokens(quote::quote!(
            __krs_update_
        ))));
    }

    #[test]
    fn an_authored_raw_identifier_reserves_its_name_for_a_fresh_binder() {
        // `r#bits` is the identifier `bits`, so the hidden binder takes `bits1`.
        let (tokens, renamed) =
            rename_hidden_tokens(quote::quote!(f(r#bits, __krs_bits_0))).unwrap();
        assert_eq!(renamed["__krs_bits_0"].to_string(), "bits1");
        assert_eq!(tokens.to_string(), "f (r#bits , bits1)");
    }

    #[test]
    fn a_variable_named_by_a_keyword_prints_raw() {
        let package = PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap();
        let variable = DescriptorTerm::Variable {
            key: ProvenanceKey::new(ProvenanceRole::ClaimEnsuresReference, 0),
            path_key: ProvenanceKey::new(ProvenanceRole::ClaimEnsuresPath, 0),
            name: "match".to_owned(),
        };
        let rendered = render_term(
            &variable,
            true,
            local(&package),
            &DescriptorBundle::new(Vec::new()).unwrap(),
        )
        .unwrap()
        .to_string();
        assert_eq!(rendered, "r#match");
    }

    /// The scope of `package`'s own source, which names no dependency.
    fn local(package: &PackageId) -> PathScope<'_> {
        static NONE: BTreeMap<PackageId, String> = BTreeMap::new();
        static AUTHORED: BTreeMap<(String, String), BTreeSet<Vec<String>>> = BTreeMap::new();
        PathScope {
            package,
            crates: &NONE,
            authored: &AUTHORED,
            written: Box::leak(Box::default()),
            at: None,
            module: &[],
            tree: None,
        }
    }

    #[test]
    fn a_turbofish_marker_of_a_framework_sort_is_the_facade_marker() {
        let package = PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap();
        let framework = PackageId::new(
            crate::partition::FRAMEWORK_NAMESPACE,
            "krs",
            "0.1.0",
            "workspace",
        )
        .unwrap();
        let sort = |package: &PackageId, name: &str| {
            krs_ir::DescriptorSortRef::Declared(
                StableItemId::new(
                    package.clone(),
                    std::iter::empty::<String>(),
                    name,
                    ItemKind::Sort,
                    "",
                )
                .unwrap(),
            )
        };
        let marker = |sort| {
            render_sort_marker(&sort, local(&package))
                .unwrap()
                .to_string()
        };
        assert_eq!(marker(sort(&framework, "KItem")), "dyn k :: KItemSort");
        assert_eq!(marker(sort(&framework, "KResult")), "dyn k :: KResultSort");
        assert_eq!(marker(sort(&package, "Exp")), "dyn crate :: ExpSort");
        // A dependency's sort, by the crate name the source gives the dependency, and a package
        // the source names no crate of, which has no path there.
        let dependency = PackageId::new("DEP", "dep-semantics", "0.1.0", "workspace").unwrap();
        let other = PackageId::new("OTHER", "other", "0.1.0", "workspace").unwrap();
        let crates = BTreeMap::from([(dependency.clone(), "semantic_dep".to_owned())]);
        let written = WrittenPaths::default();
        let scope = PathScope {
            package: &package,
            crates: &crates,
            authored: &BTreeMap::new(),
            written: &written,
            at: None,
            module: &[],
            tree: None,
        };
        assert_eq!(
            render_sort_marker(&sort(&dependency, "Exp"), scope)
                .unwrap()
                .to_string(),
            "dyn :: semantic_dep :: ExpSort"
        );
        assert!(matches!(
            render_sort_marker(&sort(&other, "Exp"), scope),
            Err(ReferenceExpansionError::ExternalDeclaration(_))
        ));
    }

    /// Another crate's items are visible alike from every module of the printed crate, so a path
    /// through a dependency's module written in one module file is evidence in every other.
    #[test]
    fn a_path_another_module_file_writes_is_evidence_for_a_dependency_item() {
        let package = PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap();
        let dependency = PackageId::new("DEP", "dep-semantics", "0.1.0", "workspace").unwrap();
        let crates = BTreeMap::from([(dependency.clone(), "semantic_dep".to_owned())]);
        let unit = StableItemId::new(
            dependency,
            ["sorts".to_owned()],
            "Unit",
            ItemKind::Constructor,
            "",
        )
        .unwrap();
        let written = WrittenPaths::default();
        let files = ["fn f() {}", "pub use semantic_dep::sorts;"]
            .map(|source| syn::parse_file(source).unwrap());
        let printed = |files: &[syn::File]| {
            let facade = krs_syntax::surface::FacadeScope::new(["k".to_owned()].into());
            let authored = authored_paths(files, &crates, &facade);
            let scope = PathScope {
                package: &package,
                crates: &crates,
                authored: &authored,
                written: &written,
                at: None,
                module: &[],
                tree: None,
            };
            render_declared_path(&unit, scope).map(|path| path.to_string().replace(' ', ""))
        };
        assert_eq!(printed(&files).unwrap(), "::semantic_dep::sorts::Unit");
        assert_eq!(
            printed(&files[..1]).unwrap_err().to_diagnostic().code,
            codes::reference::DEPENDENCY_PATH
        );
    }

    /// A dependency's item that the printed clause writes no path to prints by its declaring
    /// path where that is known to compile: at the crate root, or where the source writes it (a
    /// rename of the crate or a module in the same module counts, one in another module does
    /// not). A path ending in the item's name through a re-export is no evidence (a renaming
    /// re-export gives that name another item), so elsewhere the print is refused.
    #[test]
    fn a_dependency_item_without_a_written_path_prints_by_its_declaring_path() {
        let package = PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap();
        let dependency = PackageId::new("DEP", "dep-semantics", "0.1.0", "workspace").unwrap();
        let crates = BTreeMap::from([(dependency.clone(), "semantic_dep".to_owned())]);
        let item = |module: &[&str], name: &str| {
            StableItemId::new(
                dependency.clone(),
                module.iter().map(|segment| (*segment).to_owned()),
                name,
                ItemKind::Constructor,
                "",
            )
            .unwrap()
        };
        let written = WrittenPaths::default();
        let printed = |source: &str, id: &StableItemId| {
            let file = syn::parse_file(source).unwrap();
            let facade = krs_syntax::surface::FacadeScope::new(["k".to_owned()].into());
            let authored = authored_paths(std::iter::once(&file), &crates, &facade);
            let scope = PathScope {
                package: &package,
                crates: &crates,
                authored: &authored,
                written: &written,
                at: None,
                module: &[],
                tree: None,
            };
            render_declared_path(id, scope).map(|path| path.to_string().replace(' ', ""))
        };
        let unit = item(&["sorts"], "Unit");
        let source = "k::rules! { cross: semantic_dep::Unit => semantic_dep::sorts::Same; }";
        assert_eq!(
            printed(source, &item(&["sorts"], "Same")).unwrap(),
            "::semantic_dep::sorts::Same"
        );
        // A path through the declaring module shows the module reaches the printed crate, so
        // every item it declares prints by its declaring path, whichever item the path names.
        for through in [source, "pub use semantic_dep::sorts;"] {
            assert_eq!(
                printed(through, &unit).unwrap(),
                "::semantic_dep::sorts::Unit",
                "{through}"
            );
        }
        for refused in [
            "use semantic_dep::{Unit as U, other::Same};",
            "use semantic_dep::sorts_other::Unit;",
            "fn f() {}",
            // A path under `#[cfg]` is no evidence: rustc resolved it only where the condition
            // held.
            "#[cfg(any())] pub use semantic_dep::sorts;",
            "#[cfg(any())] mod m { pub use semantic_dep::sorts; }",
            "mod m { #![cfg(any())] pub use semantic_dep::sorts; }",
            // Only `use` trees and readable macros count: a fn body or a `macro_rules!` body
            // may hold paths rustc never resolved (a `#[cfg]` on a statement, a macro never
            // invoked).
            "fn f() { #[cfg(any())] let _ = semantic_dep::sorts::Same; }",
            "macro_rules! m { () => { semantic_dep::sorts::Same }; }",
            // Where the module declares or imports an item of the crate's name, the path is
            // through that item.
            "mod semantic_dep { pub mod sorts {} } k::rules! { cross: semantic_dep::sorts::Unit => semantic_dep::sorts::Unit; }",
            "use other::semantic_dep; pub use semantic_dep::sorts;",
            "use other::module as semantic_dep; pub use semantic_dep::sorts;",
        ] {
            let error = printed(refused, &unit).unwrap_err();
            assert_eq!(
                error.to_diagnostic().code,
                codes::reference::DEPENDENCY_PATH,
                "{refused}"
            );
        }
        assert_eq!(
            printed("fn f() {}", &item(&[], "Unit")).unwrap(),
            "::semantic_dep::Unit"
        );
        for renamed in [
            "use semantic_dep as sd; k::rules! { cross: sd::sorts::Unit => sd::sorts::Unit; }",
            "use semantic_dep::sorts as s; k::rules! { cross: s::Unit => s::Unit; }",
            "extern crate semantic_dep as sd; k::rules! { cross: sd::sorts::Unit => sd::sorts::Unit; }",
            "mod m { use semantic_dep as sd; k::rules! { cross: sd::sorts::Unit => sd::sorts::Unit; } }",
            // A module's own item of the crate's name does not hide the crate from the
            // modules it declares.
            "mod semantic_dep {} mod m { pub use semantic_dep::sorts; }",
            "use semantic_dep; pub use semantic_dep::sorts;",
        ] {
            assert_eq!(
                printed(renamed, &unit).unwrap(),
                "::semantic_dep::sorts::Unit",
                "{renamed}"
            );
        }
        // A module's `use` does not reach the modules around it, and a name given two paths
        // is no rename.
        for unrenamed in [
            "mod m { use semantic_dep as sd; } k::rules! { cross: sd::sorts::Unit => sd::sorts::Unit; }",
            "use semantic_dep as sd; mod m { k::rules! { cross: sd::sorts::Unit => sd::Unit; } }",
            "use semantic_dep as sd; use semantic_dep::other as sd; k::rules! { cross: sd::sorts::Unit => sd::Unit; }",
        ] {
            assert!(
                matches!(
                    printed(unrenamed, &unit),
                    Err(ReferenceExpansionError::DependencyPath { .. })
                ),
                "{unrenamed}"
            );
        }
    }

    /// A path a clause writes prints as the long form prints it in the clause's module: a path
    /// of two or more segments verbatim, a path of one name through the one `use` of the module
    /// that binds it, a path the block's `use` items reach through that `use`; none where a glob
    /// may bind its first name, or a `use` that may not hold does.
    #[test]
    fn a_written_path_prints_as_it_resolves_where_the_long_form_stands() {
        let module = Bindings::of_items(
            &syn::parse_file(
                "use mid::{Common, Same, alt::{self as alternative}}; use mid::alt::Unit as AltUnit; \
                 use ::mid::Wrap; use other::*; #[cfg(test)] use mid::Tested; extern crate mid as m;",
            )
            .unwrap()
            .items,
        );
        let path = |text: &str| syn::parse_str::<syn::Path>(text).unwrap();
        let printed = |text: &str, block: Option<&Bindings>| {
            written_path(path(text), block, &module)
                .map(|path| path.to_token_stream().to_string().replace(' ', ""))
        };
        for (written, expected) in [
            ("p::Unit", Some("p::Unit")),
            ("Choose::<Int>", None),
            ("mid::Choose::<Int>", Some("mid::Choose")),
            ("Same", Some("mid::Same")),
            ("AltUnit", Some("mid::alt::Unit")),
            ("alternative", Some("mid::alt")),
            ("Wrap", Some("::mid::Wrap")),
            ("m", Some("::mid")),
            ("::mid::Same", Some("::mid::Same")),
            ("crate::p::Unit", Some("crate::p::Unit")),
            ("self", None),
            ("Globbed", None),
            ("Tested", None),
        ] {
            assert_eq!(printed(written, None).as_deref(), expected, "{written}");
        }
        let block = Bindings::of_uses(&[
            syn::parse_quote!(
                use mid::alt as a;
            ),
            syn::parse_quote!(
                use a::Unit as Inner;
            ),
        ]);
        for (written, expected) in [
            ("a::Unit", Some("mid::alt::Unit")),
            ("Same", Some("mid::Same")),
            ("p::Unit", Some("p::Unit")),
            ("Inner", None),
        ] {
            assert_eq!(
                printed(written, Some(&block)).as_deref(),
                expected,
                "{written}"
            );
        }
        let globbed = Bindings::of_uses(&[syn::parse_quote!(
            use Syntax::*;
        )]);
        assert_eq!(printed("p::Unit", Some(&globbed)), None);
    }

    #[test]
    fn a_clause_is_configured_out_only_under_a_cfg() {
        let attributes = |text: &str| {
            syn::parse_str::<syn::ItemFn>(&format!("{text} fn f() {{}}"))
                .unwrap()
                .attrs
        };
        assert!(configured_out(&attributes("#[cfg(any())]")));
        assert!(configured_out(&attributes(
            "#[doc = \"a clause\"] #[cfg(any())]"
        )));
        assert!(!configured_out(&attributes("#[doc = \"a clause\"]")));
        assert!(!configured_out(&attributes("#[k::rule(priority = 1)]")));
    }
}
