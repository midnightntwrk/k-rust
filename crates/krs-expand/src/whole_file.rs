//! Whole-file expansion of one authored KRS source file.
//!
//! [`expand_file`] turns an authored file into Rust that rustc compiles
//! without invoking a KRS procedural macro:
//!
//! 1. The file is lexed once ([`AuthoredFile::lex`]) and parsed from those
//!    tokens, so every authored span locates exact authored bytes.
//! 2. A `syn` walk over items, inline `mod` bodies, `impl` and `trait` items,
//!    statements, expressions, patterns, and types finds the outermost KRS
//!    invocations, and the token trees of every other macro are scanned for
//!    KRS function-like invocations, which rustc reaches after that macro
//!    re-emits its input.
//! 3. Each invocation receives the input rustc passes: an attribute macro
//!    gets its attribute's arguments and the authored tokens of the item
//!    with that one attribute removed, and a function-like macro gets the
//!    tokens inside its delimiters.
//! 4. Each output is rescanned for KRS function-like invocations, which are
//!    expanded in turn under their parent (rustc's re-expansion of macro
//!    output), up to [`RECURSION_LIMIT`] levels.
//! 5. The file is printed with [`print_with_map`]: authored text outside
//!    every invocation is copied unchanged, and each outermost expansion,
//!    with its nested expansions spliced in, replaces the invocation's
//!    authored range.
//! 6. Every `__register_host_descriptor!` and `__request_framework_sorts!`
//!    the expansions emit is collected, and the crate-root explicit
//!    descriptor registration table (`__KRS_REGISTRATIONS`) is appended as
//!    generated-only text.
//!
//! Declarative and standard macros, including the facade's registration
//! macros, are left for rustc. KRS invocations that only a declarative macro
//! could produce are not found; the lesson policy rejects `macro_rules!`
//! definitions and KRS names used without the facade prefix, so a lesson
//! cannot contain one.
//!
//! Attribute order follows rustc's choice of the first attribute that is not
//! a doc comment, a built-in inert attribute, or a tool attribute. When that
//! attribute is not the KRS attribute (for example a `#[derive]` or a
//! `#[cfg]` before it), rustc would expand the other attribute first; this
//! driver reports [`ATTRIBUTE_ORDER`] instead of emulating that order.

use krs_syntax::surface::{self, AttributeMacro, Entry, FunctionMacro};
use proc_macro2::{Delimiter, Spacing, Span, TokenStream, TokenTree};
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::{Attribute, ImplItem, Item, Macro, Meta, Path, PathSegment, TraitItem};

use crate::browser_env::BrowserEnvironment;
use crate::sink::{
    AuthoredFile, ByteRange, GeneratedSource, InvocationId, MappingClass, Splice, print_with_map,
    splice_tokens,
};

/// Maximum nesting depth of rescanned invocations: rustc's default
/// `recursion_limit`.
pub const RECURSION_LIMIT: usize = 128;

/// The authored file does not lex or parse as a Rust file.
pub const PARSE: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::expand::PARSE;
    CODE.as_str()
};
/// The authored file starts with a byte order mark or a shebang line, which
/// rustc strips and the fallback lexer does not.
pub const UNSUPPORTED_SOURCE: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::expand::UNSUPPORTED_SOURCE;
    CODE.as_str()
};
/// A KRS attribute follows an attribute that rustc would expand first.
pub const ATTRIBUTE_ORDER: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::expand::ATTRIBUTE_ORDER;
    CODE.as_str()
};
/// A KRS attribute has a `key = value` form, which rustc rejects for
/// attribute macros.
pub const ATTRIBUTE_FORM: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::expand::ATTRIBUTE_FORM;
    CODE.as_str()
};
/// The first expandable attribute names a facade item that is not a KRS
/// attribute macro.
pub const NOT_AN_ATTRIBUTE_MACRO: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::expand::NOT_AN_ATTRIBUTE_MACRO;
    CODE.as_str()
};
/// An expansion emitted a KRS attribute invocation, which this driver does
/// not expand.
pub const NESTED_ATTRIBUTE: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::expand::NESTED_ATTRIBUTE;
    CODE.as_str()
};
/// Rescanned invocations nest deeper than [`RECURSION_LIMIT`].
pub const RECURSION: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::expand::RECURSION;
    CODE.as_str()
};
/// A descriptor factory is defined where the crate-root registration table
/// cannot name it.
pub const REGISTRATION_SCOPE: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::expand::REGISTRATION_SCOPE;
    CODE.as_str()
};
/// An explicitly selected invocation does not match a discovered one.
pub const SELECTION: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::expand::SELECTION;
    CODE.as_str()
};
/// An expansion cannot be printed as text without changing its tokens.
pub const PRINT: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::expand::PRINT;
    CODE.as_str()
};

/// Name of the crate-root registration table, which replaces `inventory`
/// collection where link-time constructors do not run (the browser rustc).
pub const REGISTRATION_TABLE: &str = "__KRS_REGISTRATIONS";

/// Which invocations [`expand_file`] expands.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Selection {
    /// Every outermost KRS invocation of the file.
    WholeFile,
    /// Only the listed outermost invocations; every other invocation is left
    /// in the output unexpanded. For editor tooling and tests.
    Invocations(Vec<SelectedInvocation>),
}

/// One explicitly selected invocation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SelectedInvocation {
    /// The `krs-macros` entry-point name, such as `sorts`.
    pub kind: String,
    /// The authored byte range the expansion replaces (see
    /// [`crate::sink::Invocation::replaced`]).
    pub replaced: ByteRange,
}

/// The inputs of one whole-file expansion.
#[derive(Clone, Debug)]
pub struct FileRequest<'a> {
    /// The package-relative display file rustc reports for the authored file
    /// (`Span::file()`), for example `src/lib.rs`; it enters expansion nonces
    /// and `HostProvenance`.
    pub display_file: &'a str,
    /// The complete authored source.
    pub source: &'a str,
    /// Path of the generated file rustc compiles; recorded in the map.
    pub generated_file: &'a str,
    /// The dependency name through which authored code names the facade.
    pub facade_alias: &'a str,
    /// The path through which generated code names the facade, `::k` for
    /// facade alias `k`.
    pub facade_path: Path,
    /// Module path of the authored file, starting with the crate name.
    pub module_path: &'a [String],
    /// Which invocations to expand.
    pub selection: &'a Selection,
}

/// One registered descriptor factory.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Registration {
    /// The outermost invocation whose expansion registers the factory.
    pub invocation: InvocationId,
    /// Module path of the factory, starting with the crate name.
    pub module_path: Vec<String>,
    /// The factory's name.
    pub factory: String,
    /// The `#[cfg]` attributes of the registration, as Rust text.
    pub cfg: Vec<String>,
}

/// A successful whole-file expansion.
#[derive(Debug)]
pub struct FileExpansion {
    /// The authored file; valid until the next
    /// `proc_macro2::extra::invalidate_current_thread_spans`.
    pub authored: AuthoredFile,
    /// The generated text and its map.
    pub generated: GeneratedSource,
    /// Registered descriptor factories, in expansion order.
    pub registrations: Vec<Registration>,
    /// Whether some expansion requests the framework `KItem`/`KResult`
    /// descriptors.
    pub requests_framework: bool,
    /// Every invocation's own output (nested invocations unexpanded), in
    /// invocation-id order.
    pub expansions: Vec<Expansion>,
}

/// One invocation's expansion.
#[derive(Clone, Debug)]
pub struct Expansion {
    /// The invocation.
    pub id: InvocationId,
    /// The `krs-macros` entry-point name.
    pub kind: &'static str,
    /// The renderer's output, as `krs-macros` would return it to rustc.
    pub output: TokenStream,
}

/// One expansion diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpandDiagnostic {
    /// `None` for a renderer diagnostic, which rustc reports through
    /// `compile_error!` without a code; one of this module's codes otherwise.
    pub code: Option<&'static str>,
    /// The message.
    pub message: String,
    /// [`MappingClass::ExactAuthored`] when `authored` is the exact span of
    /// the diagnostic, [`MappingClass::InvocationLevel`] when it is the
    /// invocation's call site, [`MappingClass::Unmappable`] without a range.
    pub class: MappingClass,
    /// Authored UTF-8 byte range.
    pub authored: Option<ByteRange>,
    /// The invocation that reported it, numbered as in the source map.
    pub invocation: Option<InvocationId>,
}

impl ExpandDiagnostic {
    fn exact(code: &'static str, message: String, authored: ByteRange) -> Self {
        Self {
            code: Some(code),
            message,
            class: MappingClass::ExactAuthored,
            authored: Some(authored),
            invocation: None,
        }
    }

    fn unmappable(code: &'static str, message: String) -> Self {
        Self {
            code: Some(code),
            message,
            class: MappingClass::Unmappable,
            authored: None,
            invocation: None,
        }
    }
}

/// Expands `request.source` as one authored file.
///
/// # Errors
///
/// Returns every diagnostic when the file cannot be expanded: a renderer
/// error of any invocation (expansion continues past it, as rustc's does), or
/// one of this module's codes.
pub fn expand_file(request: &FileRequest<'_>) -> Result<FileExpansion, Vec<ExpandDiagnostic>> {
    if let Some(diagnostic) = unsupported_prefix(request.source) {
        return Err(vec![diagnostic]);
    }
    let (authored, tokens) =
        AuthoredFile::lex(request.display_file, request.source).map_err(|error| {
            vec![ExpandDiagnostic::unmappable(
                PARSE,
                format!("the authored file does not lex: {error}"),
            )]
        })?;
    let file: syn::File = syn::parse2(tokens.clone()).map_err(|error| {
        error
            .into_iter()
            .map(|error| {
                let range = authored.byte_range(error.span());
                ExpandDiagnostic {
                    code: Some(PARSE),
                    message: error.to_string(),
                    class: if range.is_some() {
                        MappingClass::ExactAuthored
                    } else {
                        MappingClass::Unmappable
                    },
                    authored: range,
                    invocation: None,
                }
            })
            .collect::<Vec<_>>()
    })?;

    let mut discovery = Discovery {
        alias: request.facade_alias,
        authored: &authored,
        root: &tokens,
        scope: Scope::Module(Vec::new()),
        found: Vec::new(),
        diagnostics: Vec::new(),
    };
    discovery.visit_file(&file);
    let Discovery {
        mut found,
        mut diagnostics,
        ..
    } = discovery;
    found.sort_by_key(|found| found.replaced.start());
    let found = select(found, request.selection, &mut diagnostics);

    let env = BrowserEnvironment::new(&authored, request.facade_path.clone());
    let mut expander = Expander {
        env: &env,
        authored: &authored,
        alias: request.facade_alias,
        facade: &request.facade_path,
        next_id: 0,
        diagnostics,
    };
    let mut roots = Vec::new();
    for found in found {
        let scope = found.scope.clone();
        if let Some(node) = expander.expand(Pending {
            entry: found.entry,
            attributes: found.attributes,
            input: found.input,
            call_site: found.call_site,
            replaced: found.replaced,
            parent: None,
            depth: 1,
        }) {
            roots.push((node, scope));
        }
    }
    let mut diagnostics = expander.diagnostics;

    let (registrations, requests_framework) =
        collect_registrations(&roots, request.module_path, &authored, &mut diagnostics);
    if !diagnostics.is_empty() {
        return Err(diagnostics);
    }
    let generated = print(
        &roots,
        request,
        &authored,
        requests_framework,
        &registrations,
    )?;
    let mut expansions = Vec::new();
    for (node, _) in &roots {
        node.collect(&mut expansions);
    }
    Ok(FileExpansion {
        authored,
        generated,
        registrations,
        requests_framework,
        expansions,
    })
}

/// Collects the registrations of every outermost expansion; a factory the
/// crate-root table cannot name is reported instead.
fn collect_registrations(
    roots: &[(Node, Scope)],
    module_path: &[String],
    authored: &AuthoredFile,
    diagnostics: &mut Vec<ExpandDiagnostic>,
) -> (Vec<Registration>, bool) {
    let mut registrations = Vec::new();
    let mut requests_framework = false;
    for (node, scope) in roots {
        let spliced = splice_tokens(&node.output, &node.splices());
        let mut found = Vec::new();
        scan_registrations(&spliced, 0, &mut found, &mut requests_framework);
        for (depth, factory, cfg, span) in found {
            let at_crate_root =
                matches!((scope, depth), (Scope::Module(modules), 0) if modules.is_empty());
            if !at_crate_root {
                diagnostics.push(ExpandDiagnostic {
                    code: Some(REGISTRATION_SCOPE),
                    message: format!(
                        "descriptor factory `{factory}` is not defined at the crate root, so the crate-root registration table cannot name it"
                    ),
                    class: MappingClass::InvocationLevel,
                    authored: authored
                        .byte_range(span)
                        .filter(|range| !range.is_empty())
                        .or(Some(node.call_site)),
                    invocation: Some(node.id),
                });
                continue;
            }
            registrations.push(Registration {
                invocation: node.id,
                module_path: module_path.to_vec(),
                factory,
                cfg,
            });
        }
    }
    (registrations, requests_framework)
}

/// Prints the file: authored text outside every outermost invocation, each
/// expansion with its nested expansions spliced in, and the registration
/// table.
fn print(
    roots: &[(Node, Scope)],
    request: &FileRequest<'_>,
    authored: &AuthoredFile,
    requests_framework: bool,
    registrations: &[Registration],
) -> Result<GeneratedSource, Vec<ExpandDiagnostic>> {
    let mut generated = GeneratedSource::new(request.generated_file, authored);
    let mut cursor = 0;
    for (node, _) in roots {
        generated.copy_authored(
            authored,
            ByteRange::new(cursor, node.replaced.start()).expect("outermost nodes are ordered"),
        );
        let splices = node.register(&mut generated, None);
        print_with_map(&node.output, authored, node.id, &splices, &mut generated).map_err(
            |error| {
                vec![ExpandDiagnostic {
                    code: Some(PRINT),
                    message: error.to_string(),
                    class: MappingClass::InvocationLevel,
                    authored: Some(node.call_site),
                    invocation: Some(node.id),
                }]
            },
        )?;
        cursor = node.replaced.end();
    }
    generated.copy_authored(
        authored,
        ByteRange::new(cursor, request.source.len()).expect("remaining source range is ordered"),
    );
    let facade = quote::ToTokens::to_token_stream(&request.facade_path)
        .to_string()
        .replace(' ', "");
    generated.push_generated(&registration_table(
        &facade,
        requests_framework,
        registrations,
    ));
    Ok(generated)
}

/// Renders the crate-root explicit descriptor registration table.
///
/// Each factory is listed once, sorted by path, under the `#[cfg]`
/// attributes of its registration; `#[cfg]` on statements is stable.
#[must_use]
pub fn registration_table(
    facade: &str,
    requests_framework: bool,
    registrations: &[Registration],
) -> String {
    let mut entries = registrations
        .iter()
        .map(|registration| {
            let mut path = String::from("crate::");
            for module in registration.module_path.iter().skip(1) {
                path.push_str(module);
                path.push_str("::");
            }
            path.push_str(&registration.factory);
            (path, registration.cfg.clone())
        })
        .collect::<Vec<_>>();
    entries.sort();
    entries.dedup();
    let mut table = format!(
        "\n// @generated by krs-expand: explicit descriptor registration table.\n\
         #[doc(hidden)]\n\
         pub static {REGISTRATION_TABLE}: {facade}::__private::RegistrationTable =\n    \
         {facade}::__private::RegistrationTable {{\n        \
         manifest_dir: ::core::env!(\"CARGO_MANIFEST_DIR\"),\n        \
         requests_framework: {requests_framework},\n        \
         register: __krs_register_descriptors,\n    \
         }};\n\n\
         #[doc(hidden)]\n\
         fn __krs_register_descriptors(registrar: &mut {facade}::__private::Registrar) {{\n"
    );
    if entries.is_empty() {
        table.push_str("    let _ = registrar;\n");
    }
    for (path, cfg) in entries {
        table.push_str("    ");
        for attribute in cfg {
            table.push_str(&attribute);
            table.push(' ');
        }
        table.push_str("registrar.factory(");
        table.push_str(&path);
        table.push_str(");\n");
    }
    table.push_str("}\n");
    table
}

/// A byte order mark or a shebang line, which rustc strips before lexing.
fn unsupported_prefix(source: &str) -> Option<ExpandDiagnostic> {
    if source.starts_with('\u{feff}') {
        return Some(ExpandDiagnostic::exact(
            UNSUPPORTED_SOURCE,
            "the authored file starts with a byte order mark; save it as UTF-8 without one"
                .to_owned(),
            ByteRange::prefix(3),
        ));
    }
    let rest = source.strip_prefix("#!")?;
    if rest.trim_start().starts_with('[') {
        return None;
    }
    let end = source.find('\n').unwrap_or(source.len());
    Some(ExpandDiagnostic::exact(
        UNSUPPORTED_SOURCE,
        "a lesson file cannot start with a shebang line".to_owned(),
        ByteRange::prefix(end),
    ))
}

/// Where an invocation's output lands.
#[derive(Clone, Debug)]
enum Scope {
    /// Module level, in the inline modules listed (empty: the file's module).
    Module(Vec<String>),
    /// Inside an `impl`, `trait`, function body, block, or macro input.
    Nested,
}

/// One discovered outermost invocation.
struct Found {
    entry: Entry,
    call_site: Span,
    replaced: ByteRange,
    attributes: TokenStream,
    input: TokenStream,
    scope: Scope,
}

struct Discovery<'a> {
    alias: &'a str,
    authored: &'a AuthoredFile,
    root: &'a TokenStream,
    scope: Scope,
    found: Vec<Found>,
    diagnostics: Vec<ExpandDiagnostic>,
}

impl Discovery<'_> {
    fn range(&self, span: Span) -> ByteRange {
        self.authored
            .byte_range(span)
            .expect("discovered nodes come from the authored tokens")
    }

    /// Records a function-like KRS invocation, or scans another macro's
    /// tokens for KRS invocations. Returns whether `mac` is a KRS invocation.
    fn visit_mac(&mut self, mac: &Macro, replaced: Option<ByteRange>) -> bool {
        let Some(Entry::Function(entry)) = surface::resolve(&mac.path, self.alias) else {
            self.scan_tokens(&mac.tokens);
            return false;
        };
        let call_site = mac.span();
        let replaced = replaced.unwrap_or_else(|| self.range(call_site));
        self.found.push(Found {
            entry: Entry::Function(entry),
            call_site,
            replaced,
            attributes: TokenStream::new(),
            input: mac.tokens.clone(),
            scope: self.scope.clone(),
        });
        true
    }

    /// Finds KRS function-like invocations in the token trees of a macro
    /// that is not a KRS macro; rustc reaches them when that macro re-emits
    /// its input.
    fn scan_tokens(&mut self, tokens: &TokenStream) {
        let trees = tokens.clone().into_iter().collect::<Vec<_>>();
        let mut index = 0;
        while index < trees.len() {
            if let Some(call) = function_call(&trees, index, self.alias, None) {
                let call_site = trees[index]
                    .span()
                    .join(call.group.span())
                    .expect("authored tokens share one fallback file");
                self.found.push(Found {
                    entry: Entry::Function(call.entry),
                    call_site,
                    replaced: self.range(call_site),
                    attributes: TokenStream::new(),
                    input: call.group.stream(),
                    scope: Scope::Nested,
                });
                index += call.len;
                continue;
            }
            if let TokenTree::Group(group) = &trees[index] {
                self.scan_tokens(&group.stream());
            }
            index += 1;
        }
    }

    /// Records the attribute invocation of an item, impl item, or trait
    /// item, if any. Returns whether the node is a KRS invocation (or an
    /// invalid one), in which case its contents are not visited.
    fn visit_attributes(&mut self, attrs: &[Attribute], node: Span) -> bool {
        let krs = attrs
            .iter()
            .position(|attribute| surface::facade_member(attribute.path(), self.alias).is_some());
        let Some(krs) = krs else {
            return false;
        };
        let first = attrs
            .iter()
            .position(|attribute| !surface::is_inert(attribute.path()))
            .expect("a facade attribute is not inert");
        let attribute = &attrs[first];
        let call_site = attribute.span();
        let Some(name) = surface::facade_member(attribute.path(), self.alias) else {
            let name = quote::ToTokens::to_token_stream(attribute.path())
                .to_string()
                .replace(' ', "");
            self.diagnostics.push(ExpandDiagnostic::exact(
                ATTRIBUTE_ORDER,
                format!(
                    "`#[{name}]` precedes a KRS attribute; the KRS attribute must come before every attribute that is not inert"
                ),
                self.range(attrs[krs].span()),
            ));
            return true;
        };
        let Some(Entry::Attribute(entry)) = Entry::from_name(&name) else {
            self.diagnostics.push(ExpandDiagnostic::exact(
                NOT_AN_ATTRIBUTE_MACRO,
                format!("`{}::{name}` is not a KRS attribute macro", self.alias),
                self.range(attribute.path().span()),
            ));
            return true;
        };
        let attributes = match &attribute.meta {
            Meta::Path(_) => TokenStream::new(),
            Meta::List(list) => list.tokens.clone(),
            Meta::NameValue(_) => {
                self.diagnostics.push(ExpandDiagnostic::exact(
                    ATTRIBUTE_FORM,
                    "key-value macro attributes are not supported".to_owned(),
                    self.range(call_site),
                ));
                return true;
            }
        };
        let replaced = self.range(node);
        let input = slice_trees(self.root, self.authored, &replaced, &self.range(call_site))
            .expect("an item consists of authored token trees");
        self.found.push(Found {
            entry: Entry::Attribute(entry),
            call_site,
            replaced,
            attributes,
            input,
            scope: self.scope.clone(),
        });
        true
    }

    fn nested<F: FnOnce(&mut Self)>(&mut self, visit: F) {
        let saved = std::mem::replace(&mut self.scope, Scope::Nested);
        visit(self);
        self.scope = saved;
    }
}

impl<'ast> Visit<'ast> for Discovery<'_> {
    fn visit_item(&mut self, item: &'ast Item) {
        if let Item::Macro(node) = item
            && self.visit_mac(&node.mac, Some(self.range(item.span())))
        {
            return;
        }
        if item_attributes(item).is_some_and(|attrs| self.visit_attributes(attrs, item.span())) {
            return;
        }
        match item {
            Item::Mod(module) => {
                let saved = self.scope.clone();
                if let Scope::Module(modules) = &mut self.scope {
                    modules.push(module.ident.to_string());
                }
                visit::visit_item_mod(self, module);
                self.scope = saved;
            }
            Item::Macro(_) => {}
            _ => self.nested(|this| visit::visit_item(this, item)),
        }
    }

    fn visit_impl_item(&mut self, item: &'ast ImplItem) {
        let attrs = match item {
            ImplItem::Const(item) => &item.attrs,
            ImplItem::Fn(item) => &item.attrs,
            ImplItem::Type(item) => &item.attrs,
            ImplItem::Macro(node) => {
                if !self.visit_mac(&node.mac, Some(self.range(item.span()))) {
                    self.visit_attributes(&node.attrs, item.span());
                }
                return;
            }
            _ => return visit::visit_impl_item(self, item),
        };
        if !self.visit_attributes(attrs, item.span()) {
            self.nested(|this| visit::visit_impl_item(this, item));
        }
    }

    fn visit_trait_item(&mut self, item: &'ast TraitItem) {
        let attrs = match item {
            TraitItem::Const(item) => &item.attrs,
            TraitItem::Fn(item) => &item.attrs,
            TraitItem::Type(item) => &item.attrs,
            TraitItem::Macro(node) => {
                if !self.visit_mac(&node.mac, Some(self.range(item.span()))) {
                    self.visit_attributes(&node.attrs, item.span());
                }
                return;
            }
            _ => return visit::visit_trait_item(self, item),
        };
        if !self.visit_attributes(attrs, item.span()) {
            self.nested(|this| visit::visit_trait_item(this, item));
        }
    }

    fn visit_macro(&mut self, mac: &'ast Macro) {
        self.visit_mac(mac, None);
    }

    fn visit_block(&mut self, block: &'ast syn::Block) {
        self.nested(|this| visit::visit_block(this, block));
    }
}

fn item_attributes(item: &Item) -> Option<&[Attribute]> {
    Some(match item {
        Item::Const(item) => &item.attrs,
        Item::Enum(item) => &item.attrs,
        Item::ExternCrate(item) => &item.attrs,
        Item::Fn(item) => &item.attrs,
        Item::ForeignMod(item) => &item.attrs,
        Item::Impl(item) => &item.attrs,
        Item::Macro(item) => &item.attrs,
        Item::Mod(item) => &item.attrs,
        Item::Static(item) => &item.attrs,
        Item::Struct(item) => &item.attrs,
        Item::Trait(item) => &item.attrs,
        Item::TraitAlias(item) => &item.attrs,
        Item::Type(item) => &item.attrs,
        Item::Union(item) => &item.attrs,
        Item::Use(item) => &item.attrs,
        _ => return None,
    })
}

/// The token trees of `stream` that lie inside `range`, without those inside
/// `exclude`, taken from the innermost group that contains `range`.
fn slice_trees(
    stream: &TokenStream,
    authored: &AuthoredFile,
    range: &ByteRange,
    exclude: &ByteRange,
) -> Option<TokenStream> {
    let mut output = TokenStream::new();
    let mut any = false;
    for tree in stream.clone() {
        let Some(tree_range) = authored.byte_range(tree.span()) else {
            continue;
        };
        if range.start() <= tree_range.start() && tree_range.end() <= range.end() {
            any = true;
            if !(exclude.start() <= tree_range.start() && tree_range.end() <= exclude.end()) {
                output.extend([tree]);
            }
        } else if let TokenTree::Group(group) = &tree
            && tree_range.start() <= range.start()
            && range.end() <= tree_range.end()
        {
            return slice_trees(&group.stream(), authored, range, exclude);
        }
    }
    any.then_some(output)
}

/// Keeps the selected invocations, reporting each selection that matches
/// none.
fn select(
    found: Vec<Found>,
    selection: &Selection,
    diagnostics: &mut Vec<ExpandDiagnostic>,
) -> Vec<Found> {
    let Selection::Invocations(selected) = selection else {
        return found;
    };
    for selected in selected {
        if !found
            .iter()
            .any(|found| found.entry.name() == selected.kind && found.replaced == selected.replaced)
        {
            diagnostics.push(ExpandDiagnostic {
                code: Some(SELECTION),
                message: format!(
                    "no outermost `{}` invocation replaces bytes {}..{}",
                    selected.kind,
                    selected.replaced.start(),
                    selected.replaced.end()
                ),
                class: MappingClass::Unmappable,
                authored: None,
                invocation: None,
            });
        }
    }
    found
        .into_iter()
        .filter(|found| {
            selected.iter().any(|selected| {
                found.entry.name() == selected.kind && found.replaced == selected.replaced
            })
        })
        .collect()
}

/// A function-like facade macro invocation in a token sequence.
struct FunctionCall {
    entry: FunctionMacro,
    /// Number of token trees from the path through the group.
    len: usize,
    group: proc_macro2::Group,
}

fn is_punct(tree: Option<&TokenTree>, ch: char) -> bool {
    matches!(tree, Some(TokenTree::Punct(punct)) if punct.as_char() == ch)
}

fn is_joint_colon(tree: Option<&TokenTree>) -> bool {
    matches!(tree, Some(TokenTree::Punct(punct)) if punct.as_char() == ':' && punct.spacing() == Spacing::Joint)
}

/// The path starting at `trees[index]` (with an optional leading `::`) and
/// the number of trees it occupies.
fn path_at(trees: &[TokenTree], index: usize) -> Option<(Path, usize)> {
    if index > 0 && is_punct(trees.get(index - 1), ':') {
        return None;
    }
    let mut at = index;
    let leading = is_joint_colon(trees.get(at)) && is_punct(trees.get(at + 1), ':');
    if leading {
        at += 2;
    }
    let mut path = Path {
        leading_colon: leading.then(Default::default),
        segments: syn::punctuated::Punctuated::new(),
    };
    loop {
        let Some(TokenTree::Ident(ident)) = trees.get(at) else {
            return None;
        };
        path.segments.push(PathSegment::from(ident.clone()));
        at += 1;
        if is_joint_colon(trees.get(at)) && is_punct(trees.get(at + 1), ':') {
            at += 2;
        } else {
            return Some((path, at - index));
        }
    }
}

/// The entry point that `path` invokes as `<alias>::<entry>` or, in
/// generated code, as `<facade>::<entry>`.
fn resolve(path: &Path, alias: &str, facade: Option<&Path>) -> Option<Entry> {
    surface::resolve(path, alias)
        .or_else(|| facade.and_then(|facade| surface::resolve_under(path, facade)))
}

fn function_call(
    trees: &[TokenTree],
    index: usize,
    alias: &str,
    facade: Option<&Path>,
) -> Option<FunctionCall> {
    let (path, len) = path_at(trees, index)?;
    let Entry::Function(entry) = resolve(&path, alias, facade)? else {
        return None;
    };
    if !is_punct(trees.get(index + len), '!') {
        return None;
    }
    let Some(TokenTree::Group(group)) = trees.get(index + len + 1) else {
        return None;
    };
    if group.delimiter() == Delimiter::None {
        return None;
    }
    Some(FunctionCall {
        entry,
        len: len + 2,
        group: group.clone(),
    })
}

/// The KRS attribute entry named by `#[...]` at `trees[index]`, if any.
fn attribute_call(
    trees: &[TokenTree],
    index: usize,
    alias: &str,
    facade: Option<&Path>,
) -> Option<AttributeMacro> {
    if !is_punct(trees.get(index), '#') {
        return None;
    }
    let Some(TokenTree::Group(group)) = trees.get(index + 1) else {
        return None;
    };
    if group.delimiter() != Delimiter::Bracket {
        return None;
    }
    let inner = group.stream().into_iter().collect::<Vec<_>>();
    let (path, _) = path_at(&inner, 0)?;
    match resolve(&path, alias, facade)? {
        Entry::Attribute(entry) => Some(entry),
        Entry::Function(_) => None,
    }
}

/// One invocation to expand.
struct Pending {
    entry: Entry,
    attributes: TokenStream,
    input: TokenStream,
    call_site: Span,
    replaced: ByteRange,
    parent: Option<(InvocationId, ByteRange)>,
    depth: usize,
}

/// One expanded invocation and the invocations nested in its output.
struct Node {
    id: InvocationId,
    kind: &'static str,
    call_site: ByteRange,
    replaced: ByteRange,
    parent: Option<InvocationId>,
    output: TokenStream,
    /// (position of the first replaced tree, number of replaced trees, node).
    nested: Vec<(Vec<usize>, usize, Node)>,
}

impl Node {
    /// The splices of this node's nested invocations, without recording
    /// them.
    fn splices(&self) -> Vec<Splice> {
        self.nested
            .iter()
            .map(|(at, len, node)| Splice {
                at: at.clone(),
                len: *len,
                owner: node.id,
                tokens: node.output.clone(),
                splices: node.splices(),
            })
            .collect()
    }

    fn collect(&self, expansions: &mut Vec<Expansion>) {
        expansions.push(Expansion {
            id: self.id,
            kind: self.kind,
            output: self.output.clone(),
        });
        for (_, _, node) in &self.nested {
            node.collect(expansions);
        }
    }

    /// Records this node and its nested invocations in pre-order, which is
    /// the order their ids were assigned, and returns the nested splices.
    fn register(
        &self,
        generated: &mut GeneratedSource,
        parent: Option<InvocationId>,
    ) -> Vec<Splice> {
        debug_assert_eq!(parent, self.parent);
        let id = generated.begin_invocation(self.kind, self.call_site, self.replaced, parent);
        assert_eq!(id, self.id, "invocations are recorded in expansion order");
        self.nested
            .iter()
            .map(|(at, len, node)| {
                let splices = node.register(generated, Some(id));
                Splice {
                    at: at.clone(),
                    len: *len,
                    owner: node.id,
                    tokens: node.output.clone(),
                    splices,
                }
            })
            .collect()
    }
}

struct Expander<'a> {
    env: &'a BrowserEnvironment<'a>,
    authored: &'a AuthoredFile,
    alias: &'a str,
    facade: &'a Path,
    next_id: usize,
    diagnostics: Vec<ExpandDiagnostic>,
}

impl Expander<'_> {
    /// Expands one invocation and, in turn, the invocations its output
    /// contains; ids are assigned in pre-order.
    fn expand(&mut self, call: Pending) -> Option<Node> {
        let id = InvocationId(self.next_id);
        self.next_id += 1;
        let call_site = self.authored.byte_range(call.call_site).unwrap_or_else(|| {
            call.parent
                .as_ref()
                .map(|(_, range)| *range)
                .expect("an outermost call site is authored")
        });
        if call.depth > RECURSION_LIMIT {
            self.diagnostics.push(ExpandDiagnostic {
                code: Some(RECURSION),
                message: format!(
                    "KRS invocations nest deeper than the recursion limit of {RECURSION_LIMIT}"
                ),
                class: MappingClass::InvocationLevel,
                authored: Some(call_site),
                invocation: Some(id),
            });
            return None;
        }
        self.env.set_call_site(call.call_site);
        let result = match call.entry {
            Entry::Attribute(entry) => {
                crate::expand_attribute(entry, self.env, call.attributes, call.input)
            }
            Entry::Function(entry) => crate::expand_function(entry, self.env, call.input),
        };
        let output = match result {
            Ok(output) => output,
            Err(error) => {
                for error in error {
                    let authored = self
                        .authored
                        .byte_range(error.span())
                        .filter(|range| !range.is_empty());
                    self.diagnostics.push(ExpandDiagnostic {
                        code: None,
                        message: error.to_string(),
                        class: if authored.is_some() {
                            MappingClass::ExactAuthored
                        } else {
                            MappingClass::InvocationLevel
                        },
                        authored: authored.or(Some(call_site)),
                        invocation: Some(id),
                    });
                }
                return None;
            }
        };

        let mut calls = Vec::new();
        self.rescan(&output, &mut Vec::new(), &mut calls, id, &call_site);
        let mut nested = Vec::new();
        for (at, len, entry, group, first) in calls {
            let span = first
                .join(group.span())
                .filter(|span| self.authored.contains(*span))
                .unwrap_or(call.call_site);
            let range = self.authored.byte_range(span).unwrap_or(call_site);
            let node = self.expand(Pending {
                entry: Entry::Function(entry),
                attributes: TokenStream::new(),
                input: group.stream(),
                call_site: span,
                replaced: range,
                parent: Some((id, call_site)),
                depth: call.depth + 1,
            });
            if let Some(node) = node {
                nested.push((at, len, node));
            }
        }
        // Restore the call site for the parent's remaining work.
        self.env.set_call_site(call.call_site);
        Some(Node {
            id,
            kind: call.entry.name(),
            call_site,
            replaced: call.replaced,
            parent: call.parent.map(|(parent, _)| parent),
            output,
            nested,
        })
    }

    /// Finds the KRS invocations in an expansion's output: function-like
    /// invocations to expand, and attribute invocations to reject.
    fn rescan(
        &mut self,
        stream: &TokenStream,
        path: &mut Vec<usize>,
        calls: &mut Vec<(Vec<usize>, usize, FunctionMacro, proc_macro2::Group, Span)>,
        owner: InvocationId,
        call_site: &ByteRange,
    ) {
        let trees = stream.clone().into_iter().collect::<Vec<_>>();
        let mut index = 0;
        while index < trees.len() {
            if let Some(call) = function_call(&trees, index, self.alias, Some(self.facade)) {
                let mut at = path.clone();
                at.push(index);
                calls.push((at, call.len, call.entry, call.group, trees[index].span()));
                index += call.len;
                continue;
            }
            if let Some(entry) = attribute_call(&trees, index, self.alias, Some(self.facade)) {
                self.diagnostics.push(ExpandDiagnostic {
                    code: Some(NESTED_ATTRIBUTE),
                    message: format!(
                        "the expansion contains a `#[{}::{}]` invocation, which the browser expander does not expand",
                        self.alias,
                        entry.name()
                    ),
                    class: MappingClass::InvocationLevel,
                    authored: Some(*call_site),
                    invocation: Some(owner),
                });
            }
            if let TokenTree::Group(group) = &trees[index] {
                path.push(index);
                self.rescan(&group.stream(), path, calls, owner, call_site);
                path.pop();
            }
            index += 1;
        }
    }
}

/// Collects `__register_host_descriptor!(factory)` sites as (group depth,
/// factory, `#[cfg]` attributes, span) and notes `__request_framework_sorts!`.
fn scan_registrations(
    stream: &TokenStream,
    depth: usize,
    found: &mut Vec<(usize, String, Vec<String>, Span)>,
    requests_framework: &mut bool,
) {
    let trees = stream.clone().into_iter().collect::<Vec<_>>();
    for (index, tree) in trees.iter().enumerate() {
        match tree {
            TokenTree::Ident(ident)
                if is_punct(trees.get(index + 1), '!')
                    && matches!(trees.get(index + 2), Some(TokenTree::Group(_))) =>
            {
                if ident == "__request_framework_sorts" {
                    *requests_framework = true;
                } else if ident == "__register_host_descriptor" {
                    let Some(TokenTree::Group(group)) = trees.get(index + 2) else {
                        continue;
                    };
                    let factory = group.stream().to_string().replace(' ', "");
                    let cfg = preceding_cfg(&trees, path_start(&trees, index));
                    found.push((depth, factory, cfg, ident.span()));
                }
            }
            TokenTree::Group(group) => {
                scan_registrations(&group.stream(), depth + 1, found, requests_framework);
            }
            _ => {}
        }
    }
}

/// The index of the first tree of the path ending at `trees[last]`.
fn path_start(trees: &[TokenTree], last: usize) -> usize {
    let mut start = last;
    while start >= 2 && is_punct(trees.get(start - 1), ':') && is_joint_colon(trees.get(start - 2))
    {
        if start >= 3 && matches!(trees.get(start - 3), Some(TokenTree::Ident(_))) {
            start -= 3;
        } else {
            start -= 2;
            break;
        }
    }
    start
}

/// The `#[cfg(...)]` attributes directly before `trees[start]`, in order.
fn preceding_cfg(trees: &[TokenTree], start: usize) -> Vec<String> {
    let mut cfg = Vec::new();
    let mut at = start;
    while at >= 2 {
        let (Some(TokenTree::Punct(pound)), Some(TokenTree::Group(group))) =
            (trees.get(at - 2), trees.get(at - 1))
        else {
            break;
        };
        if pound.as_char() != '#' || group.delimiter() != Delimiter::Bracket {
            break;
        }
        if matches!(group.stream().into_iter().next(), Some(TokenTree::Ident(ident)) if ident == "cfg")
        {
            cfg.push(format!("#[{}]", group.stream()));
        }
        at -= 2;
    }
    cfg.reverse();
    cfg
}

/// How a macro is used in [`macro_uses`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum MacroUseKind {
    /// `path!(...)`, in the syntax tree or in another macro's tokens.
    Bang,
    /// `#[path ...]` that is not inert.
    Attribute,
    /// A path inside `#[derive(...)]`.
    Derive,
}

/// One macro use found by [`macro_uses`].
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MacroUse {
    /// How the macro is used.
    pub kind: MacroUseKind,
    /// The macro path without spaces, such as `::k::__register_host_descriptor`.
    pub path: String,
}

/// Every macro use of a Rust file: bang macros in the syntax tree and in
/// macro token trees, non-inert attributes, and derive paths.
///
/// This is the check that expanded text invokes no KRS procedural macro: a
/// path whose last segment is a `krs-macros` entry point, a `rustversion`
/// path, or a Serde derive would be listed.
///
/// # Errors
///
/// Returns the parse error when `source` is not a Rust file.
pub fn macro_uses(source: &str) -> syn::Result<Vec<MacroUse>> {
    struct Uses(Vec<MacroUse>);

    fn text(path: &Path) -> String {
        quote::ToTokens::to_token_stream(path)
            .to_string()
            .replace(' ', "")
    }

    fn scan(tokens: &TokenStream, uses: &mut Vec<MacroUse>) {
        let trees = tokens.clone().into_iter().collect::<Vec<_>>();
        for index in 0..trees.len() {
            if let Some((path, len)) = path_at(&trees, index)
                && is_punct(trees.get(index + len), '!')
                && matches!(trees.get(index + len + 1), Some(TokenTree::Group(_)))
            {
                uses.push(MacroUse {
                    kind: MacroUseKind::Bang,
                    path: text(&path),
                });
            }
            if is_punct(trees.get(index), '#')
                && let Some(TokenTree::Group(group)) = trees.get(index + 1)
                && group.delimiter() == Delimiter::Bracket
                && let Ok(meta) = syn::parse2::<Meta>(group.stream())
            {
                let attribute = Attribute {
                    pound_token: syn::token::Pound::default(),
                    style: syn::AttrStyle::Outer,
                    bracket_token: syn::token::Bracket::default(),
                    meta,
                };
                Uses::attribute(&attribute, uses);
            }
            if let TokenTree::Group(group) = &trees[index] {
                scan(&group.stream(), uses);
            }
        }
    }

    impl Uses {
        fn attribute(attribute: &Attribute, uses: &mut Vec<MacroUse>) {
            if attribute.path().is_ident("derive") {
                if let Ok(paths) = attribute.parse_args_with(
                    syn::punctuated::Punctuated::<Path, syn::Token![,]>::parse_terminated,
                ) {
                    uses.extend(paths.iter().map(|path| MacroUse {
                        kind: MacroUseKind::Derive,
                        path: text(path),
                    }));
                }
            } else if !surface::is_inert(attribute.path()) {
                uses.push(MacroUse {
                    kind: MacroUseKind::Attribute,
                    path: text(attribute.path()),
                });
            }
            if let Meta::List(list) = &attribute.meta {
                scan(&list.tokens, uses);
            }
        }
    }

    impl<'ast> Visit<'ast> for Uses {
        fn visit_attribute(&mut self, attribute: &'ast Attribute) {
            Self::attribute(attribute, &mut self.0);
        }

        fn visit_macro(&mut self, mac: &'ast Macro) {
            self.0.push(MacroUse {
                kind: MacroUseKind::Bang,
                path: text(&mac.path),
            });
            scan(&mac.tokens, &mut self.0);
        }
    }

    let file = syn::parse_file(source)?;
    let mut uses = Uses(Vec::new());
    uses.visit_file(&file);
    Ok(uses.0)
}
