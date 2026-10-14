//! Whole-file expansion of one authored KRS source file.
//!
//! [`expand_file`] turns an authored file into Rust that rustc compiles
//! without invoking a KRS procedural macro:
//!
//! 1. The file is lexed once ([`AuthoredFile::lex`]) and parsed from those
//!    tokens, so every authored span locates exact authored bytes.
//! 2. [`surface::invocations`] discovers the KRS invocations in the syntax tree and in other macros' token trees.
//!    This driver expands the outermost invocations, which rustc reaches after the surrounding macro re-emits its input.
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

use krs_diagnostic::{Code, Diagnostic, Location, ToDiagnostic};
use krs_syntax::surface::{self, Entry, InvocationKind, Scope, TokenCallKind};
use proc_macro2::{Span, TokenStream, TokenTree};
use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::{Attribute, Macro, Meta, Path};

use crate::browser_env::BrowserEnvironment;
use crate::sink::{
    AuthoredFile, ByteRange, GeneratedSource, InvocationId, MappingClass, Splice, print_with_map,
    splice_tokens,
};

/// Maximum nesting depth of rescanned invocations: rustc's default
/// `recursion_limit`.
pub const RECURSION_LIMIT: usize = 128;

pub use krs_diagnostic::codes::expand::{
    ATTRIBUTE_FORM, ATTRIBUTE_ORDER, NESTED_ATTRIBUTE, NOT_AN_ATTRIBUTE_MACRO, PARSE, PRINT,
    RECURSION, REGISTRATION_SCOPE, SELECTION, UNSUPPORTED_SOURCE,
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
    /// The authored file's path relative to the package manifest directory,
    /// for example `src/lib.rs`; it enters expansion nonces, which rustc
    /// hashes with the same package-relative path
    /// ([`crate::MacroEnvironment::span_package_file`]), and
    /// `HostProvenance`.
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
    /// The producer's registered diagnostic code.
    pub code: Code,
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
    /// Builds the whole-file view from a shared diagnostic and mapping context.
    #[must_use]
    pub fn from_diagnostic(
        diagnostic: Diagnostic,
        class: MappingClass,
        authored: Option<ByteRange>,
        invocation: Option<InvocationId>,
    ) -> Self {
        Self {
            code: diagnostic.code,
            message: diagnostic.message,
            class,
            authored,
            invocation,
        }
    }

    fn located(
        code: Code,
        message: String,
        class: MappingClass,
        authored: Option<ByteRange>,
        invocation: Option<InvocationId>,
    ) -> Self {
        Self::from_diagnostic(
            Diagnostic::error(
                code,
                message,
                authored.map_or(Location::None, Location::Range),
            ),
            class,
            authored,
            invocation,
        )
    }

    fn exact(code: Code, message: String, authored: ByteRange) -> Self {
        Self::located(
            code,
            message,
            MappingClass::ExactAuthored,
            Some(authored),
            None,
        )
    }

    fn unmappable(code: Code, message: String) -> Self {
        Self::located(code, message, MappingClass::Unmappable, None, None)
    }
}

impl ToDiagnostic for ExpandDiagnostic {
    fn to_diagnostic(&self) -> Diagnostic {
        Diagnostic::error(
            self.code.clone(),
            self.message.clone(),
            self.authored.map_or(Location::None, Location::Range),
        )
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
                ExpandDiagnostic::located(
                    PARSE,
                    error.to_string(),
                    if range.is_some() {
                        MappingClass::ExactAuthored
                    } else {
                        MappingClass::Unmappable
                    },
                    range,
                    None,
                )
            })
            .collect::<Vec<_>>()
    })?;

    let resolve = surface::AuthoredResolver::new(request.facade_alias);
    let mut diagnostics = Vec::new();
    let mut found = surface::invocations(&file, &resolve)
        .into_iter()
        .filter(|invocation| invocation.parent.is_none())
        .filter_map(|invocation| {
            found_invocation(
                invocation,
                request.facade_alias,
                &authored,
                &tokens,
                &mut diagnostics,
            )
        })
        .collect::<Vec<_>>();
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
                diagnostics.push(ExpandDiagnostic::located(
                    REGISTRATION_SCOPE,
                    format!(
                        "descriptor factory `{factory}` is not defined at the crate root, so the crate-root registration table cannot name it"
                    ),
                    MappingClass::InvocationLevel,
                    authored
                        .byte_range(span)
                        .filter(|range| !range.is_empty())
                        .or(Some(node.call_site)),
                    Some(node.id),
                ));
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
                vec![ExpandDiagnostic::located(
                    PRINT,
                    error.to_string(),
                    MappingClass::InvocationLevel,
                    Some(node.call_site),
                    Some(node.id),
                )]
            },
        )?;
        cursor = node.replaced.end();
    }
    generated.copy_authored(
        authored,
        ByteRange::new(cursor, request.source.len()).expect("remaining source range is ordered"),
    );
    let facade = path_spelling(&request.facade_path);
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

/// One discovered outermost invocation.
struct Found {
    entry: Entry,
    call_site: Span,
    replaced: ByteRange,
    attributes: TokenStream,
    input: TokenStream,
    scope: Scope,
}

fn found_invocation(
    invocation: surface::Invocation<'_>,
    alias: &str,
    authored: &AuthoredFile,
    root: &TokenStream,
    diagnostics: &mut Vec<ExpandDiagnostic>,
) -> Option<Found> {
    let range = |span| {
        authored
            .byte_range(span)
            .expect("discovered nodes come from the authored tokens")
    };
    let (entry, attributes, input) = match invocation.kind {
        InvocationKind::Function { entry, tokens, .. } => {
            (Entry::Function(entry), TokenStream::new(), tokens)
        }
        InvocationKind::Attribute(attribute) => {
            let attrs = attribute.attributes;
            let first = &attrs[attribute.first_expandable_index];
            if attribute.facade_index != attribute.first_expandable_index {
                let name = path_spelling(first.path());
                diagnostics.push(ExpandDiagnostic::exact(
                    ATTRIBUTE_ORDER,
                    format!(
                        "`#[{name}]` precedes a KRS attribute; the KRS attribute must come before every attribute that is not inert"
                    ),
                    range(attrs[attribute.facade_index].span()),
                ));
                return None;
            }
            let Some(Entry::Attribute(entry)) = attribute.entry else {
                diagnostics.push(ExpandDiagnostic::exact(
                    NOT_AN_ATTRIBUTE_MACRO,
                    format!(
                        "`{alias}::{}` is not a KRS attribute macro",
                        attribute.member
                    ),
                    range(first.path().span()),
                ));
                return None;
            };
            let attributes = match &first.meta {
                Meta::Path(_) => TokenStream::new(),
                Meta::List(list) => list.tokens.clone(),
                Meta::NameValue(_) => {
                    diagnostics.push(ExpandDiagnostic::exact(
                        ATTRIBUTE_FORM,
                        "key-value macro attributes are not supported".to_owned(),
                        range(first.span()),
                    ));
                    return None;
                }
            };
            let input = slice_trees(
                root,
                authored,
                &range(invocation.replaced),
                &range(first.span()),
            )
            .expect("an item consists of authored token trees");
            (Entry::Attribute(entry), attributes, input)
        }
        InvocationKind::RawAttribute(_) => return None,
    };
    Some(Found {
        entry,
        call_site: invocation.call_site,
        replaced: range(invocation.replaced),
        attributes,
        input,
        scope: invocation.scope,
    })
}

/// Spells ordinary paths through the shared surface representation.
fn path_spelling(path: &Path) -> String {
    if path
        .segments
        .iter()
        .all(|segment| segment.arguments.is_empty())
    {
        surface::path_text(path)
    } else {
        quote::ToTokens::to_token_stream(path)
            .to_string()
            .replace(' ', "")
    }
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
            diagnostics.push(ExpandDiagnostic::located(
                SELECTION,
                format!(
                    "no outermost `{}` invocation replaces bytes {}..{}",
                    selected.kind,
                    selected.replaced.start(),
                    selected.replaced.end()
                ),
                MappingClass::Unmappable,
                None,
                None,
            ));
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
    fn check_nested_attributes(
        &mut self,
        calls: &[surface::TokenCall],
        call_site: ByteRange,
        id: InvocationId,
    ) {
        for token_call in calls {
            if let Entry::Attribute(entry) = token_call.entry {
                self.diagnostics.push(ExpandDiagnostic::located(
                    NESTED_ATTRIBUTE,
                    format!(
                        "the expansion contains a `#[{}::{}]` invocation, which the browser expander does not expand",
                        self.alias,
                        entry.name()
                    ),
                    MappingClass::InvocationLevel,
                    Some(call_site),
                    Some(id),
                ));
            }
        }
    }

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
            self.diagnostics.push(ExpandDiagnostic::located(
                RECURSION,
                format!(
                    "KRS invocations nest deeper than the recursion limit of {RECURSION_LIMIT}"
                ),
                MappingClass::InvocationLevel,
                Some(call_site),
                Some(id),
            ));
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
                for diagnostic in error.into_diagnostics() {
                    let authored = match diagnostic.primary.location {
                        Location::Span(span) => self.authored.byte_range(span),
                        Location::Range(range) => Some(range),
                        _ => None,
                    }
                    .filter(|range| !range.is_empty());
                    self.diagnostics.push(ExpandDiagnostic::from_diagnostic(
                        diagnostic,
                        if authored.is_some() {
                            MappingClass::ExactAuthored
                        } else {
                            MappingClass::InvocationLevel
                        },
                        authored.or(Some(call_site)),
                        Some(id),
                    ));
                }
                return None;
            }
        };

        let resolve = surface::GeneratedResolver::new(self.alias, self.facade);
        let calls = surface::token_calls(&output, &resolve);
        self.check_nested_attributes(&calls, call_site, id);
        let mut nested = Vec::new();
        for token_call in calls {
            let (Entry::Function(entry), TokenCallKind::Function(group)) =
                (token_call.entry, token_call.kind)
            else {
                continue;
            };
            let span = token_call
                .span
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
                nested.push((token_call.at, token_call.len, node));
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
}

/// Collects `__register_host_descriptor!(factory)` sites as (group depth,
/// factory, `#[cfg]` attributes, span) and notes `__request_framework_sorts!`.
/// Macro calls and attributes are recognized by the shared token-tree rules;
/// these hidden macros are matched by their last path segment because they occur only in generated output.
fn scan_registrations(
    stream: &TokenStream,
    depth: usize,
    found: &mut Vec<(usize, String, Vec<String>, Span)>,
    requests_framework: &mut bool,
) {
    let trees = stream.clone().into_iter().collect::<Vec<_>>();
    let mut index = 0;
    while index < trees.len() {
        if let Some(call) = surface::macro_call(&trees, index) {
            let name = &call
                .path
                .segments
                .last()
                .expect("a path has a segment")
                .ident;
            if name == "__request_framework_sorts" {
                *requests_framework = true;
            } else if name == "__register_host_descriptor" {
                let factory = call.group.stream().to_string().replace(' ', "");
                found.push((depth, factory, preceding_cfg(&trees, index), name.span()));
            }
            scan_registrations(&call.group.stream(), depth + 1, found, requests_framework);
            index += call.len;
            continue;
        }
        if let TokenTree::Group(group) = &trees[index] {
            scan_registrations(&group.stream(), depth + 1, found, requests_framework);
        }
        index += 1;
    }
}

/// The `#[cfg(...)]` attributes directly before `trees[start]`, in order.
fn preceding_cfg(trees: &[TokenTree], start: usize) -> Vec<String> {
    let mut cfg = Vec::new();
    let mut at = start;
    while let Some(attribute) = at
        .checked_sub(2)
        .and_then(|index| surface::attribute_call(trees, index))
        .filter(|attribute| attribute.len == 2)
    {
        let stream = attribute.group.stream();
        if matches!(stream.clone().into_iter().next(), Some(TokenTree::Ident(ident)) if ident == "cfg")
        {
            cfg.push(format!("#[{stream}]"));
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

    fn scan(tokens: &TokenStream, uses: &mut Vec<MacroUse>) {
        let trees = tokens.clone().into_iter().collect::<Vec<_>>();
        for index in 0..trees.len() {
            if let Some(call) = surface::macro_call(&trees, index) {
                uses.push(MacroUse {
                    kind: MacroUseKind::Bang,
                    path: path_spelling(&call.path),
                });
            }
            if let Some(call) = surface::attribute_call(&trees, index)
                && let Ok(meta) = syn::parse2::<Meta>(call.group.stream())
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
                        path: path_spelling(path),
                    }));
                }
            } else if !surface::is_inert(attribute.path()) {
                uses.push(MacroUse {
                    kind: MacroUseKind::Attribute,
                    path: path_spelling(attribute.path()),
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
                path: path_spelling(&mac.path),
            });
            scan(&mac.tokens, &mut self.0);
        }
    }

    let file = syn::parse_file(source)?;
    let mut uses = Uses(Vec::new());
    uses.visit_file(&file);
    Ok(uses.0)
}

#[cfg(test)]
mod tests {
    use super::{MacroUse, MacroUseKind, macro_uses, scan_registrations};

    #[test]
    fn registrations_keep_preceding_cfg_attributes_and_group_depth() {
        let tokens: proc_macro2::TokenStream = syn::parse_str(
            "#[cfg(a)] #[doc = \"x\"] #[cfg(b)] ::k::__register_host_descriptor!(f); \
             const _: () = { k::__register_host_descriptor!(g) }; \
             other! { k::__request_framework_sorts!() }",
        )
        .unwrap();
        let mut found = Vec::new();
        let mut requests_framework = false;
        scan_registrations(&tokens, 0, &mut found, &mut requests_framework);
        assert!(requests_framework);
        assert_eq!(
            found
                .into_iter()
                .map(|(depth, factory, cfg, _)| (depth, factory, cfg))
                .collect::<Vec<_>>(),
            [
                (
                    0,
                    "f".to_owned(),
                    vec!["#[cfg (a)]".to_owned(), "#[cfg (b)]".to_owned()]
                ),
                (1, "g".to_owned(), Vec::new()),
            ]
        );
    }

    #[test]
    fn macro_uses_finds_outer_and_inner_attributes_in_macro_tokens() {
        let uses = macro_uses("other! { #[k::sort] #![k::rules] #[doc = \"inert\"] }").unwrap();
        assert_eq!(
            uses,
            [
                (MacroUseKind::Bang, "other"),
                (MacroUseKind::Attribute, "k::sort"),
                (MacroUseKind::Attribute, "k::rules"),
            ]
            .map(|(kind, path)| MacroUse {
                kind,
                path: path.to_owned(),
            })
        );
    }

    #[test]
    fn macro_uses_shares_token_path_rules() {
        let uses = macro_uses(
            "outer! { if !(x) match !(x) return !(x) x: k::id!(x) foo::k::id!(x) ::r#k::r#id!(x) }",
        )
        .unwrap();
        assert_eq!(
            uses,
            ["outer", "k::id", "foo::k::id", "::r#k::r#id"].map(|path| MacroUse {
                kind: MacroUseKind::Bang,
                path: path.to_owned(),
            })
        );
    }

    #[test]
    fn macro_uses_preserves_generic_path_spelling() {
        let uses = macro_uses("#[derive(Some::<u8>)] struct Example;").unwrap();
        assert_eq!(
            uses,
            vec![MacroUse {
                kind: MacroUseKind::Derive,
                path: "Some::<u8>".to_owned(),
            }]
        );
    }
}
