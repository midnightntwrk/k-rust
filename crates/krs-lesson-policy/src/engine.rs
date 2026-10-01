//! The syntactic checker of the lesson policy.
//!
//! The normative rules and the lesson allowlists are in [`crate::rules`];
//! entry points, helpers, and inert attributes come from
//! [`krs_syntax::surface`], and every KRS path is resolved by its resolver.

use krs_diagnostic::Code;
use krs_syntax::SourceRange as ByteRange;
use krs_syntax::surface::{self, AttributeMacro, Entry, FunctionMacro};
use proc_macro2::{Delimiter, Span, TokenStream, TokenTree};
use syn::ext::IdentExt;
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::{
    Attribute, FnArg, ForeignItem, Ident, ImplItem, Item, ItemEnum, ItemExternCrate, ItemMacro,
    ItemMod, ItemStruct, ItemUse, Macro, Meta, Path, PathSegment, TraitItem, UseTree, Variant,
};

use crate::rules::{
    ATTRIBUTE_ORDER, BUILTIN_DERIVES, CFG, DERIVE_CRATES, ENV, EXTERN_CRATE, INCLUDE,
    INERT_ATTRIBUTES, KRS_IMPORT, KRS_ITEM_SCOPE, MACRO_DEFINITION, NON_KRS_PROC_MACRO,
    ORDER_SENSITIVE_ATTRIBUTES, OUT_OF_LINE_MODULE, PARSE, PATH_ATTRIBUTE, RESERVED_FACADE_ITEM,
    RESERVED_NAME, RESERVED_NAME_PREFIX, STANDARD_MACRO_CRATES, STANDARD_MACROS, TOOL_ATTRIBUTES,
    VARIANT_ATTRIBUTES,
};
use crate::{LessonPolicy, PolicyDiagnostic};

const INCLUDE_MACROS: &[&str] = &["include", "include_str", "include_bytes"];
const ENV_MACROS: &[&str] = &["env", "option_env"];

/// Checks one authored file.
pub(crate) fn check(
    source: &str,
    display_file: &str,
    policy: &LessonPolicy,
) -> Vec<PolicyDiagnostic> {
    let bom = if source.starts_with('\u{feff}') { 3 } else { 0 };
    let parsed = syn::parse_file(source);
    let offset = match &parsed {
        Ok(file) => bom + file.shebang.as_ref().map_or(0, String::len),
        Err(_) => bom + shebang_len(&source[bom..]),
    };
    let mut checker = Checker {
        offset,
        file: display_file,
        policy,
        diagnostics: Vec::new(),
        contexts: Vec::new(),
        module_path: Vec::new(),
        module_scope: usize::from(!is_crate_root(display_file)),
        block_scope: 0,
        item_position: false,
        krs_depth: 0,
        helpers: PendingHelpers::default(),
    };
    match &parsed {
        Ok(file) => checker.visit_file(file),
        Err(error) => {
            let range = checker.range(error.span());
            checker.report(
                PARSE,
                format!("the lesson source does not parse: {error}"),
                range,
            );
        }
    }
    let mut diagnostics = checker.diagnostics;
    diagnostics.sort_by(|left, right| {
        let key = |diagnostic: &PolicyDiagnostic| {
            diagnostic
                .authored
                .as_ref()
                .map(|range| (range.start(), range.end()))
        };
        key(left).cmp(&key(right)).then(left.code.cmp(&right.code))
    });
    diagnostics.dedup();
    diagnostics
}

/// Mirrors `syn::parse_file`'s shebang rule for the parse-error path.
fn shebang_len(content: &str) -> usize {
    if content.starts_with("#!") && !content[2..].trim_start().starts_with('[') {
        content.find('\n').unwrap_or(content.len())
    } else {
        0
    }
}

fn is_crate_root(display_file: &str) -> bool {
    matches!(display_file, "src/lib.rs" | "src/main.rs")
}

/// The directory, with a trailing `/` unless empty, that owns the child
/// modules of `display_file`.
fn module_directory(display_file: &str) -> String {
    let (parent, file) = display_file
        .rsplit_once('/')
        .map_or(("", display_file), |(parent, file)| (parent, file));
    let parent = if parent.is_empty() {
        String::new()
    } else {
        format!("{parent}/")
    };
    match file {
        "lib.rs" | "main.rs" | "mod.rs" => parent,
        other => format!("{parent}{}/", other.strip_suffix(".rs").unwrap_or(other)),
    }
}

/// Helpers that the next attributed child node of the current item accepts.
#[derive(Clone, Copy, Default)]
struct PendingHelpers {
    variant: &'static [&'static str],
    field: &'static [&'static str],
    parameter: &'static [&'static str],
}

/// The position of one attribute list.
struct AttributeContext<'ast> {
    attrs: &'ast [Attribute],
    /// KRS attribute entries are accepted (item, impl item, trait item).
    entries: bool,
    helpers: &'static [&'static str],
    /// Helpers are accepted only at this index and later.
    helpers_from: usize,
    /// The attributes of an enum variant.
    variant: bool,
}

/// How an attribute's position constrains it.
#[derive(Clone, Copy)]
enum Position {
    /// A position of the syntax tree with the given entry and helper sets.
    Tree {
        entries: bool,
        helpers: &'static [&'static str],
        variant: bool,
    },
    /// An attribute inside a macro's token trees.
    TokenBody,
}

enum MacroClass {
    Krs(FunctionMacro),
    Standard,
    Include,
    Env,
    Definition,
    Reserved,
    Unprefixed,
    Other,
}

struct Checker<'a, 'ast> {
    offset: usize,
    file: &'a str,
    policy: &'a LessonPolicy,
    diagnostics: Vec<PolicyDiagnostic>,
    contexts: Vec<AttributeContext<'ast>>,
    /// Inline modules between the file root and the current node.
    module_path: Vec<String>,
    /// Enclosing inline modules, plus one for a file that is not the crate
    /// root.
    module_scope: usize,
    /// Enclosing blocks that no KRS invocation consumes.
    block_scope: usize,
    /// The macro being checked is in item or statement position.
    item_position: bool,
    /// Enclosing KRS invocations.
    krs_depth: usize,
    helpers: PendingHelpers,
}

impl<'ast> Checker<'_, 'ast> {
    fn alias(&self) -> &str {
        &self.policy.facade_alias
    }

    fn range(&self, span: Span) -> ByteRange {
        ByteRange::from_proc_macro2(span)
            .ok()
            .and_then(|range| range.checked_shift(self.offset))
            .expect("span byte range and source offset are valid")
    }

    fn span_range(&self, first: Span, last: Span) -> ByteRange {
        self.range(first).cover(self.range(last))
    }

    fn report(&mut self, code: Code, message: String, range: ByteRange) {
        self.diagnostics
            .push(PolicyDiagnostic::authored(code, message, self.file, range));
    }

    /// `Some(name)` when `path` is exactly `<alias>::<name>`.
    fn facade_member(&self, path: &Path) -> Option<String> {
        surface::facade_member(path, self.alias())
    }

    /// The KRS attribute entry that `attribute` invokes, when its path is
    /// exactly `<alias>::<entry>` and the entry is not reserved.
    fn krs_attribute(&self, attribute: &Attribute) -> Option<AttributeMacro> {
        match surface::resolve(attribute.path(), self.alias()) {
            Some(Entry::Attribute(entry)) if !entry.is_reserved() => Some(entry),
            _ => None,
        }
    }

    fn names_reserved_facade_item(&self, segments: &[String]) -> bool {
        segments.first().is_some_and(|first| first == self.alias())
            && segments[1..]
                .iter()
                .any(|segment| segment.starts_with("__"))
    }

    fn has_krs_attribute(&self, attrs: &[Attribute], entries: &[AttributeMacro]) -> bool {
        attrs.iter().any(|attribute| {
            self.krs_attribute(attribute)
                .is_some_and(|entry| entries.contains(&entry))
        })
    }

    /// Records a KRS invocation and rejects it outside the crate root's
    /// module level. `item_position` is true for attribute invocations and
    /// for macros in item or statement position.
    fn krs_invocation(&mut self, name: &str, range: ByteRange, item_position: bool) {
        if self.krs_depth == 0 && (self.module_scope > 0 || (self.block_scope > 0 && item_position))
        {
            let alias = self.alias().to_owned();
            self.report(
                KRS_ITEM_SCOPE,
                format!(
                    "`{alias}::{name}` must be invoked at the module level of the crate root; \
                     explicit descriptor registration cannot name a factory defined in a nested \
                     module or block"
                ),
                range,
            );
        }
    }

    fn position_of(&self, attribute: &Attribute) -> Position {
        for context in self.contexts.iter().rev() {
            if let Some(index) = context
                .attrs
                .iter()
                .position(|candidate| std::ptr::eq(candidate, attribute))
            {
                let helpers = if index >= context.helpers_from {
                    context.helpers
                } else {
                    &[]
                };
                return Position::Tree {
                    entries: context.entries,
                    helpers,
                    variant: context.variant,
                };
            }
        }
        Position::Tree {
            entries: false,
            helpers: &[],
            variant: false,
        }
    }

    /// Checks an attribute whose path is the single segment `name`.
    fn check_single_segment_attribute(
        &mut self,
        attribute: &Attribute,
        name: &str,
        position: Position,
    ) {
        let attribute_range = self.range(attribute.span());
        let path_range = self.range(attribute.path().span());
        match name {
            "cfg" | "cfg_attr" => self.report(
                CFG,
                format!("`#[{name}]` is not accepted in lesson source"),
                attribute_range,
            ),
            "path" => self.report(
                PATH_ATTRIBUTE,
                "`#[path]` is not accepted in lesson source".to_owned(),
                attribute_range,
            ),
            "derive" => self.check_derive(attribute, path_range),
            name if INERT_ATTRIBUTES.contains(&name) => {}
            name if VARIANT_ATTRIBUTES.contains(&name) => {
                let on_variant = matches!(position, Position::Tree { variant: true, .. });
                if !on_variant || !matches!(attribute.meta, Meta::Path(_)) {
                    self.report(
                        NON_KRS_PROC_MACRO,
                        format!("`#[{name}]` is accepted only as a bare attribute on an enum variant"),
                        path_range,
                    );
                }
            }
            name if is_krs_entry_name(name) => {
                let alias = self.alias().to_owned();
                self.report(
                    KRS_IMPORT,
                    format!("KRS attribute `{name}` must be named `{alias}::{name}`"),
                    path_range,
                );
            }
            name => self.report(
                NON_KRS_PROC_MACRO,
                format!("attribute `{name}` is neither a KRS attribute nor an inert attribute accepted in lessons"),
                path_range,
            ),
        }
    }

    /// Checks one attribute; returns whether its arguments belong to a KRS
    /// renderer and must be scanned as token trees.
    fn check_attribute(&mut self, attribute: &Attribute, position: Position) -> bool {
        let path = attribute.path();
        let attribute_range = self.range(attribute.span());
        let path_range = self.range(path.span());
        if let Some(ident) = path.get_ident() {
            let name = ident.unraw().to_string();
            self.check_single_segment_attribute(attribute, &name, position);
            return false;
        }
        if let Some(name) = self.facade_member(path) {
            let alias = self.alias().to_owned();
            if name.starts_with("__") {
                self.report(
                    RESERVED_FACADE_ITEM,
                    format!("`{alias}::{name}` is a hidden facade item and cannot be named in lesson source"),
                    path_range,
                );
                return false;
            }
            let entry = AttributeMacro::from_name(&name).is_some();
            let accepted = match position {
                Position::Tree {
                    entries, helpers, ..
                } => {
                    if entries && entry {
                        self.krs_invocation(&name, attribute_range, true);
                        true
                    } else {
                        helpers.contains(&name.as_str())
                    }
                }
                Position::TokenBody => {
                    entry
                        || [
                            surface::ENUM_HELPERS,
                            surface::VARIANT_HELPERS,
                            surface::FIELD_HELPERS,
                            surface::PARAMETER_HELPERS,
                        ]
                        .iter()
                        .any(|helpers| helpers.contains(&name.as_str()))
                }
            };
            if !accepted {
                self.report(
                    NON_KRS_PROC_MACRO,
                    format!(
                        "`#[{alias}::{name}]` is not a KRS attribute accepted in this position"
                    ),
                    path_range,
                );
            }
            return accepted;
        }
        let (leading, segments) = path_segments(path);
        if self.names_reserved_facade_item(&segments) {
            self.report(
                RESERVED_FACADE_ITEM,
                "hidden facade items cannot be named in lesson source".to_owned(),
                path_range,
            );
        } else if Self::is_tool_attribute(attribute) {
            // Accepted: a tool attribute without arguments has no expansion
            // effect and nothing to scan.
        } else {
            self.report(
                NON_KRS_PROC_MACRO,
                format!(
                    "attribute `{}` is neither a KRS attribute nor an inert attribute accepted in lessons",
                    display_path(leading, &segments)
                ),
                path_range,
            );
        }
        false
    }

    fn check_derive(&mut self, attribute: &Attribute, path_range: ByteRange) {
        let parsed =
            attribute.parse_args_with(Punctuated::<Path, syn::Token![,]>::parse_terminated);
        let Ok(paths) = parsed else {
            self.report(
                NON_KRS_PROC_MACRO,
                "`derive` must list built-in derive paths".to_owned(),
                path_range,
            );
            return;
        };
        for path in &paths {
            if !Self::is_builtin_derive(path) {
                let (leading, segments) = path_segments(path);
                let range = self.range(path.span());
                self.report(
                    NON_KRS_PROC_MACRO,
                    format!(
                        "derive `{}` is not a built-in derive; lessons cannot run external procedural macros",
                        display_path(leading, &segments)
                    ),
                    range,
                );
            }
        }
    }

    fn classify_macro(&self, path: &Path) -> MacroClass {
        let (leading, segments) = path_segments(path);
        let Some(last) = segments.last() else {
            return MacroClass::Other;
        };
        if INCLUDE_MACROS.contains(&last.as_str()) {
            return MacroClass::Include;
        }
        if ENV_MACROS.contains(&last.as_str()) {
            return MacroClass::Env;
        }
        if self.names_reserved_facade_item(&segments) {
            return MacroClass::Reserved;
        }
        if let Some(Entry::Function(entry)) = surface::resolve(path, self.alias()) {
            return MacroClass::Krs(entry);
        }
        match (leading, segments.as_slice()) {
            (false, [name]) if name == "macro_rules" => MacroClass::Definition,
            (false, [name])
                if FunctionMacro::from_name(name).is_some_and(|entry| !entry.is_reserved()) =>
            {
                MacroClass::Unprefixed
            }
            (false, [name]) if STANDARD_MACROS.contains(&name.as_str()) => MacroClass::Standard,
            (_, [krate, name])
                if STANDARD_MACRO_CRATES.contains(&krate.as_str())
                    && STANDARD_MACROS.contains(&name.as_str()) =>
            {
                MacroClass::Standard
            }
            _ => MacroClass::Other,
        }
    }

    /// Checks one macro invocation and scans its tokens when it is accepted.
    fn check_macro(
        &mut self,
        path: &Path,
        path_range: ByteRange,
        close: Span,
        tokens: &TokenStream,
    ) {
        let whole = path_range.cover(self.range(close));
        let (leading, segments) = path_segments(path);
        let shown = display_path(leading, &segments);
        let item_position = std::mem::take(&mut self.item_position);
        match self.classify_macro(path) {
            MacroClass::Krs(entry) => {
                self.krs_invocation(entry.name(), whole, item_position);
                self.krs_depth += 1;
                self.scan_tokens(tokens);
                self.krs_depth -= 1;
            }
            MacroClass::Standard => self.scan_tokens(tokens),
            MacroClass::Include => self.report(
                INCLUDE,
                format!("`{shown}!` reads a file outside the lesson source"),
                whole,
            ),
            MacroClass::Env => self.report(
                ENV,
                format!("`{shown}!` reads the compiler environment"),
                whole,
            ),
            MacroClass::Definition => self.report(
                MACRO_DEFINITION,
                "lesson source cannot define macros".to_owned(),
                whole,
            ),
            MacroClass::Reserved => self.report(
                RESERVED_FACADE_ITEM,
                format!("`{shown}!` is a hidden facade item and cannot be invoked in lesson source"),
                path_range,
            ),
            MacroClass::Unprefixed => {
                let alias = self.alias().to_owned();
                self.report(
                    KRS_IMPORT,
                    format!("KRS macro `{shown}!` must be named `{alias}::{shown}!`"),
                    path_range,
                );
            }
            MacroClass::Other => self.report(
                NON_KRS_PROC_MACRO,
                format!("macro `{shown}!` is neither a KRS macro nor a standard macro accepted in lessons"),
                path_range,
            ),
        }
    }

    fn check_out_of_line_module(&mut self, name: &str, range: ByteRange) {
        let mut directory = module_directory(self.file);
        for module in &self.module_path {
            directory.push_str(module);
            directory.push('/');
        }
        let candidates = [
            format!("{directory}{name}.rs"),
            format!("{directory}{name}/mod.rs"),
        ];
        if !candidates
            .iter()
            .any(|candidate| self.policy.editable_files.contains(candidate))
        {
            self.report(
                OUT_OF_LINE_MODULE,
                format!(
                    "`mod {name};` resolves to `{}` or `{}`, which is not an editable file of this lesson",
                    candidates[0], candidates[1]
                ),
                range,
            );
        }
    }

    fn check_module_name(&mut self, ident: &syn::Ident) {
        if ident.unraw() == self.alias() {
            let alias = self.alias().to_owned();
            let range = self.range(ident.span());
            self.report(
                KRS_IMPORT,
                format!("a module named `{alias}` shadows the KRS facade alias"),
                range,
            );
        }
    }

    fn check_use_tree(&mut self, tree: &UseTree, prefix: &mut Vec<String>) {
        let alias = self.alias().to_owned();
        let under_facade = prefix.first().is_some_and(|first| *first == alias);
        let direct_facade_child = prefix.len() == 1 && under_facade;
        match tree {
            UseTree::Path(path) => {
                let name = path.ident.unraw().to_string();
                if under_facade && name.starts_with("__") {
                    let range = self.range(path.ident.span());
                    self.report(
                        RESERVED_FACADE_ITEM,
                        format!("`{name}` is a hidden facade item and cannot be imported"),
                        range,
                    );
                    return;
                }
                prefix.push(name);
                self.check_use_tree(&path.tree, prefix);
                prefix.pop();
            }
            UseTree::Name(name) => {
                let ident = name.ident.unraw().to_string();
                let range = self.range(name.span());
                self.check_use_leaf(&ident, None, prefix, range);
            }
            UseTree::Rename(rename) => {
                let ident = rename.ident.unraw().to_string();
                let binding = rename.rename.unraw().to_string();
                let range = self.range(rename.span());
                self.check_use_leaf(&ident, Some(&binding), prefix, range);
            }
            UseTree::Glob(glob) => {
                if direct_facade_child {
                    let range = self.range(glob.span());
                    self.report(
                        KRS_IMPORT,
                        format!("`use {alias}::*` imports KRS macros without the facade prefix"),
                        range,
                    );
                }
            }
            UseTree::Group(group) => {
                for tree in &group.items {
                    self.check_use_tree(tree, prefix);
                }
            }
        }
    }

    fn check_use_leaf(
        &mut self,
        ident: &str,
        rename: Option<&str>,
        prefix: &[String],
        range: ByteRange,
    ) {
        let alias = self.alias().to_owned();
        let under_facade = prefix.first().is_some_and(|first| *first == alias);
        let names_facade =
            (prefix.is_empty() && ident == alias) || (prefix == [alias.clone()] && ident == "self");
        if under_facade && ident.starts_with("__") {
            self.report(
                RESERVED_FACADE_ITEM,
                format!("`{ident}` is a hidden facade item and cannot be imported"),
                range,
            );
            return;
        }
        if names_facade {
            if rename.is_some_and(|binding| binding != alias) {
                self.report(
                    KRS_IMPORT,
                    format!("the KRS facade must be named `{alias}`; renaming it hides KRS macros from the lesson policy"),
                    range,
                );
            }
            return;
        }
        if prefix.len() == 1 && under_facade && is_krs_entry_name(ident) {
            self.report(
                KRS_IMPORT,
                format!(
                    "KRS macro `{ident}` must be named `{alias}::{ident}` at each use, not imported"
                ),
                range,
            );
            return;
        }
        let binding = match rename {
            Some(binding) => binding,
            None if ident == "self" => prefix.last().map_or("", String::as_str),
            None => ident,
        };
        if binding == alias {
            self.report(
                KRS_IMPORT,
                format!("this import binds `{alias}`, which shadows the KRS facade alias"),
                range,
            );
            return;
        }
        let binding = binding.to_owned();
        self.check_reserved_binding(&binding, range);
    }

    /// Scans macro or attribute token trees for nested constructs.
    fn scan_tokens(&mut self, stream: &TokenStream) {
        let tokens: Vec<TokenTree> = stream.clone().into_iter().collect();
        let mut index = 0;
        while index < tokens.len() {
            index = self.scan_token(&tokens, index);
        }
    }

    /// Scans the construct starting at `index` and returns the next index.
    fn scan_token(&mut self, tokens: &[TokenTree], index: usize) -> usize {
        match &tokens[index] {
            TokenTree::Group(group) => {
                self.scan_tokens(&group.stream());
                index + 1
            }
            TokenTree::Punct(punct) if punct.as_char() == '#' => {
                self.scan_attribute(tokens, index).unwrap_or(index + 1)
            }
            TokenTree::Ident(ident)
                if ident == "extern" && is_ident(tokens.get(index + 1), "crate") =>
            {
                let end = tokens[index + 2..]
                    .iter()
                    .position(|token| is_punct(Some(token), ';'))
                    .map_or((index + 2).min(tokens.len() - 1), |offset| {
                        index + 2 + offset
                    });
                let range = self.span_range(ident.span(), tokens[end].span());
                self.report(
                    EXTERN_CRATE,
                    "lesson source cannot declare `extern crate`".to_owned(),
                    range,
                );
                end + 1
            }
            TokenTree::Ident(ident)
                if ident == "mod"
                    && matches!(tokens.get(index + 1), Some(TokenTree::Ident(_)))
                    && is_punct(tokens.get(index + 2), ';') =>
            {
                let TokenTree::Ident(name) = &tokens[index + 1] else {
                    unreachable!("the guard matched an identifier");
                };
                let name = name.unraw().to_string();
                let range = self.span_range(ident.span(), tokens[index + 2].span());
                self.check_out_of_line_module(&name, range);
                index + 3
            }
            TokenTree::Ident(_) | TokenTree::Punct(_) => self.scan_macro_path(tokens, index),
            TokenTree::Literal(_) => index + 1,
        }
    }

    /// Recognizes `#[…]` or `#![…]` at `index`.
    fn scan_attribute(&mut self, tokens: &[TokenTree], index: usize) -> Option<usize> {
        let inner = is_punct(tokens.get(index + 1), '!');
        let group_index = index + 1 + usize::from(inner);
        let Some(TokenTree::Group(group)) = tokens.get(group_index) else {
            return None;
        };
        if group.delimiter() != Delimiter::Bracket {
            return None;
        }
        let stream: TokenStream = tokens[index..=group_index].iter().cloned().collect();
        let parser = if inner {
            Attribute::parse_inner
        } else {
            Attribute::parse_outer
        };
        let attributes = parser.parse2(stream).ok()?;
        let [attribute] = attributes.as_slice() else {
            return None;
        };
        if self.check_attribute(attribute, Position::TokenBody) || scans_arguments(attribute) {
            self.scan_tokens(&group.stream());
        }
        Some(group_index + 1)
    }

    /// Recognizes `[::]a::b…! (…)` at `index`.
    fn scan_macro_path(&mut self, tokens: &[TokenTree], index: usize) -> usize {
        let mut cursor = index;
        let leading = is_path_separator(tokens, cursor);
        if leading {
            cursor += 2;
        }
        let mut segments: Punctuated<PathSegment, syn::Token![::]> = Punctuated::new();
        let first = cursor;
        while let Some(TokenTree::Ident(ident)) = tokens.get(cursor) {
            segments.push(PathSegment::from(ident.clone()));
            cursor += 1;
            if is_path_separator(tokens, cursor) {
                cursor += 2;
            } else {
                break;
            }
        }
        if segments.is_empty() {
            return index + 1;
        }
        let single_keyword = !leading
            && segments.len() == 1
            && krs_syntax::keyword::is_keyword(&segments[0].ident.unraw().to_string());
        if single_keyword || !is_punct(tokens.get(cursor), '!') {
            return cursor.max(index + 1);
        }
        let path_start = tokens[if leading { index } else { first }].span();
        let path_end = tokens[cursor - 1].span();
        let path_range = self.span_range(path_start, path_end);
        let path = Path {
            leading_colon: leading.then(|| syn::Token![::](path_start)),
            segments,
        };
        match tokens.get(cursor + 1) {
            Some(TokenTree::Group(group)) => {
                self.check_macro(&path, path_range, group.span_close(), &group.stream());
                cursor + 2
            }
            Some(TokenTree::Ident(_)) if !leading && path.is_ident("macro_rules") => {
                let end = match tokens.get(cursor + 2) {
                    Some(TokenTree::Group(group)) => (
                        cursor + 2 + usize::from(is_punct(tokens.get(cursor + 3), ';')),
                        group.span_close(),
                    ),
                    _ => (cursor + 1, tokens[cursor + 1].span()),
                };
                let range = self.span_range(path_start, end.1);
                self.report(
                    MACRO_DEFINITION,
                    "lesson source cannot define macros".to_owned(),
                    range,
                );
                end.0 + 1
            }
            _ => cursor + 1,
        }
    }

    fn push_context(
        &mut self,
        attrs: &'ast [Attribute],
        entries: bool,
        helpers: &'static [&'static str],
        helpers_from: usize,
        variant: bool,
    ) {
        self.contexts.push(AttributeContext {
            attrs,
            entries,
            helpers,
            helpers_from,
            variant,
        });
    }

    /// Visits an item-like node: pushes its attribute context, marks the
    /// node as consumed by KRS when it carries a KRS attribute invocation,
    /// and restores the state afterward.
    fn with_item(
        &mut self,
        attrs: &'ast [Attribute],
        helpers: &'static [&'static str],
        helpers_from: usize,
        pending: PendingHelpers,
        visit: impl FnOnce(&mut Self),
    ) {
        let krs = attrs
            .iter()
            .any(|attribute| self.krs_attribute(attribute).is_some());
        self.check_attribute_order(attrs);
        let saved = std::mem::replace(&mut self.helpers, pending);
        self.push_context(attrs, true, helpers, helpers_from, false);
        // Attributes are checked at the item's own scope; the body counts
        // as consumed by the KRS invocation.
        for attribute in attrs {
            self.visit_attribute(attribute);
        }
        self.contexts.pop();
        self.krs_depth += usize::from(krs);
        visit(self);
        self.krs_depth -= usize::from(krs);
        self.helpers = saved;
    }
}

impl Checker<'_, '_> {
    /// Rejects an order-sensitive attribute (`#[derive]`) that precedes the
    /// first KRS attribute invocation of the same item: rustc expands it
    /// before the KRS attribute, which the path-C expander does not emulate.
    fn check_attribute_order(&mut self, attrs: &[Attribute]) {
        let Some((first_krs, krs)) = attrs.iter().enumerate().find_map(|(index, attribute)| {
            self.krs_attribute(attribute)
                .map(|entry| (index, entry.name()))
        }) else {
            return;
        };
        let alias = self.alias().to_owned();
        for attribute in &attrs[..first_krs] {
            let Some(ident) = attribute.path().get_ident() else {
                continue;
            };
            let name = ident.unraw().to_string();
            if ORDER_SENSITIVE_ATTRIBUTES.contains(&name.as_str()) {
                let range = self.range(attribute.span());
                self.report(
                    ATTRIBUTE_ORDER,
                    format!(
                        "`#[{name}]` precedes `#[{alias}::{krs}]`; rustc expands `#[{name}]` first, \
                         so it must follow the KRS attribute"
                    ),
                    range,
                );
            }
        }
    }

    /// Rejects an authored name in the namespace that KRS expansion
    /// generates names in.
    fn check_reserved_name(&mut self, ident: &Ident) {
        let range = self.range(ident.span());
        self.check_reserved_binding(&ident.unraw().to_string(), range);
    }

    /// Rejects `name`, bound at `range`, when it is in the reserved
    /// generated-name namespace.
    fn check_reserved_binding(&mut self, name: &str, range: ByteRange) {
        let prefix = RESERVED_NAME_PREFIX;
        if name.to_ascii_lowercase().starts_with(prefix) {
            self.report(
                RESERVED_NAME,
                format!(
                    "`{name}` is in the `{prefix}` namespace, which is reserved for names that KRS \
                     expansion generates (such as `__KRS_REGISTRATIONS`)"
                ),
                range,
            );
        }
    }

    /// A bare two-segment attribute in [`TOOL_ATTRIBUTES`], such as
    /// `#[rustfmt::skip]`.
    fn is_tool_attribute(attribute: &Attribute) -> bool {
        let path = attribute.path();
        matches!(attribute.meta, Meta::Path(_))
            && path.leading_colon.is_none()
            && path.segments.len() == 2
            && path
                .segments
                .iter()
                .all(|segment| segment.arguments.is_none())
            && TOOL_ATTRIBUTES.iter().any(|(tool, name)| {
                path.segments[0].ident.unraw() == tool && path.segments[1].ident.unraw() == name
            })
    }

    fn is_builtin_derive(path: &Path) -> bool {
        if path
            .segments
            .iter()
            .any(|segment| !segment.arguments.is_none())
        {
            return false;
        }
        let (leading, segments) = path_segments(path);
        match segments.as_slice() {
            [name] if !leading => BUILTIN_DERIVES.iter().any(|(derive, _)| derive == name),
            [krate, module, name] => {
                DERIVE_CRATES.contains(&krate.as_str())
                    && BUILTIN_DERIVES
                        .iter()
                        .any(|(derive, home)| derive == name && home == module)
            }
            _ => false,
        }
    }
}

/// The name an item defines in its module's namespaces, other than
/// `extern crate` and macro definitions, which are rejected outright.
fn defined_name(item: &Item) -> Option<&Ident> {
    match item {
        Item::Const(item) => Some(&item.ident),
        Item::Enum(item) => Some(&item.ident),
        Item::Fn(item) => Some(&item.sig.ident),
        Item::Mod(item) => Some(&item.ident),
        Item::Static(item) => Some(&item.ident),
        Item::Struct(item) => Some(&item.ident),
        Item::Trait(item) => Some(&item.ident),
        Item::TraitAlias(item) => Some(&item.ident),
        Item::Type(item) => Some(&item.ident),
        Item::Union(item) => Some(&item.ident),
        _ => None,
    }
}

/// Whether `name` is a KRS entry point that authored code may name.
fn is_krs_entry_name(name: &str) -> bool {
    Entry::from_name(name).is_some_and(|entry| !entry.is_reserved())
}

/// Whether an accepted attribute's arguments are checked as Rust: an inert
/// attribute or `derive`.
fn scans_arguments(attribute: &Attribute) -> bool {
    attribute.path().get_ident().is_some_and(|ident| {
        let name = ident.unraw().to_string();
        name == "derive" || INERT_ATTRIBUTES.contains(&name.as_str())
    })
}

fn path_segments(path: &Path) -> (bool, Vec<String>) {
    (
        path.leading_colon.is_some(),
        path.segments
            .iter()
            .map(|segment| segment.ident.unraw().to_string())
            .collect(),
    )
}

fn display_path(leading: bool, segments: &[String]) -> String {
    let joined = segments.join("::");
    if leading {
        format!("::{joined}")
    } else {
        joined
    }
}

fn is_punct(token: Option<&TokenTree>, character: char) -> bool {
    matches!(token, Some(TokenTree::Punct(punct)) if punct.as_char() == character)
}

fn is_ident(token: Option<&TokenTree>, name: &str) -> bool {
    matches!(token, Some(TokenTree::Ident(ident)) if ident == name)
}

fn is_path_separator(tokens: &[TokenTree], index: usize) -> bool {
    matches!(
        (tokens.get(index), tokens.get(index + 1)),
        (Some(TokenTree::Punct(first)), Some(TokenTree::Punct(second)))
            if first.as_char() == ':'
                && first.spacing() == proc_macro2::Spacing::Joint
                && second.as_char() == ':'
    )
}

impl<'ast> Visit<'ast> for Checker<'_, 'ast> {
    fn visit_attribute(&mut self, attribute: &'ast Attribute) {
        let position = self.position_of(attribute);
        if self.check_attribute(attribute, position) {
            if let Meta::List(list) = &attribute.meta {
                self.krs_depth += 1;
                self.scan_tokens(&list.tokens);
                self.krs_depth -= 1;
            }
            return;
        }
        if scans_arguments(attribute) {
            visit::visit_attribute(self, attribute);
        }
    }

    fn visit_item(&mut self, item: &'ast Item) {
        if let Some(ident) = defined_name(item) {
            self.check_reserved_name(ident);
        }
        let (attrs, helpers, helpers_from, pending): (
            &'ast [Attribute],
            &'static [&'static str],
            usize,
            PendingHelpers,
        ) = match item {
            Item::Enum(ItemEnum { attrs, .. }) => {
                let constructors = attrs.iter().position(|attribute| {
                    self.krs_attribute(attribute) == Some(AttributeMacro::Constructors)
                });
                match constructors {
                    Some(index) => (
                        attrs,
                        surface::ENUM_HELPERS,
                        index + 1,
                        PendingHelpers {
                            variant: surface::VARIANT_HELPERS,
                            ..PendingHelpers::default()
                        },
                    ),
                    None => (attrs, &[], 0, PendingHelpers::default()),
                }
            }
            Item::Struct(ItemStruct { attrs, .. }) => {
                let pending = if self.has_krs_attribute(
                    attrs,
                    &[AttributeMacro::Configuration, AttributeMacro::Cell],
                ) {
                    PendingHelpers {
                        field: surface::FIELD_HELPERS,
                        ..PendingHelpers::default()
                    }
                } else {
                    PendingHelpers::default()
                };
                (attrs, &[], 0, pending)
            }
            Item::Fn(function) => {
                let pending = if self.has_krs_attribute(&function.attrs, &[AttributeMacro::Init]) {
                    PendingHelpers {
                        parameter: surface::PARAMETER_HELPERS,
                        ..PendingHelpers::default()
                    }
                } else {
                    PendingHelpers::default()
                };
                (&function.attrs, &[], 0, pending)
            }
            Item::Const(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::ExternCrate(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::ForeignMod(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Impl(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Macro(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Mod(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Static(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Trait(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::TraitAlias(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Type(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Union(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Use(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Verbatim(tokens) => {
                self.check_verbatim_item(tokens);
                return;
            }
            _ => (&[], &[], 0, PendingHelpers::default()),
        };
        self.with_item(attrs, helpers, helpers_from, pending, |checker| {
            checker.visit_item_body(item);
        });
    }

    fn visit_impl_item(&mut self, item: &'ast ImplItem) {
        match item {
            ImplItem::Const(item) => self.check_reserved_name(&item.ident),
            ImplItem::Fn(item) => self.check_reserved_name(&item.sig.ident),
            ImplItem::Type(item) => self.check_reserved_name(&item.ident),
            _ => {}
        }
        let (attrs, pending): (&'ast [Attribute], PendingHelpers) = match item {
            ImplItem::Fn(function) => (
                &function.attrs,
                if self.has_krs_attribute(&function.attrs, &[AttributeMacro::Init]) {
                    PendingHelpers {
                        parameter: surface::PARAMETER_HELPERS,
                        ..PendingHelpers::default()
                    }
                } else {
                    PendingHelpers::default()
                },
            ),
            ImplItem::Const(item) => (&item.attrs, PendingHelpers::default()),
            ImplItem::Type(item) => (&item.attrs, PendingHelpers::default()),
            ImplItem::Macro(item) => (&item.attrs, PendingHelpers::default()),
            ImplItem::Verbatim(tokens) => {
                self.scan_tokens(tokens);
                return;
            }
            _ => (&[], PendingHelpers::default()),
        };
        self.with_item(attrs, &[], 0, pending, |checker| {
            checker.visit_impl_item_body(item);
        });
    }

    fn visit_trait_item(&mut self, item: &'ast TraitItem) {
        match item {
            TraitItem::Const(item) => self.check_reserved_name(&item.ident),
            TraitItem::Fn(item) => self.check_reserved_name(&item.sig.ident),
            TraitItem::Type(item) => self.check_reserved_name(&item.ident),
            _ => {}
        }
        let (attrs, pending): (&'ast [Attribute], PendingHelpers) = match item {
            TraitItem::Fn(function) => (
                &function.attrs,
                if self.has_krs_attribute(&function.attrs, &[AttributeMacro::Init]) {
                    PendingHelpers {
                        parameter: surface::PARAMETER_HELPERS,
                        ..PendingHelpers::default()
                    }
                } else {
                    PendingHelpers::default()
                },
            ),
            TraitItem::Const(item) => (&item.attrs, PendingHelpers::default()),
            TraitItem::Type(item) => (&item.attrs, PendingHelpers::default()),
            TraitItem::Macro(item) => (&item.attrs, PendingHelpers::default()),
            TraitItem::Verbatim(tokens) => {
                self.scan_tokens(tokens);
                return;
            }
            _ => (&[], PendingHelpers::default()),
        };
        self.with_item(attrs, &[], 0, pending, |checker| {
            checker.visit_trait_item_body(item);
        });
    }

    fn visit_foreign_item(&mut self, item: &'ast ForeignItem) {
        match item {
            ForeignItem::Fn(item) => self.check_reserved_name(&item.sig.ident),
            ForeignItem::Static(item) => self.check_reserved_name(&item.ident),
            ForeignItem::Type(item) => self.check_reserved_name(&item.ident),
            _ => {}
        }
        visit::visit_foreign_item(self, item);
    }

    fn visit_variant(&mut self, variant: &'ast Variant) {
        let helpers = self.helpers.variant;
        let saved = std::mem::take(&mut self.helpers);
        self.push_context(&variant.attrs, false, helpers, 0, true);
        visit::visit_variant(self, variant);
        self.contexts.pop();
        self.helpers = saved;
    }

    fn visit_field(&mut self, field: &'ast syn::Field) {
        let helpers = self.helpers.field;
        let saved = std::mem::take(&mut self.helpers);
        self.push_context(&field.attrs, false, helpers, 0, false);
        visit::visit_field(self, field);
        self.contexts.pop();
        self.helpers = saved;
    }

    fn visit_fn_arg(&mut self, argument: &'ast FnArg) {
        let helpers = self.helpers.parameter;
        let saved = std::mem::take(&mut self.helpers);
        let attrs = match argument {
            FnArg::Receiver(receiver) => &receiver.attrs,
            FnArg::Typed(typed) => &typed.attrs,
        };
        self.push_context(attrs, false, helpers, 0, false);
        visit::visit_fn_arg(self, argument);
        self.contexts.pop();
        self.helpers = saved;
    }

    fn visit_block(&mut self, block: &'ast syn::Block) {
        let nested = usize::from(self.krs_depth == 0);
        let saved = std::mem::take(&mut self.helpers);
        self.block_scope += nested;
        visit::visit_block(self, block);
        self.block_scope -= nested;
        self.helpers = saved;
    }

    fn visit_item_mod(&mut self, module: &'ast ItemMod) {
        self.check_module_name(&module.ident);
        match &module.content {
            None => {
                let mut bare = module.clone();
                bare.attrs.clear();
                let range = self.range(bare.span());
                let name = module.ident.unraw().to_string();
                self.check_out_of_line_module(&name, range);
            }
            Some((_, items)) => {
                self.module_path.push(module.ident.unraw().to_string());
                self.module_scope += 1;
                for item in items {
                    self.visit_item(item);
                }
                self.module_scope -= 1;
                self.module_path.pop();
            }
        }
    }

    fn visit_item_extern_crate(&mut self, item: &'ast ItemExternCrate) {
        let mut bare = item.clone();
        bare.attrs.clear();
        let range = self.range(bare.span());
        self.report(
            EXTERN_CRATE,
            "lesson source cannot declare `extern crate`".to_owned(),
            range,
        );
    }

    fn visit_item_macro(&mut self, item: &'ast ItemMacro) {
        if item.mac.path.is_ident("macro_rules") {
            let mut bare = item.clone();
            bare.attrs.clear();
            let range = self.range(bare.span());
            self.report(
                MACRO_DEFINITION,
                "lesson source cannot define macros".to_owned(),
                range,
            );
            return;
        }
        self.visit_item_position_macro(&item.mac);
    }

    fn visit_stmt_macro(&mut self, statement: &'ast syn::StmtMacro) {
        for attribute in &statement.attrs {
            self.visit_attribute(attribute);
        }
        self.visit_item_position_macro(&statement.mac);
    }

    fn visit_item_use(&mut self, item: &'ast ItemUse) {
        self.check_use_tree(&item.tree, &mut Vec::new());
    }

    fn visit_macro(&mut self, mac: &'ast Macro) {
        let path_range = self.range(mac.path.span());
        self.check_macro(
            &mac.path,
            path_range,
            mac.delimiter.span().close(),
            &mac.tokens,
        );
    }
}

impl<'ast> Checker<'_, 'ast> {
    fn visit_item_position_macro(&mut self, mac: &'ast Macro) {
        self.item_position = true;
        self.visit_macro(mac);
    }

    /// Visits an item's children other than its attributes, which
    /// [`Checker::with_item`] has already checked.
    fn visit_item_body(&mut self, item: &'ast Item) {
        match item {
            Item::Mod(module) => self.visit_item_mod(module),
            Item::ExternCrate(item) => self.visit_item_extern_crate(item),
            Item::Macro(item) => self.visit_item_macro(item),
            Item::Use(item) => self.visit_item_use(item),
            Item::Enum(item) => {
                self.visit_visibility(&item.vis);
                self.visit_generics(&item.generics);
                for variant in &item.variants {
                    self.visit_variant(variant);
                }
            }
            Item::Struct(item) => {
                self.visit_visibility(&item.vis);
                self.visit_generics(&item.generics);
                self.visit_fields(&item.fields);
            }
            Item::Fn(item) => {
                self.visit_visibility(&item.vis);
                self.visit_signature(&item.sig);
                self.visit_block(&item.block);
            }
            Item::Impl(item) => {
                self.visit_generics(&item.generics);
                if let Some((_, path, _)) = &item.trait_ {
                    self.visit_path(path);
                }
                self.visit_type(&item.self_ty);
                for item in &item.items {
                    self.visit_impl_item(item);
                }
            }
            Item::Trait(item) => {
                self.visit_visibility(&item.vis);
                self.visit_generics(&item.generics);
                for bound in &item.supertraits {
                    self.visit_type_param_bound(bound);
                }
                for item in &item.items {
                    self.visit_trait_item(item);
                }
            }
            Item::Const(item) => {
                self.visit_type(&item.ty);
                self.visit_expr(&item.expr);
            }
            Item::Static(item) => {
                self.visit_type(&item.ty);
                self.visit_expr(&item.expr);
            }
            Item::Type(item) => {
                self.visit_generics(&item.generics);
                self.visit_type(&item.ty);
            }
            Item::Union(item) => {
                self.visit_generics(&item.generics);
                self.visit_fields_named(&item.fields);
            }
            Item::TraitAlias(item) => {
                self.visit_generics(&item.generics);
                for bound in &item.bounds {
                    self.visit_type_param_bound(bound);
                }
            }
            Item::ForeignMod(item) => {
                for item in &item.items {
                    self.visit_foreign_item(item);
                }
            }
            _ => {}
        }
    }

    fn visit_impl_item_body(&mut self, item: &'ast ImplItem) {
        match item {
            ImplItem::Fn(function) => {
                self.visit_visibility(&function.vis);
                self.visit_signature(&function.sig);
                self.visit_block(&function.block);
            }
            ImplItem::Const(item) => {
                self.visit_generics(&item.generics);
                self.visit_type(&item.ty);
                self.visit_expr(&item.expr);
            }
            ImplItem::Type(item) => {
                self.visit_generics(&item.generics);
                self.visit_type(&item.ty);
            }
            ImplItem::Macro(item) => self.visit_item_position_macro(&item.mac),
            _ => {}
        }
    }

    fn visit_trait_item_body(&mut self, item: &'ast TraitItem) {
        match item {
            TraitItem::Fn(function) => {
                self.visit_signature(&function.sig);
                if let Some(block) = &function.default {
                    self.visit_block(block);
                }
            }
            TraitItem::Const(item) => {
                self.visit_generics(&item.generics);
                self.visit_type(&item.ty);
                if let Some((_, expr)) = &item.default {
                    self.visit_expr(expr);
                }
            }
            TraitItem::Type(item) => {
                self.visit_generics(&item.generics);
                for bound in &item.bounds {
                    self.visit_type_param_bound(bound);
                }
                if let Some((_, ty)) = &item.default {
                    self.visit_type(ty);
                }
            }
            TraitItem::Macro(item) => self.visit_item_position_macro(&item.mac),
            _ => {}
        }
    }

    /// A `macro` item or other syntax that `syn` keeps verbatim.
    fn check_verbatim_item(&mut self, tokens: &TokenStream) {
        let trees: Vec<TokenTree> = tokens.clone().into_iter().collect();
        let defines_macro = trees.iter().take_while(|token| !matches!(token, TokenTree::Group(group) if group.delimiter() == Delimiter::Brace)).any(|token| is_ident(Some(token), "macro"));
        if defines_macro {
            let range = self.range(tokens.span());
            self.report(
                MACRO_DEFINITION,
                "lesson source cannot define macros".to_owned(),
                range,
            );
        } else {
            self.scan_tokens(tokens);
        }
    }
}
