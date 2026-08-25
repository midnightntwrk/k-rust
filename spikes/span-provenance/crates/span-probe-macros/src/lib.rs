use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2, TokenTree};
use quote::{ToTokens, format_ident, quote};
use syn::{
    ExprPath, FnArg, ItemFn, Pat, Path, Token, Type, parse::Parse, parse::ParseStream,
    parse_macro_input, spanned::Spanned, visit::Visit,
};

struct ProbeArgs {
    _path_token: syn::Ident,
    _equals: Token![=],
    path: Path,
}

impl Parse for ProbeArgs {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let path_token: syn::Ident = input.parse()?;
        if path_token != "path" {
            return Err(syn::Error::new(path_token.span(), "expected `path = RustPath`"));
        }
        Ok(Self {
            _path_token: path_token,
            _equals: input.parse()?,
            path: input.parse()?,
        })
    }
}

fn leaves(stream: TokenStream2, output: &mut Vec<Span>) {
    for tree in stream {
        match tree {
            TokenTree::Group(group) => {
                output.push(group.span_open());
                leaves(group.stream(), output);
                output.push(group.span_close());
            }
            other => output.push(other.span()),
        }
    }
}

fn bounds(tokens: &impl ToTokens) -> syn::Result<(Span, Span)> {
    let mut spans = Vec::new();
    leaves(tokens.to_token_stream(), &mut spans);
    match (spans.first(), spans.last()) {
        (Some(first), Some(last)) => Ok((*first, *last)),
        _ => Err(syn::Error::new(tokens.span(), "probe target had no tokens")),
    }
}

fn option_string(value: Option<String>) -> TokenStream2 {
    match value {
        Some(value) => quote!(::core::option::Option::Some(#value)),
        None => quote!(::core::option::Option::None),
    }
}

fn captured_range(label: &str, first: Span, last: Span) -> TokenStream2 {
    // proc_macro2::Span::start/end and file forwarding are functional on this
    // stable compiler, but its byte_range still falls back to 0..0 because
    // proc_macro::Span::byte_range remains unstable. Unwrap lets us exercise
    // the direct stable proc_macro location API as the production macro can.
    let p2_start = first.start();
    let p2_end = last.end();
    let p2_first_bytes = first.byte_range();
    let p2_last_bytes = last.byte_range();
    let p2_join_succeeded = first.join(last).is_some();

    let first = first.unwrap();
    let last = last.unwrap();
    let start = first.start();
    let end = last.end();
    let display_file = first.file();
    let had_local_file = first.local_file().is_some();
    let first_text = option_string(first.source_text());
    let last_text = option_string(last.source_text());
    let start_line = start.line();
    let start_column = start.column();
    let end_line = end.line();
    let end_column = end.column();
    let p2_start_line = p2_start.line;
    let p2_start_column = p2_start.column;
    let p2_end_line = p2_end.line;
    let p2_end_column = p2_end.column;
    let p2_first_start = p2_first_bytes.start;
    let p2_first_end = p2_first_bytes.end;
    let p2_last_start = p2_last_bytes.start;
    let p2_last_end = p2_last_bytes.end;

    quote! {
        ::span_probe_model::CapturedRange {
            label: #label,
            display_file: #display_file,
            had_local_file: #had_local_file,
            start: ::span_probe_model::Position { line: #start_line, column: #start_column },
            end: ::span_probe_model::Position { line: #end_line, column: #end_column },
            first_token_text: #first_text,
            last_token_text: #last_text,
            proc_macro2_start: ::span_probe_model::Position {
                line: #p2_start_line,
                column: #p2_start_column,
            },
            proc_macro2_end: ::span_probe_model::Position {
                line: #p2_end_line,
                column: #p2_end_column,
            },
            proc_macro2_first_byte_range: (#p2_first_start, #p2_first_end),
            proc_macro2_last_byte_range: (#p2_last_start, #p2_last_end),
            proc_macro2_join_succeeded: #p2_join_succeeded,
        }
    }
}

#[derive(Default)]
struct BodyPaths<'ast> {
    paths: Vec<&'ast Path>,
}

impl<'ast> Visit<'ast> for BodyPaths<'ast> {
    fn visit_expr_path(&mut self, node: &'ast ExprPath) {
        self.paths.push(&node.path);
        syn::visit::visit_expr_path(self, node);
    }
}

fn pattern_constructor(pattern: &Pat) -> syn::Result<&Path> {
    match pattern {
        Pat::TupleStruct(pattern) => Ok(&pattern.path),
        Pat::Struct(pattern) => Ok(&pattern.path),
        Pat::Wild(pattern) => Err(syn::Error::new_spanned(
            pattern,
            "a probe rule needs a refutable constructor pattern",
        )),
        other => Err(syn::Error::new_spanned(
            other,
            "expected a tuple-struct or struct parameter pattern",
        )),
    }
}

#[proc_macro_attribute]
pub fn probe(arguments: TokenStream, input: TokenStream) -> TokenStream {
    let arguments = parse_macro_input!(arguments as ProbeArgs);
    let item = parse_macro_input!(input as ItemFn);
    if item.sig.inputs.len() != 1 {
        return syn::Error::new_spanned(&item.sig.inputs, "expected exactly one parameter")
            .into_compile_error()
            .into();
    }
    let FnArg::Typed(parameter) = item.sig.inputs.first().expect("checked length") else {
        return syn::Error::new_spanned(&item.sig.inputs, "`self` is not supported")
            .into_compile_error()
            .into();
    };
    let constructor = match pattern_constructor(&parameter.pat) {
        Ok(path) => path,
        Err(error) => return error.into_compile_error().into(),
    };
    let mut body_paths = BodyPaths::default();
    body_paths.visit_block(&item.block);
    let Some(nested_path) = body_paths
        .paths
        .into_iter()
        .max_by_key(|path| path.segments.len())
    else {
        return syn::Error::new_spanned(&item.block, "expected a body path")
            .into_compile_error()
            .into();
    };

    let attr_bounds = match bounds(&arguments.path) {
        Ok(value) => value,
        Err(error) => return error.into_compile_error().into(),
    };
    let pattern_bounds = match bounds(&parameter.pat) {
        Ok(value) => value,
        Err(error) => return error.into_compile_error().into(),
    };
    let type_bounds = match bounds(&parameter.ty) {
        Ok(value) => value,
        Err(error) => return error.into_compile_error().into(),
    };
    let nested_bounds = match bounds(nested_path) {
        Ok(value) => value,
        Err(error) => return error.into_compile_error().into(),
    };

    let ranges = [
        captured_range("attribute argument path", attr_bounds.0, attr_bounds.1),
        captured_range("refutable parameter pattern", pattern_bounds.0, pattern_bounds.1),
        captured_range("parameter type", type_bounds.0, type_bounds.1),
        captured_range("nested body path", nested_bounds.0, nested_bounds.1),
    ];
    let visibility = &item.vis;
    let name = &item.sig.ident;
    let descriptor_name = format_ident!("{}_PROVENANCE", name.to_string().to_uppercase());
    let attr_path = &arguments.path;
    let parameter_type: &Type = &parameter.ty;

    // Each authored path has one meaningful expansion use. The semantic item
    // itself is consumed so rustc never applies irrefutable-parameter checking.
    quote! {
        #[doc(hidden)]
        #visibility fn #name() {}
        const _: ::core::marker::PhantomData<dyn #attr_path> = ::core::marker::PhantomData;
        const _: ::core::marker::PhantomData<#parameter_type> = ::core::marker::PhantomData;
        const _: ::core::marker::PhantomData<#constructor> = ::core::marker::PhantomData;
        const _: () = { let _ = #nested_path; };
        #visibility static #descriptor_name: &[::span_probe_model::CapturedRange] = &[#(#ranges),*];
    }
    .into()
}

#[proc_macro]
pub fn payload_probe(input: TokenStream) -> TokenStream {
    let path = parse_macro_input!(input as Path);
    let (first, last) = match bounds(&path) {
        Ok(value) => value,
        Err(error) => return error.into_compile_error().into(),
    };
    let range = captured_range("function-like macro payload path", first, last);
    quote! {{
        const _: ::core::marker::PhantomData<#path> = ::core::marker::PhantomData;
        #range
    }}
    .into()
}

#[proc_macro]
pub fn single_path(input: TokenStream) -> TokenStream {
    let path = parse_macro_input!(input as Path);
    quote! {{ let _ = #path; }}.into()
}

#[proc_macro]
pub fn duplicated_source_path(input: TokenStream) -> TokenStream {
    let path = parse_macro_input!(input as Path);
    quote! {{ let _ = #path; let _ = #path; }}.into()
}

#[proc_macro]
pub fn callsite_duplicate_path(input: TokenStream) -> TokenStream {
    let path = parse_macro_input!(input as Path);
    let generated: Path = match syn::parse_str(&path.to_token_stream().to_string()) {
        Ok(path) => path,
        Err(error) => return error.into_compile_error().into(),
    };
    quote! {{ let _ = #path; let _ = #generated; }}.into()
}

