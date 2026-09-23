use std::path::Path;

use krs_syntax::{ProvenanceAnchor, TokenRange};
use quote::quote;

use crate::environment::MacroEnvironment;

#[derive(Clone, Debug)]
struct CapturedAnchor {
    display_file: String,
    absolute_display_file: bool,
    start_line: u32,
    start_column: u32,
    end_line: u32,
    end_column: u32,
    exact: bool,
}

pub(crate) fn host_provenance(
    env: &dyn MacroEnvironment,
    facade: &syn::Path,
    fallback: TokenRange,
    anchors: &[ProvenanceAnchor],
) -> syn::Result<proc_macro2::TokenStream> {
    let invocation = capture_call_site(env)
        .or_else(|| capture(env, fallback, false))
        .unwrap_or_else(|| unavailable_invocation(env, fallback));

    let invocation_tokens = source_anchor(facade, &invocation);
    let mut authored = Vec::with_capacity(anchors.len());
    for anchor in anchors {
        let captured = capture(env, anchor.range(), true).unwrap_or_else(|| {
            let mut inherited = invocation.clone();
            inherited.exact = false;
            inherited
        });
        let anchor_tokens = source_anchor(facade, &captured);
        let key = anchor.key().map_err(|error| {
            syn::Error::new(
                anchor.range().first(),
                format!("invalid provenance key: {error}"),
            )
        })?;
        let role = key.role();
        let ordinal = key.ordinal();
        authored.push(quote! {
            #facade::HostAuthoredAnchor::new(
                #facade::ProvenanceKey::new(#role, #ordinal)
                    .expect("KRS parser roles are nonempty"),
                #anchor_tokens,
            )
        });
    }

    Ok(quote! {
        #facade::HostProvenance::new(
            #invocation_tokens,
            ::std::vec![#(#authored),*],
        )
        .expect("KRS shared parsers emit nonempty, uniquely keyed provenance")
    })
}

/// Keep proc-macro expansion available to hosts such as rust-analyzer that do
/// not expose stable source locations. The emitted descriptor remains
/// fail-closed: collection rejects every `InvocationFallback` authored anchor.
fn unavailable_invocation(env: &dyn MacroEnvironment, range: TokenRange) -> CapturedAnchor {
    let file = env.span_file(range.first());
    let display_file = normalized_display_file(&file);
    CapturedAnchor {
        display_file: if display_file.is_empty() {
            "<proc-macro-input>".to_owned()
        } else {
            display_file
        },
        absolute_display_file: is_absolute_display_file(&file),
        start_line: 1,
        start_column: 1,
        end_line: 1,
        end_column: 2,
        exact: false,
    }
}

fn capture_call_site(env: &dyn MacroEnvironment) -> Option<CapturedAnchor> {
    let span = env.call_site()?;
    capture(env, TokenRange::new(span, span), true)
}

fn capture(env: &dyn MacroEnvironment, range: TokenRange, exact: bool) -> Option<CapturedAnchor> {
    let first = range.first();
    let last = range.last();
    let first_file = env.span_file(first);
    let last_file = env.span_file(last);
    if first_file != last_file {
        return None;
    }

    let start = env.span_start(first)?;
    let end = env.span_end(last)?;
    let start_line = start.line;
    let start_column = start.column;
    let end_line = end.line;
    let end_column = end.column;
    if start_line == 0
        || start_column == 0
        || end_line == 0
        || end_column == 0
        || (end_line, end_column) <= (start_line, start_column)
    {
        return None;
    }

    Some(CapturedAnchor {
        display_file: normalized_display_file(&first_file),
        absolute_display_file: is_absolute_display_file(&first_file),
        start_line,
        start_column,
        end_line,
        end_column,
        exact,
    })
}

fn normalized_display_file(file: &str) -> String {
    file.replace('\\', "/").trim_start_matches("./").to_owned()
}

fn is_absolute_display_file(file: &str) -> bool {
    let normalized = file.replace('\\', "/");
    Path::new(file).is_absolute()
        || normalized.starts_with("file://")
        || normalized.starts_with("//")
        || is_windows_absolute(&normalized)
}

fn is_windows_absolute(file: &str) -> bool {
    let bytes = file.as_bytes();
    bytes.len() >= 3 && bytes[0].is_ascii_alphabetic() && bytes[1] == b':' && bytes[2] == b'/'
}

fn source_anchor(facade: &syn::Path, anchor: &CapturedAnchor) -> proc_macro2::TokenStream {
    let display_file = &anchor.display_file;
    let display_file = if anchor.absolute_display_file {
        quote! {{
            let source = ::std::path::Path::new(#display_file);
            let manifest = ::std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
            source
                .strip_prefix(manifest)
                .expect("rustc's absolute display path must remain inside the Cargo package")
                .to_string_lossy()
                .replace('\\', "/")
        }}
    } else {
        quote!(#display_file.to_owned())
    };
    let start_line = anchor.start_line;
    let start_column = anchor.start_column;
    let end_line = anchor.end_line;
    let end_column = anchor.end_column;
    let precision = if anchor.exact {
        quote!(#facade::AnchorPrecision::Exact)
    } else {
        quote!(#facade::AnchorPrecision::InvocationFallback)
    };
    quote! {
        #facade::HostSourceAnchor::new(
            #display_file,
            #facade::HostSourcePosition::new(#start_line, #start_column)
                .expect("stable proc-macro positions are one-based"),
            #facade::HostSourcePosition::new(#end_line, #end_column)
                .expect("stable proc-macro positions are one-based"),
            #precision,
        )
        .expect("KRS emits ordered, non-absolute display anchors")
    }
}
