use krs_ir::{DisplayPath, HostRawProvenance};
use krs_syntax::{ProvenanceAnchor, TokenRange, role_tokens};
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

/// Emits the provenance expression of one descriptor factory.
///
/// The literal file table and anchors are checked by
/// `__KrsRawProvenance::new` in a `const` block, so the generated factory has
/// no runtime check except resolving an absolute display filename against its
/// Cargo manifest directory. The authored anchors are a named constant item:
/// a slice of `const fn` calls is not promoted when passed as an argument, and
/// Clippy's `large_stack_arrays` exempts an array only inside a constant item,
/// not inside an inline `const` block, so large rule anchor tables need one.
pub(crate) fn host_provenance(
    env: &dyn MacroEnvironment,
    facade: &syn::Path,
    fallback: TokenRange,
    anchors: &[ProvenanceAnchor],
) -> proc_macro2::TokenStream {
    let invocation = capture_call_site(env)
        .or_else(|| capture(env, fallback, false))
        .unwrap_or_else(|| unavailable_invocation(env, fallback));

    let mut files = Vec::new();
    let mut any_absolute = invocation.absolute_display_file;
    let invocation_tokens = raw_anchor(facade, &invocation, &mut files);
    let mut authored = Vec::with_capacity(anchors.len());
    for anchor in anchors {
        let captured = capture(env, anchor.range(), true).unwrap_or_else(|| {
            let mut inherited = invocation.clone();
            inherited.exact = false;
            inherited
        });
        any_absolute |= captured.absolute_display_file;
        let anchor_tokens = raw_anchor(facade, &captured, &mut files);
        let key = anchor.key();
        let role = role_tokens(key.role(), facade);
        let ordinal = key.ordinal();
        authored.push(quote! { (#role, #ordinal, #anchor_tokens) });
    }

    let manifest_dir = if any_absolute {
        quote!(env!("CARGO_MANIFEST_DIR"))
    } else {
        quote!("")
    };

    quote! {
        #facade::__krs_host_provenance(
            #manifest_dir,
            const {
                const __KRS_AUTHORED: &[(#facade::ProvenanceRole, u32, #facade::__KrsRawAnchor)] =
                    &[#(#authored),*];
                &#facade::__KrsRawProvenance::new(
                    &[#(#files),*],
                    #invocation_tokens,
                    __KRS_AUTHORED,
                )
            },
        )?
    }
}

/// Keep proc-macro expansion available to hosts such as rust-analyzer that do
/// not expose stable source locations. The emitted descriptor remains
/// fail-closed: collection rejects every `InvocationFallback` authored anchor.
fn unavailable_invocation(env: &dyn MacroEnvironment, range: TokenRange) -> CapturedAnchor {
    let display_file = normalized_display_file(&env.span_file(range.first()));
    let absolute_display_file = DisplayPath::is_absolute_spelling(&display_file);
    CapturedAnchor {
        display_file: if absolute_display_file
            || HostRawProvenance::accepts_relative_display_file(&display_file)
        {
            display_file
        } else {
            "<proc-macro-input>".to_owned()
        },
        absolute_display_file,
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

    let display_file = normalized_display_file(&first_file);
    let absolute_display_file = DisplayPath::is_absolute_spelling(&display_file);
    if !absolute_display_file && !HostRawProvenance::accepts_relative_display_file(&display_file) {
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
        display_file,
        absolute_display_file,
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

fn raw_anchor(
    facade: &syn::Path,
    anchor: &CapturedAnchor,
    files: &mut Vec<String>,
) -> proc_macro2::TokenStream {
    let file = files
        .iter()
        .position(|file| file == &anchor.display_file)
        .unwrap_or_else(|| {
            files.push(anchor.display_file.clone());
            files.len() - 1
        });
    let absolute = anchor.absolute_display_file;
    let start_line = anchor.start_line;
    let start_column = anchor.start_column;
    let end_line = anchor.end_line;
    let end_column = anchor.end_column;
    let exact = anchor.exact;
    quote! {
        #facade::__KrsRawAnchor::new(
            #file,
            #absolute,
            (#start_line, #start_column),
            (#end_line, #end_column),
            #exact
        )
    }
}
