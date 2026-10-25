use std::collections::HashSet;

use krs_diagnostic::codes::expand;
use krs_ir::{DisplayPath, HostRawProvenance};
use krs_syntax::{ProvenanceAnchor, TokenRange, role_tokens};
use quote::quote;

use crate::ExpandError;
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
///
/// A provenance key names one authored node of the sentence, so the anchors'
/// keys must be distinct; the `const` block asserts it. A repeated key is a
/// numbering bug in KRS, never a mistake in the definition, so it is reported
/// here, at the node that repeats the key, instead of as a const-evaluation
/// panic at the invocation.
pub(crate) fn host_provenance(
    env: &dyn MacroEnvironment,
    facade: &syn::Path,
    fallback: TokenRange,
    anchors: &[ProvenanceAnchor],
) -> proc_macro2::TokenStream {
    if let Some(error) = repeated_key(anchors) {
        // The error stands beside a provenance without authored anchors, so
        // the expression keeps its type and the const block has nothing to
        // reject: rustc reports the KRS error alone.
        let error = error.into_compile_error(fallback.first());
        let provenance = host_provenance(env, facade, fallback, &[]);
        return quote! {{ #error #provenance }};
    }
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

/// The error at the first anchor whose key an earlier anchor of the sentence
/// already has.
fn repeated_key(anchors: &[ProvenanceAnchor]) -> Option<ExpandError> {
    let mut keys = HashSet::with_capacity(anchors.len());
    let anchor = anchors.iter().find(|anchor| !keys.insert(anchor.key()))?;
    let key = anchor.key();
    Some(ExpandError::new(
        expand::DUPLICATE_PROVENANCE_KEY,
        anchor.range().first(),
        format_args!(
            "internal KRS error: this node repeats the provenance key `{} {}` of an earlier node in the same sentence; this is a bug in KRS, not in the definition",
            key.role().as_str(),
            key.ordinal(),
        ),
    ))
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

#[cfg(test)]
mod tests {
    use krs_diagnostic::Location;
    use krs_diagnostic::codes::expand;
    use krs_syntax::{ProvenanceAnchor, ProvenanceRole, TokenRange};

    use super::{host_provenance, repeated_key};
    use crate::environment::FixedEnvironment;

    /// Anchors on `first second third` with the given keys, in that order.
    fn anchors(
        keys: [(ProvenanceRole, u32); 3],
    ) -> (Vec<ProvenanceAnchor>, Vec<proc_macro2::Span>) {
        let tokens: proc_macro2::TokenStream = "first second third".parse().unwrap();
        let spans = tokens
            .into_iter()
            .map(|token| token.span())
            .collect::<Vec<_>>();
        let anchors = keys
            .iter()
            .zip(&spans)
            .map(|((role, ordinal), span)| {
                ProvenanceAnchor::new(*role, *ordinal, TokenRange::new(*span, *span))
            })
            .collect();
        (anchors, spans)
    }

    #[test]
    fn a_repeated_key_is_a_coded_error_at_the_repeating_node() {
        let (distinct, _) = anchors([
            (ProvenanceRole::KSequencePayload, 0),
            (ProvenanceRole::KSequencePayload, 1),
            (ProvenanceRole::MapPayload, 0),
        ]);
        assert!(repeated_key(&distinct).is_none());

        let (repeated, spans) = anchors([
            (ProvenanceRole::KSequencePayload, 0),
            (ProvenanceRole::MapPayload, 0),
            (ProvenanceRole::KSequencePayload, 0),
        ]);
        let error = repeated_key(&repeated).unwrap();
        let diagnostics = error.diagnostics().collect::<Vec<_>>();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].code, expand::DUPLICATE_PROVENANCE_KEY);
        assert_eq!(
            diagnostics[0].message,
            "internal KRS error: this node repeats the provenance key `k_sequence_payload 0` of an earlier node in the same sentence; this is a bug in KRS, not in the definition"
        );
        let Location::Span(span) = diagnostics[0].primary.location else {
            panic!("the error has a span");
        };
        assert_eq!(span.start(), spans[2].start());

        // The error replaces the authored anchors.
        let environment = FixedEnvironment::new("src/lib.rs", "k");
        let tokens = host_provenance(
            &environment,
            &environment.facade,
            TokenRange::new(spans[0], spans[2]),
            &repeated,
        )
        .to_string();
        assert!(tokens.contains("compile_error"), "{tokens}");
        assert!(
            tokens.contains("[krs::expand::duplicate-provenance-key]"),
            "{tokens}"
        );
        assert!(!tokens.contains("KSequencePayload"), "{tokens}");
        let accepted = host_provenance(
            &environment,
            &environment.facade,
            TokenRange::new(spans[0], spans[2]),
            &distinct,
        )
        .to_string();
        assert!(accepted.contains("KSequencePayload"), "{accepted}");
    }
}
