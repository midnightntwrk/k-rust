use proc_macro::{Span, TokenStream};

#[proc_macro]
pub fn unavailable_on_stable(_input: TokenStream) -> TokenStream {
    let span = Span::call_site();
    let _ = span.byte_range();
    let _ = span.join(span);
    let _ = span.parent();
    let _ = span.source();
    TokenStream::new()
}

