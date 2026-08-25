use span_probe_macros::{
    callsite_duplicate_path, duplicated_source_path, payload_probe, probe, single_path,
};

pub mod model {
    pub trait Expr {}

    pub struct Term<T: ?Sized>(pub core::marker::PhantomData<T>);
    pub struct Foo(pub u8);

    pub mod nested {
        pub struct Bar;
    }

    pub const fn wrap(_bar: nested::Bar) -> Term<dyn Expr> {
        Term(core::marker::PhantomData)
    }
}

#[probe(path = model::Expr)]
#[rustfmt::skip]
pub fn rewrite(model::Foo(value): model::Term<dyn model::Expr>) -> model::Term<dyn model::Expr> {
    let 日本 = value; let _ = 日本; model::wrap(model::nested::Bar)
}

pub static PAYLOAD_PROVENANCE: span_probe_model::CapturedRange =
    payload_probe!(model::nested::Bar);

pub fn lsp_single() {
    single_path!(model::nested::Bar);
}

pub fn lsp_duplicated_source() {
    duplicated_source_path!(model::nested::Bar);
}

pub fn lsp_callsite_duplicate() {
    callsite_duplicate_path!(model::nested::Bar);
}

#[cfg(test)]
mod tests {
    use super::*;
    use span_probe_model::byte_range;

    #[test]
    fn stable_locations_recover_every_authored_range() {
        let source = include_str!("lib.rs");
        let expected = [
            ("attribute argument path", "model::Expr"),
            ("refutable parameter pattern", "model::Foo(value)"),
            ("parameter type", "model::Term<dyn model::Expr>"),
            ("nested body path", "model::nested::Bar"),
            ("function-like macro payload path", "model::nested::Bar"),
        ];
        let captured = REWRITE_PROVENANCE
            .iter()
            .copied()
            .chain(core::iter::once(PAYLOAD_PROVENANCE));
        for (range, (label, text)) in captured.zip(expected) {
            assert_eq!(range.label, label);
            assert!(range.display_file.ends_with("crates/accepted/src/lib.rs"));
            assert!(range.had_local_file);
            assert_eq!(range.proc_macro2_start.line, range.start.line);
            assert_eq!(range.proc_macro2_start.column + 1, range.start.column);
            assert_eq!(range.proc_macro2_end.line, range.end.line);
            assert_eq!(range.proc_macro2_end.column + 1, range.end.column);
            assert_eq!(range.proc_macro2_first_byte_range, (0, 0));
            assert_eq!(range.proc_macro2_last_byte_range, (0, 0));
            assert!(!range.proc_macro2_join_succeeded);
            let bytes = byte_range(source, range).expect("valid stable source coordinates");
            assert_eq!(&source[bytes], text, "{}", range.label);
        }
    }
}

