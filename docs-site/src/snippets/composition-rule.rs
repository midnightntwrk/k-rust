#[k::rule]
pub fn cross_package(
    semantic_base::Same: Term<dyn semantic_base::CommonSort>,
) -> Term<dyn semantic_base::CommonSort> {
    semantic_base::Same
}
