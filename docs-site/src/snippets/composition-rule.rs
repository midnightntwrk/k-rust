#[k::rule]
pub fn cross_package(
    semantic_base::Same: Term<dyn semantic_base::Common>,
) -> Term<dyn semantic_base::Common> {
    semantic_base::Same
}
