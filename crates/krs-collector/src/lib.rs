//! Deterministic host descriptor collection for KRS generated collectors.
//!
//! This crate owns the sole conversion from process-local
//! [`krs_ir::HostDescriptor`] values to a serializable
//! [`krs_ir::DescriptorBundle`]. Cargo orchestration remains in `krs-cli`, and
//! adapters consume only the stable bundle or later IRs.

mod collect;
mod error;
mod facade;

pub use collect::{
    PackageContext, collect_host_descriptors, collect_host_descriptors_with_builtins,
    collect_host_descriptors_with_builtins_timed, run_collector,
};
pub use error::{CollectionError, CollectionErrorKind};
pub use facade::{AttributeResolver, FacadeAliases};
