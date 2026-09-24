//! Original-relative typed patch algebra.
//!
//! [`definition`] patches a loaded k-rust definition. The portable model at
//! the crate root is the frozen portable v1 slice, kept until the native
//! validator switches to [`definition`].
//!
//! This crate applies supplied patches only. It does not discover mutation
//! sites and it never promotes locally checked portable output to native proof.

mod apply;
pub mod definition;
mod failure;
mod model;

pub use apply::{
    AppliedPatch, NativeIrValidation, NativeTransactionFailure, NativeValidatedPatch,
    NativeValidationRejection, NativeValidationRejectionKind, PortableApplication,
    StagedNativeInput, apply_patch, apply_patch_with_native_validation,
};
pub use failure::{PatchFailure, PatchFailureKind};
pub use model::{
    Edit, EditValue, InsertPosition, InsertPositionKind, Operation, Patch, PatchModelError,
    PatchModelErrorKind, PathStep, TypedPath,
};
