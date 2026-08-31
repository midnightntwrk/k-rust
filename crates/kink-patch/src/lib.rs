//! Original-relative typed patch algebra over the frozen portable v1 slice.
//!
//! This crate applies supplied patches only. It does not discover mutation
//! sites and it never promotes locally checked portable output to native proof.

mod apply;
mod model;

pub use apply::{
    AppliedPatch, NativeIrValidation, NativeTransactionFailure, NativeValidatedPatch,
    NativeValidationRejection, NativeValidationRejectionKind, PatchFailure, PatchFailureKind,
    PortableApplication, StagedNativeInput, apply_patch, apply_patch_with_native_validation,
};
pub use model::{
    Edit, EditValue, InsertPosition, InsertPositionKind, Operation, Patch, PatchModelError,
    PatchModelErrorKind, PathStep, TypedPath,
};
