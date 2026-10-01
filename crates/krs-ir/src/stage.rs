//! Reference identities and generated transport traversals across pipeline stages.

use std::fmt::Debug;

/// Reference representations used by one transport stage.
/// Host references remain process-local and need not implement serde.
pub trait Stage: Clone + Debug {
    /// A sort occurrence with provenance.
    type Sort: Clone + Debug;
    /// An application head occurrence with provenance.
    type Application: Clone + Debug;
    /// A nominal declaration identity.
    type Nominal: Clone + Debug;
    /// A context-alias occurrence with provenance.
    type ContextAlias: Clone + Debug;
    /// A configuration occurrence with provenance.
    type Configuration: Clone + Debug;
    /// A selected cell occurrence with provenance.
    type Cell: Clone + Debug;
    /// An extra-cell selection in a readable head rule.
    type HeadRuleCell: Clone + Debug;
    /// An item identity.
    type Item: Clone + Debug;
    /// A nominal nested-cell occurrence with provenance.
    type CellDeclaration: Clone + Debug;
    /// The owner of a paired initializer.
    type InitializerOwner: Clone + Debug;
    /// A direct parent-sort reference.
    type Parent: Clone + Debug;
    /// The ordered or canonical collection of direct parent references.
    type Parents: Clone + Debug + IntoIterator<Item = Self::Parent> + FromIterator<Self::Parent>;
    /// The result-sort reference in a constructor declaration.
    type ConstructorSort: Clone + Debug;
    /// The declared field-sort reference in a constructor declaration.
    type ConstructorFieldSort: Clone + Debug;

    /// Whether an unresolved constructor field sort is omitted from JSON.
    fn skip_constructor_field_sort(value: &Self::ConstructorFieldSort) -> bool;

    /// Whether an absent optional field is omitted in this stage's JSON.
    fn skip_none<T>(value: &Option<T>) -> bool;
}

/// Static indexed references emitted by macros.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WireStage;
/// Build-local Rust references used by the collector.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct HostStage;
/// Stable references written into descriptor bundles.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DescriptorStage;

impl Stage for WireStage {
    type Sort = crate::wire::WireSortReference;
    type Application = crate::wire::WireApplicationReference;
    type Nominal = crate::wire::WireTypeReference;
    type ContextAlias = crate::wire::WireContextAliasReference;
    type Configuration = crate::wire::WireConfigurationReference;
    type Cell = crate::wire::WireHeadRuleCellReference;
    type HeadRuleCell = crate::wire::WireHeadRuleCellReference;
    type Item = usize;
    type CellDeclaration = crate::wire::WireTypeReference;
    type InitializerOwner = crate::wire::WireTypeReference;
    type Parent = crate::wire::WireTypeReference;
    type Parents = Vec<Self::Parent>;
    type ConstructorSort = crate::wire::WireSortReference;
    type ConstructorFieldSort = crate::wire::WireTypeReference;

    fn skip_constructor_field_sort(_: &Self::ConstructorFieldSort) -> bool {
        false
    }
    fn skip_none<T>(_: &Option<T>) -> bool {
        false
    }
}
impl Stage for HostStage {
    type Sort = crate::HostSortReference;
    type Application = crate::HostApplicationReference;
    type Nominal = crate::HostTypeReference;
    type ContextAlias = crate::HostContextAliasReference;
    type Configuration = crate::HostConfigurationReference;
    type Cell = crate::HostCellReference;
    type HeadRuleCell = crate::HostHeadRuleCellReference;
    type Item = crate::HostItemId;
    type CellDeclaration = crate::HostCellDeclarationReference;
    type InitializerOwner = crate::HostTypeKey;
    type Parent = crate::HostTypeReference;
    type Parents = Vec<Self::Parent>;
    type ConstructorSort = crate::HostSortReference;
    type ConstructorFieldSort = crate::HostTypeReference;

    fn skip_constructor_field_sort(_: &Self::ConstructorFieldSort) -> bool {
        false
    }
    fn skip_none<T>(_: &Option<T>) -> bool {
        false
    }
}
impl Stage for DescriptorStage {
    type Sort = crate::DescriptorSortReference;
    type Application = crate::DescriptorApplicationReference;
    type Nominal = crate::StableItemId;
    type ContextAlias = crate::DescriptorContextAliasReference;
    type Configuration = crate::DescriptorConfigurationReference;
    type Cell = crate::DescriptorCellReference;
    type HeadRuleCell = crate::DescriptorCellReference;
    type Item = crate::StableItemId;
    type CellDeclaration = crate::DescriptorCellDeclarationReference;
    type InitializerOwner = crate::StableItemId;
    type Parent = crate::StableItemId;
    type Parents = std::collections::BTreeSet<Self::Parent>;
    type ConstructorSort = crate::DescriptorSortRef;
    type ConstructorFieldSort = Option<crate::DescriptorSortRef>;

    fn skip_constructor_field_sort(value: &Self::ConstructorFieldSort) -> bool {
        value.is_none()
    }
    fn skip_none<T>(value: &Option<T>) -> bool {
        value.is_none()
    }
}

/// Fallible resolution of references between transport stages.
/// Structural traversal is generated from each shape's declaration.
pub trait RefMap<From: Stage, To: Stage> {
    /// Reference-resolution failure.
    type Error;
    /// Maps a sort occurrence.
    ///
    /// # Errors
    ///
    /// Returns the implementation's error when reference mapping fails.
    fn sort(&mut self, reference: From::Sort) -> Result<To::Sort, Self::Error>;
    /// Maps an application occurrence.
    ///
    /// # Errors
    ///
    /// Returns the implementation's error when reference mapping fails.
    fn application(&mut self, reference: From::Application)
    -> Result<To::Application, Self::Error>;
    /// Maps a nominal declaration identity.
    ///
    /// # Errors
    ///
    /// Returns the implementation's error when reference mapping fails.
    fn nominal(&mut self, reference: From::Nominal) -> Result<To::Nominal, Self::Error>;
    /// Maps a context-alias occurrence.
    ///
    /// # Errors
    ///
    /// Returns the implementation's error when reference mapping fails.
    fn context_alias(
        &mut self,
        reference: From::ContextAlias,
    ) -> Result<To::ContextAlias, Self::Error>;
    /// Maps a configuration occurrence.
    ///
    /// # Errors
    ///
    /// Returns the implementation's error when reference mapping fails.
    fn configuration(
        &mut self,
        reference: From::Configuration,
    ) -> Result<To::Configuration, Self::Error>;
    /// Maps a selected cell occurrence.
    ///
    /// # Errors
    ///
    /// Returns the implementation's error when reference mapping fails.
    fn cell(&mut self, reference: From::Cell) -> Result<To::Cell, Self::Error>;
    /// Maps a readable head-rule cell selection.
    ///
    /// # Errors
    ///
    /// Returns the implementation's error when reference mapping fails.
    fn head_rule_cell(
        &mut self,
        reference: From::HeadRuleCell,
    ) -> Result<To::HeadRuleCell, Self::Error>;
    /// Maps an item identity.
    ///
    /// # Errors
    ///
    /// Returns the implementation's error when reference mapping fails.
    fn item(&mut self, reference: From::Item) -> Result<To::Item, Self::Error>;
    /// Maps a nominal nested-cell occurrence.
    ///
    /// # Errors
    ///
    /// Returns the implementation's error when reference mapping fails.
    fn cell_declaration(
        &mut self,
        reference: From::CellDeclaration,
    ) -> Result<To::CellDeclaration, Self::Error>;
    /// Maps a paired initializer owner.
    ///
    /// # Errors
    ///
    /// Returns the implementation's error when reference mapping fails.
    fn initializer_owner(
        &mut self,
        reference: From::InitializerOwner,
    ) -> Result<To::InitializerOwner, Self::Error>;
    /// Maps a direct parent-sort reference.
    ///
    /// # Errors
    ///
    /// Returns the implementation's error when reference mapping fails.
    fn parent(&mut self, reference: From::Parent) -> Result<To::Parent, Self::Error>;
    /// Maps a constructor's result-sort reference.
    ///
    /// # Errors
    ///
    /// Returns the implementation's error when reference mapping fails.
    fn constructor_sort(
        &mut self,
        reference: From::ConstructorSort,
    ) -> Result<To::ConstructorSort, Self::Error>;
    /// Maps a constructor field's declared sort.
    ///
    /// # Errors
    ///
    /// Returns the implementation's error when reference mapping fails.
    fn constructor_field_sort(
        &mut self,
        reference: From::ConstructorFieldSort,
    ) -> Result<To::ConstructorFieldSort, Self::Error>;
}

// Every field declares its mapping beside its type, including invariant fields.
macro_rules! stage_shape {
    ($(#[$attr:meta])* pub enum $name:ident<$s:ident: Stage, $extra:ident => $mapper:ident => $target:ident> {
        $($(#[$variant_attr:meta])* $variant:ident($value:ident: $ty:ty => [$($mapping:tt)+])),* $(,)?
    }) => {
        $(#[$attr])* pub enum $name<$s: $crate::Stage, $extra> {
            $($(#[$variant_attr])* $variant($ty)),*
        }
        $crate::stage::descriptor_shape_traits! {
            enum $name<$extra> { $($variant($value)),* }
        }
        impl<$s: $crate::Stage, $extra> $name<$s, $extra> {
            /// Resolves references and maps the stage-specific completed head-rule shape.
            /// # Errors
            /// Returns the first resolution or head-rule completion error.
            pub fn try_map_refs<To: $crate::Stage, $target, M: $crate::RefMap<$s, To>>(
                self, map: &mut M,
                $mapper: &mut impl FnMut($extra, &mut M) -> Result<$target, M::Error>,
            ) -> Result<$name<To, $target>, M::Error> {
                Ok(match self { $(Self::$variant($value) =>
                    $name::$variant(stage_shape!(@map [$($mapping)+] $value map))),* })
            }
        }
    };

    ($(#[$attr:meta])* pub struct $name:ident<$s:ident: Stage> {
        $($(#[$field_attr:meta])* pub $field:ident: $ty:ty => [$($mapping:tt)+]),* $(,)?
    }) => {
        $(#[$attr])* pub struct $name<$s: $crate::Stage> {
            $($(#[$field_attr])* pub $field: $ty),*
        }
        $crate::stage::descriptor_shape_traits! { struct $name { $($field),* } }
        impl<$s: $crate::Stage> $name<$s> {
            /// Resolves every reference in declaration order.
            /// # Errors
            /// Returns the first reference-resolution error.
            pub fn try_map_refs<To: $crate::Stage, M: $crate::RefMap<$s, To>>(
                self, map: &mut M,
            ) -> Result<$name<To>, M::Error> {
                Ok($name { $($field: stage_shape!(@map [$($mapping)+] (self.$field) map)),* })
            }
        }
    };
    ($(#[$attr:meta])* pub enum $name:ident<$s:ident: Stage> {
        $($(#[$variant_attr:meta])* $variant:ident
          $(($value:ident: $value_ty:ty => [$($value_map:tt)+]))?
          $({ $($(#[$field_attr:meta])* $field:ident: $ty:ty => [$($mapping:tt)+]),* $(,)? })?
        ),* $(,)?
    }) => {
        $(#[$attr])* pub enum $name<$s: $crate::Stage> {
            $($(#[$variant_attr])* $variant $(($value_ty))? $({ $($(#[$field_attr])* $field: $ty),* })?),*
        }
        $crate::stage::descriptor_shape_traits! {
            enum $name { $($variant $(($value))? $({ $($field),* })?),* }
        }
        impl<$s: $crate::Stage> $name<$s> {
            /// Resolves every reference in the selected variant in declaration order.
            /// # Errors
            /// Returns the first reference-resolution error.
            pub fn try_map_refs<To: $crate::Stage, M: $crate::RefMap<$s, To>>(
                self, map: &mut M,
            ) -> Result<$name<To>, M::Error> {
                Ok(match self { $(Self::$variant $(($value))? $({ $($field),* })? =>
                    $name::$variant $((stage_shape!(@map [$($value_map)+] $value map)))?
                        $({ $($field: stage_shape!(@map [$($mapping)+] $field map)),* })?),* })
            }
        }
    };
    (@map [keep] $value:expr, $map:ident) => { $value };
    (@map [keep] $value:tt $map:ident) => { $value };
    (@map [box $($inner:tt)+] $value:tt $map:ident) => { Box::new(stage_shape!(@map [$($inner)+] (*$value) $map)) };
    (@map [vec $($inner:tt)+] $value:tt $map:ident) => { $value.into_iter().map(|value| Ok(stage_shape!(@map [$($inner)+] value $map))).collect::<Result<Vec<_>, M::Error>>()? };
    (@map [option $($inner:tt)+] $value:tt $map:ident) => { $value.map(|value| Ok(stage_shape!(@map [$($inner)+] value $map))).transpose()? };
    (@map [nested] $value:tt $map:ident) => { $value.try_map_refs($map)? };
    (@map [protocol $($inner:ident)+] $value:tt $map:ident) => { $value.try_map_refs($map, $(&mut |value, map| Ok(stage_shape!(@map [$inner] value map))),+)? };
    (@map [via $function:ident] $value:tt $map:ident) => { $function($value, $map)? };
    (@map [with ($($function:ident)::+) $from:ident] $value:tt $map:ident) => { $($function)::+ :: <$from, _, _>($value, $map)? };
    (@map [with $function:path] $value:tt $map:ident) => { $function($value, $map)? };
    (@map [parents] $value:tt $map:ident) => { $value.into_iter().map(|value| $map.parent(value)).collect::<Result<To::Parents, M::Error>>()? };
    (@map [$method:ident] $value:tt $map:ident) => { $map.$method($value)? };
}
pub(crate) use stage_shape;

// Descriptor references support structural comparison; host references need not do so.
macro_rules! descriptor_shape_traits {
    (struct $name:ident { $($field:ident),* $(,)? }) => {
        impl std::cmp::PartialEq for $name<$crate::DescriptorStage> {
            fn eq(&self, other: &Self) -> bool {
                $(self.$field == other.$field)&&*
            }
        }
        impl std::cmp::Eq for $name<$crate::DescriptorStage> {}
        impl std::cmp::Ord for $name<$crate::DescriptorStage> {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                std::cmp::Ordering::Equal
                    $(.then_with(|| std::cmp::Ord::cmp(&self.$field, &other.$field)))*
            }
        }
        impl std::cmp::PartialOrd for $name<$crate::DescriptorStage> {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(std::cmp::Ord::cmp(self, other))
            }
        }
        impl std::hash::Hash for $name<$crate::DescriptorStage> {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                $(std::hash::Hash::hash(&self.$field, state);)*
            }
        }
    };
    (enum $name:ident $(<$extra:ident>)? {
        $($variant:ident $(($value:ident))? $({ $($field:ident),* })?),* $(,)?
    }) => {
        impl $(<$extra>)? $name<$crate::DescriptorStage $(, $extra)?> {
            fn descriptor_variant_order(&self) -> usize {
                #[repr(usize)]
                enum VariantOrder { $($variant),* }
                match self {
                    $(Self::$variant
                        $(($crate::stage::descriptor_shape_traits!(@ignore $value)))?
                        $({ $($field: _,)* })? => VariantOrder::$variant as usize),*
                }
            }
        }
        impl $(<$extra: std::cmp::PartialEq>)? std::cmp::PartialEq
            for $name<$crate::DescriptorStage $(, $extra)?>
        {
            fn eq(&self, other: &Self) -> bool {
                match self {
                    $(Self::$variant $(($value))? $({ $($field),* })? => {
                        let left = ($($value,)? $($($field,)*)?);
                        match other {
                            Self::$variant $(($value))? $({ $($field),* })? =>
                                left == ($($value,)? $($($field,)*)?),
                            _ => false,
                        }
                    }),*
                }
            }
        }
        impl $(<$extra: std::cmp::Eq>)? std::cmp::Eq
            for $name<$crate::DescriptorStage $(, $extra)?> {}
        impl $(<$extra: std::cmp::Ord>)? std::cmp::Ord
            for $name<$crate::DescriptorStage $(, $extra)?>
        {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                let variant_order = self.descriptor_variant_order().cmp(&other.descriptor_variant_order());
                if variant_order != std::cmp::Ordering::Equal {
                    return variant_order;
                }
                match self {
                    $(Self::$variant $(($value))? $({ $($field),* })? => {
                        let left = ($($value,)? $($($field,)*)?);
                        match other {
                            Self::$variant $(($value))? $({ $($field),* })? =>
                                std::cmp::Ord::cmp(&left, &($($value,)? $($($field,)*)?)),
                            _ => unreachable!("equal variant indices must identify the same variant"),
                        }
                    }),*
                }
            }
        }
        $crate::stage::descriptor_shape_traits! {
            @partial_ord $name $(<$extra>)? { $($variant $(($value))? $({ $($field),* })?),* }
        }
        impl $(<$extra: std::hash::Hash>)? std::hash::Hash
            for $name<$crate::DescriptorStage $(, $extra)?>
        {
            fn hash<Hasher: std::hash::Hasher>(&self, state: &mut Hasher) {
                std::hash::Hash::hash(&std::mem::discriminant(self), state);
                match self {
                    $(Self::$variant $(($value))? $({ $($field),* })? => {
                        $(std::hash::Hash::hash($value, state);)?
                        $($(std::hash::Hash::hash($field, state);)*)?
                    }),*
                }
            }
        }
    };
    (@ignore $identifier:ident) => { _ };
    (@partial_ord $name:ident $(<$extra:ident>)? { $($variants:tt)* }) => {
        impl $(<$extra: std::cmp::Ord>)? std::cmp::PartialOrd
            for $name<$crate::DescriptorStage $(, $extra)?>
        {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(std::cmp::Ord::cmp(self, other))
            }
        }
    };
}
pub(crate) use descriptor_shape_traits;

// Protocol generics retain their parameterized serde names and String probes.
macro_rules! protocol_shape {
    ($(#[$attr:meta])* pub struct $name:ident<$($from:ident => $mapping:ident => $to:ident),+> {
        $($(#[$field_attr:meta])* pub $field:ident: $ty:ty => [$($field_map:tt)+]),* $(,)?
    }) => {
        $(#[$attr])* pub struct $name<$($from),+> { $($(#[$field_attr])* pub $field: $ty),* }
        impl<$($from),+> $name<$($from),+> {
            /// Maps reference-bearing parameters in declaration order.
            /// # Errors
            /// Returns the first error from a supplied mapping function.
            pub fn try_map_refs<$($to),+, E, Context>(self, context: &mut Context,
                $($mapping: &mut impl FnMut($from, &mut Context) -> Result<$to, E>),+
            ) -> Result<$name<$($to),+>, E> {
                Ok($name { $($field: protocol_shape!(@map [$($field_map)+] (self.$field) context)),* })
            }
        }
    };
    ($(#[$attr:meta])* pub enum $name:ident<$($from:ident => $mapping:ident => $to:ident),+> {
        $($(#[$variant_attr:meta])* $variant:ident
          $(($value:ident: $value_ty:ty => [$($value_map:tt)+]))?
          $({ $($(#[$field_attr:meta])* $field:ident: $ty:ty => [$($field_map:tt)+]),* $(,)? })?
        ),* $(,)?
    }) => {
        $(#[$attr])* pub enum $name<$($from),+> {
            $($(#[$variant_attr])* $variant $(($value_ty))? $({ $($(#[$field_attr])* $field: $ty),* })?),*
        }
        impl<$($from),+> $name<$($from),+> {
            /// Maps reference-bearing parameters in the selected variant.
            /// # Errors
            /// Returns the first error from a supplied mapping function.
            pub fn try_map_refs<$($to),+, E, Context>(self, context: &mut Context,
                $($mapping: &mut impl FnMut($from, &mut Context) -> Result<$to, E>),+
            ) -> Result<$name<$($to),+>, E> {
                Ok(match self { $(Self::$variant $(($value))? $({ $($field),* })? =>
                    $name::$variant $((protocol_shape!(@map [$($value_map)+] $value context)))?
                        $({ $($field: protocol_shape!(@map [$($field_map)+] $field context)),* })?),* })
            }
        }
    };
    (@map [keep] $value:tt $context:ident) => { $value };
    (@map [box $($inner:tt)+] $value:tt $context:ident) => { Box::new(protocol_shape!(@map [$($inner)+] (*$value) $context)) };
    (@map [vec $($inner:tt)+] $value:tt $context:ident) => { $value.into_iter().map(|value| Ok(protocol_shape!(@map [$($inner)+] value $context))).collect::<Result<Vec<_>, E>>()? };
    (@map [option $($inner:tt)+] $value:tt $context:ident) => { $value.map(|value| Ok(protocol_shape!(@map [$($inner)+] value $context))).transpose()? };
    (@map [nested $($mapping:ident)+] $value:tt $context:ident) => { $value.try_map_refs($context, $($mapping),+)? };
    (@map [$mapping:ident] $value:tt $context:ident) => { $mapping($value, $context)? };
}
pub(crate) use protocol_shape;

#[cfg(test)]
pub(crate) mod tests {
    use super::{RefMap, Stage};

    #[derive(Default)]
    pub(crate) struct CountingMap {
        pub(crate) calls: Vec<&'static str>,
        pub(crate) fail: Option<&'static str>,
    }
    impl CountingMap {
        fn record<T>(&mut self, name: &'static str, reference: T) -> Result<T, &'static str> {
            self.calls.push(name);
            if self.fail == Some(name) {
                Err(name)
            } else {
                Ok(reference)
            }
        }
    }
    macro_rules! count_refs {
        ($($name:ident: $associated:ident),+ $(,)?) => {
            impl<S: Stage> RefMap<S, S> for CountingMap {
                type Error = &'static str;
                $(fn $name(&mut self, reference: S::$associated) -> Result<S::$associated, Self::Error> {
                    self.record(stringify!($name), reference)
                })+
            }
        };
    }
    count_refs! {
        sort: Sort, application: Application, nominal: Nominal, context_alias: ContextAlias,
        configuration: Configuration, cell: Cell, head_rule_cell: HeadRuleCell, item: Item,
        cell_declaration: CellDeclaration, initializer_owner: InitializerOwner, parent: Parent,
        constructor_sort: ConstructorSort, constructor_field_sort: ConstructorFieldSort,
    }
}
