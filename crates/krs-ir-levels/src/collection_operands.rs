//! Typed operands of Map, List, and Set terms, one variant per catalog operation.
//!
//! Each enum stores exactly the operands its operation takes, so a collection
//! term cannot have the wrong arity. [`MapOperands::operands`] and its List and
//! Set counterparts traverse operands in wire order: the order of the
//! serialized `arguments` array, which source-map child paths also follow.

use std::error::Error;
use std::fmt;

use krs_ir::{ListOperation, MapOperation, NonEmpty, SetOperation};

/// A collection operation received the wrong number of operands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CollectionArityError {
    /// A Map operation.
    Map {
        /// The operation.
        operation: MapOperation,
        /// The number of operands received.
        operands: usize,
    },
    /// A List operation.
    List {
        /// The operation.
        operation: ListOperation,
        /// The number of operands received.
        operands: usize,
    },
    /// A Set operation.
    Set {
        /// The operation.
        operation: SetOperation,
        /// The number of operands received.
        operands: usize,
    },
}

impl fmt::Display for CollectionArityError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Map {
                operation,
                operands,
            } => write!(
                formatter,
                "the {operation} operation has invalid arity {operands}"
            ),
            Self::List {
                operation,
                operands,
            } => write!(
                formatter,
                "the {operation} operation has invalid arity {operands}"
            ),
            Self::Set {
                operation,
                operands,
            } => write!(
                formatter,
                "the {operation} operation has invalid arity {operands}"
            ),
        }
    }
}

impl Error for CollectionArityError {}

fn exact<const N: usize, T>(operands: Vec<T>) -> Option<[T; N]> {
    operands.try_into().ok()
}

fn entries<T>(operands: Vec<T>) -> Option<NonEmpty<MapEntry<T>>> {
    let mut operands = operands.into_iter();
    let mut entries = Vec::new();
    while let Some(key) = operands.next() {
        let value = operands.next()?;
        entries.push(MapEntry { key, value });
    }
    let mut entries = entries.into_iter();
    let first = entries.next()?;
    Some(NonEmpty::new(first, entries.collect()))
}

/// One key/value item of a Map term.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MapEntry<T> {
    /// The key.
    pub key: T,
    /// The value.
    pub value: T,
}

/// Typed operands of a Map term.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MapOperands<T> {
    /// `.Map`.
    Empty,
    /// One or more key/value items, juxtaposed.
    Items(NonEmpty<MapEntry<T>>),
    /// `map [ key <- value ]`.
    Update {
        /// The updated map.
        map: T,
        /// The updated key.
        key: T,
        /// The new value.
        value: T,
    },
    /// `map [ key ]`, projected to the expected sort.
    Get {
        /// The looked-up map.
        map: T,
        /// The looked-up key.
        key: T,
    },
    /// `key in_keys(map)`.
    InKeys {
        /// The tested key.
        key: T,
        /// The tested map.
        map: T,
    },
}

impl<T> MapOperands<T> {
    /// Builds typed operands from operands in wire order.
    ///
    /// # Errors
    ///
    /// Returns [`CollectionArityError::Map`] when the count does not fit the
    /// operation: `Item` takes a nonzero even count, every other operation its
    /// catalog arity.
    pub fn from_operands(
        operation: MapOperation,
        operands: Vec<T>,
    ) -> Result<Self, CollectionArityError> {
        let count = operands.len();
        match operation {
            MapOperation::Empty => exact(operands).map(|[]| Self::Empty),
            MapOperation::Item => entries(operands).map(Self::Items),
            MapOperation::Update => {
                exact(operands).map(|[map, key, value]| Self::Update { map, key, value })
            }
            MapOperation::Get => exact(operands).map(|[map, key]| Self::Get { map, key }),
            MapOperation::InKeys => exact(operands).map(|[key, map]| Self::InKeys { key, map }),
        }
        .ok_or(CollectionArityError::Map {
            operation,
            operands: count,
        })
    }

    /// Builds the items of a Map term.
    ///
    /// # Errors
    ///
    /// Returns [`CollectionArityError::Map`] for an empty entry list.
    pub fn items(entries: Vec<MapEntry<T>>) -> Result<Self, CollectionArityError> {
        let mut entries = entries.into_iter();
        let first = entries.next().ok_or(CollectionArityError::Map {
            operation: MapOperation::Item,
            operands: 0,
        })?;
        Ok(Self::Items(NonEmpty::new(first, entries.collect())))
    }

    /// Builds the items of a Map term holding one entry.
    #[must_use]
    pub fn entry(key: T, value: T) -> Self {
        Self::Items(NonEmpty::new(MapEntry { key, value }, Vec::new()))
    }

    /// Returns the catalog operation.
    #[must_use]
    pub const fn operation(&self) -> MapOperation {
        match self {
            Self::Empty => MapOperation::Empty,
            Self::Items(_) => MapOperation::Item,
            Self::Update { .. } => MapOperation::Update,
            Self::Get { .. } => MapOperation::Get,
            Self::InKeys { .. } => MapOperation::InKeys,
        }
    }

    /// Traverses operands in wire order; items yield each key, then its value.
    pub fn operands(&self) -> impl Iterator<Item = &T> {
        let (fixed, entries) = match self {
            Self::Empty => ([None, None, None], None),
            Self::Items(entries) => ([None, None, None], Some(entries)),
            Self::Update { map, key, value } => ([Some(map), Some(key), Some(value)], None),
            Self::Get { map, key } => ([Some(map), Some(key), None], None),
            Self::InKeys { key, map } => ([Some(key), Some(map), None], None),
        };
        fixed.into_iter().flatten().chain(
            entries
                .into_iter()
                .flat_map(|entries| entries.iter().flat_map(|entry| [&entry.key, &entry.value])),
        )
    }

    /// Consumes the operands in wire order.
    #[must_use]
    pub fn into_operands(self) -> Vec<T> {
        match self {
            Self::Empty => Vec::new(),
            Self::Items(entries) => entries
                .into_iter()
                .flat_map(|entry| [entry.key, entry.value])
                .collect(),
            Self::Update { map, key, value } => vec![map, key, value],
            Self::Get { map, key } => vec![map, key],
            Self::InKeys { key, map } => vec![key, map],
        }
    }

    /// Maps every operand in wire order without changing the operation.
    ///
    /// # Errors
    ///
    /// Returns the first mapping error.
    pub fn try_map_ref<U, E>(
        &self,
        mut map: impl FnMut(&T) -> Result<U, E>,
    ) -> Result<MapOperands<U>, E> {
        Ok(match self {
            Self::Empty => MapOperands::Empty,
            Self::Items(entries) => MapOperands::Items(entries.try_map_ref(|entry| {
                Ok(MapEntry {
                    key: map(&entry.key)?,
                    value: map(&entry.value)?,
                })
            })?),
            Self::Update {
                map: base,
                key,
                value,
            } => MapOperands::Update {
                map: map(base)?,
                key: map(key)?,
                value: map(value)?,
            },
            Self::Get { map: base, key } => MapOperands::Get {
                map: map(base)?,
                key: map(key)?,
            },
            Self::InKeys { key, map: base } => MapOperands::InKeys {
                key: map(key)?,
                map: map(base)?,
            },
        })
    }
}

/// Typed operands of a List term.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ListOperands<T> {
    /// `.List`.
    Empty,
    /// `ListItem(element)`.
    Item {
        /// The element.
        element: T,
    },
    /// `left right`.
    Concat {
        /// The left list.
        left: T,
        /// The right list.
        right: T,
    },
    /// `list [ index ]`, projected to the expected sort.
    Get {
        /// The looked-up list.
        list: T,
        /// The index.
        index: T,
    },
    /// `list [ index <- value ]`.
    Update {
        /// The updated list.
        list: T,
        /// The index.
        index: T,
        /// The new element.
        value: T,
    },
    /// `size(list)`.
    Size {
        /// The measured list.
        list: T,
    },
    /// `makeList(length, value)`.
    Make {
        /// The length.
        length: T,
        /// The repeated element.
        value: T,
    },
    /// `range(list, from_front, from_back)`.
    Range {
        /// The trimmed list.
        list: T,
        /// The number of elements trimmed from the front.
        from_front: T,
        /// The number of elements trimmed from the back.
        from_back: T,
    },
    /// `updateList(list, index, replacement)`.
    UpdateAll {
        /// The updated list.
        list: T,
        /// The first replaced index.
        index: T,
        /// The replacement list.
        replacement: T,
    },
}

impl<T> ListOperands<T> {
    /// Builds typed operands from operands in wire order.
    ///
    /// # Errors
    ///
    /// Returns [`CollectionArityError::List`] when the count is not the operation's catalog arity.
    pub fn from_operands(
        operation: ListOperation,
        operands: Vec<T>,
    ) -> Result<Self, CollectionArityError> {
        let count = operands.len();
        match operation {
            ListOperation::Empty => exact(operands).map(|[]| Self::Empty),
            ListOperation::Item => exact(operands).map(|[element]| Self::Item { element }),
            ListOperation::Concat => {
                exact(operands).map(|[left, right]| Self::Concat { left, right })
            }
            ListOperation::Get => exact(operands).map(|[list, index]| Self::Get { list, index }),
            ListOperation::Update => {
                exact(operands).map(|[list, index, value]| Self::Update { list, index, value })
            }
            ListOperation::Size => exact(operands).map(|[list]| Self::Size { list }),
            ListOperation::Make => {
                exact(operands).map(|[length, value]| Self::Make { length, value })
            }
            ListOperation::Range => {
                exact(operands).map(|[list, from_front, from_back]| Self::Range {
                    list,
                    from_front,
                    from_back,
                })
            }
            ListOperation::UpdateAll => {
                exact(operands).map(|[list, index, replacement]| Self::UpdateAll {
                    list,
                    index,
                    replacement,
                })
            }
        }
        .ok_or(CollectionArityError::List {
            operation,
            operands: count,
        })
    }

    /// Returns the catalog operation.
    #[must_use]
    pub const fn operation(&self) -> ListOperation {
        match self {
            Self::Empty => ListOperation::Empty,
            Self::Item { .. } => ListOperation::Item,
            Self::Concat { .. } => ListOperation::Concat,
            Self::Get { .. } => ListOperation::Get,
            Self::Update { .. } => ListOperation::Update,
            Self::Size { .. } => ListOperation::Size,
            Self::Make { .. } => ListOperation::Make,
            Self::Range { .. } => ListOperation::Range,
            Self::UpdateAll { .. } => ListOperation::UpdateAll,
        }
    }

    /// Traverses operands in wire order.
    pub fn operands(&self) -> impl Iterator<Item = &T> {
        let fixed = match self {
            Self::Empty => [None, None, None],
            Self::Item { element } => [Some(element), None, None],
            Self::Size { list } => [Some(list), None, None],
            Self::Concat { left, right } => [Some(left), Some(right), None],
            Self::Get { list, index } => [Some(list), Some(index), None],
            Self::Make { length, value } => [Some(length), Some(value), None],
            Self::Update { list, index, value } => [Some(list), Some(index), Some(value)],
            Self::Range {
                list,
                from_front,
                from_back,
            } => [Some(list), Some(from_front), Some(from_back)],
            Self::UpdateAll {
                list,
                index,
                replacement,
            } => [Some(list), Some(index), Some(replacement)],
        };
        fixed.into_iter().flatten()
    }

    /// Consumes the operands in wire order.
    #[must_use]
    pub fn into_operands(self) -> Vec<T> {
        match self {
            Self::Empty => Vec::new(),
            Self::Item { element } => vec![element],
            Self::Size { list } => vec![list],
            Self::Concat { left, right } => vec![left, right],
            Self::Get { list, index } => vec![list, index],
            Self::Make { length, value } => vec![length, value],
            Self::Update { list, index, value } => vec![list, index, value],
            Self::Range {
                list,
                from_front,
                from_back,
            } => vec![list, from_front, from_back],
            Self::UpdateAll {
                list,
                index,
                replacement,
            } => vec![list, index, replacement],
        }
    }

    /// Maps every operand in wire order without changing the operation.
    ///
    /// # Errors
    ///
    /// Returns the first mapping error.
    pub fn try_map_ref<U, E>(
        &self,
        mut map: impl FnMut(&T) -> Result<U, E>,
    ) -> Result<ListOperands<U>, E> {
        Ok(match self {
            Self::Empty => ListOperands::Empty,
            Self::Item { element } => ListOperands::Item {
                element: map(element)?,
            },
            Self::Concat { left, right } => ListOperands::Concat {
                left: map(left)?,
                right: map(right)?,
            },
            Self::Get { list, index } => ListOperands::Get {
                list: map(list)?,
                index: map(index)?,
            },
            Self::Update { list, index, value } => ListOperands::Update {
                list: map(list)?,
                index: map(index)?,
                value: map(value)?,
            },
            Self::Size { list } => ListOperands::Size { list: map(list)? },
            Self::Make { length, value } => ListOperands::Make {
                length: map(length)?,
                value: map(value)?,
            },
            Self::Range {
                list,
                from_front,
                from_back,
            } => ListOperands::Range {
                list: map(list)?,
                from_front: map(from_front)?,
                from_back: map(from_back)?,
            },
            Self::UpdateAll {
                list,
                index,
                replacement,
            } => ListOperands::UpdateAll {
                list: map(list)?,
                index: map(index)?,
                replacement: map(replacement)?,
            },
        })
    }
}

/// Typed operands of a Set term.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SetOperands<T> {
    /// `.Set`.
    Empty,
    /// `SetItem(element)`.
    Item {
        /// The element.
        element: T,
    },
    /// `left right`, on disjoint sets.
    Concat {
        /// The left set.
        left: T,
        /// The right set.
        right: T,
    },
    /// `left |Set right`.
    Union {
        /// The left set.
        left: T,
        /// The right set.
        right: T,
    },
    /// `element in set`.
    Contains {
        /// The tested element.
        element: T,
        /// The tested set.
        set: T,
    },
}

impl<T> SetOperands<T> {
    /// Builds typed operands from operands in wire order.
    ///
    /// # Errors
    ///
    /// Returns [`CollectionArityError::Set`] when the count is not the operation's catalog arity.
    pub fn from_operands(
        operation: SetOperation,
        operands: Vec<T>,
    ) -> Result<Self, CollectionArityError> {
        let count = operands.len();
        match operation {
            SetOperation::Empty => exact(operands).map(|[]| Self::Empty),
            SetOperation::Item => exact(operands).map(|[element]| Self::Item { element }),
            SetOperation::Concat => {
                exact(operands).map(|[left, right]| Self::Concat { left, right })
            }
            SetOperation::Union => exact(operands).map(|[left, right]| Self::Union { left, right }),
            SetOperation::Contains => {
                exact(operands).map(|[element, set]| Self::Contains { element, set })
            }
        }
        .ok_or(CollectionArityError::Set {
            operation,
            operands: count,
        })
    }

    /// Returns the catalog operation.
    #[must_use]
    pub const fn operation(&self) -> SetOperation {
        match self {
            Self::Empty => SetOperation::Empty,
            Self::Item { .. } => SetOperation::Item,
            Self::Concat { .. } => SetOperation::Concat,
            Self::Union { .. } => SetOperation::Union,
            Self::Contains { .. } => SetOperation::Contains,
        }
    }

    /// Traverses operands in wire order.
    pub fn operands(&self) -> impl Iterator<Item = &T> {
        let fixed = match self {
            Self::Empty => [None, None],
            Self::Item { element } => [Some(element), None],
            Self::Concat { left, right } | Self::Union { left, right } => [Some(left), Some(right)],
            Self::Contains { element, set } => [Some(element), Some(set)],
        };
        fixed.into_iter().flatten()
    }

    /// Consumes the operands in wire order.
    #[must_use]
    pub fn into_operands(self) -> Vec<T> {
        match self {
            Self::Empty => Vec::new(),
            Self::Item { element } => vec![element],
            Self::Concat { left, right } | Self::Union { left, right } => vec![left, right],
            Self::Contains { element, set } => vec![element, set],
        }
    }

    /// Maps every operand in wire order without changing the operation.
    ///
    /// # Errors
    ///
    /// Returns the first mapping error.
    pub fn try_map_ref<U, E>(
        &self,
        mut map: impl FnMut(&T) -> Result<U, E>,
    ) -> Result<SetOperands<U>, E> {
        Ok(match self {
            Self::Empty => SetOperands::Empty,
            Self::Item { element } => SetOperands::Item {
                element: map(element)?,
            },
            Self::Concat { left, right } => SetOperands::Concat {
                left: map(left)?,
                right: map(right)?,
            },
            Self::Union { left, right } => SetOperands::Union {
                left: map(left)?,
                right: map(right)?,
            },
            Self::Contains { element, set } => SetOperands::Contains {
                element: map(element)?,
                set: map(set)?,
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn operands_round_trip_in_wire_order_for_every_operation() {
        for operation in MapOperation::ALL {
            let count = if operation == MapOperation::Item {
                4
            } else {
                operation.spec().arity()
            };
            let operands: Vec<usize> = (0..count).collect();
            let typed = MapOperands::from_operands(operation, operands.clone()).unwrap();
            assert_eq!(typed.operation(), operation);
            assert_eq!(typed.operands().copied().collect::<Vec<_>>(), operands);
            let mut visited = Vec::new();
            let mapped = typed
                .try_map_ref(|operand| {
                    visited.push(*operand);
                    Ok::<_, ()>(*operand)
                })
                .unwrap();
            assert_eq!(visited, operands);
            assert_eq!(mapped.into_operands(), operands);
        }
        for operation in ListOperation::ALL {
            let operands: Vec<usize> = (0..operation.spec().arity()).collect();
            let typed = ListOperands::from_operands(operation, operands.clone()).unwrap();
            assert_eq!(typed.operation(), operation);
            assert_eq!(typed.operands().copied().collect::<Vec<_>>(), operands);
            let mut visited = Vec::new();
            let mapped = typed
                .try_map_ref(|operand| {
                    visited.push(*operand);
                    Ok::<_, ()>(*operand)
                })
                .unwrap();
            assert_eq!(visited, operands);
            assert_eq!(mapped.into_operands(), operands);
        }
        for operation in SetOperation::ALL {
            let operands: Vec<usize> = (0..operation.spec().arity()).collect();
            let typed = SetOperands::from_operands(operation, operands.clone()).unwrap();
            assert_eq!(typed.operation(), operation);
            assert_eq!(typed.operands().copied().collect::<Vec<_>>(), operands);
            let mut visited = Vec::new();
            let mapped = typed
                .try_map_ref(|operand| {
                    visited.push(*operand);
                    Ok::<_, ()>(*operand)
                })
                .unwrap();
            assert_eq!(visited, operands);
            assert_eq!(mapped.into_operands(), operands);
        }
    }

    #[test]
    fn wrong_operand_counts_are_rejected() {
        assert_eq!(
            MapOperands::from_operands(MapOperation::Empty, vec![1]),
            Err(CollectionArityError::Map {
                operation: MapOperation::Empty,
                operands: 1
            })
        );
        for count in [0, 1, 3] {
            assert!(MapOperands::from_operands(MapOperation::Item, vec![0; count]).is_err());
        }
        assert!(MapOperands::<u8>::items(Vec::new()).is_err());
        assert!(ListOperands::from_operands(ListOperation::Get, vec![0]).is_err());
        assert!(SetOperands::from_operands(SetOperation::Contains, vec![0, 1, 2]).is_err());
        assert_eq!(
            CollectionArityError::List {
                operation: ListOperation::Get,
                operands: 1
            }
            .to_string(),
            "the List lookup operation has invalid arity 1"
        );
    }
}
