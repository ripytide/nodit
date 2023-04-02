/*
Copyright 2022 James Forster

This file is part of range_bounds_map.

range_bounds_map is free software: you can redistribute it and/or
modify it under the terms of the GNU Affero General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

range_bounds_map is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with range_bounds_map. If not, see <https://www.gnu.org/licenses/>.
*/

use std::cmp::Ordering;
use std::fmt::{self, Debug};
use std::iter::once;
use std::marker::PhantomData;
use std::ops::{Bound, RangeBounds};

use btree_monstousity::btree_map::SearchBoundCustom;
use btree_monstousity::BTreeMap;
use itertools::Itertools;
use labels::{parent_tested, tested, trivial};
use serde::de::{MapAccess, Visitor};
use serde::ser::SerializeMap;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::bound_ord::BoundOrd;
use crate::helpers::{cmp_range_bounds_with_bound_ord, is_valid_range_bounds};
use crate::TryFromBounds;

/// An ordered map of non-overlapping [`RangeBounds`] based on [`BTreeMap`].
///
/// `I` is the generic type parameter for the [`Ord`] type the `K` type
/// is [`RangeBounds`] over.
///
/// `K` is the generic type parameter for the [`RangeBounds`]
/// implementing type stored as the keys in the map.
///
/// `V` is the generic type parameter for the values associated with the
/// keys in the map.
///
/// # Examples
/// ```
/// use range_bounds_map::RangeBoundsMap;
///
/// // Make a map of ranges to booleans
/// let mut map = RangeBoundsMap::from_slice_strict([
/// 	(4..8, false),
/// 	(8..18, true),
/// 	(20..100, false),
/// ])
/// .unwrap();
///
/// // Change a value in the map
/// *map.get_at_point_mut(&(7)).unwrap() = true;
///
/// if map.contains_point(&99) {
/// 	println!("Map contains value at 99 :)");
/// }
///
/// // Iterate over the entries in the map
/// for (range, value) in map.iter() {
/// 	println!("{range:?}, {value:?}");
/// }
/// ```
/// Example using a custom [`RangeBounds`] type:
/// ```
/// use std::ops::{Bound, RangeBounds};
///
/// use ordered_float::NotNan;
/// use range_bounds_map::RangeBoundsMap;
///
/// // An Exclusive-Exclusive range of [`f32`]s not provided by any
/// // std::ops ranges
/// // We use [`ordered_float::NotNan`]s as the inner type must be Ord
/// // similar to a normal [`BTreeMap`]
/// #[derive(Debug, PartialEq)]
/// struct ExEx {
/// 	start: NotNan<f32>,
/// 	end: NotNan<f32>,
/// }
/// # impl ExEx {
/// #    fn new(start: f32, end: f32) -> ExEx {
/// #        ExEx {
/// #            start: NotNan::new(start).unwrap(),
/// #            end: NotNan::new(end).unwrap(),
/// #        }
/// #    }
/// # }
///
/// // Implement RangeBounds<f32> on our new type
/// impl RangeBounds<NotNan<f32>> for ExEx {
/// 	fn start_bound(&self) -> Bound<&NotNan<f32>> {
/// 		Bound::Excluded(&self.start)
/// 	}
/// 	fn end_bound(&self) -> Bound<&NotNan<f32>> {
/// 		Bound::Excluded(&self.end)
/// 	}
/// }
///
/// // Now we can make a [`RangeBoundsMap`] of [`ExEx`]s to `u8`
/// let mut map = RangeBoundsMap::new();
///
/// map.insert_strict(ExEx::new(0.0, 5.0), 8).unwrap();
/// map.insert_strict(ExEx::new(5.0, 7.5), 32).unwrap();
///
/// assert_eq!(map.contains_point(&NotNan::new(5.0).unwrap()), false);
///
/// assert_eq!(map.get_at_point(&NotNan::new(9.0).unwrap()), None);
/// assert_eq!(
/// 	map.get_at_point(&NotNan::new(7.0).unwrap()),
/// 	Some(&32)
/// );
///
/// assert_eq!(
/// 	map.get_entry_at_point(&NotNan::new(2.0).unwrap()),
/// 	Some((&ExEx::new(0.0, 5.0), &8))
/// );
/// ```
///
/// [`RangeBounds`]: https://doc.rust-lang.org/std/ops/trait.RangeBounds.html
/// [`BTreeMap`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
pub struct RangeBoundsMap<I, K, V> {
	inner: BTreeMap<K, V>,
	phantom: PhantomData<I>,
}

/// An error type to represent a [`RangeBounds`] overlapping another
/// [`RangeBounds`] when it should not have.
#[derive(PartialEq, Debug)]
pub struct OverlapError;

/// An error type to represent a failed [`TryFromBounds`] within a
/// method.
///
/// There are several methods that return this error, and some of the
/// causes of this error can be very subtle, so here are some examples
/// showing all the reasons this error might be returned.
///
/// # Example with [`RangeBoundsMap::cut()`]
///
/// The first way you may recieve [`TryFromBoundsError`] is from
/// [`RangeBoundsMap::cut()`].
///
/// In this example we try to cut `4..=6` out of a `RangeBoundsMap`
/// that contains `2..8`. If this was successful then the
/// `RangeBoundsMap` would hold `2..4` and `(Bound::Exclusive(6),
/// Bound::Exclusive(8))`. However, since the `RangeBounds` type of
/// this `RangeBoundsMap` is `Range<{integer}>` the latter of the two
/// new `RangeBounds` is "unrepresentable", and hence will fail to be
/// created via [`TryFromBounds`] and [`RangeBoundsMap::cut()`] will
/// return Err(TryFromBoundsError).
///
/// ```
/// use range_bounds_map::{RangeBoundsMap, TryFromBoundsError};
///
/// let mut map =
/// 	RangeBoundsMap::from_slice_strict([(2..8, true)]).unwrap();
///
/// assert!(map.cut(&(4..=6)).is_err());
/// ```
///
/// # Example with `insert_merge_*` functions.
///
/// The second and final way you may recieve a [`TryFromBoundsError`]
/// is via coalescing methods such as
/// [`RangeBoundsMap::insert_merge_touching`].
///
/// In the first example it was fairly easy to create an invalid
/// `RangeBounds` by cutting with a different `RangeBounds` than the
/// underlying `RangeBoundsMap`'s `RangeBounds` type. However, the
/// `insert_merge_*` functions all take `range_bounds: K` as an
/// argument so it is not possible to create an invalid `K` type
/// directly. However upon "coalescing" of two `RangeBounds` (even if
/// both of them are type `K`), you can create a `RangeBounds` that *cannot* be
/// of type `K`.
///
/// In this example we use a `RangeBounds` type that can be either
/// Inclusive-Inclusive OR Exclusive-Exclusive. We then try to use
/// [`RangeBoundsMap::insert_merge_touching()`] to "merge" an
/// Inclusive-Inclusive and a Exclusive-Exclusive `MultiBounds`. This
/// will however fail as the resulting "merged" `RangeBounds` would
/// have to be Inclusive-Exclusive which `MultiBounds` does not support.
///
/// ```
/// use std::ops::{Bound, RangeBounds};
///
/// use range_bounds_map::{
/// 	OverlapOrTryFromBoundsError, RangeBoundsMap, TryFromBounds,
/// 	TryFromBoundsError,
/// };
///
/// #[derive(Debug, PartialEq)]
/// enum MultiBounds {
/// 	Inclusive(u8, u8),
/// 	Exclusive(u8, u8),
/// }
///
/// impl RangeBounds<u8> for MultiBounds {
/// 	fn start_bound(&self) -> Bound<&u8> {
/// 		match self {
/// 			MultiBounds::Inclusive(start, _) => {
/// 				Bound::Included(start)
/// 			}
/// 			MultiBounds::Exclusive(start, _) => {
/// 				Bound::Excluded(start)
/// 			}
/// 		}
/// 	}
/// 	fn end_bound(&self) -> Bound<&u8> {
/// 		match self {
/// 			MultiBounds::Inclusive(_, end) => {
/// 				Bound::Included(end)
/// 			}
/// 			MultiBounds::Exclusive(_, end) => {
/// 				Bound::Excluded(end)
/// 			}
/// 		}
/// 	}
/// }
///
/// impl TryFromBounds<u8> for MultiBounds {
/// 	fn try_from_bounds(
/// 		start_bound: Bound<u8>,
/// 		end_bound: Bound<u8>,
/// 	) -> Option<Self> {
/// 		match (start_bound, end_bound) {
/// 			(Bound::Included(start), Bound::Included(end)) => {
/// 				Some(MultiBounds::Inclusive(start, end))
/// 			}
/// 			(Bound::Excluded(start), Bound::Excluded(end)) => {
/// 				Some(MultiBounds::Exclusive(start, end))
/// 			}
/// 			_ => None,
/// 		}
/// 	}
/// }
///
/// let mut map = RangeBoundsMap::from_slice_strict([(
/// 	MultiBounds::Inclusive(2, 4),
/// 	true,
/// )])
/// .unwrap();
///
/// assert_eq!(
/// 	map.insert_merge_touching(
/// 		MultiBounds::Exclusive(4, 6),
/// 		false
/// 	),
/// 	Err(OverlapOrTryFromBoundsError::TryFromBounds(
/// 		TryFromBoundsError
/// 	))
/// );
/// ```
#[derive(PartialEq, Debug)]
pub struct TryFromBoundsError;

/// An error type to represent either an [`OverlapError`] or a
/// [`TryFromBoundsError`].
#[derive(PartialEq, Debug)]
pub enum OverlapOrTryFromBoundsError {
	Overlap(OverlapError),
	TryFromBounds(TryFromBoundsError),
}

impl<I, K, V> RangeBoundsMap<I, K, V>
where
	I: Ord,
	K: RangeBounds<I>,
{
	/// Makes a new, empty `RangeBoundsMap`.
	///
	/// # Examples
	/// ```
	/// use std::ops::Range;
	///
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let map: RangeBoundsMap<u8, Range<u8>, bool> =
	/// 	RangeBoundsMap::new();
	/// ```
	#[trivial]
	pub fn new() -> Self {
		RangeBoundsMap {
			inner: BTreeMap::new(),
			phantom: PhantomData,
		}
	}

	/// Returns the number of `RangeBounds` in the map.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut map = RangeBoundsMap::new();
	///
	/// assert_eq!(map.len(), 0);
	/// map.insert_strict(0..1, false).unwrap();
	/// assert_eq!(map.len(), 1);
	/// ```
	#[trivial]
	pub fn len(&self) -> usize {
		self.inner.len()
	}

	/// Returns `true` if the map contains no `RangeBounds`, and
	/// `false` if it does.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut map = RangeBoundsMap::new();
	///
	/// assert_eq!(map.is_empty(), true);
	/// map.insert_strict(0..1, false).unwrap();
	/// assert_eq!(map.is_empty(), false);
	/// ```
	#[trivial]
	pub fn is_empty(&self) -> bool {
		self.inner.is_empty()
	}

	/// Adds a new (`RangeBounds`, `Value`) entry to the map without
	/// modifying other entries.
	///
	/// If the given `RangeBounds` overlaps one or more `RangeBounds`
	/// already in the map, then an [`OverlapError`] is returned and
	/// the map is not updated.
	///
	/// # Panics
	///
	/// Panics if the given `range_bounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::{OverlapError, RangeBoundsMap};
	///
	/// let mut map = RangeBoundsMap::new();
	///
	/// assert_eq!(map.insert_strict(5..10, 9), Ok(()));
	/// assert_eq!(map.insert_strict(5..10, 2), Err(OverlapError));
	/// assert_eq!(map.len(), 1);
	/// ```
	#[tested]
	pub fn insert_strict(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<(), OverlapError> {
		if self.overlaps((range_bounds.start_bound(), range_bounds.end_bound()))
		{
			return Err(OverlapError);
		}

		let double_comp = |inner_range_bounds: &K, new_range_bounds: &K| {
			let retult = BoundOrd::start(new_range_bounds.start_bound())
				.cmp(&BoundOrd::start(inner_range_bounds.start_bound()));
			retult
		};

		self.inner.insert(range_bounds, value, double_comp);

		return Ok(());
	}

	/// Returns `true` if the given `RangeBounds` overlaps any of the
	/// `RangeBounds` in the map, and `false` if not.
	///
	/// # Panics
	///
	/// Panics if the given `range_bounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut map = RangeBoundsMap::new();
	///
	/// map.insert_strict(5..10, false);
	///
	/// assert_eq!(map.overlaps(&(1..=3)), false);
	/// assert_eq!(map.overlaps(&(4..5)), false);
	///
	/// assert_eq!(map.overlaps(&(4..=5)), true);
	/// assert_eq!(map.overlaps(&(4..6)), true);
	/// ```
	#[trivial]
	pub fn overlaps<Q>(&self, range_bounds: Q) -> bool
	where
		Q: RangeBounds<I>,
	{
		self.overlapping(range_bounds).next().is_some()
	}

	/// Returns an iterator over every (`RangeBounds`, `Value`) entry
	/// in the map which overlap the given `RangeBounds` in
	/// ascending order.
	///
	/// # Panics
	///
	/// Panics if the given `range_bounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let map = RangeBoundsMap::from_slice_strict([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// let mut overlapping = map.overlapping(&(2..8));
	///
	/// assert_eq!(
	/// 	overlapping.collect::<Vec<_>>(),
	/// 	[(&(1..4), &false), (&(4..8), &true)]
	/// );
	/// ```
	#[tested]
	pub fn overlapping<Q>(
		&self,
		range_bounds: Q,
	) -> impl DoubleEndedIterator<Item = (&K, &V)>
	where
		Q: RangeBounds<I>,
	{
		let lower_comp = comp_start(range_bounds.start_bound());
		let upper_comp = comp_end(range_bounds.end_bound());

		let lower_bound = SearchBoundCustom::Included;
		let upper_bound = SearchBoundCustom::Included;

		self.inner
			.range(lower_comp, lower_bound, upper_comp, upper_bound)
	}

	/// Returns a reference to the `Value` corresponding to the
	/// `RangeBounds` in the map that overlaps the given point, if
	/// any.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let map = RangeBoundsMap::from_slice_strict([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(map.get_at_point(&3), Some(&false));
	/// assert_eq!(map.get_at_point(&4), Some(&true));
	/// assert_eq!(map.get_at_point(&101), None);
	/// ```
	#[trivial]
	pub fn get_at_point(&self, point: &I) -> Option<&V> {
		self.get_entry_at_point(point).map(|(key, value)| value)
	}

	/// Returns `true` if the map contains a `RangeBounds` that
	/// overlaps the given point, and `false` if not.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let map = RangeBoundsMap::from_slice_strict([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(map.contains_point(&3), true);
	/// assert_eq!(map.contains_point(&4), true);
	/// assert_eq!(map.contains_point(&101), false);
	/// ```
	#[trivial]
	pub fn contains_point(&self, point: &I) -> bool {
		self.get_entry_at_point(point).is_some()
	}

	/// Returns a mutable reference to the `Value` corresponding to
	/// the `RangeBounds` that overlaps the given point, if any.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut map =
	/// 	RangeBoundsMap::from_slice_strict([(1..4, false)]).unwrap();
	///
	/// if let Some(x) = map.get_at_point_mut(&2) {
	/// 	*x = true;
	/// }
	///
	/// assert_eq!(map.get_at_point(&1), Some(&true));
	/// ```
	#[tested]
	pub fn get_at_point_mut(&mut self, point: &I) -> Option<&mut V> {
		self.inner.get_mut(comp_start(Bound::Included(point)))
	}

	/// Returns an (`RangeBounds`, `Value`) entry corresponding to the
	/// `RangeBounds` that overlaps the given point, if any.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let map = RangeBoundsMap::from_slice_strict([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(map.get_entry_at_point(&3), Some((&(1..4), &false)));
	/// assert_eq!(map.get_entry_at_point(&4), Some((&(4..8), &true)));
	/// assert_eq!(map.get_entry_at_point(&101), None);
	/// ```
	#[trivial]
	pub fn get_entry_at_point(&self, point: &I) -> Option<(&K, &V)> {
        self.inner.get_key_value(comp_start(Bound::Included(point)))
	}

	/// Returns an iterator over every (`RangeBounds`, `Value`) entry
	/// in the map in ascending order.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let map = RangeBoundsMap::from_slice_strict([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// let mut iter = map.iter();
	///
	/// assert_eq!(iter.next(), Some((&(1..4), &false)));
	/// assert_eq!(iter.next(), Some((&(4..8), &true)));
	/// assert_eq!(iter.next(), Some((&(8..100), &false)));
	/// assert_eq!(iter.next(), None);
	/// ```
	//#[trivial]
	//pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&K, &V)> {
	//todo!()
	//}

	/// Removes every (`RangeBounds`, `Value`) entry in the map which
	/// overlaps the given `RangeBounds` and returns them in
	/// an iterator.
	///
	/// # Panics
	///
	/// Panics if the given `range_bounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut map = RangeBoundsMap::from_slice_strict([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// let mut removed = map.remove_overlapping(&(2..8));
	///
	/// assert_eq!(
	/// 	removed.collect::<Vec<_>>(),
	/// 	[(1..4, false), (4..8, true)]
	/// );
	///
	/// assert_eq!(map.iter().collect::<Vec<_>>(), [(&(8..100), &false)]);
	/// ```
	//#[tested]
	//pub fn remove_overlapping<Q>(
	//&mut self,
	//range_bounds: Q,
	//) -> impl DoubleEndedIterator<Item = (K, V)>
	//where
	//Q: RangeBounds<I>,
	//{
	//todo!()
	//}

	/// Cuts a given `RangeBounds` out of the map and returns an
	/// iterator of the full or partial `RangeBounds` that were cut in
	/// as `((Bound, Bound), Value)`.
	///
	/// If the remaining `RangeBounds` left in the map after the cut
	/// are not able be created with the [`TryFromBounds`] trait then
	/// a [`TryFromBoundsError`] will be returned and the map will not
	/// be cut.
	///
	/// `V` must implement `Clone` as if you try to cut out the center
	/// of a `RangeBounds` in the map it will split into two different
	/// (`RangeBounds`, `Value`) entries using `Clone`. Or if you
	/// partially cut a `RangeBounds` then `V` must be cloned to be
	/// returned in the iterator.
	///
	/// # Panics
	///
	/// Panics if the given `range_bounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use std::ops::Bound;
	///
	/// use range_bounds_map::{RangeBoundsMap, TryFromBoundsError};
	///
	/// let mut base = RangeBoundsMap::from_slice_strict([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// let after_cut = RangeBoundsMap::from_slice_strict([
	/// 	(1..2, false),
	/// 	(40..100, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(
	/// 	base.cut(&(2..40)).unwrap().collect::<Vec<_>>(),
	/// 	[
	/// 		((Bound::Included(2), Bound::Excluded(4)), false),
	/// 		((Bound::Included(4), Bound::Excluded(8)), true),
	/// 		((Bound::Included(8), Bound::Excluded(40)), false),
	/// 	]
	/// );
	/// assert_eq!(base, after_cut);
	/// assert!(base.cut(&(60..=80)).is_err());
	/// ```
	//#[tested]
	//pub fn cut<Q>(
	//&mut self,
	//range_bounds: Q,
	//) -> Result<
	//impl DoubleEndedIterator<Item = ((Bound<&I>, Bound<&I>), V)>,
	//TryFromBoundsError,
	//>
	//where
	//Q: RangeBounds<I> + Clone,
	//{
	//todo!()
	//}

	/// Identical to [`RangeBoundsMap::cut()`] except it returns an
	/// iterator of `(Result<RangeBounds, TryFromBoundsError>,
	/// Value)`.
	///
	/// # Panics
	///
	/// Panics if the given `range_bounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::{RangeBoundsMap, TryFromBoundsError};
	///
	/// let mut base = RangeBoundsMap::from_slice_strict([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// let after_cut = RangeBoundsMap::from_slice_strict([
	/// 	(1..2, false),
	/// 	(40..100, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(
	/// 	base.cut_same(&(2..40)).unwrap().collect::<Vec<_>>(),
	/// 	[(Ok(2..4), false), (Ok(4..8), true), (Ok(8..40), false)]
	/// );
	/// assert_eq!(base, after_cut);
	/// assert!(base.cut_same(&(60..=80)).is_err());
	/// ```
	//#[trivial]
	//pub fn cut_same<Q>(
	//&mut self,
	//range_bounds: Q,
	//) -> Result<
	//impl DoubleEndedIterator<Item = (Result<K, TryFromBoundsError>, V)>,
	//TryFromBoundsError,
	//>
	//where
	//Q: RangeBounds<I> + Clone,
	//{
	//todo!()
	//}

	/// Returns an iterator of `(Bound<&I>, Bound<&I>)` over all the
	/// maximally-sized gaps in the map that are also within the given
	/// `outer_range_bounds`.
	///
	/// To get all possible gaps call `gaps()` with an unbounded
	/// `RangeBounds` such as `&(..)` or `&(Bound::Unbounded,
	/// Bound::Unbounded)`.
	///
	/// # Panics
	///
	/// Panics if the given `outer_range_bounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use std::ops::Bound;
	///
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let map = RangeBoundsMap::from_slice_strict([
	/// 	(1..3, false),
	/// 	(5..7, true),
	/// 	(9..100, false),
	/// ])
	/// .unwrap();
	///
	/// let mut gaps = map.gaps(&(2..));
	///
	/// assert_eq!(
	/// 	gaps.collect::<Vec<_>>(),
	/// 	[
	/// 		(Bound::Included(&3), Bound::Excluded(&5)),
	/// 		(Bound::Included(&7), Bound::Excluded(&9)),
	/// 		(Bound::Included(&100), Bound::Unbounded)
	/// 	]
	/// );
	/// ```
	//#[tested]
	//pub fn gaps<Q>(
	//&self,
	//outer_range_bounds: Q,
	//) -> impl Iterator<Item = (Bound<&I>, Bound<&I>)>
	//where
	//Q: RangeBounds<I> + Clone,
	//{
	//todo!()
	//}

	/// Identical to [`RangeBoundsMap::gaps()`] except it returns an
	/// iterator of `Result<RangeBounds, TryFromBoundsError>`.
	///
	/// # Panics
	///
	/// Panics if the given `outer_range_bounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use std::ops::Bound;
	///
	/// use range_bounds_map::{RangeBoundsMap, TryFromBoundsError};
	///
	/// let map = RangeBoundsMap::from_slice_strict([
	/// 	(1..3, false),
	/// 	(5..7, true),
	/// 	(9..100, false),
	/// ])
	/// .unwrap();
	///
	/// let mut gaps_same = map.gaps_same(&(2..));
	///
	/// assert_eq!(
	/// 	gaps_same.collect::<Vec<_>>(),
	/// 	[Ok(3..5), Ok(7..9), Err(TryFromBoundsError),]
	/// );
	/// ```
	//#[trivial]
	//pub fn gaps_same<Q>(
	//&self,
	//outer_range_bounds: Q,
	//) -> impl Iterator<Item = Result<K, TryFromBoundsError>>
	//where
	//Q: RangeBounds<I> + Clone,
	//{
	//todo!()
	//}

	/// Returns `true` if the map covers every point in the given
	/// `RangeBounds`, and `false` if it doesn't.
	///
	/// # Panics
	///
	/// Panics if the given `range_bounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let map = RangeBoundsMap::from_slice_strict([
	/// 	(1..3, false),
	/// 	(5..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(map.contains_range_bounds(&(1..3)), true);
	/// assert_eq!(map.contains_range_bounds(&(2..6)), false);
	/// assert_eq!(map.contains_range_bounds(&(6..50)), true);
	/// ```
	#[trivial]
	pub fn contains_range_bounds<Q>(&self, range_bounds: Q) -> bool
	where
		Q: RangeBounds<I> + Clone,
	{
		todo!()
	}

	/// Adds a new (`RangeBounds`, `Value`) entry to the map and
	/// merges into other `RangeBounds` in the map which touch it.
	///
	/// The `Value` of the merged `RangeBounds` is set to the given
	/// `Value`.
	///
	/// If successful then a reference to the newly inserted
	/// `RangeBounds` is returned.
	///
	/// If the given `RangeBounds` overlaps one or more `RangeBounds`
	/// already in the map, then an [`OverlapError`] is returned and
	/// the map is not updated.
	///
	/// If the merged `RangeBounds` cannot be created with the
	/// [`TryFromBounds`] trait then a [`TryFromBoundsError`] will be
	/// returned.
	///
	/// # Panics
	///
	/// Panics if the given `range_bounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::{
	/// 	OverlapError, OverlapOrTryFromBoundsError, RangeBoundsMap,
	/// };
	///
	/// let mut map =
	/// 	RangeBoundsMap::from_slice_strict([(1..4, false)]).unwrap();
	///
	/// // Touching
	/// assert_eq!(map.insert_merge_touching(4..6, true), Ok(&(1..6)));
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching(4..8, false),
	/// 	Err(OverlapOrTryFromBoundsError::Overlap(OverlapError)),
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching(10..16, false),
	/// 	Ok(&(10..16))
	/// );
	///
	/// assert_eq!(
	/// 	map.iter().collect::<Vec<_>>(),
	/// 	[(&(1..6), &true), (&(10..16), &false)]
	/// );
	/// ```
	#[tested]
	pub fn insert_merge_touching(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<&K, OverlapOrTryFromBoundsError> {
		todo!()
	}
	#[parent_tested]
	fn touching_left(&self, range_bounds: &K) -> Option<&K> {
		todo!()
	}
	#[parent_tested]
	fn touching_right(&self, range_bounds: &K) -> Option<&K> {
		todo!()
	}

	/// Adds a new (`RangeBounds`, `Value`) entry to the map and
	/// merges into other `RangeBounds` in the map which overlap
	/// it.
	///
	/// The `Value` of the merged `RangeBounds` is set to the given
	/// `Value`.
	///
	/// If successful then a reference to the newly inserted
	/// `RangeBounds` is returned.
	///
	/// If the merged `RangeBounds` cannot be created with the
	/// [`TryFromBounds`] trait then a [`TryFromBoundsError`] will be
	/// returned.
	///
	/// # Panics
	///
	/// Panics if the given `range_bounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut map =
	/// 	RangeBoundsMap::from_slice_strict([(1..4, false)]).unwrap();
	///
	/// // Touching
	/// assert_eq!(
	/// 	map.insert_merge_overlapping(-4..1, true),
	/// 	Ok(&(-4..1))
	/// );
	///
	/// // Overlapping
	/// assert_eq!(map.insert_merge_overlapping(2..8, true), Ok(&(1..8)));
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_overlapping(10..16, false),
	/// 	Ok(&(10..16))
	/// );
	///
	/// assert_eq!(
	/// 	map.iter().collect::<Vec<_>>(),
	/// 	[(&(-4..1), &true), (&(1..8), &true), (&(10..16), &false)]
	/// );
	/// ```
	#[tested]
	pub fn insert_merge_overlapping(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<&K, TryFromBoundsError> {
		todo!()
	}

	/// Adds a new (`RangeBounds`, `Value`) entry to the map and
	/// merges into other `RangeBounds` in the map which touch or
	/// overlap it.
	///
	/// The `Value` of the merged `RangeBounds` is set to the given
	/// `Value`.
	///
	/// If successful then a reference to the newly inserted
	/// `RangeBounds` is returned.
	///
	/// If the merged `RangeBounds` cannot be created with the
	/// [`TryFromBounds`] trait then a [`TryFromBoundsError`] will be
	/// returned.
	///
	/// # Panics
	///
	/// Panics if the given `range_bounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut map =
	/// 	RangeBoundsMap::from_slice_strict([(1..4, false)]).unwrap();
	///
	/// // Touching
	/// assert_eq!(
	/// 	map.insert_merge_touching_or_overlapping(-4..1, true),
	/// 	Ok(&(-4..4))
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching_or_overlapping(2..8, true),
	/// 	Ok(&(-4..8))
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching_or_overlapping(10..16, false),
	/// 	Ok(&(10..16))
	/// );
	///
	/// assert_eq!(
	/// 	map.iter().collect::<Vec<_>>(),
	/// 	[(&(-4..8), &true), (&(10..16), &false)]
	/// );
	/// ```
	#[tested]
	pub fn insert_merge_touching_or_overlapping(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<&K, TryFromBoundsError> {
		todo!()
	}

	/// Adds a new (`RangeBounds`, `Value`) entry to the map and
	/// overwrites any other `RangeBounds` that overlap the new
	/// `RangeBounds`.
	///
	/// This is equivalent to using [`RangeBoundsMap::cut()`]
	/// followed by [`RangeBoundsMap::insert_strict()`]. Hence the
	/// same `V: Clone` trait bound applies.
	///
	/// If the remaining `RangeBounds` left after the cut are not able
	/// to be created with the [`TryFromBounds`] trait then a
	/// [`TryFromBoundsError`] will be returned.
	///
	/// # Panics
	///
	/// Panics if the given `range_bounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut map =
	/// 	RangeBoundsMap::from_slice_strict([(2..8, false)]).unwrap();
	///
	/// assert_eq!(map.insert_overwrite(4..6, true), Ok(()));
	///
	/// assert_eq!(
	/// 	map.iter().collect::<Vec<_>>(),
	/// 	[(&(2..4), &false), (&(4..6), &true), (&(6..8), &false)]
	/// );
	/// ```
	#[trivial]
	pub fn insert_overwrite(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<(), TryFromBoundsError> {
		todo!()
	}

	/// Returns the first (`RangeBounds`, `Value`) entry in the map, if
	/// any.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let map = RangeBoundsMap::from_slice_strict([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(map.first_entry(), Some((&(1..4), &false)));
	/// ```
	#[trivial]
	pub fn first_entry(&self) -> Option<(&K, &V)> {
		todo!()
	}

	/// Returns the last (`RangeBounds`, `Value`) entry in the map, if
	/// any.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let map = RangeBoundsMap::from_slice_strict([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(
	/// 	map.last_entry(),
	/// 	Some((&(8..100), &false))
	/// );
	#[trivial]
	pub fn last_entry(&self) -> Option<(&K, &V)> {
		todo!()
	}

	/// Moves all elements from `other` into `self` using
	/// [`RangeBoundsMap::insert_strict()`] in ascending order,
	/// leaving `other` empty.
	///
	/// If the underlying [`RangeBoundsMap::insert_strict()`] returns
	/// an `Err` at any point, then the element it failed on and all
	/// those following are dropped, but not inserted into `self`.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut base = RangeBoundsMap::from_slice_strict([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// ])
	/// .unwrap();
	///
	/// let mut add = RangeBoundsMap::from_slice_strict([
	/// 	(10..38, true),
	/// 	(40..42, false),
	/// ])
	/// .unwrap();
	///
	/// let expected = RangeBoundsMap::from_slice_strict([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(10..38, true),
	/// 	(40..42, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(base.append_strict(&mut add), Ok(()));
	/// assert_eq!(base, expected);
	/// assert!(add.is_empty());
	/// ```
	#[trivial]
	pub fn append_strict(
		&mut self,
		other: &mut RangeBoundsMap<I, K, V>,
	) -> Result<(), OverlapError> {
		todo!()
	}
	/// Moves all elements from `other` into `self` using
	/// [`RangeBoundsMap::insert_merge_touching()`] in ascending order,
	/// leaving `other` empty.
	///
	/// If the underlying [`RangeBoundsMap::insert_merge_touching()`] returns
	/// an `Err` at any point, then the element it failed on and all
	/// those following are dropped, but not inserted into `self`.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut base = RangeBoundsMap::from_slice_merge_touching([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// ])
	/// .unwrap();
	///
	/// let mut add = RangeBoundsMap::from_slice_merge_touching([
	/// 	(10..38, true),
	/// 	(40..42, false),
	/// ])
	/// .unwrap();
	///
	/// let expected = RangeBoundsMap::from_slice_merge_touching([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(10..38, true),
	/// 	(40..42, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(base.append_merge_touching(&mut add), Ok(()));
	/// assert_eq!(base, expected);
	/// assert!(add.is_empty());
	/// ```
	#[trivial]
	pub fn append_merge_touching(
		&mut self,
		other: &mut RangeBoundsMap<I, K, V>,
	) -> Result<(), OverlapOrTryFromBoundsError> {
		todo!()
	}
	/// Moves all elements from `other` into `self` using
	/// [`RangeBoundsMap::insert_merge_overlapping()`] in ascending order,
	/// leaving `other` empty.
	///
	/// If the underlying [`RangeBoundsMap::insert_merge_overlapping()`] returns
	/// an `Err` at any point, then the element it failed on and all
	/// those following are dropped, but not inserted into `self`.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut base = RangeBoundsMap::from_slice_merge_overlapping([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// ])
	/// .unwrap();
	///
	/// let mut add = RangeBoundsMap::from_slice_merge_overlapping([
	/// 	(10..38, true),
	/// 	(40..42, false),
	/// ])
	/// .unwrap();
	///
	/// let expected = RangeBoundsMap::from_slice_merge_overlapping([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(10..38, true),
	/// 	(40..42, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(base.append_merge_overlapping(&mut add), Ok(()));
	/// assert_eq!(base, expected);
	/// assert!(add.is_empty());
	/// ```
	#[trivial]
	pub fn append_merge_overlapping(
		&mut self,
		other: &mut RangeBoundsMap<I, K, V>,
	) -> Result<(), TryFromBoundsError> {
		todo!()
	}
	/// Moves all elements from `other` into `self` using
	/// [`RangeBoundsMap::insert_merge_touching_or_overlapping()`] in ascending order,
	/// leaving `other` empty.
	///
	/// If the underlying [`RangeBoundsMap::insert_merge_touching_or_overlapping()`] returns
	/// an `Err` at any point, then the element it failed on and all
	/// those following are dropped, but not inserted into `self`.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut base =
	/// 	RangeBoundsMap::from_slice_merge_touching_or_overlapping([
	/// 		(1..4, false),
	/// 		(4..8, true),
	/// 	])
	/// 	.unwrap();
	///
	/// let mut add =
	/// 	RangeBoundsMap::from_slice_merge_touching_or_overlapping([
	/// 		(10..38, true),
	/// 		(40..42, false),
	/// 	])
	/// 	.unwrap();
	///
	/// let expected =
	/// 	RangeBoundsMap::from_slice_merge_touching_or_overlapping([
	/// 		(1..4, false),
	/// 		(4..8, true),
	/// 		(10..38, true),
	/// 		(40..42, false),
	/// 	])
	/// 	.unwrap();
	///
	/// assert_eq!(
	/// 	base.append_merge_touching_or_overlapping(&mut add),
	/// 	Ok(())
	/// );
	/// assert_eq!(base, expected);
	/// assert!(add.is_empty());
	/// ```
	#[trivial]
	pub fn append_merge_touching_or_overlapping(
		&mut self,
		other: &mut RangeBoundsMap<I, K, V>,
	) -> Result<(), TryFromBoundsError> {
		todo!()
	}
	/// Moves all elements from `other` into `self` using
	/// [`RangeBoundsMap::insert_overwrite()`] in ascending order,
	/// leaving `other` empty.
	///
	/// If the underlying [`RangeBoundsMap::insert_overwrite()`] returns
	/// an `Err` at any point, then the element it failed on and all
	/// those following are dropped, but not inserted into `self`.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut base = RangeBoundsMap::from_slice_overwrite([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// ])
	/// .unwrap();
	///
	/// let mut add = RangeBoundsMap::from_slice_overwrite([
	/// 	(10..38, true),
	/// 	(40..42, false),
	/// ])
	/// .unwrap();
	///
	/// let expected = RangeBoundsMap::from_slice_overwrite([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(10..38, true),
	/// 	(40..42, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(base.append_overwrite(&mut add), Ok(()));
	/// assert_eq!(base, expected);
	/// assert!(add.is_empty());
	/// ```
	#[trivial]
	pub fn append_overwrite(
		&mut self,
		other: &mut RangeBoundsMap<I, K, V>,
	) -> Result<(), TryFromBoundsError> {
		todo!()
	}

	/// Splits the map in two at the given `start_bound()`. Returns
	/// the full or partial `RangeBounds` after the split.
	///
	/// If the remaining `RangeBounds` left in either the base or the
	/// returned map are not able be created with the
	/// [`TryFromBounds`] trait then a [`TryFromBoundsError`] will be
	/// returned and the base map will not be split.
	///
	/// `V` must implement `Clone` as if you try to split the map
	/// inside a `RangeBounds` then that entries value will need to be
	/// cloned into the returned `RangeBoundsMap`.
	///
	/// # Examples
	/// ```
	/// use std::ops::Bound;
	///
	/// use range_bounds_map::{RangeBoundsMap, TryFromBoundsError};
	///
	/// let mut a = RangeBoundsMap::from_slice_strict([
	/// 	(1..2, false),
	/// 	(4..8, true),
	/// 	(10..16, true),
	/// ])
	/// .unwrap();
	///
	/// // Fails because that would leave an Inclusive-Inclusive
	/// // `RangeBounds` in `a`
	/// assert_eq!(
	/// 	a.split_off(Bound::Excluded(6)),
	/// 	Err(TryFromBoundsError)
	/// );
	///
	/// let b = a.split_off(Bound::Included(6)).unwrap();
	///
	/// assert_eq!(
	/// 	a.into_iter().collect::<Vec<_>>(),
	/// 	[(1..2, false), (4..6, true)],
	/// );
	/// assert_eq!(
	/// 	b.into_iter().collect::<Vec<_>>(),
	/// 	[(6..8, true), (10..16, true)],
	/// );
	/// ```
	#[trivial]
	pub fn split_off(
		&mut self,
		start_bound: Bound<I>,
	) -> Result<RangeBoundsMap<I, K, V>, TryFromBoundsError> {
		todo!()
	}

	/// Similar to [`RangeBoundsMap::overlapping()`] except the
	/// `(Bound, Bound)`s returned in the iterator have been
	/// trimmed/cut by the given `RangeBounds`.
	///
	/// This is sort of the analogue to the AND function between a
	/// `RangeBounds` AND a [`RangeBoundsMap`].
	///
	/// # Panics
	///
	/// Panics if the given `range_bounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use std::ops::Bound;
	///
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let map = RangeBoundsMap::from_slice_strict([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// let mut overlapping_trimmed = map.overlapping_trimmed(&(2..20));
	///
	/// assert_eq!(
	/// 	overlapping_trimmed.collect::<Vec<_>>(),
	/// 	[
	/// 		((Bound::Included(&2), Bound::Excluded(&4)), &false),
	/// 		((Bound::Included(&4), Bound::Excluded(&8)), &true),
	/// 		((Bound::Included(&8), Bound::Excluded(&20)), &false)
	/// 	]
	/// );
	/// ```
	//#[tested]
	//pub fn overlapping_trimmed<Q>(
	//&self,
	//range_bounds: Q,
	//) -> impl DoubleEndedIterator<Item = ((Bound<&I>, Bound<&I>), &V)>
	//where
	//Q: RangeBounds<I>,
	//{
	//todo!()
	//}

	/// Identical to [`RangeBoundsMap::overlapping_trimmed()`] except
	/// it returns an iterator of `(Result<RangeBounds,
	/// TryFromBoundsError>, Value)`.
	///
	/// # Panics
	///
	/// Panics if the given `range_bounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::{RangeBoundsMap, TryFromBoundsError};
	///
	/// let map = RangeBoundsMap::from_slice_strict([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// let mut overlapping_trimmed_same =
	/// 	map.overlapping_trimmed_same(&(2..=20));
	///
	/// assert_eq!(
	/// 	overlapping_trimmed_same.collect::<Vec<_>>(),
	/// 	[
	/// 		(Ok(2..4), &false),
	/// 		(Ok(4..8), &true),
	/// 		// Due to using a RangeInclusive in `overlapping_trimmed_same()`
	/// 		(Err(TryFromBoundsError), &false)
	/// 	]
	/// );
	/// ```
	//#[trivial]
	//pub fn overlapping_trimmed_same<Q>(
	//&self,
	//range_bounds: Q,
	//) -> impl DoubleEndedIterator<Item = (Result<K, TryFromBoundsError>, &V)>
	//where
	//Q: RangeBounds<I>,
	//{
	//todo!()
	//}

	/// Allocate a `RangeBoundsMap` and move the given (`RangeBounds`,
	/// `Value`) entries from the slice into the map using
	/// [`RangeBoundsMap::insert_strict()`].
	///
	/// May return an `Err` while inserting. See
	/// [`RangeBoundsMap::insert_strict()`] for details.
	///
	/// # Panics
	///
	/// Panics if any of the given `RangeBounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::{RangeBoundsMap, TryFromBoundsError};
	///
	/// let map = RangeBoundsMap::from_slice_strict([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	/// ```
	#[trivial]
	pub fn from_slice_strict<const N: usize>(
		slice: [(K, V); N],
	) -> Result<RangeBoundsMap<I, K, V>, OverlapError> {
		todo!()
	}
	/// Allocate a `RangeBoundsMap` and move the given (`RangeBounds`,
	/// `Value`) entries from the slice into the map using
	/// [`RangeBoundsMap::insert_merge_touching()`].
	///
	/// May return an `Err` while inserting. See
	/// [`RangeBoundsMap::insert_merge_touching()`] for details.
	///
	/// # Panics
	///
	/// Panics if any of the given `RangeBounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::{RangeBoundsMap, TryFromBoundsError};
	///
	/// let map = RangeBoundsMap::from_slice_merge_touching([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	/// ```
	#[trivial]
	pub fn from_slice_merge_touching<const N: usize>(
		slice: [(K, V); N],
	) -> Result<RangeBoundsMap<I, K, V>, OverlapOrTryFromBoundsError> {
		todo!()
	}
	/// Allocate a `RangeBoundsMap` and move the given (`RangeBounds`,
	/// `Value`) entries from the slice into the map using
	/// [`RangeBoundsMap::insert_merge_overlapping()`].
	///
	/// May return an `Err` while inserting. See
	/// [`RangeBoundsMap::insert_merge_overlapping()`] for details.
	///
	/// # Panics
	///
	/// Panics if any of the given `RangeBounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::{RangeBoundsMap, TryFromBoundsError};
	///
	/// let map = RangeBoundsMap::from_slice_merge_overlapping([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	/// ```
	#[trivial]
	pub fn from_slice_merge_overlapping<const N: usize>(
		slice: [(K, V); N],
	) -> Result<RangeBoundsMap<I, K, V>, TryFromBoundsError> {
		todo!()
	}
	/// Allocate a `RangeBoundsMap` and move the given (`RangeBounds`,
	/// `Value`) entries from the slice into the map using
	/// [`RangeBoundsMap::insert_merge_touching_or_overlapping()`].
	///
	/// May return an `Err` while inserting. See
	/// [`RangeBoundsMap::insert_merge_touching_or_overlapping()`] for
	/// details.
	///
	/// # Panics
	///
	/// Panics if any of the given `RangeBounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::{RangeBoundsMap, TryFromBoundsError};
	///
	/// let map =
	/// 	RangeBoundsMap::from_slice_merge_touching_or_overlapping([
	/// 		(1..4, false),
	/// 		(4..8, true),
	/// 		(8..100, false),
	/// 	])
	/// 	.unwrap();
	/// ```
	#[trivial]
	pub fn from_slice_merge_touching_or_overlapping<const N: usize>(
		slice: [(K, V); N],
	) -> Result<RangeBoundsMap<I, K, V>, TryFromBoundsError> {
		todo!()
	}
	/// Allocate a `RangeBoundsMap` and move the given (`RangeBounds`,
	/// `Value`) entries from the slice into the map using
	/// [`RangeBoundsMap::insert_overwrite()`].
	///
	/// May return an `Err` while inserting. See
	/// [`RangeBoundsMap::overwrite()`] for details.
	///
	/// # Panics
	///
	/// Panics if any of the given `RangeBounds` is an invalid
	/// `RangeBounds`. See [`Invalid
	/// RangeBounds`](https://docs.rs/range_bounds_map/latest/range_bounds_map/index.html#Invalid-RangeBounds)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::{RangeBoundsMap, TryFromBoundsError};
	///
	/// let map = RangeBoundsMap::from_slice_overwrite([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	/// ```
	#[trivial]
	pub fn from_slice_overwrite<const N: usize>(
		slice: [(K, V); N],
	) -> Result<RangeBoundsMap<I, K, V>, TryFromBoundsError> {
		todo!()
	}
}

fn comp_start<I, K>(bound: Bound<&I>) -> impl FnMut(&K) -> Ordering + '_
where
	I: Ord,
	K: RangeBounds<I>,
{
	move |inner_range_bounds: &K| {
		cmp_range_bounds_with_bound_ord(
			inner_range_bounds,
			BoundOrd::start(bound),
		)
	}
}
fn comp_end<I, K>(bound: Bound<&I>) -> impl FnMut(&K) -> Ordering + '_
where
	I: Ord,
	K: RangeBounds<I>,
{
	move |inner_range_bounds: &K| {
		cmp_range_bounds_with_bound_ord(
			inner_range_bounds,
			BoundOrd::end(bound),
		)
	}
}
