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
use either::Either;
use itertools::Itertools;
use serde::de::{MapAccess, Visitor};
use serde::ser::SerializeMap;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::bound_ord::BoundOrd;
use crate::helpers::{
	cmp_range_with_bound_ord, cut_range, flip_bound, is_valid_range, overlaps,
};
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
	I: Ord + Copy,
	K: NiceRange<I> + TryFromBounds<I>,
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
	pub fn is_empty(&self) -> bool {
		self.inner.is_empty()
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
	pub fn overlaps<Q>(&self, range: Q) -> bool
	where
		Q: NiceRange<I>,
	{
		self.overlapping(range).next().is_some()
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
	pub fn overlapping<Q>(
		&self,
		range: Q,
	) -> impl DoubleEndedIterator<Item = (&K, &V)>
	where
		Q: NiceRange<I>,
	{
		let lower_comp = overlapping_start_comp(range.start());
		let upper_comp = overlapping_end_comp(range.end());

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
	pub fn get_at_point(&self, point: I) -> Option<&V> {
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
	pub fn contains_point(&self, point: I) -> bool {
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
	pub fn get_at_point_mut(&mut self, point: I) -> Option<&mut V> {
		self.inner
			.get_mut(overlapping_start_comp(Bound::Included(point)))
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
	pub fn get_entry_at_point(&self, point: I) -> Option<(&K, &V)> {
		self.inner
			.get_key_value(overlapping_start_comp(Bound::Included(point)))
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
	pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&K, &V)> {
		self.inner.iter()
	}

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
	pub fn remove_overlapping<'a, Q>(
		&'a mut self,
		range: Q,
	) -> impl Iterator<Item = (K, V)> + '_
	where
		Q: NiceRange<I> + 'a,
	{
		//optimisation, switch to BTreeMap::drain_range if it ever gets
		//implemented
		return self
			.inner
			.drain_filter(move |inner_range, _| overlaps(*inner_range, range));
	}

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
	pub fn cut<'a, Q>(
		&'a mut self,
		range: Q,
	) -> Result<
		impl Iterator<Item = ((Bound<I>, Bound<I>), V)> + '_,
		TryFromBoundsError,
	>
	where
		Q: NiceRange<I> + 'a,
		V: Clone,
	{
		let start_comp = overlapping_start_comp(range.start());
		let end_comp = overlapping_end_comp(range.end());

		let left_overlapping =
			self.inner.get_key_value(start_comp).map(|(key, _)| *key);
		let right_overlapping =
			self.inner.get_key_value(end_comp).map(|(key, _)| *key);

		if let Some(left) = left_overlapping && let Some(right) = right_overlapping && left.start() == right.start() {
            Ok(Either::Left(self.cut_single_overlapping(range, left)?))
        } else {
            Ok(Either::Right(self.cut_non_single_overlapping(range, left_overlapping, right_overlapping)?))
        }
	}
	pub fn cut_single_overlapping<Q>(
		&mut self,
		range: Q,
		single_overlapping_range: K,
	) -> Result<
		impl Iterator<Item = ((Bound<I>, Bound<I>), V)>,
		TryFromBoundsError,
	>
	where
		Q: NiceRange<I>,
		V: Clone,
	{
		let cut_result = cut_range(single_overlapping_range, range);
		let returning_before_cut = match cut_result.before_cut {
			Some((start, end)) => Some(K::try_from_bounds(start, end)?),
			None => None,
		};
		let returning_after_cut = match cut_result.after_cut {
			Some((start, end)) => Some(K::try_from_bounds(start, end)?),
			None => None,
		};

		let value = self
			.inner
			.remove(overlapping_start_comp(range.start()))
			.unwrap();

		if let Some(before) = returning_before_cut {
			self.insert_unchecked(before, value.clone());
		}
		if let Some(after) = returning_after_cut {
			self.insert_unchecked(after, value.clone());
		}

		Ok(once((cut_result.inside_cut.unwrap(), value)))
	}
	pub fn cut_non_single_overlapping<'a, Q>(
		&'a mut self,
		range: Q,
		left_overlapping: Option<K>,
		right_overlapping: Option<K>,
	) -> Result<
		impl Iterator<Item = ((Bound<I>, Bound<I>), V)> + '_,
		TryFromBoundsError,
	>
	where
		Q: NiceRange<I> + 'a,
		V: Clone,
	{
		let before_config = match left_overlapping {
			Some(before) => {
				let cut_result = cut_range(before, range);

				Some((
					match cut_result.before_cut {
						Some((start, end)) => {
							Some(K::try_from_bounds(start, end)?)
						}
						None => None,
					},
					cut_result.inside_cut.unwrap(),
				))
			}
			None => None,
		};
		let after_config = match right_overlapping {
			Some(after) => {
				let cut_result = cut_range(after, range);

				Some((
					match cut_result.after_cut {
						Some((start, end)) => {
							Some(K::try_from_bounds(start, end)?)
						}
						None => None,
					},
					cut_result.inside_cut.unwrap(),
				))
			}
			None => None,
		};

		let before_value =
			self.inner.remove(overlapping_start_comp(range.start()));
		let after_value = self.inner.remove(overlapping_end_comp(range.end()));

		if let Some((Some(returning_before_cut), _)) = before_config {
			self.insert_unchecked(
				returning_before_cut,
				before_value.as_ref().cloned().unwrap(),
			);
		}
		if let Some((Some(returning_after_cut), _)) = after_config {
			self.insert_unchecked(
				returning_after_cut,
				after_value.as_ref().cloned().unwrap(),
			);
		}

		let keeping_before_entry =
			before_config.map(|(_, keeping_before_entry)| {
				(keeping_before_entry, before_value.unwrap())
			});
		let keeping_after_entry =
			after_config.map(|(_, keeping_after_entry)| {
				(keeping_after_entry, after_value.unwrap())
			});

		return Ok(keeping_before_entry
			.into_iter()
			.chain(
				self.remove_overlapping(range)
					.map(|(key, value)| ((key.start(), key.end()), value)),
			)
			.chain(keeping_after_entry.into_iter()));
	}

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
	pub fn gaps<'a, Q>(
		&'a self,
		outer_range: Q,
	) -> impl Iterator<Item = (Bound<I>, Bound<I>)> + '_
	where
		Q: NiceRange<I> + 'a,
	{
		// I'm in love with how clean/mindblowing this entire function is
		let overlapping = self
			.overlapping(outer_range)
			.map(|(key, _)| (key.start(), key.end()));

		// If the start or end point of outer_range_bounds is not
		// contained within a RangeBounds in the map then we need to
		// generate a artificial RangeBounds to use instead.
		//
		// We also have to flip the artificial ones ahead of time as
		// we actually want the range_bounds endpoints included
		// not excluded unlike with other bounds in artificials

		let artificial_start = (
			flip_bound(outer_range.start()),
			flip_bound(outer_range.start()),
		);
		let artificial_end =
			(flip_bound(outer_range.end()), flip_bound(outer_range.end()));
		let mut artificials = once(artificial_start)
			.chain(overlapping)
			.chain(once(artificial_end));

		let start_contained = self
			.inner
			.contains_key(overlapping_start_comp(outer_range.start()));
		let end_contained = self
			.inner
			.contains_key(overlapping_end_comp(outer_range.end()));

		if start_contained {
			artificials.next();
		}
		if end_contained {
			artificials.next_back();
		}

		return artificials
			.tuple_windows()
			.map(|((_, first_end), (second_start, _))| {
				(flip_bound(first_end), flip_bound(second_start))
			})
			.filter(|range| is_valid_range(*range));
	}

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
	pub fn contains_range_bounds<Q>(&self, range_bounds: Q) -> bool
	where
		Q: NiceRange<I>,
	{
		// Soooo clean and mathematical 🥰!
		self.gaps(range_bounds).next().is_none()
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
	pub fn insert_strict(
		&mut self,
		range: K,
		value: V,
	) -> Result<(), OverlapError> {
		if self.overlaps(range) {
			return Err(OverlapError);
		}

		self.insert_unchecked(range, value);

		return Ok(());
	}
	fn insert_unchecked(&mut self, range: K, value: V) {
		self.inner.insert(range, value, double_comp());
	}

	fn insert_merge_with_comps<C1, C2>(
		&mut self,
		range: K,
		value: V,
		start_comp: C1,
		end_comp: C2,
	) -> Result<K, TryFromBoundsError>
	where
		C1: FnMut(&K) -> Ordering,
		C2: FnMut(&K) -> Ordering,
	{
		let matching_start =
			self.inner.get_key_value(start_comp).map(|(key, _)| key);
		let matching_end =
			self.inner.get_key_value(end_comp).map(|(key, _)| key);

		let returning = match (matching_start, matching_end) {
			(Some(matching_start), Some(matching_end)) => {
				K::try_from_bounds(matching_start.start(), matching_end.end())?
			}
			(Some(matching_start), None) => {
				K::try_from_bounds(matching_start.start(), range.end())?
			}
			(None, Some(matching_end)) => {
				K::try_from_bounds(range.start(), matching_end.end())?
			}
			(None, None) => range,
		};

		self.inner.remove(start_comp);
		self.inner.remove(end_comp);

		self.insert_unchecked(returning, value);

		Ok(returning)
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
	pub fn insert_merge_touching(
		&mut self,
		range: K,
		value: V,
	) -> Result<K, OverlapOrTryFromBoundsError> {
		if self.overlaps(range) {
			return Err(OverlapOrTryFromBoundsError::Overlap(OverlapError));
		}

		self.insert_merge_with_comps(
			range,
			value,
			touching_start_comp(range.start()),
			touching_end_comp(range.end()),
		)
		.map_err(OverlapOrTryFromBoundsError::TryFromBounds)
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
	pub fn insert_merge_overlapping(
		&mut self,
		range: K,
		value: V,
	) -> Result<K, TryFromBoundsError> {
		self.insert_merge_with_comps(
			range,
			value,
			overlapping_start_comp(range.start()),
			overlapping_end_comp(range.end()),
		)
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
	pub fn insert_merge_touching_or_overlapping(
		&mut self,
		range: K,
		value: V,
	) -> Result<K, TryFromBoundsError> {
		self.insert_merge_with_comps(
			range,
			value,
			touching_or_overlapping_start_comp(range.start()),
			touching_or_overlapping_end_comp(range.end()),
		)
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
	pub fn insert_overwrite(
		&mut self,
		range: K,
		value: V,
	) -> Result<(), TryFromBoundsError>
	where
		V: Clone,
	{
		let _ = self.cut(range)?;
		self.insert_unchecked(range, value);

		return Ok(());
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
	pub fn first_entry(&self) -> Option<(&K, &V)> {
		self.inner.first_key_value()
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
	pub fn last_entry(&self) -> Option<(&K, &V)> {
		self.inner.last_key_value()
	}
}

fn overlapping_start_comp<I, K>(start: Bound<I>) -> impl FnMut(&K) -> Ordering
where
	I: Ord + Copy,
	K: NiceRange<I>,
{
	move |inner_range: &K| {
		cmp_range_with_bound_ord(*inner_range, BoundOrd::start(start))
	}
}
fn overlapping_end_comp<I, K>(end: Bound<I>) -> impl FnMut(&K) -> Ordering
where
	I: Ord + Copy,
	K: NiceRange<I>,
{
	move |inner_range: &K| {
		cmp_range_with_bound_ord(*inner_range, BoundOrd::end(end))
	}
}
fn double_comp<K, I>() -> impl FnMut(&K, &K) -> Ordering
where
	K: NiceRange<I>,
	I: Ord,
{
	|inner_range: &K, new_range: &K| {
		BoundOrd::start(new_range.start())
			.cmp(&BoundOrd::start(inner_range.start()))
	}
}
fn touching_start_comp<I, K>(start: Bound<I>) -> impl FnMut(&K) -> Ordering
where
	I: Ord + Copy,
	K: NiceRange<I>,
{
	move |inner_range: &K| match (inner_range.end(), start) {
		//we only allow Ordering::Equal here since if they are equal
		//then the ranges would be touching
		(Bound::Included(end), Bound::Excluded(start)) if end == start => {
			Ordering::Equal
		}
		(Bound::Excluded(end), Bound::Included(start)) if end == start => {
			Ordering::Equal
		}

		(end, start) => {
			let normal_result = BoundOrd::start(start).cmp(&BoundOrd::end(end));

			//we overide any Equals to a random non-Equal since we
			//don't want non-touching matches
			match normal_result {
				Ordering::Equal => Ordering::Less,
				x => x,
			}
		}
	}
}
fn touching_end_comp<I, K>(end: Bound<I>) -> impl FnMut(&K) -> Ordering
where
	I: Ord + Copy,
	K: NiceRange<I>,
{
	move |inner_range: &K| match (end, inner_range.start()) {
		//we only allow Ordering::Equal here since if they are equal
		//then the ranges would be touching
		(Bound::Included(end), Bound::Excluded(start)) if end == start => {
			Ordering::Equal
		}
		(Bound::Excluded(end), Bound::Included(start)) if end == start => {
			Ordering::Equal
		}

		(end, start) => {
			let normal_result =
				BoundOrd::end(end).cmp(&BoundOrd::start(inner_range.start()));

			//we overide any Equals to a random non-Equal since we
			//don't want non-touching matches
			match normal_result {
				Ordering::Equal => Ordering::Less,
				x => x,
			}
		}
	}
}
fn touching_or_overlapping_start_comp<I, K>(
	start: Bound<I>,
) -> impl FnMut(&K) -> Ordering
where
	I: Ord + Copy,
	K: NiceRange<I>,
{
	move |inner_range: &K| {
		let normal_result =
			cmp_range_with_bound_ord(*inner_range, BoundOrd::start(start));

		//we overide touchings as matches also
		match (inner_range.end(), start) {
			(Bound::Included(end), Bound::Excluded(start)) if end == start => {
				Ordering::Equal
			}
			(Bound::Excluded(end), Bound::Included(start)) if end == start => {
				Ordering::Equal
			}
			x => normal_result,
		}
	}
}
fn touching_or_overlapping_end_comp<I, K>(
	end: Bound<I>,
) -> impl FnMut(&K) -> Ordering
where
	I: Ord + Copy,
	K: NiceRange<I>,
{
	move |inner_range: &K| {
		let normal_result =
			cmp_range_with_bound_ord(*inner_range, BoundOrd::end(end));

		//we overide touchings as matches also
		match (end, inner_range.start()) {
			(Bound::Included(end), Bound::Excluded(start)) if end == start => {
				Ordering::Equal
			}
			(Bound::Excluded(end), Bound::Included(start)) if end == start => {
				Ordering::Equal
			}
			x => normal_result,
		}
	}
}

pub trait NiceRange<I>: Copy {
	fn start(&self) -> Bound<I>;
	fn end(&self) -> Bound<I>;
}

impl<K, I> NiceRange<I> for K
where
	I: Copy,
	K: RangeBounds<I> + Copy,
{
	fn start(&self) -> Bound<I> {
		self.start_bound().cloned()
	}
	fn end(&self) -> Bound<I> {
		self.end_bound().cloned()
	}
}
