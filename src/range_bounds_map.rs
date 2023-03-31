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

use std::collections::btree_map::IntoValues;
use std::collections::BTreeMap;
use std::fmt::{self, Debug};
use std::iter::once;
use std::marker::PhantomData;
use std::ops::{Bound, RangeBounds};

use either::Either;
use itertools::Itertools;
use labels::{parent_tested, tested, trivial};
use serde::de::{MapAccess, Visitor};
use serde::ser::SerializeMap;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::bound_ord::BoundOrd;
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
/// let mut map = RangeBoundsMap::try_from([
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
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct RangeBoundsMap<I, K, V>
where
	I: PartialOrd,
{
	starts: BTreeMap<BoundOrd<I>, (K, V)>,
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
/// let mut range_bounds_map =
/// 	RangeBoundsMap::try_from([(2..8, true)]).unwrap();
///
/// assert!(range_bounds_map.cut(&(4..=6)).is_err());
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
/// let mut range_bounds_map = RangeBoundsMap::try_from([(
/// 	MultiBounds::Inclusive(2, 4),
/// 	true,
/// )])
/// .unwrap();
///
/// assert_eq!(
/// 	range_bounds_map.insert_merge_touching(
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
	K: RangeBounds<I>,
	I: Ord + Clone,
{
	/// Makes a new, empty `RangeBoundsMap`.
	///
	/// # Examples
	/// ```
	/// use std::ops::Range;
	///
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let range_bounds_map: RangeBoundsMap<u8, Range<u8>, bool> =
	/// 	RangeBoundsMap::new();
	/// ```
	#[trivial]
	pub fn new() -> Self {
		RangeBoundsMap {
			starts: BTreeMap::new(),
		}
	}

	/// Returns the number of `RangeBounds` in the map.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut range_bounds_map = RangeBoundsMap::new();
	///
	/// assert_eq!(range_bounds_map.len(), 0);
	/// range_bounds_map.insert_strict(0..1, false).unwrap();
	/// assert_eq!(range_bounds_map.len(), 1);
	/// ```
	#[trivial]
	pub fn len(&self) -> usize {
		self.starts.len()
	}

	/// Returns `true` if the map contains no `RangeBounds`, and
	/// `false` if it does.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut range_bounds_map = RangeBoundsMap::new();
	///
	/// assert_eq!(range_bounds_map.is_empty(), true);
	/// range_bounds_map.insert_strict(0..1, false).unwrap();
	/// assert_eq!(range_bounds_map.is_empty(), false);
	/// ```
	#[trivial]
	pub fn is_empty(&self) -> bool {
		self.starts.is_empty()
	}

	/// Adds a new (`RangeBounds`, `Value`) pair to the map without
	/// modifying other entries.
	///
	/// If the given `RangeBounds` overlaps one or more `RangeBounds`
	/// already in the map rather than just touching, then an
	/// [`OverlapError`] is returned and the map is not updated.
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
	/// let mut range_bounds_map = RangeBoundsMap::new();
	///
	/// assert_eq!(range_bounds_map.insert_strict(5..10, 9), Ok(()));
	/// assert_eq!(
	/// 	range_bounds_map.insert_strict(5..10, 2),
	/// 	Err(OverlapError)
	/// );
	/// assert_eq!(range_bounds_map.len(), 1);
	/// ```
	#[tested]
	pub fn insert_strict(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<(), OverlapError> {
		if self.overlaps(&range_bounds) {
			return Err(OverlapError);
		}

		if !is_valid_range_bounds(&range_bounds) {
			panic!("Invalid range_bounds!");
		}

		self.starts.insert(
			BoundOrd::start(range_bounds.start_bound().cloned()),
			(range_bounds, value),
		);

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
	/// let mut range_bounds_map = RangeBoundsMap::new();
	///
	/// range_bounds_map.insert_strict(5..10, false);
	///
	/// assert_eq!(range_bounds_map.overlaps(&(1..=3)), false);
	/// assert_eq!(range_bounds_map.overlaps(&(4..5)), false);
	///
	/// assert_eq!(range_bounds_map.overlaps(&(4..=5)), true);
	/// assert_eq!(range_bounds_map.overlaps(&(4..6)), true);
	/// ```
	#[trivial]
	pub fn overlaps<Q>(&self, range_bounds: &Q) -> bool
	where
		Q: RangeBounds<I>,
	{
		self.overlapping(range_bounds).next().is_some()
	}

	/// Returns an iterator over every (`RangeBounds`, `Value`) pair
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
	/// let range_bounds_map = RangeBoundsMap::try_from([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// let mut overlapping = range_bounds_map.overlapping(&(2..8));
	///
	/// assert_eq!(
	/// 	overlapping.collect::<Vec<_>>(),
	/// 	[(&(1..4), &false), (&(4..8), &true)]
	/// );
	/// ```
	#[tested]
	pub fn overlapping<Q>(
		&self,
		range_bounds: &Q,
	) -> impl DoubleEndedIterator<Item = (&K, &V)>
	where
		Q: RangeBounds<I>,
	{
		if !is_valid_range_bounds(range_bounds) {
			panic!("Invalid range_bounds!");
		}

		let start = BoundOrd::start(range_bounds.start_bound().cloned());
		let end = BoundOrd::end(range_bounds.end_bound().cloned());

		let start_range_bounds = (
			//Included is lossless regarding meta-bounds searches
			//which is what we want
			Bound::Included(start),
			Bound::Included(end),
		);
		//this range will hold all the ranges we want except possibly
		//the first RangeBounds in the range
		let most_range_bounds = self.starts.range(start_range_bounds);

		//then we check for this possibly missing range_bounds
		if let Some(missing_entry @ (_, (possible_missing_range_bounds, _))) =
			//Excluded is lossy regarding meta-bounds searches because
			//we don't want equal bounds as they would have be covered
			//in the previous step and we don't want duplicates
			self.starts
					.range((
						Bound::Unbounded,
						Bound::Excluded(BoundOrd::start(
							range_bounds.start_bound().cloned(),
						)),
					))
					.next_back()
		{
			if overlaps(possible_missing_range_bounds, range_bounds) {
				return Either::Left(
					once(missing_entry)
						.chain(most_range_bounds)
						.map(|(_, (key, value))| (key, value)),
				);
			}
		}

		return Either::Right(
			most_range_bounds.map(|(_, (key, value))| (key, value)),
		);
	}

	/// Returns a reference to the `Value` corresponding to the
	/// `RangeBounds` in the map that overlaps the given point, if
	/// any.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let range_bounds_map = RangeBoundsMap::try_from([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(range_bounds_map.get_at_point(&3), Some(&false));
	/// assert_eq!(range_bounds_map.get_at_point(&4), Some(&true));
	/// assert_eq!(range_bounds_map.get_at_point(&101), None);
	/// ```
	#[trivial]
	pub fn get_at_point(&self, point: &I) -> Option<&V> {
		self.get_entry_at_point(point).map(|(_, value)| value)
	}

	/// Returns `true` if the map contains a `RangeBounds` that
	/// overlaps the given point, and `false` if not.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let range_bounds_map = RangeBoundsMap::try_from([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(range_bounds_map.contains_point(&3), true);
	/// assert_eq!(range_bounds_map.contains_point(&4), true);
	/// assert_eq!(range_bounds_map.contains_point(&101), false);
	/// ```
	#[trivial]
	pub fn contains_point(&self, point: &I) -> bool {
		self.get_at_point(point).is_some()
	}

	/// Returns a mutable reference to the `Value` corresponding to
	/// the `RangeBounds` that overlaps the given point, if any.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut range_bounds_map =
	/// 	RangeBoundsMap::try_from([(1..4, false)]).unwrap();
	///
	/// if let Some(x) = range_bounds_map.get_at_point_mut(&2) {
	/// 	*x = true;
	/// }
	///
	/// assert_eq!(range_bounds_map.get_at_point(&1), Some(&true));
	/// ```
	#[tested]
	pub fn get_at_point_mut(&mut self, point: &I) -> Option<&mut V> {
		if let Some(overlapping_start_bound) = self
			.get_entry_at_point(point)
			.map(|(key, _)| key.start_bound())
		{
			return self
				.starts
				.get_mut(&BoundOrd::start(overlapping_start_bound.cloned()))
				.map(|(_, value)| value);
		}
		return None;
	}

	/// Returns an (`RangeBounds`, `Value`) pair corresponding to the
	/// `RangeBounds` that overlaps the given point, if any.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let range_bounds_map = RangeBoundsMap::try_from([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(
	/// 	range_bounds_map.get_entry_at_point(&3),
	/// 	Some((&(1..4), &false))
	/// );
	/// assert_eq!(
	/// 	range_bounds_map.get_entry_at_point(&4),
	/// 	Some((&(4..8), &true))
	/// );
	/// assert_eq!(range_bounds_map.get_entry_at_point(&101), None);
	/// ```
	#[trivial]
	pub fn get_entry_at_point(&self, point: &I) -> Option<(&K, &V)> {
		//a zero-range included-included range is equivalent to a point
		return self
			.overlapping(&(
				Bound::Included(point.clone()),
				Bound::Included(point.clone()),
			))
			.next();
	}

	/// Returns an iterator over every (`RangeBounds`, `Value`) pair
	/// in the map in ascending order.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let range_bounds_map = RangeBoundsMap::try_from([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// let mut iter = range_bounds_map.iter();
	///
	/// assert_eq!(iter.next(), Some((&(1..4), &false)));
	/// assert_eq!(iter.next(), Some((&(4..8), &true)));
	/// assert_eq!(iter.next(), Some((&(8..100), &false)));
	/// assert_eq!(iter.next(), None);
	/// ```
	#[trivial]
	pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&K, &V)> {
		self.starts.iter().map(|(_, (key, value))| (key, value))
	}

	/// Removes every (`RangeBounds`, `Value`) pair in the map which
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
	/// let mut range_bounds_map = RangeBoundsMap::try_from([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// let mut removed = range_bounds_map.remove_overlapping(&(2..8));
	///
	/// assert_eq!(
	/// 	removed.collect::<Vec<_>>(),
	/// 	[(1..4, false), (4..8, true)]
	/// );
	///
	/// assert_eq!(
	/// 	range_bounds_map.iter().collect::<Vec<_>>(),
	/// 	[(&(8..100), &false)]
	/// );
	/// ```
	#[tested]
	pub fn remove_overlapping<Q>(
		&mut self,
		range_bounds: &Q,
	) -> impl DoubleEndedIterator<Item = (K, V)>
	where
		Q: RangeBounds<I>,
	{
		//optimisation do this whole function without cloning anything
		//or collectiong anything, may depend on a nicer upstream
		//BTreeMap remove_range function

		let to_remove: Vec<BoundOrd<I>> = self
			.overlapping(range_bounds)
			.map(|(key, _)| (BoundOrd::start(key.start_bound().cloned())))
			.collect();

		let mut output = Vec::new();

		for start_bound in to_remove {
			output.push(self.starts.remove(&start_bound).unwrap());
		}

		return output.into_iter();
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
	/// (`RangeBounds`, `Value`) pairs using `Clone`. Or if you
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
	/// let mut base = RangeBoundsMap::try_from([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// let after_cut =
	/// 	RangeBoundsMap::try_from([(1..2, false), (40..100, false)])
	/// 		.unwrap();
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
	#[tested]
	pub fn cut<Q>(
		&mut self,
		range_bounds: &Q,
	) -> Result<
		impl DoubleEndedIterator<Item = ((Bound<I>, Bound<I>), V)>,
		TryFromBoundsError,
	>
	where
		Q: RangeBounds<I>,
		K: TryFromBounds<I>,
		V: Clone,
	{
		let mut to_insert = Vec::new();
		let mut partial_first = None;
		let mut partial_last = None;

		{
			// only the first and last range_bounds in overlapping stand a
			// change of remaining after the cut so we don't need to
			// collect the iterator and can just look at the first and
			// last elements since range is a double ended iterator ;p
			let mut overlapping = self.overlapping(range_bounds);

			if let Some(first) = overlapping.next() {
				let cut_result = cut_range_bounds(first.0, range_bounds);

				if let Some(before) = cut_result.before_cut {
					to_insert.push((cloned_bounds(before), first.1.clone()));
				}
				if let Some(after) = cut_result.after_cut {
					to_insert.push((cloned_bounds(after), first.1.clone()));
				}

				partial_first = cut_result.inside_cut.map(cloned_bounds);
			}
			if let Some(last) = overlapping.next_back() {
				let cut_result = cut_range_bounds(last.0, range_bounds);

				if cut_result.before_cut.is_some() {
					unreachable!()
				}
				if let Some(after) = cut_result.after_cut {
					to_insert.push((cloned_bounds(after), last.1.clone()));
				}

				partial_last = cut_result.inside_cut.map(cloned_bounds);
			}
		}

		// Make sure that the inserts will work before we try to do
		// them, so if one fails the map remains unchanged
		if to_insert.iter().all(|(x, _)| K::is_valid(x)) {
			let mut removed = self.remove_overlapping(range_bounds);
			for ((start, end), value) in to_insert.into_iter() {
				self.insert_strict(
					K::try_from_bounds(start, end).unwrap(),
					value,
				)
				.unwrap();
			}

			let mut removed_first = removed
				.next()
				.map(|(key, value)| (expand_cloned(&key), value));
			let mut removed_last = removed
				.next_back()
				.map(|(key, value)| (expand_cloned(&key), value));

			//remove the full rangebounds and replace with their partial cuts
			//if they exist
			if let Some(partial_first) = partial_first {
				removed_first = removed_first.map(|(_, v)| (partial_first, v));
			}
			if let Some(partial_last) = partial_last {
				removed_last = removed_last.map(|(_, v)| (partial_last, v));
			}

			// I'm in love again with this lol
			let result = removed_first
				.into_iter()
				.chain(removed.map(|(key, value)| (expand_cloned(&key), value)))
				.chain(removed_last.into_iter());

			return Ok(result);
		} else {
			return Err(TryFromBoundsError);
		}
	}

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
	/// let mut base = RangeBoundsMap::try_from([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// let after_cut =
	/// 	RangeBoundsMap::try_from([(1..2, false), (40..100, false)])
	/// 		.unwrap();
	///
	/// assert_eq!(
	/// 	base.cut_same(&(2..40)).unwrap().collect::<Vec<_>>(),
	/// 	[(Ok(2..4), false), (Ok(4..8), true), (Ok(8..40), false)]
	/// );
	/// assert_eq!(base, after_cut);
	/// assert!(base.cut_same(&(60..=80)).is_err());
	/// ```
	#[trivial]
	pub fn cut_same<Q>(
		&mut self,
		range_bounds: &Q,
	) -> Result<
		impl DoubleEndedIterator<Item = (Result<K, TryFromBoundsError>, V)>,
		TryFromBoundsError,
	>
	where
		Q: RangeBounds<I>,
		K: TryFromBounds<I>,
		V: Clone,
	{
		Ok(self.cut(range_bounds)?.map(|((start, end), value)| {
			(
				K::try_from_bounds(start, end).ok_or(TryFromBoundsError),
				value,
			)
		}))
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
	/// let range_bounds_map = RangeBoundsMap::try_from([
	/// 	(1..3, false),
	/// 	(5..7, true),
	/// 	(9..100, false),
	/// ])
	/// .unwrap();
	///
	/// let mut gaps = range_bounds_map.gaps(&(2..));
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
	#[tested]
	pub fn gaps<'a, Q>(
		&'a self,
		outer_range_bounds: &'a Q,
	) -> impl Iterator<Item = (Bound<&I>, Bound<&I>)>
	where
		Q: RangeBounds<I>,
	{
		// I'm in love with how clean/mindblowing this entire function is
		let overlapping = self
			.overlapping(outer_range_bounds)
			.map(|(key, _)| (key.start_bound(), key.end_bound()));

		// If the start or end point of outer_range_bounds is not
		// contained within a RangeBounds in the map then we need to
		// generate a artificial RangeBounds to use instead.
		//
		// We also have to flip the artificial ones ahead of time as
		// we actually want the range_bounds endpoints included
		// not excluded unlike with other bounds in artificials

		let artificial_start = (
			flip_bound(outer_range_bounds.start_bound()),
			flip_bound(outer_range_bounds.start_bound()),
		);
		let artificial_end = (
			flip_bound(outer_range_bounds.end_bound()),
			flip_bound(outer_range_bounds.end_bound()),
		);
		let mut artificials = once(artificial_start)
			.chain(overlapping)
			.chain(once(artificial_end));

		let start_contained = match outer_range_bounds.start_bound() {
			Bound::Included(point) => self.contains_point(point),
			Bound::Excluded(point) => self.contains_point(point),
			Bound::Unbounded => self.starts.first_key_value().is_some_and(
				|(_, (range_bounds, _))| {
					range_bounds.start_bound() == Bound::Unbounded
				},
			),
		};
		let end_contained = match outer_range_bounds.end_bound() {
			Bound::Included(point) => self.contains_point(point),
			Bound::Excluded(point) => self.contains_point(point),
			Bound::Unbounded => self.starts.last_key_value().is_some_and(
				|(_, (range_bounds, _))| {
					range_bounds.end_bound() == Bound::Unbounded
				},
			),
		};

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
			.filter(is_valid_range_bounds::<(Bound<&I>, Bound<&I>), I>);
	}

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
	/// let range_bounds_map = RangeBoundsMap::try_from([
	/// 	(1..3, false),
	/// 	(5..7, true),
	/// 	(9..100, false),
	/// ])
	/// .unwrap();
	///
	/// let mut gaps_same = range_bounds_map.gaps_same(&(2..));
	///
	/// assert_eq!(
	/// 	gaps_same.collect::<Vec<_>>(),
	/// 	[Ok(3..5), Ok(7..9), Err(TryFromBoundsError),]
	/// );
	/// ```
	#[trivial]
	pub fn gaps_same<'a, Q>(
		&'a self,
		outer_range_bounds: &'a Q,
	) -> impl Iterator<Item = Result<K, TryFromBoundsError>> + 'a
	where
		Q: RangeBounds<I>,
		K: TryFromBounds<I>,
	{
		self.gaps(outer_range_bounds).map(|(start, end)| {
			K::try_from_bounds(start.cloned(), end.cloned())
				.ok_or(TryFromBoundsError)
		})
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
	/// let range_bounds_map = RangeBoundsMap::try_from([
	/// 	(1..3, false),
	/// 	(5..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(range_bounds_map.contains_range_bounds(&(1..3)), true);
	/// assert_eq!(
	/// 	range_bounds_map.contains_range_bounds(&(2..6)),
	/// 	false
	/// );
	/// assert_eq!(
	/// 	range_bounds_map.contains_range_bounds(&(6..50)),
	/// 	true
	/// );
	/// ```
	#[trivial]
	pub fn contains_range_bounds<Q>(&self, range_bounds: &Q) -> bool
	where
		Q: RangeBounds<I>,
	{
		// Soooo clean and mathematical 🥰!
		self.gaps(range_bounds).next().is_none()
	}

	/// Adds a new (`RangeBounds`, `Value`) pair to the map and
	/// merges into other `RangeBounds` in the map which touch it.
	///
	/// The `Value` of the merged `RangeBounds` is set to the given
	/// `Value`.
	///
	/// If successful then a reference to the newly inserted
	/// `RangeBounds` is returned.
	///
	/// If the given `RangeBounds` overlaps one or more `RangeBounds`
	/// already in the map rather than just touching, then an
	/// [`OverlapError`] is returned and the map is not updated.
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
	/// use range_bounds_map::{
	/// 	OverlapError, OverlapOrTryFromBoundsError, RangeBoundsMap,
	/// };
	///
	/// let mut range_bounds_map =
	/// 	RangeBoundsMap::try_from([(1..4, false)]).unwrap();
	///
	/// // Touching
	/// assert_eq!(
	/// 	range_bounds_map.insert_merge_touching(4..6, true),
	/// 	Ok(&(1..6))
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	range_bounds_map.insert_merge_touching(4..8, false),
	/// 	Err(OverlapOrTryFromBoundsError::Overlap(OverlapError)),
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	range_bounds_map.insert_merge_touching(10..16, false),
	/// 	Ok(&(10..16))
	/// );
	///
	/// assert_eq!(
	/// 	range_bounds_map.iter().collect::<Vec<_>>(),
	/// 	[(&(1..6), &true), (&(10..16), &false)]
	/// );
	/// ```
	#[tested]
	pub fn insert_merge_touching(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<&K, OverlapOrTryFromBoundsError>
	where
		K: TryFromBounds<I>,
	{
		if self.overlaps(&range_bounds) {
			return Err(OverlapOrTryFromBoundsError::Overlap(OverlapError));
		}

		let touching_left_start_bound = self
			.touching_left(&range_bounds)
			.map(|x| BoundOrd::start(x.start_bound().cloned()));
		let touching_right_start_bound = self
			.touching_right(&range_bounds)
			.map(|x| BoundOrd::start(x.start_bound().cloned()));

		let start_bound = match touching_left_start_bound {
			Some(ref x) => self.starts.get(x).unwrap().0.start_bound().cloned(),
			None => range_bounds.start_bound().cloned(),
		};
		let end_bound = match touching_right_start_bound {
			Some(ref x) => self.starts.get(x).unwrap().0.end_bound(),
			None => range_bounds.end_bound(),
		};

		let new_range_bounds =
			K::try_from_bounds(start_bound.clone(), end_bound.cloned()).ok_or(
				OverlapOrTryFromBoundsError::TryFromBounds(TryFromBoundsError),
			)?;

		// Out with the old!
		if let Some(ref left) = touching_left_start_bound {
			self.starts.remove(left);
		}
		if let Some(ref right) = touching_right_start_bound {
			self.starts.remove(right);
		}

		// In with the new!
		self.starts.insert(
			BoundOrd::start(new_range_bounds.start_bound().cloned()),
			(new_range_bounds, value),
		);

		return Ok(&self.starts.get(&BoundOrd::start(start_bound)).unwrap().0);
	}
	#[parent_tested]
	fn touching_left(&self, range_bounds: &K) -> Option<&K> {
		return self
			.starts
			.range((
				Bound::Unbounded,
				Bound::Excluded(BoundOrd::start(
					range_bounds.start_bound().cloned(),
				)),
			))
			.next_back()
			.map(|x| &x.1.0)
			.filter(|x| touches(range_bounds, *x));
	}
	#[parent_tested]
	fn touching_right(&self, range_bounds: &K) -> Option<&K> {
		return self
			.starts
			.range((
				Bound::Excluded(BoundOrd::start(
					range_bounds.start_bound().cloned(),
				)),
				Bound::Unbounded,
			))
			.next()
			.map(|x| &x.1.0)
			.filter(|x| touches(range_bounds, *x));
	}

	/// Adds a new (`RangeBounds`, `Value`) pair to the map and
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
	/// let mut range_bounds_map =
	/// 	RangeBoundsMap::try_from([(1..4, false)]).unwrap();
	///
	/// // Touching
	/// assert_eq!(
	/// 	range_bounds_map.insert_merge_overlapping(-4..1, true),
	/// 	Ok(&(-4..1))
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	range_bounds_map.insert_merge_overlapping(2..8, true),
	/// 	Ok(&(1..8))
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	range_bounds_map.insert_merge_overlapping(10..16, false),
	/// 	Ok(&(10..16))
	/// );
	///
	/// assert_eq!(
	/// 	range_bounds_map.iter().collect::<Vec<_>>(),
	/// 	[(&(-4..1), &true), (&(1..8), &true), (&(10..16), &false)]
	/// );
	/// ```
	#[tested]
	pub fn insert_merge_overlapping(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<&K, TryFromBoundsError>
	where
		K: TryFromBounds<I>,
	{
		let (start_bound, end_bound) = {
			let overlapping_swell = self.overlapping_swell(&range_bounds);
			(overlapping_swell.0.cloned(), overlapping_swell.1.cloned())
		};

		let new_range_bounds =
			K::try_from_bounds(start_bound.clone(), end_bound)
				.ok_or(TryFromBoundsError)?;

		// Out with the old!
		let _ = self.remove_overlapping(&range_bounds);

		// In with the new!
		self.starts.insert(
			BoundOrd::start(new_range_bounds.start_bound().cloned()),
			(new_range_bounds, value),
		);

		return Ok(&self.starts.get(&BoundOrd::start(start_bound)).unwrap().0);
	}
	#[parent_tested]
	fn overlapping_swell<'a>(
		&'a self,
		range_bounds: &'a K,
	) -> (Bound<&I>, Bound<&I>) {
		let mut overlapping = self.overlapping(range_bounds).peekable();

		let start_bound = match overlapping.peek() {
			Some((first, _)) => std::cmp::min(
				BoundOrd::start(first.start_bound()),
				BoundOrd::start(range_bounds.start_bound()),
			),
			None => BoundOrd::start(range_bounds.start_bound()),
		};
		let end_bound = match overlapping.next_back() {
			Some((last, _)) => std::cmp::max(
				BoundOrd::end(last.end_bound()),
				BoundOrd::end(range_bounds.end_bound()),
			),
			None => BoundOrd::start(range_bounds.end_bound()),
		};

		return (Bound::from(start_bound), Bound::from(end_bound));
	}

	/// Adds a new (`RangeBounds`, `Value`) pair to the map and
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
	/// let mut range_bounds_map =
	/// 	RangeBoundsMap::try_from([(1..4, false)]).unwrap();
	///
	/// // Touching
	/// assert_eq!(
	/// 	range_bounds_map
	/// 		.insert_merge_touching_or_overlapping(-4..1, true),
	/// 	Ok(&(-4..4))
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	range_bounds_map
	/// 		.insert_merge_touching_or_overlapping(2..8, true),
	/// 	Ok(&(-4..8))
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	range_bounds_map
	/// 		.insert_merge_touching_or_overlapping(10..16, false),
	/// 	Ok(&(10..16))
	/// );
	///
	/// assert_eq!(
	/// 	range_bounds_map.iter().collect::<Vec<_>>(),
	/// 	[(&(-4..8), &true), (&(10..16), &false)]
	/// );
	/// ```
	#[tested]
	pub fn insert_merge_touching_or_overlapping(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<&K, TryFromBoundsError>
	where
		K: TryFromBounds<I>,
	{
		let overlapping_swell = self.overlapping_swell(&range_bounds);
		let start_bound = match self.touching_left(&range_bounds) {
			Some(touching_left) => touching_left.start_bound().cloned(),
			None => overlapping_swell.0.cloned(),
		};
		let end_bound = match self.touching_right(&range_bounds) {
			Some(touching_right) => touching_right.end_bound().cloned(),
			None => overlapping_swell.1.cloned(),
		};

		let new_range_bounds =
			K::try_from_bounds(start_bound.clone(), end_bound)
				.ok_or(TryFromBoundsError)?;

		let _ = self.remove_overlapping(&new_range_bounds);
		self.starts.insert(
			BoundOrd::start(start_bound.clone()),
			(new_range_bounds, value),
		);

		return Ok(&self.starts.get(&BoundOrd::start(start_bound)).unwrap().0);
	}

	/// Adds a new (`RangeBounds`, `Value`) pair to the map and
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
	/// let mut range_bounds_map =
	/// 	RangeBoundsMap::try_from([(2..8, false)]).unwrap();
	///
	/// assert_eq!(range_bounds_map.insert_overwrite(4..6, true), Ok(()));
	///
	/// assert_eq!(
	/// 	range_bounds_map.iter().collect::<Vec<_>>(),
	/// 	[(&(2..4), &false), (&(4..6), &true), (&(6..8), &false)]
	/// );
	/// ```
	#[trivial]
	pub fn insert_overwrite(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<(), TryFromBoundsError>
	where
		V: Clone,
		K: TryFromBounds<I>,
	{
		let _ = self.cut(&range_bounds)?;
		self.insert_strict(range_bounds, value).unwrap();

		return Ok(());
	}

	/// Returns the first (`RangeBounds`, `Value`) pair in the map, if
	/// any.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let range_bounds_map = RangeBoundsMap::try_from([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(
	/// 	range_bounds_map.first_entry(),
	/// 	Some((&(1..4), &false))
	/// );
	/// ```
	#[trivial]
	pub fn first_entry(&self) -> Option<(&K, &V)> {
		self.iter().next()
	}

	/// Returns the last (`RangeBounds`, `Value`) pair in the map, if
	/// any.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let range_bounds_map = RangeBoundsMap::try_from([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(
	/// 	range_bounds_map.last_entry(),
	/// 	Some((&(8..100), &false))
	/// );
	#[trivial]
	pub fn last_entry(&self) -> Option<(&K, &V)> {
		self.iter().next_back()
	}

	/// Moves all elements from `other` into `self` by
	/// [`RangeBoundsMap::insert_strict()`] in ascending order,
	/// leaving `other` empty.
	///
	/// If any of the `RangeBounds` in `other` overlap `self` then
	/// that `RangeBounds` is not inserted and the function returns.
	/// This will mean all `RangeBounds` after the failed one will not
	/// be inserted into `self`.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut base =
	/// 	RangeBoundsMap::try_from([(1..4, false), (4..8, true)])
	/// 		.unwrap();
	///
	/// let mut add =
	/// 	RangeBoundsMap::try_from([(10..38, true), (40..42, false)])
	/// 		.unwrap();
	///
	/// let expected = RangeBoundsMap::try_from([
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
		for (range_bounds, value) in
			other.remove_overlapping(&(Bound::Unbounded::<I>, Bound::Unbounded))
		{
			self.insert_strict(range_bounds, value)?;
		}

		return Ok(());
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
	/// let mut a = RangeBoundsMap::try_from([
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
	) -> Result<RangeBoundsMap<I, K, V>, TryFromBoundsError>
	where
		K: TryFromBounds<I> + Clone,
		V: Clone,
	{
		// optimisation: this is a terrible way of being atomic
		let before = self.clone();

		let split_off = self.cut_same(&(start_bound, Bound::Unbounded))?;
		let mut output = RangeBoundsMap::new();

		for (possible_key, value) in split_off {
			match possible_key {
				Ok(key) => output.insert_strict(key, value).unwrap(),
				Err(TryFromBoundsError) => {
					*self = before;
					return Err(TryFromBoundsError);
				}
			}
		}

		return Ok(output);
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
	/// let range_bounds_map = RangeBoundsMap::try_from([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// let mut overlapping_trimmed =
	/// 	range_bounds_map.overlapping_trimmed(&(2..20));
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
	#[tested]
	pub fn overlapping_trimmed<'a, Q>(
		&'a self,
		range_bounds: &'a Q,
	) -> impl DoubleEndedIterator<Item = ((Bound<&I>, Bound<&I>), &V)>
	where
		Q: RangeBounds<I>,
	{
		let mut overlapping = self.overlapping(range_bounds);
		let first = overlapping.next();
		let mut overlapping = overlapping.rev();
		let last = overlapping.next();
		let overlapping = overlapping.rev();

		let trimmed_first =
			first.and_then(|x| cut_range_bounds(x.0, range_bounds).inside_cut);
		let trimmed_last =
			last.and_then(|x| cut_range_bounds(x.0, range_bounds).inside_cut);

		let trimmed_first_entry = trimmed_first.map(|x| (x, first.unwrap().1));
		let trimmed_last_entry = trimmed_last.map(|x| (x, last.unwrap().1));

		return trimmed_first_entry
			.into_iter()
			.chain(overlapping.map(|(key, value)| (expand(key), value)))
			.chain(trimmed_last_entry.into_iter());
	}

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
	/// let range_bounds_map = RangeBoundsMap::try_from([
	/// 	(1..4, false),
	/// 	(4..8, true),
	/// 	(8..100, false),
	/// ])
	/// .unwrap();
	///
	/// let mut overlapping_trimmed_same =
	/// 	range_bounds_map.overlapping_trimmed_same(&(2..=20));
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
	#[trivial]
	pub fn overlapping_trimmed_same<'a, Q>(
		&'a self,
		range_bounds: &'a Q,
	) -> impl DoubleEndedIterator<Item = (Result<K, TryFromBoundsError>, &V)>
	where
		Q: RangeBounds<I>,
		K: TryFromBounds<I>,
	{
		self.overlapping_trimmed(range_bounds).map(|(key, value)| {
			(
				K::try_from_bounds(key.0.cloned(), key.1.cloned())
					.ok_or(TryFromBoundsError),
				value,
			)
		})
	}
}

impl<const N: usize, I, K, V> TryFrom<[(K, V); N]> for RangeBoundsMap<I, K, V>
where
	K: RangeBounds<I>,
	I: Ord + Clone,
{
	type Error = OverlapError;
	#[trivial]
	fn try_from(pairs: [(K, V); N]) -> Result<Self, Self::Error> {
		let mut range_bounds_map = RangeBoundsMap::new();
		for (range_bounds, value) in pairs {
			range_bounds_map.insert_strict(range_bounds, value)?;
		}

		return Ok(range_bounds_map);
	}
}
impl<I, K, V> TryFrom<Vec<(K, V)>> for RangeBoundsMap<I, K, V>
where
	K: RangeBounds<I>,
	I: Ord + Clone,
{
	type Error = OverlapError;
	#[trivial]
	fn try_from(pairs: Vec<(K, V)>) -> Result<Self, Self::Error> {
		let mut range_bounds_map = RangeBoundsMap::new();
		for (range_bounds, value) in pairs {
			range_bounds_map.insert_strict(range_bounds, value)?;
		}

		return Ok(range_bounds_map);
	}
}

impl<I, K, V> FromIterator<(K, V)> for RangeBoundsMap<I, K, V>
where
	K: RangeBounds<I>,
	I: Ord + Clone,
{
	#[trivial]
	fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
		let mut output = RangeBoundsMap::new();

		for (range_bounds, value) in iter {
			output.insert_strict(range_bounds, value).unwrap();
		}

		return output;
	}
}

impl<I, K, V> IntoIterator for RangeBoundsMap<I, K, V>
where
	K: RangeBounds<I>,
	I: Ord + Clone,
{
	type Item = (K, V);
	type IntoIter = IntoIter<I, K, V>;
	#[trivial]
	fn into_iter(self) -> Self::IntoIter {
		return IntoIter {
			inner: self.starts.into_values(),
		};
	}
}
/// An owning iterator over the entries of a [`RangeBoundsMap`].
///
/// This `struct` is created by the [`into_iter`] method on
/// [`RangeBoundsMap`] (provided by the [`IntoIterator`] trait). See
/// its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
pub struct IntoIter<I, K, V> {
	inner: IntoValues<BoundOrd<I>, (K, V)>,
}
impl<I, K, V> Iterator for IntoIter<I, K, V> {
	type Item = (K, V);
	#[trivial]
	fn next(&mut self) -> Option<Self::Item> {
		self.inner.next()
	}
}

impl<I, K, V> Default for RangeBoundsMap<I, K, V>
where
	I: PartialOrd,
{
	#[trivial]
	fn default() -> Self {
		RangeBoundsMap {
			starts: BTreeMap::default(),
		}
	}
}

impl<I, K, V> Serialize for RangeBoundsMap<I, K, V>
where
	I: Ord + Clone,
	K: RangeBounds<I> + Serialize,
	V: Serialize,
{
	#[trivial]
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let mut map = serializer.serialize_map(Some(self.len()))?;
		for (range_bounds, value) in self.iter() {
			map.serialize_entry(range_bounds, value)?;
		}
		map.end()
	}
}

impl<'de, I, K, V> Deserialize<'de> for RangeBoundsMap<I, K, V>
where
	K: Deserialize<'de> + RangeBounds<I>,
	I: Ord + Clone,
	V: Deserialize<'de>,
{
	#[trivial]
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		deserializer.deserialize_map(RangeBoundsMapVisitor {
			i: PhantomData,
			k: PhantomData,
			v: PhantomData,
		})
	}
}

struct RangeBoundsMapVisitor<I, K, V> {
	i: PhantomData<I>,
	k: PhantomData<K>,
	v: PhantomData<V>,
}

impl<'de, I, K, V> Visitor<'de> for RangeBoundsMapVisitor<I, K, V>
where
	I: Ord + Clone,
	K: RangeBounds<I> + Deserialize<'de>,
	V: Deserialize<'de>,
{
	type Value = RangeBoundsMap<I, K, V>;

	#[trivial]
	fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
		formatter.write_str("a RangeBoundsMap")
	}

	#[trivial]
	fn visit_map<A>(self, mut access: A) -> Result<Self::Value, A::Error>
	where
		A: MapAccess<'de>,
	{
		let mut range_bounds_map = RangeBoundsMap::new();
		while let Some((range_bounds, value)) = access.next_entry()? {
			range_bounds_map
				.insert_strict(range_bounds, value)
				.map_err(|_| serde::de::Error::custom("RangeBounds overlap"))?;
		}
		Ok(range_bounds_map)
	}
}

#[derive(Debug, PartialEq)]
enum Config {
	LeftFirstNonOverlapping,
	LeftFirstPartialOverlap,
	LeftContainsRight,

	RightFirstNonOverlapping,
	RightFirstPartialOverlap,
	RightContainsLeft,
}

#[tested]
fn config<'a, I, A, B>(a: &'a A, b: &'a B) -> Config
where
	A: RangeBounds<I>,
	B: RangeBounds<I>,
	I: PartialOrd,
{
	let (a_start, a_end) = expand(a);
	let (b_start, b_end) = expand(b);

	match BoundOrd::start(a_start) < BoundOrd::start(b_start) {
		true => {
			match (
				contains_bound_ord(a, BoundOrd::start(b_start)),
				contains_bound_ord(a, BoundOrd::end(b_end)),
			) {
				(false, false) => Config::LeftFirstNonOverlapping,
				(true, false) => Config::LeftFirstPartialOverlap,
				(true, true) => Config::LeftContainsRight,
				(false, true) => unreachable!(),
			}
		}
		false => {
			match (
				contains_bound_ord(b, BoundOrd::start(a_start)),
				contains_bound_ord(b, BoundOrd::end(a_end)),
			) {
				(false, false) => Config::RightFirstNonOverlapping,
				(true, false) => Config::RightFirstPartialOverlap,
				(true, true) => Config::RightContainsLeft,
				(false, true) => unreachable!(),
			}
		}
	}
}

#[derive(Debug, PartialEq)]
enum SortedConfig<I> {
	NonOverlapping((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
	PartialOverlap((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
	Swallowed((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
}

#[rustfmt::skip]
#[trivial]
fn sorted_config<'a, I, A, B>(a: &'a A, b: &'a B) -> SortedConfig<&'a I>
where
	A: RangeBounds<I>,
	B: RangeBounds<I>,
	I: PartialOrd,
{
    let ae = expand(a);
    let be = expand(b);
	match config(a, b) {
        Config::LeftFirstNonOverlapping => SortedConfig::NonOverlapping(ae, be),
		Config::LeftFirstPartialOverlap => SortedConfig::Swallowed(ae, be),
		Config::LeftContainsRight => SortedConfig::Swallowed(ae, be),

        Config::RightFirstNonOverlapping => SortedConfig::NonOverlapping(be, ae),
        Config::RightFirstPartialOverlap => SortedConfig::PartialOverlap(be, ae),
		Config::RightContainsLeft => SortedConfig::Swallowed(be, ae),
	}
}

#[trivial]
fn contains_bound_ord<I, A>(range_bounds: &A, bound_ord: BoundOrd<&I>) -> bool
where
	A: RangeBounds<I>,
	I: PartialOrd,
{
	let start_bound_ord = BoundOrd::start(range_bounds.start_bound());
	let end_bound_ord = BoundOrd::end(range_bounds.end_bound());

	return bound_ord >= start_bound_ord && bound_ord <= end_bound_ord;
}

#[derive(Debug)]
struct CutResult<I> {
	before_cut: Option<(Bound<I>, Bound<I>)>,
	inside_cut: Option<(Bound<I>, Bound<I>)>,
	after_cut: Option<(Bound<I>, Bound<I>)>,
}

#[tested]
fn cut_range_bounds<'a, I, B, C>(
	base_range_bounds: &'a B,
	cut_range_bounds: &'a C,
) -> CutResult<&'a I>
where
	B: RangeBounds<I>,
	C: RangeBounds<I>,
	I: PartialOrd + Clone,
{
	let base_all @ (base_start, base_end) = (
		base_range_bounds.start_bound(),
		base_range_bounds.end_bound(),
	);
	let cut_all @ (cut_start, cut_end) =
		(cut_range_bounds.start_bound(), cut_range_bounds.end_bound());

	let mut result = CutResult {
		before_cut: None,
		inside_cut: None,
		after_cut: None,
	};

	match config(base_range_bounds, cut_range_bounds) {
		Config::LeftFirstNonOverlapping => {
			result.before_cut = Some(base_all);
		}
		Config::LeftFirstPartialOverlap => {
			result.before_cut = Some((base_start, flip_bound(cut_start)));
			result.inside_cut = Some((cut_start, base_end));
		}
		Config::LeftContainsRight => {
			result.before_cut = Some((base_start, flip_bound(cut_start)));
			result.inside_cut = Some(cut_all);
			// exception for Unbounded-ending things
			match cut_end {
				Bound::Unbounded => {}
				_ => {
					result.after_cut = Some((flip_bound(cut_end), base_end));
				}
			}
		}

		Config::RightFirstNonOverlapping => {
			result.after_cut = Some(base_all);
		}
		Config::RightFirstPartialOverlap => {
			result.after_cut = Some((flip_bound(cut_end), base_end));
			result.inside_cut = Some((base_start, cut_end));
		}
		Config::RightContainsLeft => {
			result.inside_cut = Some(base_all);
		}
	}

	//only return valid range_bounds
	return CutResult {
		before_cut: result
			.before_cut
			.filter(|x| is_valid_range_bounds::<(Bound<&I>, Bound<&I>), I>(x)),
		inside_cut: result
			.inside_cut
			.filter(|x| is_valid_range_bounds::<(Bound<&I>, Bound<&I>), I>(x)),
		after_cut: result
			.after_cut
			.filter(|x| is_valid_range_bounds::<(Bound<&I>, Bound<&I>), I>(x)),
	};
}

#[trivial]
fn is_valid_range_bounds<Q, I>(range_bounds: &Q) -> bool
where
	Q: RangeBounds<I>,
	I: std::cmp::PartialOrd,
{
	match (range_bounds.start_bound(), range_bounds.end_bound()) {
		(Bound::Included(start), Bound::Included(end)) => start <= end,
		(Bound::Included(start), Bound::Excluded(end)) => start < end,
		(Bound::Excluded(start), Bound::Included(end)) => start < end,
		(Bound::Excluded(start), Bound::Excluded(end)) => start < end,
		_ => true,
	}
}

#[tested]
fn overlaps<I, A, B>(a: &A, b: &B) -> bool
where
	A: RangeBounds<I>,
	B: RangeBounds<I>,
	I: PartialOrd,
{
	!matches!(sorted_config(a, b), SortedConfig::NonOverlapping(_, _))
}

#[tested]
fn touches<I, A, B>(a: &A, b: &B) -> bool
where
	A: RangeBounds<I>,
	B: RangeBounds<I>,
	I: PartialOrd,
{
	match sorted_config(a, b) {
		SortedConfig::NonOverlapping(a, b) => match (a.1, b.0) {
			(Bound::Included(point1), Bound::Excluded(point2)) => {
				point1 == point2
			}
			(Bound::Excluded(point1), Bound::Included(point2)) => {
				point1 == point2
			}
			_ => false,
		},
		_ => false,
	}
}

#[trivial]
fn expand<I, K>(range_bounds: &K) -> (Bound<&I>, Bound<&I>)
where
	K: RangeBounds<I>,
{
	(range_bounds.start_bound(), range_bounds.end_bound())
}

#[trivial]
fn expand_cloned<I, K>(range_bounds: &K) -> (Bound<I>, Bound<I>)
where
	K: RangeBounds<I>,
	I: Clone,
{
	cloned_bounds(expand(range_bounds))
}

#[trivial]
fn cloned_bounds<I>(
	(start, end): (Bound<&I>, Bound<&I>),
) -> (Bound<I>, Bound<I>)
where
	I: Clone,
{
	(start.cloned(), end.cloned())
}

#[trivial]
fn flip_bound<I>(bound: Bound<&I>) -> Bound<&I> {
	match bound {
		Bound::Included(point) => Bound::Excluded(point),
		Bound::Excluded(point) => Bound::Included(point),
		Bound::Unbounded => Bound::Unbounded,
	}
}

#[cfg(test)]
mod tests {
	use std::ops::{Bound, Range, RangeBounds};

	use pretty_assertions::assert_eq;

	use super::*;
	use crate::bound_ord::BoundOrd;

	type TestBounds = (Bound<u8>, Bound<u8>);

	//only every other number to allow mathematical_overlapping_definition
	//to test between bounds in finite using smaller intervalled finite
	pub(crate) const NUMBERS: &'static [u8] = &[2, 4, 6, 8, 10];
	//go a bit around on either side to compensate for Unbounded
	pub(crate) const NUMBERS_DOMAIN: &'static [u8] =
		&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

	fn basic() -> RangeBoundsMap<u8, TestBounds, bool> {
		RangeBoundsMap::try_from([
			(ui(4), false),
			(ee(5, 7), true),
			(ii(7, 7), false),
			(ie(14, 16), true),
		])
		.unwrap()
	}

	fn special() -> RangeBoundsMap<u8, MultiBounds, bool> {
		RangeBoundsMap::try_from([
			(mii(4, 6), false),
			(mee(7, 8), true),
			(mii(8, 12), false),
		])
		.unwrap()
	}

	#[derive(Debug, PartialEq, Clone)]
	enum MultiBounds {
		Inclusive(u8, u8),
		Exclusive(u8, u8),
	}

	fn mii(start: u8, end: u8) -> MultiBounds {
		MultiBounds::Inclusive(start, end)
	}
	fn mee(start: u8, end: u8) -> MultiBounds {
		MultiBounds::Exclusive(start, end)
	}

	impl RangeBounds<u8> for MultiBounds {
		fn start_bound(&self) -> Bound<&u8> {
			match self {
				MultiBounds::Inclusive(start, _) => Bound::Included(start),
				MultiBounds::Exclusive(start, _) => Bound::Excluded(start),
			}
		}
		fn end_bound(&self) -> Bound<&u8> {
			match self {
				MultiBounds::Inclusive(_, end) => Bound::Included(end),
				MultiBounds::Exclusive(_, end) => Bound::Excluded(end),
			}
		}
	}
	impl TryFromBounds<u8> for MultiBounds {
		fn try_from_bounds(
			start_bound: Bound<u8>,
			end_bound: Bound<u8>,
		) -> Option<Self> {
			match (start_bound, end_bound) {
				(Bound::Included(start), Bound::Included(end)) => {
					Some(mii(start, end))
				}
				(Bound::Excluded(start), Bound::Excluded(end)) => {
					Some(mee(start, end))
				}
				_ => None,
			}
		}
	}

	#[test]
	fn insert_strict_tests() {
		assert_insert_strict(
			basic(),
			(ii(0, 4), false),
			Err(OverlapError),
			None::<[_; 0]>,
		);
		assert_insert_strict(
			basic(),
			(ii(5, 6), false),
			Err(OverlapError),
			None::<[_; 0]>,
		);
		assert_insert_strict(
			basic(),
			(ee(7, 8), false),
			Ok(()),
			Some([
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ee(7, 8), false),
				(ie(14, 16), true),
			]),
		);
		assert_insert_strict(
			basic(),
			(ii(4, 5), true),
			Err(OverlapError),
			None::<[_; 0]>,
		);
		assert_insert_strict(
			basic(),
			(ei(4, 5), true),
			Ok(()),
			Some([
				(ui(4), false),
				(ei(4, 5), true),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			]),
		);
	}
	fn assert_insert_strict<const N: usize>(
		mut before: RangeBoundsMap<u8, TestBounds, bool>,
		to_insert: (TestBounds, bool),
		result: Result<(), OverlapError>,
		after: Option<[(TestBounds, bool); N]>,
	) {
		let clone = before.clone();
		assert_eq!(before.insert_strict(to_insert.0, to_insert.1), result);
		match after {
			Some(after) => {
				assert_eq!(before, RangeBoundsMap::try_from(after).unwrap())
			}
			None => assert_eq!(before, clone),
		}
	}

	#[test]
	fn overlapping_tests() {
		//case zero
		for overlap_range in all_valid_test_bounds() {
			//you can't overlap nothing
			assert!(
				RangeBoundsMap::<u8, Range<u8>, ()>::new()
					.overlapping(&overlap_range)
					.next()
					.is_none()
			);
		}

		//case one
		for overlap_range in all_valid_test_bounds() {
			for inside_range in all_valid_test_bounds() {
				let mut range_bounds_map = RangeBoundsMap::new();
				range_bounds_map.insert_strict(inside_range, ()).unwrap();

				let mut expected_overlapping = Vec::new();
				if overlaps(&overlap_range, &inside_range) {
					expected_overlapping.push(inside_range);
				}

				let overlapping = range_bounds_map
					.overlapping(&overlap_range)
					.map(|(key, _)| key)
					.copied()
					.collect::<Vec<_>>();

				if overlapping != expected_overlapping {
					dbg!(overlap_range, inside_range);
					dbg!(overlapping, expected_overlapping);
					panic!(
						"Discrepency in .overlapping() with single inside range detected!"
					);
				}
			}
		}

		//case two
		for overlap_range in all_valid_test_bounds() {
			for (inside_range1, inside_range2) in
				all_non_overlapping_test_bound_pairs()
			{
				let mut range_bounds_map = RangeBoundsMap::new();
				range_bounds_map.insert_strict(inside_range1, ()).unwrap();
				range_bounds_map.insert_strict(inside_range2, ()).unwrap();

				let mut expected_overlapping = Vec::new();
				if overlaps(&overlap_range, &inside_range1) {
					expected_overlapping.push(inside_range1);
				}
				if overlaps(&overlap_range, &inside_range2) {
					expected_overlapping.push(inside_range2);
				}
				//make our expected_overlapping the correct order
				if expected_overlapping.len() > 1 {
					if BoundOrd::start(expected_overlapping[0].start_bound())
						> BoundOrd::start(expected_overlapping[1].start_bound())
					{
						expected_overlapping.swap(0, 1);
					}
				}

				let overlapping = range_bounds_map
					.overlapping(&overlap_range)
					.map(|(key, _)| key)
					.copied()
					.collect::<Vec<_>>();

				if overlapping != expected_overlapping {
					dbg!(overlap_range, inside_range1, inside_range2);
					dbg!(overlapping, expected_overlapping);
					panic!(
						"Discrepency in .overlapping() with two inside ranges detected!"
					);
				}
			}
		}
	}

	#[test]
	fn overlapping_trimmed_tests() {
		//case zero
		for overlap_range in all_valid_test_bounds() {
			//you can't overlap nothing
			assert!(
				RangeBoundsMap::<u8, Range<u8>, ()>::new()
					.overlapping_trimmed(&overlap_range)
					.next()
					.is_none()
			);
		}

		//case one
		for overlap_range in all_valid_test_bounds() {
			for inside_range in all_valid_test_bounds() {
				let mut range_bounds_map = RangeBoundsMap::new();
				range_bounds_map.insert_strict(inside_range, ()).unwrap();

				let result = range_bounds_map
					.overlapping_trimmed(&overlap_range)
					.map(|(key, value)| (cloned_bounds(key), value.clone()))
					.collect::<RangeBoundsMap<u8, TestBounds, ()>>();

				for i in NUMBERS_DOMAIN {
					assert_eq!(
						overlap_range.contains(i) && inside_range.contains(i),
						result.contains_point(i)
					);
				}
			}
		}

		//case two
		for overlap_range in all_valid_test_bounds() {
			for (inside_range1, inside_range2) in
				all_non_overlapping_test_bound_pairs()
			{
				let mut range_bounds_map = RangeBoundsMap::new();
				range_bounds_map.insert_strict(inside_range1, ()).unwrap();
				range_bounds_map.insert_strict(inside_range2, ()).unwrap();

				let result = range_bounds_map
					.overlapping_trimmed(&overlap_range)
					.map(|(key, value)| (cloned_bounds(key), value.clone()))
					.collect::<RangeBoundsMap<u8, TestBounds, ()>>();

				for i in NUMBERS_DOMAIN {
					assert_eq!(
						overlap_range.contains(i)
							&& (inside_range1.contains(i)
								|| inside_range2.contains(i)),
						result.contains_point(i)
					);
				}
			}
		}
	}

	#[test]
	fn remove_overlapping_tests() {
		assert_remove_overlapping(basic(), ii(5, 5), [], None::<[_; 0]>);
		assert_remove_overlapping(
			basic(),
			uu(),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			],
			Some([]),
		);
		assert_remove_overlapping(
			basic(),
			ii(6, 7),
			[(ee(5, 7), true), (ii(7, 7), false)],
			Some([(ui(4), false), (ie(14, 16), true)]),
		);
		assert_remove_overlapping(
			basic(),
			iu(6),
			[(ee(5, 7), true), (ii(7, 7), false), (ie(14, 16), true)],
			Some([(ui(4), false)]),
		);
	}
	fn assert_remove_overlapping<const N: usize, const Y: usize>(
		mut before: RangeBoundsMap<u8, TestBounds, bool>,
		to_remove: TestBounds,
		result: [(TestBounds, bool); N],
		after: Option<[(TestBounds, bool); Y]>,
	) {
		let clone = before.clone();
		assert_eq!(
			before.remove_overlapping(&to_remove).collect::<Vec<_>>(),
			result
		);
		match after {
			Some(after) => {
				assert_eq!(before, RangeBoundsMap::try_from(after).unwrap())
			}
			None => assert_eq!(before, clone),
		}
	}

	#[test]
	fn cut_tests() {
		assert_cut(basic(), ii(50, 60), Ok([]), None::<[_; 0]>);
		assert_cut(
			basic(),
			uu(),
			Ok([
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			]),
			Some([]),
		);
		assert_cut(
			basic(),
			ui(6),
			Ok([(ui(4), false), (ei(5, 6), true)]),
			Some([(ee(6, 7), true), (ii(7, 7), false), (ie(14, 16), true)]),
		);
		assert_cut(
			basic(),
			iu(6),
			Ok([(ie(6, 7), true), (ii(7, 7), false), (ie(14, 16), true)]),
			Some([(ui(4), false), (ee(5, 6), true)]),
		);

		assert_cut(
			special(),
			mee(5, 7),
			Ok([((Bound::Excluded(5), Bound::Included(6)), false)]),
			Some([(mii(4, 5), false), (mee(7, 8), true), (mii(8, 12), false)]),
		);
		assert_cut(special(), mee(6, 7), Ok([]), None::<[_; 0]>);
		assert_cut(
			special(),
			mii(5, 6),
			Err::<[_; 0], _>(TryFromBoundsError),
			None::<[_; 0]>,
		);
		assert_cut(
			special(),
			mii(6, 7),
			Err::<[_; 0], _>(TryFromBoundsError),
			None::<[_; 0]>,
		);
		assert_cut(
			special(),
			7..8,
			Ok([(expand_cloned(&mee(7, 8)), true)]),
			Some([(mii(4, 6), false), (mii(8, 12), false)]),
		);
		assert_cut(
			special(),
			mii(7, 10),
			Err::<[_; 0], _>(TryFromBoundsError),
			None::<[_; 0]>,
		);
		assert_cut(
			special(),
			mee(4, 6),
			Ok([(expand_cloned(&mee(4, 6)), false)]),
			Some([
				(mii(4, 4), false),
				(mii(6, 6), false),
				(mee(7, 8), true),
				(mii(8, 12), false),
			]),
		);
	}

	fn assert_cut<const N: usize, const Y: usize, Q, I, K, V>(
		mut before: RangeBoundsMap<I, K, V>,
		to_cut: Q,
		result: Result<[((Bound<I>, Bound<I>), V); Y], TryFromBoundsError>,
		after: Option<[(K, V); N]>,
	) where
		I: Ord + Clone + Debug,
		K: Clone + TryFromBounds<I> + Debug + PartialEq,
		V: Clone + Debug + PartialEq,
		K: RangeBounds<I>,
		Q: RangeBounds<I>,
	{
		let clone = before.clone();
		match before.cut(&to_cut) {
			Ok(iter) => {
				assert_eq!(iter.collect::<Vec<_>>(), result.unwrap());
			}
			Err(x) => {
				assert_eq!(x, result.unwrap_err());
			}
		}
		match after {
			Some(after) => {
				assert_eq!(before, RangeBoundsMap::try_from(after).unwrap())
			}
			None => assert_eq!(before, clone),
		}
	}

	#[test]
	fn gaps_tests() {
		assert_gaps(basic(), ii(50, 60), [ii(50, 60)]);
		assert_gaps(basic(), iu(50), [iu(50)]);
		assert_gaps(basic(), ee(3, 16), [ei(4, 5), ee(7, 14)]);
		assert_gaps(basic(), ei(3, 16), [ei(4, 5), ee(7, 14), ii(16, 16)]);
		assert_gaps(basic(), ue(5), [ee(4, 5)]);
		assert_gaps(basic(), ui(3), []);
		assert_gaps(basic(), ii(5, 5), [ii(5, 5)]);
		assert_gaps(basic(), ii(6, 6), []);
		assert_gaps(basic(), ii(7, 7), []);
		assert_gaps(basic(), ii(8, 8), [ii(8, 8)]);
	}
	fn assert_gaps<const N: usize>(
		range_bounds_map: RangeBoundsMap<u8, TestBounds, bool>,
		outer_range_bounds: TestBounds,
		result: [TestBounds; N],
	) {
		assert_eq!(
			range_bounds_map
				.gaps(&outer_range_bounds)
				.map(|(start, end)| (start.cloned(), end.cloned()))
				.collect::<Vec<_>>(),
			result
		);
	}

	#[test]
	fn insert_merge_touching_tests() {
		assert_insert_merge_touching(
			basic(),
			(ii(0, 4), false),
			Err(OverlapOrTryFromBoundsError::Overlap(OverlapError)),
			None::<[_; 0]>,
		);
		assert_insert_merge_touching(
			basic(),
			(ee(7, 10), false),
			Ok(&ie(7, 10)),
			Some([
				(ui(4), false),
				(ee(5, 7), true),
				(ie(7, 10), false),
				(ie(14, 16), true),
			]),
		);
		assert_insert_merge_touching(
			basic(),
			(ee(7, 11), true),
			Ok(&ie(7, 11)),
			Some([
				(ui(4), false),
				(ee(5, 7), true),
				(ie(7, 11), true),
				(ie(14, 16), true),
			]),
		);
		assert_insert_merge_touching(
			basic(),
			(ee(12, 13), true),
			Ok(&ee(12, 13)),
			Some([
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ee(12, 13), true),
				(ie(14, 16), true),
			]),
		);
		assert_insert_merge_touching(
			basic(),
			(ee(13, 14), false),
			Ok(&ee(13, 16)),
			Some([
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ee(13, 16), false),
			]),
		);
		assert_insert_merge_touching(
			basic(),
			(ee(7, 14), false),
			Ok(&ie(7, 16)),
			Some([(ui(4), false), (ee(5, 7), true), (ie(7, 16), false)]),
		);

		assert_insert_merge_touching(
			special(),
			(mee(6, 7), true),
			Err(OverlapOrTryFromBoundsError::TryFromBounds(
				TryFromBoundsError,
			)),
			None::<[_; 0]>,
		);
		assert_insert_merge_touching(
			special(),
			(mii(6, 7), true),
			Err(OverlapOrTryFromBoundsError::Overlap(OverlapError)),
			None::<[_; 0]>,
		);
		assert_insert_merge_touching(
			special(),
			(mee(12, 15), true),
			Err(OverlapOrTryFromBoundsError::TryFromBounds(
				TryFromBoundsError,
			)),
			None::<[_; 0]>,
		);
		assert_insert_merge_touching(
			special(),
			(mii(12, 15), true),
			Err(OverlapOrTryFromBoundsError::Overlap(OverlapError)),
			None::<[_; 0]>,
		);
	}
	fn assert_insert_merge_touching<const N: usize, I, K, V>(
		mut before: RangeBoundsMap<I, K, V>,
		to_insert: (K, V),
		result: Result<&K, OverlapOrTryFromBoundsError>,
		after: Option<[(K, V); N]>,
	) where
		I: Ord + Clone + Debug,
		K: Clone + TryFromBounds<I> + Debug + PartialEq,
		V: Clone + Debug + PartialEq,
		K: RangeBounds<I>,
	{
		let clone = before.clone();
		assert_eq!(
			before.insert_merge_touching(to_insert.0, to_insert.1),
			result
		);
		match after {
			Some(after) => {
				assert_eq!(before, RangeBoundsMap::try_from(after).unwrap())
			}
			None => assert_eq!(before, clone),
		}
	}

	#[test]
	fn insert_merge_overlapping_tests() {
		assert_insert_merge_overlapping(
			basic(),
			(ii(0, 2), true),
			Ok(&(ui(4))),
			Some([
				(ui(4), true),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			]),
		);
		assert_insert_merge_overlapping(
			basic(),
			(ie(14, 16), false),
			Ok(&ie(14, 16)),
			Some([
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), false),
			]),
		);
		assert_insert_merge_overlapping(
			basic(),
			(ii(6, 11), false),
			Ok(&ei(5, 11)),
			Some([(ui(4), false), (ei(5, 11), false), (ie(14, 16), true)]),
		);
		assert_insert_merge_overlapping(
			basic(),
			(ii(15, 18), true),
			Ok(&ii(14, 18)),
			Some([
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ii(14, 18), true),
			]),
		);
		assert_insert_merge_overlapping(
			basic(),
			(uu(), false),
			Ok(&uu()),
			Some([(uu(), false)]),
		);

		assert_insert_merge_overlapping(
			special(),
			(mii(10, 18), true),
			Ok(&mii(8, 18)),
			Some([(mii(4, 6), false), (mee(7, 8), true), (mii(8, 18), true)]),
		);
		assert_insert_merge_overlapping(
			special(),
			(mee(10, 18), true),
			Err(TryFromBoundsError),
			None::<[_; 0]>,
		);
		assert_insert_merge_overlapping(
			special(),
			(mee(8, 12), true),
			Ok(&mii(8, 12)),
			Some([(mii(4, 6), false), (mee(7, 8), true), (mii(8, 12), true)]),
		);
		assert_insert_merge_overlapping(
			special(),
			(mee(7, 8), false),
			Ok(&mee(7, 8)),
			Some([(mii(4, 6), false), (mee(7, 8), false), (mii(8, 12), false)]),
		);
		assert_insert_merge_overlapping(
			special(),
			(mii(7, 8), false),
			Ok(&mii(7, 12)),
			Some([(mii(4, 6), false), (mii(7, 12), false)]),
		);
	}
	fn assert_insert_merge_overlapping<const N: usize, I, K, V>(
		mut before: RangeBoundsMap<I, K, V>,
		to_insert: (K, V),
		result: Result<&K, TryFromBoundsError>,
		after: Option<[(K, V); N]>,
	) where
		I: Ord + Clone + Debug,
		K: Clone + TryFromBounds<I> + Debug + PartialEq,
		V: Clone + Debug + PartialEq,
		K: RangeBounds<I>,
	{
		let clone = before.clone();
		assert_eq!(
			before.insert_merge_overlapping(to_insert.0, to_insert.1),
			result
		);
		match after {
			Some(after) => {
				assert_eq!(before, RangeBoundsMap::try_from(after).unwrap())
			}
			None => assert_eq!(before, clone),
		}
	}

	#[test]
	fn insert_merge_touching_or_overlapping_tests() {
		assert_insert_merge_touching_or_overlapping(
			RangeBoundsMap::try_from([(1..4, false)]).unwrap(),
			(-4..1, true),
			Ok(&(-4..4)),
			Some([(-4..4, true)]),
		);

		//copied from insert_merge_overlapping_tests
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(ii(0, 2), true),
			Ok(&(ui(4))),
			Some([
				(ui(4), true),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			]),
		);
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(ie(14, 16), false),
			Ok(&ie(14, 16)),
			Some([
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), false),
			]),
		);
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(ii(6, 11), false),
			Ok(&ei(5, 11)),
			Some([(ui(4), false), (ei(5, 11), false), (ie(14, 16), true)]),
		);
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(ii(15, 18), true),
			Ok(&ii(14, 18)),
			Some([
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ii(14, 18), true),
			]),
		);
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(uu(), false),
			Ok(&uu()),
			Some([(uu(), false)]),
		);
		//the only difference from the insert_merge_overlapping
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(ii(7, 14), false),
			Ok(&ee(5, 16)),
			Some([(ui(4), false), (ee(5, 16), false)]),
		);

		//copied from insert_merge_overlapping_tests
		assert_insert_merge_touching_or_overlapping(
			special(),
			(mii(10, 18), true),
			Ok(&mii(8, 18)),
			Some([(mii(4, 6), false), (mee(7, 8), true), (mii(8, 18), true)]),
		);
		assert_insert_merge_touching_or_overlapping(
			special(),
			(mee(10, 18), true),
			Err(TryFromBoundsError),
			None::<[_; 0]>,
		);
		assert_insert_merge_touching_or_overlapping(
			special(),
			(mee(8, 12), true),
			Ok(&mii(8, 12)),
			Some([(mii(4, 6), false), (mee(7, 8), true), (mii(8, 12), true)]),
		);
		assert_insert_merge_touching_or_overlapping(
			special(),
			(mee(7, 8), false),
			Err(TryFromBoundsError),
			None::<[_; 0]>,
		);
		assert_insert_merge_touching_or_overlapping(
			special(),
			(mii(7, 8), false),
			Ok(&mii(7, 12)),
			Some([(mii(4, 6), false), (mii(7, 12), false)]),
		);
		//copied from insert_merge_touching_tests
		assert_insert_merge_touching_or_overlapping(
			special(),
			(mee(6, 7), true),
			Err(TryFromBoundsError),
			None::<[_; 0]>,
		);
		assert_insert_merge_touching_or_overlapping(
			special(),
			(mee(12, 15), true),
			Err(TryFromBoundsError),
			None::<[_; 0]>,
		);
	}
	fn assert_insert_merge_touching_or_overlapping<const N: usize, I, K, V>(
		mut before: RangeBoundsMap<I, K, V>,
		to_insert: (K, V),
		result: Result<&K, TryFromBoundsError>,
		after: Option<[(K, V); N]>,
	) where
		I: Ord + Clone + Debug,
		K: Clone + TryFromBounds<I> + Debug + PartialEq,
		V: Clone + Debug + PartialEq,
		K: RangeBounds<I>,
	{
		let clone = before.clone();
		assert_eq!(
			before
				.insert_merge_touching_or_overlapping(to_insert.0, to_insert.1),
			result
		);
		match after {
			Some(after) => {
				assert_eq!(before, RangeBoundsMap::try_from(after).unwrap())
			}
			None => assert_eq!(before, clone),
		}
	}

	#[test]
	fn config_tests() {
		assert_eq!(config(&(1..4), &(6..8)), Config::LeftFirstNonOverlapping);
		assert_eq!(config(&(1..4), &(2..8)), Config::LeftFirstPartialOverlap);
		assert_eq!(config(&(1..4), &(2..3)), Config::LeftContainsRight);

		assert_eq!(config(&(6..8), &(1..4)), Config::RightFirstNonOverlapping);
		assert_eq!(config(&(2..8), &(1..4)), Config::RightFirstPartialOverlap);
		assert_eq!(config(&(2..3), &(1..4)), Config::RightContainsLeft);
	}

	#[test]
	fn overlaps_tests() {
		for range_bounds1 in all_valid_test_bounds() {
			for range_bounds2 in all_valid_test_bounds() {
				let our_answer = overlaps(&range_bounds1, &range_bounds2);

				let mathematical_definition_of_overlap =
					NUMBERS_DOMAIN.iter().any(|x| {
						range_bounds1.contains(x) && range_bounds2.contains(x)
					});

				if our_answer != mathematical_definition_of_overlap {
					dbg!(range_bounds1, range_bounds2);
					dbg!(mathematical_definition_of_overlap, our_answer);
					panic!("Discrepency in overlaps() detected!");
				}
			}
		}
	}

	#[test]
	fn cut_range_bounds_tests() {
		for base in all_valid_test_bounds() {
			for cut in all_valid_test_bounds() {
				let cut_result @ CutResult {
					before_cut: b,
					inside_cut: i,
					after_cut: a,
				} = cut_range_bounds(&base, &cut);

				let mut on_left = true;

				// The definition of a cut is: A && NOT B
				for x in NUMBERS_DOMAIN {
					let base_contains = base.contains(x);
					let cut_contains = cut.contains(x);

					if cut_contains {
						on_left = false;
					}

					let invariant = match (base_contains, cut_contains) {
						(false, _) => !con(b, x) && !con(i, x) && !con(a, x),
						(true, false) => {
							if on_left {
								con(b, x) && !con(i, x) && !con(a, x)
							} else {
								!con(b, x) && !con(i, x) && con(a, x)
							}
						}
						(true, true) => !con(b, x) && con(i, x) && !con(a, x),
					};

					if !invariant {
						dbg!(base_contains);
						dbg!(cut_contains);

						dbg!(on_left);

						dbg!(base);
						dbg!(cut);
						dbg!(cut_result);

						dbg!(x);

						panic!("Invariant Broken!");
					}
				}
			}
		}
	}
	fn con(x: Option<(Bound<&u8>, Bound<&u8>)>, point: &u8) -> bool {
		match x {
			Some(y) => y.contains(point),
			None => false,
		}
	}
	#[test]
	fn cut_range_bounds_should_return_valid_ranges() {
		let result = cut_range_bounds(&(3..8), &(5..8));
		if let Some(x) = result.before_cut {
			assert!(is_valid_range_bounds(&cloned_bounds(x)));
		}
		if let Some(x) = result.inside_cut {
			assert!(is_valid_range_bounds(&cloned_bounds(x)));
		}
		if let Some(x) = result.after_cut {
			assert!(is_valid_range_bounds(&cloned_bounds(x)));
		}

		let result = cut_range_bounds(&(3..8), &(3..5));
		if let Some(x) = result.before_cut {
			assert!(is_valid_range_bounds(&cloned_bounds(x)));
		}
		if let Some(x) = result.inside_cut {
			assert!(is_valid_range_bounds(&cloned_bounds(x)));
		}
		if let Some(x) = result.after_cut {
			assert!(is_valid_range_bounds(&cloned_bounds(x)));
		}
	}

	#[test]
	fn touches_tests() {
		for range_bounds1 in all_valid_test_bounds() {
			for range_bounds2 in all_valid_test_bounds() {
				let our_answer = touches(&range_bounds1, &range_bounds2);

				let mathematical_definition_of_touches =
					NUMBERS_DOMAIN.iter().tuple_windows().any(|(x1, x2)| {
						(range_bounds1.contains(x1)
							&& !range_bounds1.contains(x2)
							&& range_bounds2.contains(x2)
							&& !range_bounds2.contains(x1))
							|| (range_bounds1.contains(x2)
								&& !range_bounds1.contains(x1) && range_bounds2
								.contains(x1) && !range_bounds2.contains(x2))
					});

				if our_answer != mathematical_definition_of_touches {
					dbg!(range_bounds1, range_bounds2);
					dbg!(mathematical_definition_of_touches, our_answer);
					panic!("Discrepency in touches() detected!");
				}
			}
		}
	}

	// Test Helper Functions
	//======================
	fn all_non_overlapping_test_bound_pairs() -> Vec<(TestBounds, TestBounds)> {
		let mut output = Vec::new();
		for test_bounds1 in all_valid_test_bounds() {
			for test_bounds2 in all_valid_test_bounds() {
				if !overlaps(&test_bounds1, &test_bounds2) {
					output.push((test_bounds1, test_bounds2));
				}
			}
		}

		return output;
	}

	fn all_valid_test_bounds() -> Vec<TestBounds> {
		let mut output = Vec::new();

		//bounded-bounded
		output.append(&mut all_finite_bounded_pairs());
		//bounded-unbounded
		for start_bound in all_finite_bounded() {
			output.push((start_bound, u()));
		}
		//unbounded-bounded
		for end_bound in all_finite_bounded() {
			output.push((u(), end_bound));
		}
		//unbounded-unbounded
		output.push(uu());

		return output;
	}

	fn all_finite_bounded_pairs() -> Vec<(Bound<u8>, Bound<u8>)> {
		let mut output = Vec::new();
		for i in NUMBERS {
			for j in NUMBERS {
				for i_ex in [false, true] {
					for j_ex in [false, true] {
						if j > i || (j == i && !i_ex && !j_ex) {
							output.push((
								finite_bound(*i, i_ex),
								finite_bound(*j, j_ex),
							));
						}
					}
				}
			}
		}
		return output;
	}

	fn all_finite_bounded() -> Vec<Bound<u8>> {
		let mut output = Vec::new();
		for i in NUMBERS {
			for j in 0..=1 {
				output.push(finite_bound(*i, j == 1));
			}
		}
		return output;
	}

	fn finite_bound(x: u8, included: bool) -> Bound<u8> {
		match included {
			false => Bound::Included(x),
			true => Bound::Excluded(x),
		}
	}

	fn uu() -> TestBounds {
		(Bound::Unbounded, Bound::Unbounded)
	}
	fn ui(x: u8) -> TestBounds {
		(Bound::Unbounded, Bound::Included(x))
	}
	fn ue(x: u8) -> TestBounds {
		(Bound::Unbounded, Bound::Excluded(x))
	}
	fn iu(x: u8) -> TestBounds {
		(Bound::Included(x), Bound::Unbounded)
	}
	//fn eu(x: u8) -> TestBounds {
	//(Bound::Excluded(x), Bound::Unbounded)
	//}
	fn ii(x1: u8, x2: u8) -> TestBounds {
		(Bound::Included(x1), Bound::Included(x2))
	}
	fn ie(x1: u8, x2: u8) -> TestBounds {
		(Bound::Included(x1), Bound::Excluded(x2))
	}
	fn ei(x1: u8, x2: u8) -> TestBounds {
		(Bound::Excluded(x1), Bound::Included(x2))
	}
	fn ee(x1: u8, x2: u8) -> TestBounds {
		(Bound::Excluded(x1), Bound::Excluded(x2))
	}
	fn u() -> Bound<u8> {
		Bound::Unbounded
	}
}
