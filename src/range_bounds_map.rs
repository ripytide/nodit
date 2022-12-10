/*
Copyright 2022 James Forster

This file is part of range_bounds_map.

range_bounds_map is free software: you can redistribute it and/or
modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

range_bounds_map is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with range_bounds_map. If not, see <https://www.gnu.org/licenses/>.
*/

use std::collections::BTreeMap;
use std::fmt::Debug;
use std::iter::once;
use std::ops::{Bound, RangeBounds};

use either::Either;
use itertools::Itertools;
use labels::{tested, trivial, untested};
use serde::{Deserialize, Serialize};

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
/// map.insert_platonic(ExEx::new(0.0, 5.0), 8).unwrap();
/// map.insert_platonic(ExEx::new(5.0, 7.5), 32).unwrap();
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
#[derive(Debug, Serialize, Deserialize, PartialEq, Eq, Clone)]
pub struct RangeBoundsMap<I, K, V>
where
	I: PartialOrd,
{
	starts: BTreeMap<BoundOrd<I>, (K, V)>,
}

/// An error type to represent a `RangeBounds` overlapping another
/// `RangeBounds` when it should not have.
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
/// created via [`TryFromBounds`].
///
/// ```
/// use range_bounds_map::{RangeBoundsMap, TryFromBoundsError};
///
/// let mut range_bounds_map =
/// 	RangeBoundsMap::try_from([(2..8, true)]).unwrap();
///
/// assert_eq!(
/// 	range_bounds_map.cut(&(4..=6)),
/// 	Err(TryFromBoundsError)
/// );
/// ```
///
/// # Example with `insert_coalesce_*` functions.
///
/// The second and final way you may recieve a [`TryFromBoundsError`]
/// is via coalescing methods such as
/// [`RangeBoundsMap::insert_coalesce_touching`].
///
/// In the first example it was fairly easy to create an invalid
/// `RangeBounds` by cutting with a different `RangeBounds` than the
/// underlying `RangeBoundsMap`'s `RangeBounds` type. However, the
/// `insert_coalesce_*` functions all take `range_bounds: K` as an
/// argument so it is not possible to create an invalid `K` type
/// directly. However upon "coalescing" of two `RangeBounds` (even if
/// both of them are type `K`), you can create a `RangeBounds` that *cannot* be
/// of type `K`.
///
/// In this example we use a `RangeBounds` type that can be either
/// Inclusive-Inclusive OR Exclusive-Exclusive. We then try to use
/// [`RangeBoundsMap::insert_coalesce_touching()`] to "coalesce" an
/// Inclusive-Inclusive and a Exclusive-Exclusive `MultiBounds`. This
/// will however fail as the resulting "coalesced" `RangeBounds` would
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
/// 	range_bounds_map.insert_coalesce_touching(
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
	/// range_bounds_map.insert_platonic(0..1, false).unwrap();
	/// assert_eq!(range_bounds_map.len(), 1);
	/// ```
	#[trivial]
	pub fn len(&self) -> usize {
		self.starts.len()
	}

	/// Adds a new (`RangeBounds`, `Value`) pair to the map without
	/// modifying other entries.
	///
	/// If the new `RangeBounds` overlaps one or more `RangeBounds`
	/// already in the map rather than just touching, then an
	/// [`OverlapError`] is returned and the map is not updated.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::{OverlapError, RangeBoundsMap};
	///
	/// let mut range_bounds_map = RangeBoundsMap::new();
	///
	/// assert_eq!(range_bounds_map.insert_platonic(5..10, 9), Ok(()));
	/// assert_eq!(
	/// 	range_bounds_map.insert_platonic(5..10, 2),
	/// 	Err(OverlapError)
	/// );
	/// assert_eq!(range_bounds_map.len(), 1);
	/// ```
	#[tested]
	pub fn insert_platonic(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<(), OverlapError> {
		if self.overlaps(&range_bounds) {
			return Err(OverlapError);
		}

		let start = BoundOrd::start(range_bounds.start_bound());
		let end = BoundOrd::end(range_bounds.end_bound());

		if start > end {
			panic!("Invalid search range bounds!");
		}

		self.starts.insert(
			BoundOrd::start(range_bounds.start_bound().cloned()),
			(range_bounds, value),
		);

		return Ok(());
	}

	/// Returns `true` if the given `RangeBounds` overlaps any of the
	/// `RangeBounds` in the map.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut range_bounds_map = RangeBoundsMap::new();
	///
	/// range_bounds_map.insert_platonic(5..10, false);
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
	/// in the map which overlap the given `range_bounds` in
	/// ascending order.
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
			panic!("Invalid range bounds!");
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
	/// overlaps the given `range_bounds` and returns them in
	/// an iterator.
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
	/// a tuple with their `Value`s.
	///
	/// If the remaining `RangeBounds` left in the map after the cut
	/// or the `RangeBounds` returned in the iterator are not able to
	/// be created with the [`TryFromBounds`] trait then a
	/// [`TryFromBoundsError`] will be returned.
	///
	/// `V` must implement `Clone` as if you try to cut out the center
	/// of a `RangeBounds` in the map it will split into two different
	/// (`RangeBounds`, `Value`) pairs using `Clone`. Or if you
	/// partially cut a `RangeBounds` then `V` must be cloned to be
	/// returned in the iterator.
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
	/// assert_eq!(base.cut(&(2..40)), Ok(()));
	/// assert_eq!(base, after_cut);
	/// assert_eq!(base.cut(&(60..=80)), Err(TryFromBoundsError));
	/// ```
	//#[untested]
	//pub fn cut<Q>(&mut self, range_bounds: &Q) -> Result<(), TryFromBoundsError>
	//where
	//Q: RangeBounds<I>,
	//K: TryFromBounds<I>,
	//V: Clone,
	//{
	//let mut to_insert = Vec::new();

	//{
	//let mut overlapping = self.overlapping(range_bounds);

	//let first_last = (overlapping.next(), overlapping.next_back());

	//match first_last {
	//(Some(first), Some(last)) => {
	//match cut_range_bounds(first.0, range_bounds) {
	//CutResult::Nothing => {}
	//CutResult::Single(left_section) => {
	//to_insert.push((left_section, first.1.clone()));
	//}
	//CutResult::Double(_, _) => unreachable!(),
	//}
	//match cut_range_bounds(last.0, range_bounds) {
	//CutResult::Nothing => {}
	//CutResult::Single(right_section) => {
	//to_insert.push((right_section, last.1.clone()));
	//}
	//CutResult::Double(_, _) => unreachable!(),
	//}
	//(Some(first), None) => {
	//match cut_range_bounds(first.0, range_bounds) {
	//CutResult::Nothing => {}
	//CutResult::Single(section) => {
	//to_insert.push((section, first.1.clone()));
	//}
	//CutResult::Double(left_section, right_section) => {
	//to_insert.push((left_section, first.1.clone()));
	//to_insert.push((right_section, first.1.clone()));
	//}
	//(None, None) => {}
	//(None, Some(_)) => unreachable!(),
	//}

	//// Make sure that the inserts will work before we try to do
	//// them, so if one fails the map remains unchanged
	//if to_insert.iter().all(|(x, _)| K::is_valid(x)) {
	//let removed = self.remove_overlapping(range_bounds);
	//for ((start, end), value) in to_insert.into_iter() {
	//self.insert_platonic(
	//K::try_from_bounds(start, end).unwrap(),
	//value.clone(),
	//)
	//.unwrap();
	//}
	//return Ok(());
	//} else {
	//return Err(TryFromBoundsError);
	//}

	/// Returns an iterator of `(Bound<&I>, Bound<&I>)` over all the
	/// maximally-sized gaps in the map that are also within the given
	/// `outer_range_bounds`.
	///
	/// To get all possible gaps call `gaps()` with an unbounded
	/// `RangeBounds` such as `&(..)` or `&(Bound::Unbounded,
	/// Bound::Unbounded)`.
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

	/// Returns `true` if the map covers every point in the given
	/// `RangeBounds`, and `false` if it doesn't.
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
	/// coalesces into other `RangeBounds` in the map which touch it.
	///
	/// The `Value` of the coalesced `RangeBounds` is set to the given
	/// `Value`.
	///
	/// If successful then a reference to the newly inserted
	/// `RangeBounds` is returned.
	///
	/// If the new `RangeBounds` overlaps one or more `RangeBounds`
	/// already in the map rather than just touching, then an
	/// [`OverlapError`] is returned and the map is not updated.
	/// `RangeBounds` is returned.
	///
	/// If the coalesced `RangeBounds` cannot be created with the
	/// [`TryFromBounds`] trait then a [`TryFromBoundsError`] will be
	/// returned.
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
	/// 	range_bounds_map.insert_coalesce_touching(4..6, true),
	/// 	Ok(&(1..6))
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	range_bounds_map.insert_coalesce_touching(4..8, false),
	/// 	Err(OverlapOrTryFromBoundsError::Overlap(OverlapError)),
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	range_bounds_map.insert_coalesce_touching(10..16, false),
	/// 	Ok(&(10..16))
	/// );
	///
	/// assert_eq!(
	/// 	range_bounds_map.iter().collect::<Vec<_>>(),
	/// 	[(&(1..6), &true), (&(10..16), &false)]
	/// );
	/// ```
	#[tested]
	pub fn insert_coalesce_touching(
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
	/// coalesces into other `RangeBounds` in the map which overlap
	/// it.
	///
	/// The `Value` of the coalesced `RangeBounds` is set to the given
	/// `Value`.
	///
	/// If successful then a reference to the newly inserted
	/// `RangeBounds` is returned.
	///
	/// If the coalesced `RangeBounds` cannot be created with the
	/// [`TryFromBounds`] trait then a [`TryFromBoundsError`] will be
	/// returned.
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
	/// 	range_bounds_map.insert_coalesce_overlapping(-4..1, true),
	/// 	Ok(&(-4..1))
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	range_bounds_map.insert_coalesce_overlapping(2..8, true),
	/// 	Ok(&(1..8))
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	range_bounds_map.insert_coalesce_overlapping(10..16, false),
	/// 	Ok(&(10..16))
	/// );
	///
	/// assert_eq!(
	/// 	range_bounds_map.iter().collect::<Vec<_>>(),
	/// 	[(&(-4..1), &true), (&(1..8), &true), (&(10..16), &false)]
	/// );
	/// ```
	#[tested]
	pub fn insert_coalesce_overlapping(
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
	/// coalesces into other `RangeBounds` in the map which touch or
	/// overlap it.
	///
	/// The `Value` of the coalesced `RangeBounds` is set to the given
	/// `Value`.
	///
	/// If successful then a reference to the newly inserted
	/// `RangeBounds` is returned.
	///
	/// If the coalesced `RangeBounds` cannot be created with the
	/// [`TryFromBounds`] trait then a [`TryFromBoundsError`] will be
	/// returned.
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
	/// 		.insert_coalesce_touching_or_overlapping(-4..1, true),
	/// 	Ok(&(-4..4))
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	range_bounds_map
	/// 		.insert_coalesce_touching_or_overlapping(2..8, true),
	/// 	Ok(&(-4..8))
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	range_bounds_map
	/// 		.insert_coalesce_touching_or_overlapping(10..16, false),
	/// 	Ok(&(10..16))
	/// );
	///
	/// assert_eq!(
	/// 	range_bounds_map.iter().collect::<Vec<_>>(),
	/// 	[(&(-4..8), &true), (&(10..16), &false)]
	/// );
	/// ```
	#[tested]
	pub fn insert_coalesce_touching_or_overlapping(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<&K, TryFromBoundsError>
	where
		K: TryFromBounds<I>,
	{
		let overlapping_swell = self.overlapping_swell(&range_bounds);
		let start_bound = match self.touching_left(&range_bounds) {
			Some(touching_left) => {
				Bound::from(touching_left.start_bound().cloned())
			}
			None => overlapping_swell.0.cloned(),
		};
		let end_bound = match self.touching_right(&range_bounds) {
			Some(touching_right) => {
				Bound::from(touching_right.end_bound().cloned())
			}
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
	/// followed by [`RangeBoundsMap::insert_platonic()`]. Hence the
	/// same `V: Clone` trait bound applies.
	///
	/// If the remaining `RangeBounds` left after the cut are not able
	/// to be created with the [`TryFromBounds`] trait then a
	/// [`TryFromBoundsError`] will be returned.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsMap;
	///
	/// let mut range_bounds_map =
	/// 	RangeBoundsMap::try_from([(2..8, false)]).unwrap();
	///
	/// assert_eq!(range_bounds_map.overwrite(4..6, true), Ok(()));
	///
	/// assert_eq!(
	/// 	range_bounds_map.iter().collect::<Vec<_>>(),
	/// 	[(&(2..4), &false), (&(4..6), &true), (&(6..8), &false)]
	/// );
	/// ```
	//#[trivial]
	//pub fn overwrite(
	//&mut self,
	//range_bounds: K,
	//value: V,
	//) -> Result<(), TryFromBoundsError>
	//where
	//V: Clone,
	//K: TryFromBounds<I>,
	//{
	//self.cut(&range_bounds)?;
	//self.insert_platonic(range_bounds, value).unwrap();

	//return Ok(());
	//}

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
	pub fn last_entry(&self) -> Option<(&K, &V)> {
		self.iter().next_back()
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
			range_bounds_map.insert_platonic(range_bounds, value)?;
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
			range_bounds_map.insert_platonic(range_bounds, value)?;
		}

		return Ok(range_bounds_map);
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

#[derive(Debug, PartialEq)]
enum Config<I> {
	LeftFirstNonOverlapping((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
	LeftFirstPartialOverlap((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
	LeftContainsRight((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),

	RightFirstNonOverlapping((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
	RightFirstPartialOverlap((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
	RightContainsLeft((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
}

#[untested]
fn config<'a, I, A, B>(a: &'a A, b: &'a B) -> Config<&'a I>
where
	A: RangeBounds<I>,
	B: RangeBounds<I>,
	I: PartialOrd,
{
	let a_all @ (a_start, a_end) = (a.start_bound(), a.end_bound());
	let b_all @ (b_start, b_end) = (b.start_bound(), b.end_bound());

	match BoundOrd::start(a_start) < BoundOrd::start(b_start) {
		true => {
			match (
				contains_bound_ord(a, BoundOrd::start(b_start)),
				contains_bound_ord(a, BoundOrd::end(b_end)),
			) {
				(false, false) => Config::LeftFirstNonOverlapping(a_all, b_all),
				(true, false) => Config::LeftFirstPartialOverlap(a_all, b_all),
				(true, true) => Config::LeftContainsRight(a_all, b_all),
				(false, true) => unreachable!(),
			}
		}
		false => {
			match (
				contains_bound_ord(b, BoundOrd::start(a_start)),
				contains_bound_ord(b, BoundOrd::end(a_end)),
			) {
				(false, false) => {
					Config::RightFirstNonOverlapping(a_all, b_all)
				}
				(true, false) => Config::RightFirstPartialOverlap(a_all, b_all),
				(true, true) => Config::RightContainsLeft(a_all, b_all),
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
#[untested]
fn sorted_config<'a, I, A, B>(a: &'a A, b: &'a B) -> SortedConfig<&'a I>
where
	A: RangeBounds<I>,
	B: RangeBounds<I>,
	I: PartialOrd,
{
	match config(a, b) {
        Config::LeftFirstNonOverlapping(a, b) => SortedConfig::NonOverlapping(a, b),
		Config::LeftFirstPartialOverlap(a, b) => SortedConfig::Swallowed(a, b),
		Config::LeftContainsRight(a, b) => SortedConfig::Swallowed(a, b),

        Config::RightFirstNonOverlapping(a, b) => SortedConfig::NonOverlapping(b, a),
        Config::RightFirstPartialOverlap(a, b) => SortedConfig::PartialOverlap(b, a),
		Config::RightContainsLeft(a, b) => SortedConfig::Swallowed(b, a),
	}
}

#[untested]
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
enum CutResult<I> {
	Nothing((Bound<I>, Bound<I>)),
	Everything((Bound<I>, Bound<I>)),
	Single(SingleCutResult<I>),
	Double(DoubleCutResult<I>),
}

#[derive(Debug)]
struct SingleCutResult<I> {
	inside_cut: (Bound<I>, Bound<I>),
	outside_cut: (Bound<I>, Bound<I>),
}

#[derive(Debug)]
struct DoubleCutResult<I> {
	inside_cut: (Bound<I>, Bound<I>),
	before_cut: (Bound<I>, Bound<I>),
	after_cut: (Bound<I>, Bound<I>),
}

#[untested]
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

	match config(base_range_bounds, cut_range_bounds) {
		Config::LeftFirstNonOverlapping(_, _) => CutResult::Nothing(base_all),
		Config::LeftFirstPartialOverlap(_, _) => {
			CutResult::Single(SingleCutResult {
				inside_cut: (cut_start, base_end),
				outside_cut: (base_start, flip_bound(cut_start)),
			})
		}
		Config::LeftContainsRight(a, b) => CutResult::Double(DoubleCutResult {
			inside_cut: cut_all,
			before_cut: (base_start, flip_bound(cut_start)),
			after_cut: (flip_bound(cut_end), base_end),
		}),

		Config::RightFirstNonOverlapping(_, _) => CutResult::Nothing(base_all),
		Config::RightFirstPartialOverlap(_, _) => {
			CutResult::Single(SingleCutResult {
				inside_cut: (base_start, cut_end),
				outside_cut: (flip_bound(cut_end), base_end),
			})
		}
		Config::RightContainsLeft(_, _) => CutResult::Everything(base_all),
	}
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
	match sorted_config(a, b) {
		SortedConfig::NonOverlapping(_, _) => false,
		_ => true,
	}
}

#[rustfmt::skip]
#[tested]
fn touches<I, A, B>(a: &A, b: &B) -> bool
where
	A: RangeBounds<I>,
	B: RangeBounds<I>,
	I: PartialOrd,
{
	match sorted_config(a, b) {
		SortedConfig::NonOverlapping(a, b) => {
			match (a.1, b.0) {
				(Bound::Included(point1), Bound::Excluded(point2)) => point1 == point2,
				(Bound::Excluded(point1), Bound::Included(point2)) => point1 == point2,
                _ => false,
			}
		}
		_ => false,
	}
}

#[trivial]
fn flip_bound<I>(bound: Bound<&I>) -> Bound<&I> {
	match bound {
		Bound::Included(point) => Bound::Excluded(point),
		Bound::Excluded(point) => Bound::Included(point),
		Bound::Unbounded => Bound::Unbounded,
	}
}
