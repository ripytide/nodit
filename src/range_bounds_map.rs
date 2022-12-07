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

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::iter::once;
use std::ops::{Bound, RangeBounds};

use either::Either;
use itertools::Itertools;
use labels::{tested, trivial, untested};
use serde::{Deserialize, Serialize};

use crate::bounds::StartBound;
use crate::TryFromBounds;

/// An ordered map of [`RangeBounds`] based on [`BTreeMap`]
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
/// // Get a value in the map
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
/// // An Exlusive-Exlusive range of [`f32`]s not provided by any
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
	starts: BTreeMap<StartBound<I>, (K, V)>,
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
/// Inclusive-Inclusive OR Exlusive-Exlusive. We then try to use
/// [`RangeBoundsMap::insert_coalesce_touching()`] to "coalesce" an
/// Inclusive-Inclusive and a Exlusive-Exlusive `MultiRange`. This
/// will however fail as the resulting "coalesced" `RangeBounds` would
/// have to be Inclusive-Exlusive which `MultiRange` does not support.
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
/// enum MultiRange {
/// 	Inclusive(u8, u8),
/// 	Exclusive(u8, u8),
/// }
///
/// impl RangeBounds<u8> for MultiRange {
/// 	fn start_bound(&self) -> Bound<&u8> {
/// 		match self {
/// 			MultiRange::Inclusive(start, _) => {
/// 				Bound::Included(start)
/// 			}
/// 			MultiRange::Exclusive(start, _) => {
/// 				Bound::Excluded(start)
/// 			}
/// 		}
/// 	}
/// 	fn end_bound(&self) -> Bound<&u8> {
/// 		match self {
/// 			MultiRange::Inclusive(_, end) => Bound::Included(end),
/// 			MultiRange::Exclusive(_, end) => Bound::Excluded(end),
/// 		}
/// 	}
/// }
///
/// impl TryFromBounds<u8> for MultiRange {
/// 	fn try_from_bounds(
/// 		start_bound: Bound<u8>,
/// 		end_bound: Bound<u8>,
/// 	) -> Option<Self> {
/// 		match (start_bound, end_bound) {
/// 			(Bound::Included(start), Bound::Included(end)) => {
/// 				Some(MultiRange::Inclusive(start, end))
/// 			}
/// 			(Bound::Excluded(start), Bound::Excluded(end)) => {
/// 				Some(MultiRange::Exclusive(start, end))
/// 			}
/// 			_ => None,
/// 		}
/// 	}
/// }
///
/// let mut range_bounds_map = RangeBoundsMap::try_from([(
/// 	MultiRange::Inclusive(2, 4),
/// 	true,
/// )])
/// .unwrap();
///
/// assert_eq!(
/// 	range_bounds_map.insert_coalesce_touching(
/// 		MultiRange::Exclusive(4, 6),
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
	/// already in the map rather than just touching then an
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

		let start = StartBound::from(range_bounds.start_bound().cloned());
		let end = StartBound::from(range_bounds.end_bound().cloned())
			.into_end_bound();

		if start > end {
			panic!("Invalid search range bounds!");
		}

		self.starts.insert(
			StartBound::from(range_bounds.start_bound().cloned()),
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
	pub fn overlaps<Q>(&self, search_range_bounds: &Q) -> bool
	where
		Q: RangeBounds<I>,
	{
		self.overlapping(search_range_bounds).next().is_some()
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

		let start = StartBound::from(range_bounds.start_bound().cloned());
		let end = StartBound::from(range_bounds.end_bound().cloned())
			.into_end_bound();

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
						Bound::Excluded(StartBound::from(
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
	/// overlaps a given point, and `false` if not.
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
				.get_mut(&StartBound::from(overlapping_start_bound.cloned()))
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

		let to_remove: Vec<StartBound<I>> = self
			.overlapping(range_bounds)
			.map(|(key, _)| (StartBound::from(key.start_bound().cloned())))
			.collect();

		let mut output = Vec::new();

		for start_bound in to_remove {
			output.push(self.starts.remove(&start_bound).unwrap());
		}

		return output.into_iter();
	}

	/// Cuts a given `RangeBounds` out of the map.
	///
	/// If the remaining `RangeBounds` left after the cut are not able
	/// to be created with the [`TryFromBounds`] trait then a
	/// [`TryFromBoundsError`] will be returned.
	///
	/// `V` must implement `Clone` as if you try to cut out the center
	/// of a `RangeBounds` in the map it will split into two different
	/// (`RangeBounds`, `Value`) pairs using `Clone`.
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
	#[tested]
	pub fn cut<Q>(&mut self, range_bounds: &Q) -> Result<(), TryFromBoundsError>
	where
		Q: RangeBounds<I>,
		K: TryFromBounds<I>,
		V: Clone,
	{
		// only the first and last range_bounds in overlapping stand a
		// change of remaining after the cut so we don't need to
		// collect the iterator and can just look at the first and
		// last elements since range is a double ended iterator ;p
		let mut overlapping = self.remove_overlapping(range_bounds);

		let first_last = (overlapping.next(), overlapping.next_back());

		// optimisation don't clone the value when only changing the
		// RangeBounds via CutResult::Single()
		let mut attempt_insert_platonic =
			|(start_bound, end_bound),
			 value|
			 -> Result<(), TryFromBoundsError> {
				match K::try_from_bounds(start_bound, end_bound)
					.ok_or(TryFromBoundsError)
				{
					Ok(key) => {
						self.insert_platonic(key, value).unwrap();
						return Ok(());
					}
					Err(cut_error) => return Err(cut_error),
				}
			};

		match first_last {
			(Some(first), Some(last)) => {
				match cut_range_bounds(&first.0, range_bounds) {
					CutResult::Nothing => {}
					CutResult::Single(left_section) => {
						attempt_insert_platonic(left_section, first.1)?;
					}
					CutResult::Double(_, _) => unreachable!(),
				}
				match cut_range_bounds(&last.0, range_bounds) {
					CutResult::Nothing => {}
					CutResult::Single(right_section) => {
						attempt_insert_platonic(right_section, last.1)?;
					}
					CutResult::Double(_, _) => unreachable!(),
				}
			}
			(Some(first), None) => {
				match cut_range_bounds(&first.0, range_bounds) {
					CutResult::Nothing => {}
					CutResult::Single(section) => {
						attempt_insert_platonic(section, first.1)?;
					}
					CutResult::Double(left_section, right_section) => {
						attempt_insert_platonic(left_section, first.1.clone())?;
						attempt_insert_platonic(right_section, first.1)?;
					}
				}
			}
			(None, None) => {}
			(None, Some(_)) => unreachable!(),
		}

		return Ok(());
	}

	/// Returns an iterator of `(Bound<&I>, Bound<&I>)` over all the
	/// maximally-sized gaps in the map that are also within the given
	/// `outer_range_bounds`.
	///
	/// To get all possible gaps just call `gaps()` with an unbounded
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
		// we actually want the search_range_bounds endpoints included
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
	/// already in the map rather than just touching then an
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
	/// 	[(&(1..6), &true), (&(10..16), &false),]
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

		let (left_touching, right_touching) = (
			self.starts
				.range((
					Bound::Unbounded,
					Bound::Excluded(StartBound::from(
						range_bounds.start_bound().cloned(),
					)),
				))
				.next_back()
				.filter(|x| touches(&range_bounds, &x.1.0))
				.map(|x| x.0.clone()),
			self.starts
				.range((
					Bound::Excluded(StartBound::from(
						range_bounds.start_bound().cloned(),
					)),
					Bound::Unbounded,
				))
				.next()
				.filter(|x| touches(&range_bounds, &x.1.0))
				.map(|x| x.0.clone()),
		);

		let start_bound = match left_touching {
			Some(left) => {
				self.starts.remove(&left).unwrap().0.start_bound().cloned()
			}
			None => range_bounds.start_bound().cloned(),
		};
		let end_bound = match right_touching {
			Some(right) => {
				self.starts.remove(&right).unwrap().0.end_bound().cloned()
			}
			None => range_bounds.end_bound().cloned(),
		};

		let new_range_bounds =
			K::try_from_bounds(start_bound.clone(), end_bound).ok_or(
				OverlapOrTryFromBoundsError::TryFromBounds(TryFromBoundsError),
			)?;

		self.starts.insert(
			StartBound::from(new_range_bounds.start_bound().cloned()),
			(new_range_bounds, value),
		);

		return Ok(&self.starts.get(&StartBound::from(start_bound)).unwrap().0);
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
		let mut overlapping = self.remove_overlapping(&range_bounds).peekable();

		let start_bound = match overlapping.peek() {
			Some((first, _)) => std::cmp::min(
				StartBound::from(first.start_bound().cloned()),
				StartBound::from(range_bounds.start_bound().cloned()),
			),
			None => StartBound::from(range_bounds.start_bound().cloned()),
		};
		let end_bound = match overlapping.next_back() {
			Some((last, _)) => std::cmp::max(
				StartBound::from(last.end_bound().cloned()).into_end_bound(),
				StartBound::from(range_bounds.end_bound().cloned())
					.into_end_bound(),
			)
			.into_start_bound(),
			None => StartBound::from(range_bounds.end_bound().cloned()),
		};

		let new_range_bounds = K::try_from_bounds(
			Bound::from(start_bound.clone()),
			Bound::from(end_bound),
		)
		.ok_or(TryFromBoundsError)?;

		self.starts.insert(
			StartBound::from(new_range_bounds.start_bound().cloned()),
			(new_range_bounds, value),
		);

		return Ok(&self.starts.get(&start_bound).unwrap().0);
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
		//optimisation do this from first principles rather than cheating
		let new_start_bound = self
			.insert_coalesce_overlapping(range_bounds, value)?
			.start_bound()
			.cloned();

		let (new_start_bounds, value) = self
			.starts
			.remove(&StartBound::from(new_start_bound))
			.unwrap();

		let new_start_bound = self
			.insert_coalesce_touching(new_start_bounds, value)
			.map_err(|_| TryFromBoundsError)?
			.start_bound()
			.cloned();

		return Ok(&self
			.starts
			.get(&StartBound::from(new_start_bound))
			.unwrap()
			.0);
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
	#[trivial]
	pub fn overwrite(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<(), TryFromBoundsError>
	where
		V: Clone,
		K: TryFromBounds<I>,
	{
		self.cut(&range_bounds)?;
		self.insert_platonic(range_bounds, value).unwrap();

		return Ok(());
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

#[derive(Debug)]
enum CutResult<I> {
	Nothing,
	Single((Bound<I>, Bound<I>)),
	Double((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
}

#[tested]
fn cut_range_bounds<I, B, C>(
	base_range_bounds: &B,
	cut_range_bounds: &C,
) -> CutResult<I>
where
	B: RangeBounds<I>,
	C: RangeBounds<I>,
	I: PartialOrd + Clone,
{
	if !overlaps(base_range_bounds, cut_range_bounds) {
		// if they don't overlap just return the original
		// base_range_bounds
		return CutResult::Single((
			base_range_bounds.start_bound().cloned(),
			base_range_bounds.end_bound().cloned(),
		));
	}

	let (base_start_bound, base_end_bound) = (
		base_range_bounds.start_bound(),
		base_range_bounds.end_bound(),
	);
	let (cut_start_bound, cut_end_bound) =
		(cut_range_bounds.start_bound(), cut_range_bounds.end_bound());

	let left_section = match StartBound::from(cut_start_bound)
		> StartBound::from(base_start_bound)
	{
		false => None,
		true => Some((
			base_start_bound.cloned(),
			flip_bound(cut_start_bound).cloned(),
		)),
	};
	let right_section = match StartBound::from(cut_end_bound).into_end_bound()
		< StartBound::from(base_end_bound).into_end_bound()
	{
		false => None,
		true => {
			Some((flip_bound(cut_end_bound).cloned(), base_end_bound.cloned()))
		}
	};

	match (left_section, right_section) {
		(Some(left), Some(right)) => CutResult::Double(left, right),
		(Some(left), None) => CutResult::Single(left),
		(None, Some(right)) => CutResult::Single(right),
		(None, None) => CutResult::Nothing,
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
	// optimisation, do this with much less operations
	let a_start = a.start_bound();
	let a_end = a.end_bound();

	let b_start = b.start_bound();
	let b_end = b.end_bound();

	let (left_end, right_start) =
		match StartBound::from(a_start).cmp(&StartBound::from(b_start)) {
			Ordering::Less => (a_end, b_start),
			Ordering::Greater => (b_end, a_start),
			Ordering::Equal => return true,
		};

	match (left_end, right_start) {
		(Bound::Included(end), Bound::Included(start)) => end >= start,

		(Bound::Excluded(end), Bound::Excluded(start)) => end > start,
		(Bound::Included(end), Bound::Excluded(start)) => end > start,
		(Bound::Excluded(end), Bound::Included(start)) => end > start,

		(Bound::Unbounded, _) => true,

		(_, Bound::Unbounded) => unreachable!(),
	}
}

#[untested]
fn touches<I, A, B>(a: &A, b: &B) -> bool
where
	A: RangeBounds<I>,
	B: RangeBounds<I>,
	I: PartialOrd,
{
	// optimisation, do this with much less operations
	let a_start = a.start_bound();
	let a_end = a.end_bound();

	let b_start = b.start_bound();
	let b_end = b.end_bound();

	let (left_end, right_start) =
		match StartBound::from(a_start).cmp(&StartBound::from(b_start)) {
			Ordering::Less => (a_end, b_start),
			Ordering::Greater => (b_end, a_start),
			Ordering::Equal => return false,
		};

	match (left_end, right_start) {
		(Bound::Included(end), Bound::Excluded(start)) => end == start,
		(Bound::Excluded(end), Bound::Included(start)) => end == start,
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

#[cfg(test)]
mod tests {
	use std::ops::{Bound, Range, RangeBounds};

	use pretty_assertions::assert_eq;

	use super::*;
	use crate::bounds::StartBound;

	type TestBounds = (Bound<u8>, Bound<u8>);

	//only every other number to allow mathematical_overlapping_definition
	//to test between bounds in finite using smaller intervalled finite
	pub(crate) const NUMBERS: &'static [u8] = &[2, 4, 6, 8, 10];
	//go a bit around on either side to compensate for Unbounded
	pub(crate) const NUMBERS_DOMAIN: &'static [u8] =
		&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

	#[rustfmt::skip]
	#[test]
	fn insert_platonic_tests() {
		assert_insert_platonic::<0>(basic(), (ii(0, 4), false), Err(OverlapError), None);
		assert_insert_platonic::<0>(basic(), (ii(5, 6), false), Err(OverlapError), None);
        assert_insert_platonic(basic(), (ee(7, 8), false), Ok(()), Some([
			(ui(4), false),
			(ee(5, 7), true),
			(ii(7, 7), false),
            (ee(7, 8), false),
			(ie(14, 16), true),
        ]));
        assert_insert_platonic::<0>(basic(), (ii(4, 5), true), Err(OverlapError), None);
        assert_insert_platonic(basic(), (ei(4, 5), true), Ok(()), Some([
			(ui(4), false),
			(ei(4, 5), true),
			(ee(5, 7), true),
			(ii(7, 7), false),
			(ie(14, 16), true),
        ]));
	}
	fn assert_insert_platonic<const N: usize>(
		mut before: RangeBoundsMap<u8, TestBounds, bool>,
		to_insert: (TestBounds, bool),
		result: Result<(), OverlapError>,
		after: Option<[(TestBounds, bool); N]>,
	) {
		let clone = before.clone();
		assert_eq!(before.insert_platonic(to_insert.0, to_insert.1), result);
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
				let mut range_bounds_set = RangeBoundsMap::new();
				range_bounds_set.insert_platonic(inside_range, ()).unwrap();

				let mut expected_overlapping = Vec::new();
				if overlaps(&overlap_range, &inside_range) {
					expected_overlapping.push(inside_range);
				}

				let overlapping = range_bounds_set
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
				let mut range_bounds_set = RangeBoundsMap::new();
				range_bounds_set.insert_platonic(inside_range1, ()).unwrap();
				range_bounds_set.insert_platonic(inside_range2, ()).unwrap();

				let mut expected_overlapping = Vec::new();
				if overlaps(&overlap_range, &inside_range1) {
					expected_overlapping.push(inside_range1);
				}
				if overlaps(&overlap_range, &inside_range2) {
					expected_overlapping.push(inside_range2);
				}
				//make our expected_overlapping the correct order
				if expected_overlapping.len() > 1 {
					if StartBound::from(expected_overlapping[0].start_bound())
						> StartBound::from(
							expected_overlapping[1].start_bound(),
						) {
						expected_overlapping.swap(0, 1);
					}
				}

				let overlapping = range_bounds_set
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

	#[rustfmt::skip]
	#[test]
	fn remove_overlapping_tests() {
		assert_remove_overlapping::<0, 0>(basic(), ii(5, 5), [], None);
		assert_remove_overlapping(basic(), uu(), [
            (ui(4), false),
			(ee(5, 7), true),
            (ii(7, 7), false),
			(ie(14, 16), true),
        ], Some([]));
		assert_remove_overlapping(basic(), ii(6, 7), [
			(ee(5, 7), true),
			(ii(7, 7), false),
        ], Some([
            (ui(4), false), (ie(14, 16), true)
        ]));
		assert_remove_overlapping(basic(), iu(6), [
			(ee(5, 7), true),
			(ii(7, 7), false),
			(ie(14, 16), true),
        ], Some([
			(ui(4), false),
        ]));
	}
	fn assert_remove_overlapping<const N: usize, const Y: usize>(
		mut before: RangeBoundsMap<u8, TestBounds, bool>,
		to_remove: TestBounds,
		result: [(TestBounds, bool); N],
		after: Option<[(TestBounds, bool); Y]>,
	) {
		let clone = before.clone();
		assert_eq!(before.remove_overlapping(&to_remove).collect_vec(), result);
		match after {
			Some(after) => {
				assert_eq!(before, RangeBoundsMap::try_from(after).unwrap())
			}
			None => assert_eq!(before, clone),
		}
	}

	#[rustfmt::skip]
	#[test]
	fn cut_tests() {
		assert_cut::<0>(basic(), ii(50, 60), Ok(()), None);
		assert_cut(basic(), uu(), Ok(()), Some([]));
		assert_cut(basic(), ui(6), Ok(()), Some([
			(ee(6, 7), true),
            (ii(7, 7), false),
			(ie(14, 16), true),
        ]));
		assert_cut(basic(), iu(6), Ok(()), Some([
            (ui(4), false),
			(ee(5, 6), true),
        ]));
	}
	fn assert_cut<const N: usize>(
		mut before: RangeBoundsMap<u8, TestBounds, bool>,
		to_cut: TestBounds,
		result: Result<(), TryFromBoundsError>,
		after: Option<[(TestBounds, bool); N]>,
	) {
		let clone = before.clone();
		assert_eq!(before.cut(&to_cut), result);
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
				.collect_vec(),
			result
		);
	}

	fn basic() -> RangeBoundsMap<u8, TestBounds, bool> {
		RangeBoundsMap::try_from([
			(ui(4), false),
			(ee(5, 7), true),
			(ii(7, 7), false),
			(ie(14, 16), true),
		])
		.unwrap()
	}

	#[rustfmt::skip]
	#[test]
	fn insert_coalesce_touching_tests() {
		assert_insert_coalesce_touching::<0>(basic(), (ii(0, 4), false), Err(OverlapOrTryFromBoundsError::Overlap(OverlapError)), None);
        assert_insert_coalesce_touching::<4>(basic(), (ee(7, 10), false), Ok(&ie(7, 10)), Some([
			(ui(4), false),
			(ee(5, 7), true),
			(ie(7, 10), false),
            (ie(14, 16), true),
        ]));
        assert_insert_coalesce_touching::<4>(basic(), (ee(7, 11), true), Ok(&ie(7, 11)), Some([
			(ui(4), false),
			(ee(5, 7), true),
			(ie(7, 11), true),
            (ie(14, 16), true),
        ]));
        assert_insert_coalesce_touching::<5>(basic(), (ee(12, 13), true), Ok(&ee(12, 13)), Some([
			(ui(4), false),
			(ee(5, 7), true),
			(ii(7, 7), false),
            (ee(12, 13), true),
            (ie(14, 16), true),
        ]));
        assert_insert_coalesce_touching::<4>(basic(), (ee(13, 14), false), Ok(&ee(13, 16)), Some([
			(ui(4), false),
			(ee(5, 7), true),
			(ii(7, 7), false),
            (ee(13, 16), false),
        ]));
        assert_insert_coalesce_touching::<3>(basic(), (ee(7, 14), false), Ok(&ie(7, 16)), Some([
			(ui(4), false),
			(ee(5, 7), true),
            (ie(7, 16), false),
        ]));
	}
	fn assert_insert_coalesce_touching<const N: usize>(
		mut before: RangeBoundsMap<u8, TestBounds, bool>,
		to_insert: (TestBounds, bool),
		result: Result<&TestBounds, OverlapOrTryFromBoundsError>,
		after: Option<[(TestBounds, bool); N]>,
	) {
		let clone = before.clone();
		assert_eq!(
			before.insert_coalesce_touching(to_insert.0, to_insert.1),
			result
		);
		match after {
			Some(after) => {
				assert_eq!(before, RangeBoundsMap::try_from(after).unwrap())
			}
			None => assert_eq!(before, clone),
		}
	}

	#[rustfmt::skip]
	#[test]
	fn insert_coalesce_overlapping_tests() {
        assert_insert_coalesce_overlapping::<4>(basic(), (ii(0, 2), true), Ok(&(ui(4))), Some([
			(ui(4), true),
			(ee(5, 7), true),
			(ii(7, 7), false),
			(ie(14, 16), true),
        ]));
        assert_insert_coalesce_overlapping::<4>(basic(), (ie(14, 16), false), Ok(&ie(14, 16)), Some([
			(ui(4), false),
			(ee(5, 7), true),
			(ii(7, 7), false),
            (ie(14, 16), false),
        ]));
        assert_insert_coalesce_overlapping::<3>(basic(), (ii(6, 11), false), Ok(&ei(5, 11)), Some([
			(ui(4), false),
			(ei(5, 11), false),
            (ie(14, 16), true),
        ]));
        assert_insert_coalesce_overlapping::<4>(basic(), (ii(15, 18), true), Ok(&ii(14, 18)), Some([
			(ui(4), false),
			(ee(5, 7), true),
			(ii(7, 7), false),
			(ii(14, 18), true),
        ]));
        assert_insert_coalesce_overlapping::<1>(basic(), (uu(), false), Ok(&uu()), Some([
            (uu(), false),
        ]));
	}
	fn assert_insert_coalesce_overlapping<const N: usize>(
		mut before: RangeBoundsMap<u8, TestBounds, bool>,
		to_insert: (TestBounds, bool),
		result: Result<&TestBounds, TryFromBoundsError>,
		after: Option<[(TestBounds, bool); N]>,
	) {
		let clone = before.clone();
		assert_eq!(
			before.insert_coalesce_overlapping(to_insert.0, to_insert.1),
			result
		);
		match after {
			Some(after) => {
				assert_eq!(before, RangeBoundsMap::try_from(after).unwrap())
			}
			None => assert_eq!(before, clone),
		}
	}

	#[rustfmt::skip]
	#[test]
	fn insert_coalesce_touching_or_overlapping_tests() {
        assert_insert_coalesce_touching_or_overlapping::<4>(basic(), (ii(0, 2), true), Ok(&(ui(4))), Some([
			(ui(4), true),
			(ee(5, 7), true),
			(ii(7, 7), false),
			(ie(14, 16), true),
        ]));
        assert_insert_coalesce_touching_or_overlapping::<4>(basic(), (ie(14, 16), false), Ok(&ie(14, 16)), Some([
			(ui(4), false),
			(ee(5, 7), true),
			(ii(7, 7), false),
            (ie(14, 16), false),
        ]));
        assert_insert_coalesce_touching_or_overlapping::<3>(basic(), (ii(6, 11), false), Ok(&ei(5, 11)), Some([
			(ui(4), false),
			(ei(5, 11), false),
            (ie(14, 16), true),
        ]));
        assert_insert_coalesce_touching_or_overlapping::<4>(basic(), (ii(15, 18), true), Ok(&ii(14, 18)), Some([
			(ui(4), false),
			(ee(5, 7), true),
			(ii(7, 7), false),
			(ii(14, 18), true),
        ]));
        assert_insert_coalesce_touching_or_overlapping::<1>(basic(), (uu(), false), Ok(&uu()), Some([
            (uu(), false),
        ]));
        //the only difference from the insert_coalesce_overlapping
        assert_insert_coalesce_touching_or_overlapping::<2>(basic(), (ii(7, 14), false), Ok(&ee(5, 16)), Some([
			(ui(4), false),
            (ee(5, 16), false),
        ]));
	}
	fn assert_insert_coalesce_touching_or_overlapping<const N: usize>(
		mut before: RangeBoundsMap<u8, TestBounds, bool>,
		to_insert: (TestBounds, bool),
		result: Result<&TestBounds, TryFromBoundsError>,
		after: Option<[(TestBounds, bool); N]>,
	) {
		let clone = before.clone();
		assert_eq!(
			before.insert_coalesce_touching_or_overlapping(
				to_insert.0,
				to_insert.1
			),
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
					panic!("Discrepency in .overlaps() detected!");
				}
			}
		}
	}

	#[test]
	fn cut_range_bounds_tests() {
		for base in all_valid_test_bounds() {
			for cut in all_valid_test_bounds() {
				let cut_result = cut_range_bounds(&base, &cut);

				// The definition of a cut is: A && NOT B
				for x in NUMBERS_DOMAIN {
					let result_contains = cut_result.contains(x);
					let base_contains = base.contains(x);
					let cut_contains = cut.contains(x);

					let invariant =
						result_contains == (base_contains && !cut_contains);

					if !invariant {
						dbg!(result_contains);
						dbg!(base_contains);
						dbg!(cut_contains);

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
	impl<I> CutResult<I> {
		fn contains(&self, point: &I) -> bool
		where
			I: PartialOrd,
		{
			match self {
				CutResult::Nothing => false,
				CutResult::Single(range_bounds) => range_bounds.contains(point),
				CutResult::Double(first_range_bounds, second_range_bounds) => {
					first_range_bounds.contains(point)
						|| second_range_bounds.contains(point)
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
