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
use std::iter::once;
use std::ops::{Bound, RangeBounds};

use either::Either;
use itertools::Itertools;
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
/// let range_bounds_map =
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
	pub fn insert_platonic(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<(), OverlapError> {
		if self.overlaps(&range_bounds) {
			return Err(OverlapError);
		}

		//optimisation fix this without cloning
		let start = StartBound::from(range_bounds.start_bound().cloned());
		//optimisation fix this without cloning
		let end = StartBound::from(range_bounds.end_bound().cloned())
			.into_end_bound();

		if start > end {
			panic!("Invalid search range bounds!");
		}

		self.starts.insert(
			//optimisation fix this without cloning
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
	/// 	[(&(1..4), &false), (&(4..8), &true), (&(8..100), &false)]
	/// );
	/// ```
	pub fn overlapping<Q>(
		&self,
		range_bounds: &Q,
	) -> impl DoubleEndedIterator<Item = (&K, &V)>
	where
		Q: RangeBounds<I>,
	{
		if !is_valid_range_bounds(range_bounds) {
			panic!("Invalid search range bounds!");
		}

		//optimisation fix this without cloning
		let start = StartBound::from(range_bounds.start_bound().cloned());
		//optimisation fix this without cloning
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
			//Excluded is lossless regarding meta-bounds searches
			//because we don't want equal bounds as they would have be
			//covered in the previous step and we don't want duplicates
			self.starts
					.range((
						Bound::Unbounded,
						Bound::Excluded(StartBound::from(
							//optimisation fix this without cloning
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
	pub fn get_at_point_mut(&mut self, point: &I) -> Option<&mut V> {
		if let Some(overlapping_start_bound) = self
			.get_entry_at_point(point)
			.map(|(key, _)| key.start_bound())
		{
			return self
				.starts
				//optimisation fix this without cloning
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
	/// 	[(&(1..4), false), (&(4..8), true)]
	/// );
	/// ```
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
	pub fn gaps<'a, Q>(
		&'a self,
		outer_range_bounds: &'a Q,
	) -> impl Iterator<Item = (Bound<&I>, Bound<&I>)>
	where
		Q: RangeBounds<I>,
	{
		// I'm in love with how clean/mindblowing this entire function is
		let inners = self
			.overlapping(outer_range_bounds)
			.map(|(key, _)| (key.start_bound(), key.end_bound()));

		// We have to opposite these ahead of time as we actually want
		// the bounds included not excluded like with other bounds in
		// artificials
		let artificial_start = (
			flip_bound(outer_range_bounds.start_bound()),
			flip_bound(outer_range_bounds.start_bound()),
		);
		let artificial_end = (
			flip_bound(outer_range_bounds.end_bound()),
			flip_bound(outer_range_bounds.end_bound()),
		);
		let artificials = once(artificial_start)
			.chain(inners)
			.chain(once(artificial_end));

		eprintln!("\nnew:");

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
	/// If the new `RangeBounds` overlaps one or more `RangeBounds`
	/// already in the map rather than just touching then an
	/// [`OverlapError`] is returned and the map is not updated.
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
	/// 	Ok(())
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
	/// 	Ok(())
	/// );
	///
	/// assert_eq!(
	/// 	range_bounds_map.iter().collect::<Vec<_>>(),
	/// 	[(&(1..6), &true), (&(10..16), &false),]
	/// );
	/// ```
	pub fn insert_coalesce_touching(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<(), OverlapOrTryFromBoundsError> {
		todo!()
	}

	/// Adds a new (`RangeBounds`, `Value`) pair to the map and
	/// coalesces into other `RangeBounds` in the map which overlap
	/// it.
	///
	/// The `Value` of the coalesced `RangeBounds` is set to the given
	/// `Value`.
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
	/// 	range_bounds_map.insert_coalesce_touching(-4..1, true),
	/// 	Ok(())
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	range_bounds_map.insert_coalesce_touching(2..8, true),
	/// 	Ok(())
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	range_bounds_map.insert_coalesce_touching(10..16, false),
	/// 	Ok(())
	/// );
	///
	/// assert_eq!(
	/// 	range_bounds_map.iter().collect::<Vec<_>>(),
	/// 	[(&(-4..1), &true), (&(1..8), &true), (&(10..16), &false)]
	/// );
	/// ```
	pub fn insert_coalesce_overlapping(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<(), TryFromBoundsError> {
		todo!()
	}

	/// Adds a new (`RangeBounds`, `Value`) pair to the map and
	/// coalesces into other `RangeBounds` in the map which touch or
	/// overlap it.
	///
	/// The `Value` of the coalesced `RangeBounds` is set to the given
	/// `Value`.
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
	/// 	range_bounds_map.insert_coalesce_touching(-4..1, true),
	/// 	Ok(())
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	range_bounds_map.insert_coalesce_touching(2..8, true),
	/// 	Ok(())
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	range_bounds_map.insert_coalesce_touching(10..16, false),
	/// 	Ok(())
	/// );
	///
	/// assert_eq!(
	/// 	range_bounds_map.iter().collect::<Vec<_>>(),
	/// 	[(&(-4..8), &true), (&(10..16), &false)]
	/// );
	/// ```
	pub fn insert_coalesce_touching_or_overlapping(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<(), TryFromBoundsError> {
		todo!()
	}

	/// Adds a new (`RangeBounds`, `Value`) pair to the map and
	/// overwrites any other `RangeBounds` that overlap the new
	/// `RangeBounds`.
	///
	/// This is equivalent to using [`RangeBoundsMap::cut()`]
	/// followed by [`RangeBoundsMap::insert_platonic()`].
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
	pub fn overwrite(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<(), TryFromBoundsError> {
		todo!()
	}
}

impl<const N: usize, I, K, V> TryFrom<[(K, V); N]> for RangeBoundsMap<I, K, V>
where
	K: RangeBounds<I>,
	I: Ord + Clone,
{
	type Error = OverlapError;
	fn try_from(pairs: [(K, V); N]) -> Result<Self, Self::Error> {
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

fn flip_bound<I>(bound: Bound<&I>) -> Bound<&I> {
	match bound {
		Bound::Included(point) => Bound::Excluded(point),
		Bound::Excluded(point) => Bound::Included(point),
		Bound::Unbounded => Bound::Unbounded,
	}
}

//#[cfg(test)]
//mod tests {
//use std::ops::{Bound, Range, RangeBounds};

//use super::*;
//use crate::bounds::StartBound;
//use crate::RangeBoundsSet;

//type TestBounds = (Bound<u8>, Bound<u8>);

////only every other number to allow mathematical_overlapping_definition
////to test between bounds in finite using smaller intervalled finite
//pub(crate) const NUMBERS: &'static [u8] = &[2, 4, 6, 8, 10];
////go a bit around on either side to compensate for Unbounded
//pub(crate) const NUMBERS_DOMAIN: &'static [u8] =
//&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

//#[test]
//fn mass_overlaps_test() {
//for range_bounds1 in all_valid_test_bounds() {
//for range_bounds2 in all_valid_test_bounds() {
//let our_answer = overlaps(&range_bounds1, &range_bounds2);

//let mathematical_definition_of_overlap =
//NUMBERS_DOMAIN.iter().any(|x| {
//range_bounds1.contains(x) && range_bounds2.contains(x)
//});

//if our_answer != mathematical_definition_of_overlap {
//dbg!(range_bounds1, range_bounds2);
//dbg!(mathematical_definition_of_overlap, our_answer);
//panic!("Discrepency in .overlaps() detected!");
//}

//#[test]
//fn mass_overlapping_test() {
////case zero
//for overlap_range in all_valid_test_bounds() {
////you can't overlap nothing
//assert!(
//RangeBoundsSet::<u8, Range<u8>>::new()
//.overlapping(&overlap_range)
//.next()
//.is_none()
//);
//}

////case one
//for overlap_range in all_valid_test_bounds() {
//for inside_range in all_valid_test_bounds() {
//let mut range_bounds_set = RangeBoundsSet::new();
//range_bounds_set.insert_platonic(inside_range).unwrap();

//let mut expected_overlapping = Vec::new();
//if overlaps(&overlap_range, &inside_range) {
//expected_overlapping.push(inside_range);
//}

//let overlapping = range_bounds_set
//.overlapping(&overlap_range)
//.copied()
//.collect::<Vec<_>>();

//if overlapping != expected_overlapping {
//dbg!(overlap_range, inside_range);
//dbg!(overlapping, expected_overlapping);
//panic!(
//"Discrepency in .overlapping() with single inside range detected!"
//);
//}

////case two
//for overlap_range in all_valid_test_bounds() {
//for (inside_range1, inside_range2) in
//all_non_overlapping_test_bound_pairs()
//{
//let mut range_bounds_set = RangeBoundsSet::new();
//range_bounds_set.insert_platonic(inside_range1).unwrap();
//range_bounds_set.insert_platonic(inside_range2).unwrap();

//let mut expected_overlapping = Vec::new();
//if overlaps(&overlap_range, &inside_range1) {
//expected_overlapping.push(inside_range1);
//}
//if overlaps(&overlap_range, &inside_range2) {
//expected_overlapping.push(inside_range2);
//}
////make our expected_overlapping the correct order
//if expected_overlapping.len() > 1 {
//if StartBound::from(expected_overlapping[0].start_bound())
//> StartBound::from(
//expected_overlapping[1].start_bound(),
//) {
//expected_overlapping.swap(0, 1);
//}

//let overlapping = range_bounds_set
//.overlapping(&overlap_range)
//.copied()
//.collect::<Vec<_>>();

//if overlapping != expected_overlapping {
//dbg!(overlap_range, inside_range1, inside_range2);
//dbg!(overlapping, expected_overlapping);
//panic!(
//"Discrepency in .overlapping() with two inside ranges detected!"
//);
//}

//impl<I> CutResult<I> {
//fn contains(&self, point: &I) -> bool
//where
//I: PartialOrd,
//{
//match self {
//CutResult::Nothing => false,
//CutResult::Single(range_bounds) => range_bounds.contains(point),
//CutResult::Double(first_range_bounds, second_range_bounds) => {
//first_range_bounds.contains(point)
//|| second_range_bounds.contains(point)
//}
//#[test]
//fn mass_cut_range_bounds_tests() {
//for base in all_valid_test_bounds() {
//for cut in all_valid_test_bounds() {
//let cut_result = cut_range_bounds(&base, &cut);

//// The definition of a cut is: A && NOT B
//for x in NUMBERS_DOMAIN {
//let result_contains = cut_result.contains(x);
//let base_contains = base.contains(x);
//let cut_contains = cut.contains(x);

//let invariant =
//result_contains == (base_contains && !cut_contains);

//if !invariant {
//dbg!(result_contains);
//dbg!(base_contains);
//dbg!(cut_contains);

//dbg!(base);
//dbg!(cut);
//dbg!(cut_result);

//dbg!(x);

//panic!("Invariant Broken!");
//}

//fn all_non_overlapping_test_bound_pairs() -> Vec<(TestBounds, TestBounds)> {
//let mut output = Vec::new();
//for test_bounds1 in all_valid_test_bounds() {
//for test_bounds2 in all_valid_test_bounds() {
//if !overlaps(&test_bounds1, &test_bounds2) {
//output.push((test_bounds1, test_bounds2));
//}

//return output;
//}

//fn all_valid_test_bounds() -> Vec<TestBounds> {
//let mut output = Vec::new();

////bounded-bounded
//output.append(&mut all_finite_bounded_pairs());
////bounded-unbounded
//for start_bound in all_finite_bounded() {
//output.push((start_bound, Bound::Unbounded));
//}
////unbounded-bounded
//for end_bound in all_finite_bounded() {
//output.push((Bound::Unbounded, end_bound));
//}
////unbounded-unbounded
//output.push((Bound::Unbounded, Bound::Unbounded));

//return output;
//}

//fn all_finite_bounded_pairs() -> Vec<(Bound<u8>, Bound<u8>)> {
//let mut output = Vec::new();
//for i in NUMBERS {
//for j in NUMBERS {
//for i_ex in [false, true] {
//for j_ex in [false, true] {
//if j > i || (j == i && !i_ex && !j_ex) {
//output.push((
//finite_bound(*i, i_ex),
//finite_bound(*j, j_ex),
//));
//}
//return output;
//}

//fn all_finite_bounded() -> Vec<Bound<u8>> {
//let mut output = Vec::new();
//for i in NUMBERS {
//for j in 0..=1 {
//output.push(finite_bound(*i, j == 1));
//}
//return output;
//}

//fn finite_bound(x: u8, included: bool) -> Bound<u8> {
//match included {
//false => Bound::Included(x),
//true => Bound::Excluded(x),
//}
