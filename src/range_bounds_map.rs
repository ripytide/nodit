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
/// map.insert(ExEx::new(0.0, 5.0), 8).unwrap();
/// map.insert(ExEx::new(5.0, 7.5), 32).unwrap();
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
/// 	map.get_range_bounds_value_at_point(
/// 		&NotNan::new(2.0).unwrap()
/// 	),
/// 	Some((&ExEx::new(0.0, 5.0), &8))
/// );
/// ```
///
/// [`RangeBounds`]: https://doc.rust-lang.org/std/ops/trait.RangeBounds.html
/// [`BTreeMap`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
#[derive(Debug, Default, Serialize, Deserialize, PartialEq, Eq, Clone)]
pub struct RangeBoundsMap<I, K, V>
where
	I: PartialOrd,
{
	starts: BTreeMap<StartBound<I>, (K, V)>,
}

/// An error type to represent the possible errors from the
/// [`RangeBoundsMap::insert()`] function.
#[derive(PartialEq, Debug)]
pub enum InsertError {
	/// A `RangeBounds` is invalid if both its `start_bound()`
	/// AND `end_bound()` are (`Bound::Included` OR `Bound::Exluded`)
	/// AND the `start` point is >= than the `end`
	/// point.
	///
	/// The one exception to this rule is if both `start_bound()` AND
	/// `end_bound()` are `Bound::Included` and the `start` point is
	/// == to the `end` point then it is considered valid despite
	/// failing the previous rule.
	InvalidRangeBounds,
	/// The error given if you try to insert a `RangeBounds` that
	/// overlaps one or more `RangeBounds` already in the map.
	OverlapsPreexisting,
}

/// An error type to represent the possible errors from the
/// [`RangeBoundsMap::cut()`] function.
#[derive(PartialEq, Debug)]
pub enum CutError {
	/// When cutting out a `RangeBounds` from another `RangeBounds`
	/// you may need to change the base `RangeBounds`' start and end
	/// `Bound`s, when these need to change values that the underlying
	/// `K`: `RangeBounds` type can't handle then this error is
	/// returned.
	NonConvertibleRangeBoundsProduced,
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
	/// range_bounds_map.insert(0..1, false).unwrap();
	/// assert_eq!(range_bounds_map.len(), 1);
	/// ```
	pub fn len(&self) -> usize {
		self.starts.len()
	}

	/// Adds a new (`RangeBounds` `Value`) pair to the map.
	///
	/// If the new `RangeBounds` overlaps one or more `RangeBounds`
	/// already in the map then [`InsertError::OverlapsPreexisting`]
	/// is returned and the map is not updated.
	///
	/// If the new `RangeBounds` is invalid then
	/// [`InsertError::InvalidRangeBounds`] is returned and the map is
	/// not updated.
	/// See the [`InsertError::InvalidRangeBounds`] type
	/// to see what constitutes as an "invalid" `RangeBounds`.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::{InsertError, RangeBoundsMap};
	///
	/// let mut range_bounds_map = RangeBoundsMap::new();
	///
	/// assert_eq!(range_bounds_map.insert(5..10, 9), Ok(()));
	/// assert_eq!(
	/// 	range_bounds_map.insert(5..10, 2),
	/// 	Err(InsertError::OverlapsPreexisting)
	/// );
	/// assert_eq!(
	/// 	range_bounds_map.insert(5..1, 8),
	/// 	Err(InsertError::InvalidRangeBounds)
	/// );
	/// assert_eq!(range_bounds_map.len(), 1);
	/// ```
	pub fn insert(
		&mut self,
		range_bounds: K,
		value: V,
	) -> Result<(), InsertError> {
		if !is_valid_range_bounds(&range_bounds) {
			return Err(InsertError::InvalidRangeBounds);
		}

		if self.overlaps(&range_bounds) {
			return Err(InsertError::OverlapsPreexisting);
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
	/// range_bounds_map.insert(5..10, false);
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
	/// assert_eq!(overlapping.next(), Some((&(1..4), &false)));
	/// assert_eq!(overlapping.next(), Some((&(4..8), &true)));
	/// assert_eq!(overlapping.next(), None);
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
		self.get_range_bounds_value_at_point(point)
			.map(|(_, value)| value)
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
			.get_range_bounds_value_at_point(point)
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
	/// 	range_bounds_map.get_range_bounds_value_at_point(&3),
	/// 	Some((&(1..4), &false))
	/// );
	/// assert_eq!(
	/// 	range_bounds_map.get_range_bounds_value_at_point(&4),
	/// 	Some((&(4..8), &true))
	/// );
	/// assert_eq!(
	/// 	range_bounds_map.get_range_bounds_value_at_point(&101),
	/// 	None
	/// );
	/// ```
	pub fn get_range_bounds_value_at_point(
		&self,
		point: &I,
	) -> Option<(&K, &V)> {
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
	/// assert_eq!(removed.next(), Some((1..4, false)));
	/// assert_eq!(removed.next(), Some((4..8, true)));
	/// assert_eq!(removed.next(), None);
	///
	/// let mut remaining = range_bounds_map.iter();
	/// assert_eq!(remaining.next(), Some((&(8..100), &false)));
	/// assert_eq!(remaining.next(), None);
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
	/// `V` must implement `Clone` as if you try to cut out the center
	/// of a `RangeBounds` in the map it will split into two different
	/// (`RangeBounds`, `Value`) pairs using `Clone`.
	///
	/// If the remaining `RangeBounds` left after the cut are not able
	/// to be converted into the `K` type with the [`TryFromBounds`]
	/// trait then a [`CutError`] will be returned.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::{CutError, RangeBoundsMap};
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
	/// assert_eq!(
	/// 	base.cut(&(60..=80)),
	/// 	Err(CutError::NonConvertibleRangeBoundsProduced)
	/// );
	/// ```
	pub fn cut<Q>(&mut self, range_bounds: &Q) -> Result<(), CutError>
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

		let mut attempt_insert =
			|(start_bound, end_bound), value| -> Result<(), CutError> {
				match K::try_from_bounds(start_bound, end_bound)
					.ok_or(CutError::NonConvertibleRangeBoundsProduced)
				{
					Ok(key) => {
						self.insert(key, value).unwrap();
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
						attempt_insert(left_section, first.1)?;
					}
					CutResult::Double(_, _) => unreachable!(),
				}
				match cut_range_bounds(&last.0, range_bounds) {
					CutResult::Nothing => {}
					CutResult::Single(right_section) => {
						attempt_insert(right_section, last.1)?;
					}
					CutResult::Double(_, _) => unreachable!(),
				}
			}
			(Some(first), None) => {
				match cut_range_bounds(&first.0, range_bounds) {
					CutResult::Nothing => {}
					CutResult::Single(section) => {
						attempt_insert(section, first.1)?;
					}
					CutResult::Double(left_section, right_section) => {
						attempt_insert(left_section, first.1.clone())?;
						attempt_insert(right_section, first.1)?;
					}
				}
			}
			(None, None) => {}
			(None, Some(_)) => unreachable!(),
		}

		return Ok(());
	}
}

impl<const N: usize, I, K, V> TryFrom<[(K, V); N]> for RangeBoundsMap<I, K, V>
where
	K: RangeBounds<I>,
	I: Ord + Clone,
{
	type Error = InsertError;
	fn try_from(pairs: [(K, V); N]) -> Result<Self, Self::Error> {
		let mut range_bounds_map = RangeBoundsMap::new();
		for (range_bounds, value) in pairs {
			range_bounds_map.insert(range_bounds, value)?;
		}

		return Ok(range_bounds_map);
	}
}

#[derive(Debug)]
enum CutResult<I> {
	Nothing,
	Single((Bound<I>, Bound<I>)),
	Double((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
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
			Bound::from(StartBound::from(cut_start_bound).into_opposite())
				.cloned(),
		)),
	};
	let right_section = match StartBound::from(cut_end_bound).into_end_bound()
		< StartBound::from(base_end_bound).into_end_bound()
	{
		false => None,
		true => Some((
			Bound::from(StartBound::from(cut_end_bound).into_opposite())
				.cloned(),
			base_end_bound.cloned(),
		)),
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

#[cfg(test)]
mod tests {
	use std::ops::{Bound, Range, RangeBounds};

	use super::*;
	use crate::bounds::StartBound;
	use crate::RangeBoundsSet;

	type TestBounds = (Bound<u8>, Bound<u8>);

	//only every other number to allow mathematical_overlapping_definition
	//to test between bounds in finite using smaller intervalled finite
	pub(crate) const NUMBERS: &'static [u8] = &[2, 4, 6, 8, 10];
	//go a bit around on either side to compensate for Unbounded
	pub(crate) const NUMBERS_DOMAIN: &'static [u8] =
		&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

	#[test]
	fn mass_overlaps_test() {
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
	fn mass_overlapping_test() {
		//case zero
		for overlap_range in all_valid_test_bounds() {
			//you can't overlap nothing
			assert!(
				RangeBoundsSet::<u8, Range<u8>>::new()
					.overlapping(&overlap_range)
					.next()
					.is_none()
			);
		}

		//case one
		for overlap_range in all_valid_test_bounds() {
			for inside_range in all_valid_test_bounds() {
				let mut range_bounds_set = RangeBoundsSet::new();
				range_bounds_set.insert(inside_range).unwrap();

				let mut expected_overlapping = Vec::new();
				if overlaps(&overlap_range, &inside_range) {
					expected_overlapping.push(inside_range);
				}

				let overlapping = range_bounds_set
					.overlapping(&overlap_range)
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
				let mut range_bounds_set = RangeBoundsSet::new();
				range_bounds_set.insert(inside_range1).unwrap();
				range_bounds_set.insert(inside_range2).unwrap();

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
	fn mass_cut_range_bounds_tests() {
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
			output.push((start_bound, Bound::Unbounded));
		}
		//unbounded-bounded
		for end_bound in all_finite_bounded() {
			output.push((Bound::Unbounded, end_bound));
		}
		//unbounded-unbounded
		output.push((Bound::Unbounded, Bound::Unbounded));

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
}
