/*
Copyright 2022,2023 James Forster

This file is part of discrete_range_map.

discrete_range_map is free software: you can redistribute it and/or
modify it under the terms of the GNU Affero General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

discrete_range_map is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with discrete_range_map. If not, see <https://www.gnu.org/licenses/>.
*/

//! The module containing [`DiscreteRangeMap`] and related types.

use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt::{self, Debug};
use core::iter::once;
use core::marker::PhantomData;
use core::ops::{Bound, RangeBounds};

use btree_monstrousity::btree_map::{
	IntoIter as BTreeMapIntoIter, SearchBoundCustom,
};
use btree_monstrousity::BTreeMap;
use either::Either;
use itertools::Itertools;
use serde::de::{SeqAccess, Visitor};
use serde::ser::SerializeSeq;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::utils::{cmp_point_with_range, cut_range, is_valid_range, overlaps};
use crate::DiscreteFinite;

/// An ordered map of non-overlapping ranges based on [`BTreeMap`].
///
/// `I` is the generic type parameter for the [`Ord`] type the `K`
/// type is a range over.
///
/// `K` is the generic type parameter for the range type stored as the
/// keys in the map.
///
/// `V` is the generic type parameter for the values associated with the
/// keys in the map.
///
/// Phrasing it another way: `I` is the point type, `K` is the range type, and `V` is the value type.
///
/// # Examples
/// ```
/// use discrete_range_map::test_ranges::ie;
/// use discrete_range_map::DiscreteRangeMap;
///
/// // Make a map of ranges to booleans
/// let mut map = DiscreteRangeMap::from_slice_strict([
/// 	(ie(4, 8), false),
/// 	(ie(8, 18), true),
/// 	(ie(20, 100), false),
/// ])
/// .unwrap();
///
/// // Change a value in the map
/// *map.get_at_point_mut(7).unwrap() = true;
///
/// if map.contains_point(99) {
/// 	println!("Map contains value at 99 :)");
/// }
///
/// // Iterate over the entries in the map
/// for (range, value) in map.iter() {
/// 	println!("{range:?}, {value:?}");
/// }
/// ```
///
/// [`BTreeMap`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiscreteRangeMap<I, K, V> {
	inner: BTreeMap<K, V>,
	phantom: PhantomData<I>,
}

/// An error type to represent a range overlapping another range when
/// it should not have.
#[derive(PartialEq, Debug)]
pub struct OverlapError;

/// A compatibility type used in [`RangeType`] for allowing the library to
/// create the custom K type used in the map when necessary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct InclusiveInterval<I> {
	/// The start of the interval, inclusive.
	pub start: I,
	/// The end of the interval, inclusive.
	pub end: I,
}
impl<I> RangeBounds<I> for InclusiveInterval<I>
where
	I: PointType,
{
	fn start_bound(&self) -> Bound<&I> {
		Bound::Included(&self.start)
	}

	fn end_bound(&self) -> Bound<&I> {
		Bound::Included(&self.end)
	}
}
impl<I> InclusiveRange<I> for InclusiveInterval<I>
where
	I: PointType,
{
	fn start(&self) -> I {
		self.start
	}

	fn end(&self) -> I {
		self.end
	}
}

/// The marker trait for valid point types, a blanket implementation is provided for all types
/// which implement this traits' super-traits so you shouln't need to implement this yourself.
pub trait PointType: Ord + Copy + DiscreteFinite {}
impl<I> PointType for I where I: Ord + Copy + DiscreteFinite {}

/// The marker trait for valid range types, a blanket implementation is provided for all types
/// which implement this traits' super-traits so you shouln't need to implement this yourself.
pub trait RangeType<I>:
	InclusiveRange<I> + Copy + From<InclusiveInterval<I>>
{
}
impl<I, K> RangeType<I> for K
where
	I: PointType,
	K: InclusiveRange<I> + Copy + From<InclusiveInterval<I>>,
{
}

impl<I, K, V> DiscreteRangeMap<I, K, V>
where
	I: PointType,
	K: RangeType<I>,
{
	/// Returns `true` if the given range overlaps any of the
	/// other ranges in the map, and `false` if not.
	///
	/// # Panics
	///
	/// Panics if the given range is an invalid range. See [`Invalid
	/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::{ie, ii};
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let mut map = DiscreteRangeMap::new();
	///
	/// map.insert_strict(ie(5, 10), false);
	///
	/// assert_eq!(map.overlaps(ii(1, 3)), false);
	/// assert_eq!(map.overlaps(ie(4, 5)), false);
	///
	/// assert_eq!(map.overlaps(ii(4, 5)), true);
	/// assert_eq!(map.overlaps(ie(4, 6)), true);
	/// ```
	pub fn overlaps<Q>(&self, range: Q) -> bool
	where
		Q: RangeType<I>,
	{
		invalid_range_panic(range);

		self.overlapping(range).next().is_some()
	}

	/// Returns an iterator over every entry in the map that overlaps
	/// the given range in ascending order.
	///
	/// # Panics
	///
	/// Panics if the given range is an invalid range. See [`Invalid
	/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// let mut overlapping = map.overlapping(ie(2, 8));
	///
	/// assert_eq!(
	/// 	overlapping.collect::<Vec<_>>(),
	/// 	[(&ie(1, 4), &false), (&ie(4, 8), &true)]
	/// );
	/// ```
	pub fn overlapping<Q>(
		&self,
		range: Q,
	) -> impl DoubleEndedIterator<Item = (&K, &V)>
	where
		Q: RangeType<I>,
	{
		invalid_range_panic(range);

		let start_comp = overlapping_comp(range.start());
		let end_comp = overlapping_comp(range.end());

		let start_bound = SearchBoundCustom::Included;
		let end_bound = SearchBoundCustom::Included;

		self.inner
			.range(start_comp, start_bound, end_comp, end_bound)
	}

	/// Returns an mutable iterator over every entry in the map that
	/// overlaps the given range in ascending order.
	///
	/// # Panics
	///
	/// Panics if the given range is an invalid range. See [`Invalid
	/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let mut map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// for (range, value) in map.overlapping_mut(ie(3, 7)) {
	/// 	if *range == ie(4, 8) {
	/// 		*value = false
	/// 	} else {
	/// 		*value = true
	/// 	}
	/// }
	/// ```
	pub fn overlapping_mut<Q>(
		&mut self,
		range: Q,
	) -> impl DoubleEndedIterator<Item = (&K, &mut V)>
	where
		Q: RangeType<I>,
	{
		invalid_range_panic(range);

		let start_comp = overlapping_comp(range.start());
		let end_comp = overlapping_comp(range.end());

		let start_bound = SearchBoundCustom::Included;
		let end_bound = SearchBoundCustom::Included;

		self.inner
			.range_mut(start_comp, start_bound, end_comp, end_bound)
	}

	/// Returns a reference to the value corresponding to the range in
	/// the map that overlaps the given point, if any.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(map.get_at_point(3), Some(&false));
	/// assert_eq!(map.get_at_point(4), Some(&true));
	/// assert_eq!(map.get_at_point(101), None);
	/// ```
	pub fn get_at_point(&self, point: I) -> Option<&V> {
		self.get_entry_at_point(point).map(|(_, value)| value).ok()
	}

	/// Returns a mutable reference to the value corresponding to the
	/// range that overlaps the given point, if any.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::DiscreteRangeMap;
	/// let mut map =
	/// 	DiscreteRangeMap::from_slice_strict([(ie(1, 4), false)])
	/// 		.unwrap();
	///
	/// if let Some(x) = map.get_at_point_mut(2) {
	/// 	*x = true;
	/// }
	///
	/// assert_eq!(map.get_at_point(1), Some(&true));
	/// ```
	pub fn get_at_point_mut(&mut self, point: I) -> Option<&mut V> {
		self.inner.get_mut(overlapping_comp(point))
	}

	/// Returns `true` if the map contains a range that overlaps the
	/// given point, and `false` if not.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(map.contains_point(3), true);
	/// assert_eq!(map.contains_point(4), true);
	/// assert_eq!(map.contains_point(101), false);
	/// ```
	pub fn contains_point(&self, point: I) -> bool {
		self.get_entry_at_point(point).is_ok()
	}

	/// Returns the entry corresponding to the range that
	/// overlaps the given point, if any.
	///
	/// If there is no range that overlaps the given point the
	/// maximally-sized gap at the given point is returned.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::{ie, iu};
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 6), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(map.get_entry_at_point(3), Ok((&ie(1, 4), &false)));
	/// assert_eq!(map.get_entry_at_point(5), Ok((&ie(4, 6), &true)));
	/// assert_eq!(map.get_entry_at_point(7), Err(ie(6, 8)));
	/// assert_eq!(map.get_entry_at_point(101), Err(iu(100)));
	/// ```
	pub fn get_entry_at_point(&self, point: I) -> Result<(&K, &V), K> {
		self.inner
			.get_key_value(overlapping_comp(point))
			.ok_or_else(|| K::from(self.get_gap_at_raw(point)))
	}
	fn get_gap_at_raw(&self, point: I) -> InclusiveInterval<I> {
		let lower = self
			.inner
			.upper_bound(overlapping_comp(point), SearchBoundCustom::Included);
		let upper = self
			.inner
			.lower_bound(overlapping_comp(point), SearchBoundCustom::Included);

		InclusiveInterval {
			start: lower
				.key()
				.map_or(I::MIN, |lower| lower.end().up().unwrap()),
			end: upper
				.key()
				.map_or(I::MAX, |upper| upper.start().down().unwrap()),
		}
	}

	/// Removes every entry in the map which overlaps the given range
	/// and returns them in an iterator.
	///
	/// # Panics
	///
	/// Panics if the given range is an invalid range. See [`Invalid
	/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let mut map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// let mut removed = map.remove_overlapping(ie(2, 8));
	///
	/// assert_eq!(
	/// 	removed.collect::<Vec<_>>(),
	/// 	[(ie(1, 4), false), (ie(4, 8), true)]
	/// );
	///
	/// assert_eq!(
	/// 	map.into_iter().collect::<Vec<_>>(),
	/// 	[(ie(8, 100), false)]
	/// );
	/// ```
	pub fn remove_overlapping<'a, Q>(
		&'a mut self,
		range: Q,
	) -> impl Iterator<Item = (K, V)> + '_
	where
		Q: RangeType<I> + 'a,
	{
		invalid_range_panic(range);

		let mut result = Vec::new();

		let mut leftmost_cursor = self.inner.lower_bound_mut(
			overlapping_comp(range.start()),
			SearchBoundCustom::Included,
		);

		while leftmost_cursor
			.key()
			.is_some_and(|inner_range| overlaps(*inner_range, range))
		{
			result.push(leftmost_cursor.remove_current().unwrap());
		}

		return result.into_iter();
	}

	/// Cuts a given range out of the map and returns an iterator of
	/// the full or partial ranges that were cut.
	///
	/// `V` must implement `Clone` as if you try to cut out the center
	/// of a range in the map it will split into two different entries
	/// using `Clone`. Or if you partially cut a range then
	/// `V` must be cloned to be returned in the iterator.
	///
	/// # Panics
	///
	/// Panics if the given range is an invalid range. See [`Invalid
	/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::{ie, ii};
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let mut base = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// let after_cut = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 2), false),
	/// 	(ie(40, 100), false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(
	/// 	base.cut(ie(2, 40)).collect::<Vec<_>>(),
	/// 	[(ie(2, 4), false), (ie(4, 8), true), (ie(8, 40), false),]
	/// );
	/// assert_eq!(base, after_cut);
	/// ```
	pub fn cut<'a, Q>(
		&'a mut self,
		range: Q,
	) -> impl Iterator<Item = (K, V)> + '_
	where
		Q: RangeType<I> + 'a,
		V: Clone,
	{
		invalid_range_panic(range);

		let start_comp = overlapping_comp(range.start());
		let end_comp = overlapping_comp(range.end());

		let left_overlapping = self
			.inner
			.get_key_value(start_comp)
			.map(|(key, _)| key)
			.copied();
		let right_overlapping = self
			.inner
			.get_key_value(end_comp)
			.map(|(key, _)| key)
			.copied();

		if let Some(left) = left_overlapping
			&& let Some(right) = right_overlapping
			&& left.start() == right.start()
		{
			Either::Left(self.cut_single_overlapping(range, left))
		} else {
			Either::Right(self.cut_non_single_overlapping(
				range,
				left_overlapping,
				right_overlapping,
			))
		}
	}
	fn cut_single_overlapping<Q>(
		&mut self,
		range: Q,
		single_overlapping_range: K,
	) -> impl Iterator<Item = (K, V)>
	where
		Q: RangeType<I>,
		V: Clone,
	{
		invalid_range_panic(range);

		let cut_result = cut_range(single_overlapping_range, range);

		let returning_before_cut = cut_result.before_cut.map(K::from);
		let returning_after_cut = cut_result.after_cut.map(K::from);

		let value = self.inner.remove(overlapping_comp(range.start())).unwrap();

		if let Some(before) = returning_before_cut {
			self.insert_unchecked(before, value.clone());
		}
		if let Some(after) = returning_after_cut {
			self.insert_unchecked(after, value.clone());
		}

		once((cut_result.inside_cut.map(K::from).unwrap(), value))
	}
	fn cut_non_single_overlapping<'a, Q>(
		&'a mut self,
		range: Q,
		left_overlapping: Option<K>,
		right_overlapping: Option<K>,
	) -> impl Iterator<Item = (K, V)> + '_
	where
		Q: RangeType<I> + 'a,
		V: Clone,
	{
		invalid_range_panic(range);

		let (returning_before_cut, keeping_before) = match left_overlapping {
			Some(before) => {
				let cut_result = cut_range(before, range);

				(
					cut_result.before_cut.map(K::from),
					cut_result.inside_cut.map(K::from),
				)
			}
			None => (None, None),
		};
		let (returning_after_cut, keeping_after) = match right_overlapping {
			Some(after) => {
				let cut_result = cut_range(after, range);

				(
					cut_result.after_cut.map(K::from),
					cut_result.inside_cut.map(K::from),
				)
			}
			None => (None, None),
		};

		let before_value = self.inner.remove(overlapping_comp(range.start()));
		let after_value = self.inner.remove(overlapping_comp(range.end()));

		if let Some(returning_before_cut) = returning_before_cut {
			self.insert_unchecked(
				returning_before_cut,
				before_value.as_ref().cloned().unwrap(),
			);
		}
		if let Some(returning_after_cut) = returning_after_cut {
			self.insert_unchecked(
				returning_after_cut,
				after_value.as_ref().cloned().unwrap(),
			);
		}

		let keeping_before_entry = keeping_before
			.map(|keeping_before| (keeping_before, before_value.unwrap()));
		let keeping_after_entry = keeping_after
			.map(|keeping_after| (keeping_after, after_value.unwrap()));

		return keeping_before_entry
			.into_iter()
			.chain(self.remove_overlapping(range).map(|(key, value)| {
				(
					K::from(InclusiveInterval {
						start: key.start(),
						end: key.end(),
					}),
					value,
				)
			}))
			.chain(keeping_after_entry);
	}

	/// Returns an iterator of ranges over all the maximally-sized
	/// gaps in the map that are also within the given `outer_range`.
	///
	/// # Panics
	///
	/// Panics if the given range is an invalid range. See [`Invalid
	/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::{ie, iu};
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 3), false),
	/// 	(ie(5, 7), true),
	/// 	(ie(9, 100), false),
	/// ])
	/// .unwrap();
	///
	/// let mut gaps = map.gaps(iu(2));
	///
	/// assert_eq!(
	/// 	gaps.collect::<Vec<_>>(),
	/// 	[ie(3, 5), ie(7, 9), iu(100)]
	/// );
	/// ```
	pub fn gaps<'a, Q>(&'a self, outer_range: Q) -> impl Iterator<Item = K> + '_
	where
		Q: RangeType<I> + 'a,
	{
		invalid_range_panic(outer_range);

		// If the start or end point of outer_range is not
		// contained within a range in the map then we need to
		// generate the gaps.
		let start_gap = (!self
			.inner
			.contains_key(overlapping_comp(outer_range.start())))
		.then(|| self.get_gap_at_raw(outer_range.start()));
		let end_gap =
			(!self.inner.contains_key(overlapping_comp(outer_range.end())))
				.then(|| self.get_gap_at_raw(outer_range.end()));

		let (trimmed_start_gap, trimmed_end_gap) = match (start_gap, end_gap) {
			(Some(mut start_gap), Some(mut end_gap)) => {
				if start_gap.start() == end_gap.start() {
					//it's the same gap
					start_gap.start = outer_range.start();
					start_gap.end = outer_range.end();

					(Some(start_gap), None)
				} else {
					//it's different gaps
					start_gap.start = outer_range.start();
					end_gap.end = outer_range.end();

					(Some(start_gap), Some(end_gap))
				}
			}
			(Some(mut start_gap), None) => {
				start_gap.start = outer_range.start();
				(Some(start_gap), None)
			}
			(None, Some(mut end_gap)) => {
				end_gap.end = outer_range.end();
				(None, Some(end_gap))
			}
			(None, None) => (None, None),
		};

		let overlapping = self
			.overlapping(outer_range)
			.map(|(key, _)| (key.start(), key.end()));

		let inner_gaps = overlapping
			.tuple_windows()
			.map(|(first, second)| {
				K::from(InclusiveInterval {
					start: first.1.up().unwrap(),
					end: second.0.down().unwrap(),
				})
			})
			.filter(|range| is_valid_range(*range));

		//possibly add the trimmed start and end gaps
		return trimmed_start_gap
			.map(K::from)
			.into_iter()
			.chain(inner_gaps)
			.chain(trimmed_end_gap.map(K::from));
	}

	/// Returns `true` if the map covers every point in the given
	/// range, and `false` if it does not.
	///
	/// # Panics
	///
	/// Panics if the given range is an invalid range. See [`Invalid
	/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 3), false),
	/// 	(ie(5, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(map.contains_range(ie(1, 3)), true);
	/// assert_eq!(map.contains_range(ie(2, 6)), false);
	/// assert_eq!(map.contains_range(ie(6, 100)), true);
	/// ```
	pub fn contains_range<Q>(&self, range: Q) -> bool
	where
		Q: RangeType<I>,
	{
		invalid_range_panic(range);

		// Soooo clean and mathematical 🥰!
		self.gaps(range).next().is_none()
	}

	/// Adds a new entry to the map without modifying other entries.
	///
	/// If the given range overlaps one or more ranges already in the
	/// map, then an [`OverlapError`] is returned and the map is not
	/// updated.
	///
	/// # Panics
	///
	/// Panics if the given range is an invalid range. See [`Invalid
	/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::{DiscreteRangeMap, OverlapError};
	///
	/// let mut map = DiscreteRangeMap::new();
	///
	/// assert_eq!(map.insert_strict(ie(5, 10), 9), Ok(()));
	/// assert_eq!(map.insert_strict(ie(5, 10), 2), Err(OverlapError));
	/// assert_eq!(map.len(), 1);
	/// ```
	pub fn insert_strict(
		&mut self,
		range: K,
		value: V,
	) -> Result<(), OverlapError> {
		invalid_range_panic(range);

		if self.overlaps(range) {
			return Err(OverlapError);
		}

		self.insert_unchecked(range, value);

		return Ok(());
	}
	fn insert_unchecked(&mut self, range: K, value: V) {
		self.inner.insert(range, value, double_comp());
	}

	fn insert_merge_with_comps<G1, G2, R1, R2>(
		&mut self,
		range: K,
		value: V,
		get_start: G1,
		get_end: G2,
		remove_start: R1,
		remove_end: R2,
	) -> K
	where
		G1: FnOnce(&Self, &V) -> Option<K>,
		G2: FnOnce(&Self, &V) -> Option<K>,
		R1: FnOnce(&mut Self, &V),
		R2: FnOnce(&mut Self, &V),
	{
		invalid_range_panic(range);

		let matching_start = get_start(self, &value);
		let matching_end = get_end(self, &value);

		let returning = match (matching_start, matching_end) {
			(Some(matching_start), Some(matching_end)) => {
				K::from(InclusiveInterval {
					start: matching_start.start(),
					end: matching_end.end(),
				})
			}
			(Some(matching_start), None) => K::from(InclusiveInterval {
				start: matching_start.start(),
				end: range.end(),
			}),
			(None, Some(matching_end)) => K::from(InclusiveInterval {
				start: range.start(),
				end: matching_end.end(),
			}),
			(None, None) => range,
		};

		let _ = self.remove_overlapping(range);

		remove_start(self, &value);
		remove_end(self, &value);

		self.insert_unchecked(returning, value);

		return returning;
	}

	/// Adds a new entry to the map and merges into other ranges in
	/// the map which touch it.
	///
	/// The value of the merged-together range is set to the value given for
	/// this insertion.
	///
	/// If successful then the newly inserted (possibly merged) range is
	/// returned.
	///
	/// If the given range overlaps one or more ranges already in the
	/// map, then an [`OverlapError`] is returned and the map is not
	/// updated.
	///
	/// # Panics
	///
	/// Panics if the given range is an invalid range. See [`Invalid
	/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::{DiscreteRangeMap, OverlapError};
	///
	/// let mut map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(6, 8), true),
	/// ])
	/// .unwrap();
	///
	/// // Touching
	/// assert_eq!(
	/// 	map.insert_merge_touching(ie(4, 6), true),
	/// 	Ok(ie(1, 8))
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching(ie(4, 8), false),
	/// 	Err(OverlapError),
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching(ie(10, 16), false),
	/// 	Ok(ie(10, 16))
	/// );
	///
	/// assert_eq!(
	/// 	map.into_iter().collect::<Vec<_>>(),
	/// 	[(ie(1, 8), true), (ie(10, 16), false)]
	/// );
	/// ```
	pub fn insert_merge_touching(
		&mut self,
		range: K,
		value: V,
	) -> Result<K, OverlapError> {
		invalid_range_panic(range);

		if self.overlaps(range) {
			return Err(OverlapError);
		}

		Ok(self.insert_merge_with_comps(
			range,
			value,
			|selfy, _| {
				selfy
					.inner
					.get_key_value(touching_start_comp(range.start()))
					.map(|(key, _)| key)
					.copied()
			},
			|selfy, _| {
				selfy
					.inner
					.get_key_value(touching_end_comp(range.end()))
					.map(|(key, _)| key)
					.copied()
			},
			|selfy, _| {
				selfy.inner.remove(touching_start_comp(range.start()));
			},
			|selfy, _| {
				selfy.inner.remove(touching_end_comp(range.end()));
			},
		))
	}

	/// Adds a new entry to the map and merges into other ranges in
	/// the map which touch it if the touching ranges' values are
	/// equal to the value being inserted.
	///
	/// If successful then the newly inserted (possibly merged) range is
	/// returned.
	///
	/// If the given range overlaps one or more ranges already in the
	/// map, then an [`OverlapError`] is returned and the map is not
	/// updated.
	///
	/// # Panics
	///
	/// Panics if the given range is an invalid range. See [`Invalid
	/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::{DiscreteRangeMap, OverlapError};
	///
	/// let mut map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(6, 8), true),
	/// ])
	/// .unwrap();
	///
	/// // Touching
	/// assert_eq!(
	/// 	map.insert_merge_touching_if_values_equal(ie(4, 6), true),
	/// 	Ok(ie(4, 8))
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching_if_values_equal(ie(4, 8), false),
	/// 	Err(OverlapError),
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching_if_values_equal(ie(10, 16), false),
	/// 	Ok(ie(10, 16))
	/// );
	///
	/// assert_eq!(
	/// 	map.into_iter().collect::<Vec<_>>(),
	/// 	[(ie(1, 4), false), (ie(4, 8), true), (ie(10, 16), false)]
	/// );
	/// ```
	pub fn insert_merge_touching_if_values_equal(
		&mut self,
		range: K,
		value: V,
	) -> Result<K, OverlapError>
	where
		V: Eq,
	{
		invalid_range_panic(range);

		if self.overlaps(range) {
			return Err(OverlapError);
		}

		let get_start = |selfy: &Self, value: &V| {
			selfy
				.inner
				.get_key_value(touching_start_comp(range.start()))
				.filter(|(_, start_touching_value)| {
					*start_touching_value == value
				})
				.map(|(key, _)| key)
				.copied()
		};
		let get_end = |selfy: &Self, value: &V| {
			selfy
				.inner
				.get_key_value(touching_end_comp(range.end()))
				.filter(|(_, start_touching_value)| {
					*start_touching_value == value
				})
				.map(|(key, _)| key)
				.copied()
		};

		Ok(self.insert_merge_with_comps(
			range,
			value,
			get_start,
			get_end,
			|selfy, value| {
				if get_start(selfy, value).is_some() {
					selfy.inner.remove(touching_start_comp(range.start()));
				}
			},
			|selfy, value| {
				if get_end(selfy, value).is_some() {
					selfy.inner.remove(touching_end_comp(range.end()));
				}
			},
		))
	}

	/// Adds a new entry to the map and merges into other ranges in
	/// the map which overlap it.
	///
	/// The value of the merged-together range is set to the value given for
	/// this insertion.
	///
	/// The newly inserted (possibly merged) range is returned.
	///
	/// # Panics
	///
	/// Panics if the given range is an invalid range. See [`Invalid
	/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::{DiscreteRangeMap, OverlapError};
	///
	/// let mut map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(6, 8), true),
	/// ])
	/// .unwrap();
	///
	/// // Touching
	/// assert_eq!(
	/// 	map.insert_merge_overlapping(ie(4, 6), true),
	/// 	ie(4, 6)
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_overlapping(ie(4, 8), false),
	/// 	ie(4, 8)
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_overlapping(ie(10, 16), false),
	/// 	ie(10, 16)
	/// );
	///
	/// assert_eq!(
	/// 	map.into_iter().collect::<Vec<_>>(),
	/// 	[(ie(1, 4), false), (ie(4, 8), false), (ie(10, 16), false)]
	/// );
	/// ```
	pub fn insert_merge_overlapping(&mut self, range: K, value: V) -> K {
		invalid_range_panic(range);

		self.insert_merge_with_comps(
			range,
			value,
			|selfy, _| {
				selfy
					.inner
					.get_key_value(overlapping_comp(range.start()))
					.map(|(key, _)| key)
					.copied()
			},
			|selfy, _| {
				selfy
					.inner
					.get_key_value(overlapping_comp(range.end()))
					.map(|(key, _)| key)
					.copied()
			},
			|_, _| {},
			|_, _| {},
		)
	}

	/// Adds a new entry to the map and merges into other ranges in
	/// the map which touch or overlap it.
	///
	/// The value of the merged-together range is set to the value given for
	/// this insertion.
	///
	/// The newly inserted (possibly merged) range is returned.
	///
	/// # Panics
	///
	/// Panics if the given range is an invalid range. See [`Invalid
	/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::{DiscreteRangeMap, OverlapError};
	///
	/// let mut map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(6, 8), true),
	/// ])
	/// .unwrap();
	///
	/// // Touching
	/// assert_eq!(
	/// 	map.insert_merge_touching_or_overlapping(ie(4, 6), true),
	/// 	ie(1, 8)
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching_or_overlapping(ie(4, 8), false),
	/// 	ie(1, 8)
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching_or_overlapping(ie(10, 16), false),
	/// 	ie(10, 16)
	/// );
	///
	/// assert_eq!(
	/// 	map.into_iter().collect::<Vec<_>>(),
	/// 	[(ie(1, 8), false), (ie(10, 16), false)]
	/// );
	/// ```
	pub fn insert_merge_touching_or_overlapping(
		&mut self,
		range: K,
		value: V,
	) -> K {
		invalid_range_panic(range);

		self.insert_merge_with_comps(
			range,
			value,
			|selfy, _| {
				selfy
					.inner
					.get_key_value(touching_start_comp(range.start()))
					.map(|(key, _)| key)
					.or(selfy
						.inner
						.get_key_value(overlapping_comp(range.start()))
						.map(|(key, _)| key))
					.copied()
			},
			|selfy, _| {
				selfy
					.inner
					.get_key_value(touching_end_comp(range.end()))
					.map(|(key, _)| key)
					.or(selfy
						.inner
						.get_key_value(overlapping_comp(range.end()))
						.map(|(key, _)| key))
					.copied()
			},
			|selfy, _| {
				selfy.inner.remove(touching_start_comp(range.start()));
			},
			|selfy, _| {
				selfy.inner.remove(touching_end_comp(range.end()));
			},
		)
	}

	/// Adds a new entry to the map and overwrites any other ranges
	/// that overlap the new range.
	///
	/// This is equivalent to using [`DiscreteRangeMap::cut()`]
	/// followed by [`DiscreteRangeMap::insert_strict()`]. Hence the
	/// same `V: Clone` trait bound applies.
	///
	/// # Panics
	///
	/// Panics if the given range is an invalid range. See [`Invalid
	/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let mut map =
	/// 	DiscreteRangeMap::from_slice_strict([(ie(2, 8), false)])
	/// 		.unwrap();
	///
	/// map.insert_overwrite(ie(4, 6), true);
	///
	/// assert_eq!(
	/// 	map.into_iter().collect::<Vec<_>>(),
	/// 	[(ie(2, 4), false), (ie(4, 6), true), (ie(6, 8), false)]
	/// );
	/// ```
	pub fn insert_overwrite(&mut self, range: K, value: V)
	where
		V: Clone,
	{
		invalid_range_panic(range);

		let _ = self.cut(range);
		self.insert_unchecked(range, value);
	}

	/// Allocates a `DiscreteRangeMap` and moves the given entries from
	/// the given slice into the map using
	/// [`DiscreteRangeMap::insert_strict()`].
	///
	/// May return an `Err` while inserting. See
	/// [`DiscreteRangeMap::insert_strict()`] for details.
	///
	/// # Panics
	///
	/// Panics if the given range is an invalid range. See [`Invalid
	/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	/// ```
	pub fn from_slice_strict<const N: usize>(
		slice: [(K, V); N],
	) -> Result<DiscreteRangeMap<I, K, V>, OverlapError> {
		let mut map = DiscreteRangeMap::new();
		for (range, value) in slice {
			map.insert_strict(range, value)?;
		}
		return Ok(map);
	}

	/// Collects a `DiscreteRangeMap` from an iterator of (range,
	/// value) tuples using [`DiscreteRangeMap::insert_strict()`].
	///
	/// May return an `Err` while inserting. See
	/// [`DiscreteRangeMap::insert_strict()`] for details.
	///
	/// # Panics
	///
	/// Panics if the given range is an invalid range. See [`Invalid
	/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let slice =
	/// 	[(ie(1, 4), false), (ie(4, 8), true), (ie(8, 100), false)];
	///
	/// let map: DiscreteRangeMap<_, _, _> =
	/// 	DiscreteRangeMap::from_iter_strict(
	/// 		slice.into_iter().filter(|(range, _)| range.start > 2),
	/// 	)
	/// 	.unwrap();
	/// ```
	pub fn from_iter_strict(
		iter: impl Iterator<Item = (K, V)>,
	) -> Result<DiscreteRangeMap<I, K, V>, OverlapError> {
		let mut map = DiscreteRangeMap::new();
		for (range, value) in iter {
			map.insert_strict(range, value)?;
		}
		return Ok(map);
	}
}

impl<I, K, V> DiscreteRangeMap<I, K, V> {
	/// Makes a new, empty `DiscreteRangeMap`.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::{DiscreteRangeMap, InclusiveInterval};
	///
	/// let map: DiscreteRangeMap<i8, InclusiveInterval<i8>, bool> =
	/// 	DiscreteRangeMap::new();
	/// ```
	pub fn new() -> Self {
		DiscreteRangeMap {
			inner: BTreeMap::new(),
			phantom: PhantomData,
		}
	}

	/// Returns the number of ranges in the map.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let mut map = DiscreteRangeMap::new();
	///
	/// assert_eq!(map.len(), 0);
	/// map.insert_strict(ie(0, 1), false).unwrap();
	/// assert_eq!(map.len(), 1);
	/// ```
	pub fn len(&self) -> usize {
		self.inner.len()
	}

	/// Returns `true` if the map contains no ranges, and
	/// `false` if it does.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let mut map = DiscreteRangeMap::new();
	///
	/// assert_eq!(map.is_empty(), true);
	/// map.insert_strict(ie(0, 1), false).unwrap();
	/// assert_eq!(map.is_empty(), false);
	/// ```
	pub fn is_empty(&self) -> bool {
		self.inner.is_empty()
	}

	/// Returns an iterator over every entry in the map in ascending
	/// order.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// let mut iter = map.iter();
	///
	/// assert_eq!(iter.next(), Some((&ie(1, 4), &false)));
	/// assert_eq!(iter.next(), Some((&ie(4, 8), &true)));
	/// assert_eq!(iter.next(), Some((&ie(8, 100), &false)));
	/// assert_eq!(iter.next(), None);
	/// ```
	pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&K, &V)> {
		self.inner.iter()
	}

	/// Returns an mutable iterator over every entry in the map in
	/// ascending order.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let mut map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// for (range, value) in map.iter_mut() {
	/// 	if *range == ie(4, 8) {
	/// 		*value = false
	/// 	} else {
	/// 		*value = true
	/// 	}
	/// }
	/// ```
	pub fn iter_mut(
		&mut self,
	) -> impl DoubleEndedIterator<Item = (&K, &mut V)> {
		self.inner.iter_mut()
	}

	/// Returns the first entry in the map, if any.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::test_ranges::ie;
	/// use discrete_range_map::DiscreteRangeMap;
	///
	/// let map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(map.first_entry(), Some((&ie(1, 4), &false)));
	/// ```
	pub fn first_entry(&self) -> Option<(&K, &V)> {
		self.inner.first_key_value()
	}

	/// Returns the last entry in the map, if any.
	///
	/// # Examples
	/// ```
	/// use discrete_range_map::DiscreteRangeMap;
	/// use discrete_range_map::test_ranges::ie;
	///
	/// let map = DiscreteRangeMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(
	/// 	map.last_entry(),
	/// 	Some((&ie(8, 100), &false))
	/// );
	pub fn last_entry(&self) -> Option<(&K, &V)> {
		self.inner.last_key_value()
	}
}

// Helper Functions ==========================

fn invalid_range_panic<Q, I>(range: Q)
where
	I: PointType,
	Q: RangeType<I>,
{
	if !is_valid_range(range) {
		panic!(
			"invalid range given to function see here for more details: https://docs.rs/discrete_range_map/latest/discrete_range_map/#invalid-ranges"
		);
	}
}

fn double_comp<K, I>() -> impl FnMut(&K, &K) -> Ordering
where
	I: PointType,
	K: RangeType<I>,
{
	|inner_range: &K, new_range: &K| new_range.start().cmp(&inner_range.start())
}
fn overlapping_comp<I, K>(point: I) -> impl FnMut(&K) -> Ordering
where
	I: PointType,
	K: RangeType<I>,
{
	move |inner_range: &K| cmp_point_with_range(point, *inner_range)
}
fn touching_start_comp<I, K>(start: I) -> impl FnMut(&K) -> Ordering
where
	I: PointType,
	K: RangeType<I>,
{
	move |inner_range: &K| match inner_range.end().up() {
		Some(touching_position) => start.cmp(&touching_position),
		None => Ordering::Less,
	}
}
fn touching_end_comp<I, K>(end: I) -> impl FnMut(&K) -> Ordering
where
	I: PointType,
	K: RangeType<I>,
{
	move |inner_range: &K| match inner_range.start().down() {
		Some(touching_position) => end.cmp(&touching_position),
		None => Ordering::Greater,
	}
}

/// A range that has **Inclusive** end-points.
pub trait InclusiveRange<I> {
	/// The start of the range, inclusive.
	fn start(&self) -> I;
	/// The end of the range, inclusive.
	fn end(&self) -> I;

    /// Does the range contain the given point?
	fn contains(&self, point: I) -> bool
	where
		I: PointType,
	{
		point >= self.start() && point <= self.end()
	}

    /// Is the range is valid, which according to this crate means `start()`
    /// <= `end()`
	fn is_valid(&self) -> bool
	where
		I: PointType,
	{
		self.start() <= self.end()
	}

	/// Requires that self comes before other and they don't overlap
	fn touches_ordered(&self, other: &Self) -> bool
	where
		I: PointType,
	{
		self.end() == other.start().down().unwrap()
	}

	/// Requires that self comes before other
	fn overlaps_ordered(&self, other: &Self) -> bool
	where
		I: PointType,
	{
		self.contains(other.start()) || self.contains(other.end())
	}

	/// Intersect the range with the other one, and return Some if the intersection is not empty.
	fn intersect(&self, other: &Self) -> Option<Self>
	where
		I: PointType,
		Self: From<InclusiveInterval<I>>,
	{
		let intersect_start = I::max(self.start(), other.start());
		let intersect_end = I::min(self.end(), other.end());
		if intersect_start <= intersect_end {
			Some(Self::from(InclusiveInterval {
				start: intersect_start,
				end: intersect_end,
			}))
		} else {
			None
		}
	}

	/// Move the entire range by the given amount.
	fn translate(&self, delta: I) -> Self
	where
		I: PointType,
		I: core::ops::Add<Output = I>,
		Self: From<InclusiveInterval<I>>,
	{
		Self::from(InclusiveInterval {
			start: self.start() + delta,
			end: self.end() + delta,
		})
	}

	/// The amount between the start and the end points of the range.
	fn size(&self) -> I
	where
		I: PointType,
		I: core::ops::Sub<Output = I>,
	{
		(self.end() - self.start()).up().unwrap()
	}

	/// Requires that self comes before other
	fn merge_ordered(&self, other: &Self) -> Self
	where
		Self: From<InclusiveInterval<I>>,
	{
		Self::from(InclusiveInterval {
			start: self.start(),
			end: other.end(),
		})
	}
}

// Trait Impls ==========================

impl<I, K, V> IntoIterator for DiscreteRangeMap<I, K, V> {
	type Item = (K, V);
	type IntoIter = IntoIter<I, K, V>;
	fn into_iter(self) -> Self::IntoIter {
		return IntoIter {
			inner: self.inner.into_iter(),
			phantom: PhantomData,
		};
	}
}
/// An owning iterator over the entries of a [`DiscreteRangeMap`].
///
/// This `struct` is created by the [`into_iter`] method on
/// [`DiscreteRangeMap`] (provided by the [`IntoIterator`] trait). See
/// its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
pub struct IntoIter<I, K, V> {
	inner: BTreeMapIntoIter<K, V>,
	phantom: PhantomData<I>,
}
impl<I, K, V> Iterator for IntoIter<I, K, V> {
	type Item = (K, V);
	fn next(&mut self) -> Option<Self::Item> {
		self.inner.next()
	}
}

impl<I, K, V> Default for DiscreteRangeMap<I, K, V> {
	fn default() -> Self {
		DiscreteRangeMap {
			inner: BTreeMap::default(),
			phantom: PhantomData,
		}
	}
}

impl<I, K, V> Serialize for DiscreteRangeMap<I, K, V>
where
	K: Serialize,
	V: Serialize,
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let mut seq = serializer.serialize_seq(Some(self.len()))?;
		for (range_bounds, value) in self.iter() {
			seq.serialize_element(&(range_bounds, value))?;
		}
		seq.end()
	}
}

impl<'de, I, K, V> Deserialize<'de> for DiscreteRangeMap<I, K, V>
where
	I: PointType,
	K: RangeType<I> + Deserialize<'de>,
	V: Deserialize<'de>,
{
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		deserializer.deserialize_seq(DiscreteRangeMapVisitor {
			i: PhantomData,
			k: PhantomData,
			v: PhantomData,
		})
	}
}

struct DiscreteRangeMapVisitor<I, K, V> {
	i: PhantomData<I>,
	k: PhantomData<K>,
	v: PhantomData<V>,
}

impl<'de, I, K, V> Visitor<'de> for DiscreteRangeMapVisitor<I, K, V>
where
	I: PointType,
	K: RangeType<I> + Deserialize<'de>,
	V: Deserialize<'de>,
{
	type Value = DiscreteRangeMap<I, K, V>;

	fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
		formatter.write_str("a DiscreteRangeMap")
	}

	fn visit_seq<A>(self, mut access: A) -> Result<Self::Value, A::Error>
	where
		A: SeqAccess<'de>,
	{
		let mut map = DiscreteRangeMap::new();
		while let Some((range_bounds, value)) = access.next_element()? {
			map.insert_strict(range_bounds, value)
				.map_err(|_| serde::de::Error::custom("ranges overlap"))?;
		}
		Ok(map)
	}
}

#[cfg(test)]
mod tests {
	use pretty_assertions::assert_eq;

	use super::*;
	use crate::test_ranges::{ee, ei, ie, ii, iu, ue, ui, uu};
	use crate::utils::{config, contains_point, Config, CutResult};

	//only every other number to allow mathematical_overlapping_definition
	//to test between bounds in finite using smaller intervalled finite
	pub(crate) const NUMBERS: &[i8] = &[2, 4, 6, 8, 10];
	//go a bit around on either side to compensate for Unbounded
	pub(crate) const NUMBERS_DOMAIN: &[i8] =
		&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

	fn basic() -> DiscreteRangeMap<i8, InclusiveInterval<i8>, bool> {
		DiscreteRangeMap::from_slice_strict([
			(ui(4), false),
			(ee(5, 7), true),
			(ii(7, 7), false),
			(ie(14, 16), true),
		])
		.unwrap()
	}
	fn basic_slice() -> [(InclusiveInterval<i8>, bool); 4] {
		[
			(ui(4), false),
			(ee(5, 7), true),
			(ii(7, 7), false),
			(ie(14, 16), true),
		]
	}

	#[test]
	fn insert_strict_tests() {
		assert_insert_strict(
			basic(),
			(ii(0, 4), false),
			Err(OverlapError),
			basic_slice(),
		);
		assert_insert_strict(
			basic(),
			(ii(5, 6), false),
			Err(OverlapError),
			basic_slice(),
		);
		assert_insert_strict(
			basic(),
			(ii(4, 5), true),
			Err(OverlapError),
			basic_slice(),
		);
		assert_insert_strict(
			basic(),
			(ei(4, 5), true),
			Ok(()),
			[
				(ui(4), false),
				(ei(4, 5), true),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			],
		);
	}
	fn assert_insert_strict<const N: usize>(
		mut before: DiscreteRangeMap<i8, InclusiveInterval<i8>, bool>,
		to_insert: (InclusiveInterval<i8>, bool),
		result: Result<(), OverlapError>,
		after: [(InclusiveInterval<i8>, bool); N],
	) {
		assert_eq!(before.insert_strict(to_insert.0, to_insert.1), result);
		assert_eq!(before, DiscreteRangeMap::from_slice_strict(after).unwrap())
	}

	#[test]
	fn overlapping_tests() {
		//case zero
		for overlap_range in all_valid_test_bounds() {
			//you can't overlap nothing
			assert!(
				DiscreteRangeMap::<i8, InclusiveInterval<i8>, ()>::new()
					.overlapping(overlap_range)
					.next()
					.is_none()
			);
		}

		//case one
		for overlap_range in all_valid_test_bounds() {
			for inside_range in all_valid_test_bounds() {
				let mut map = DiscreteRangeMap::new();
				map.insert_strict(inside_range, ()).unwrap();

				let mut expected_overlapping = Vec::new();
				if overlaps(overlap_range, inside_range) {
					expected_overlapping.push(inside_range);
				}

				let overlapping = map
					.overlapping(overlap_range)
					.map(|(key, _)| key)
					.copied()
					.collect::<Vec<_>>();

				if overlapping != expected_overlapping {
					dbg!(overlap_range, inside_range);
					dbg!(overlapping, expected_overlapping);
					panic!(
						"Discrepancy in .overlapping() with single inside range detected!"
					);
				}
			}
		}

		//case two
		for overlap_range in all_valid_test_bounds() {
			for (inside_range1, inside_range2) in
				all_non_overlapping_test_bound_entries()
			{
				let mut map = DiscreteRangeMap::new();
				map.insert_strict(inside_range1, ()).unwrap();
				map.insert_strict(inside_range2, ()).unwrap();

				let mut expected_overlapping = Vec::new();
				if overlaps(overlap_range, inside_range1) {
					expected_overlapping.push(inside_range1);
				}
				if overlaps(overlap_range, inside_range2) {
					expected_overlapping.push(inside_range2);
				}
				//make our expected_overlapping the correct order
				if expected_overlapping.len() > 1
					&& expected_overlapping[0].start()
						> expected_overlapping[1].start()
				{
					expected_overlapping.swap(0, 1);
				}

				let overlapping = map
					.overlapping(overlap_range)
					.map(|(key, _)| key)
					.copied()
					.collect::<Vec<_>>();

				if overlapping != expected_overlapping {
					dbg!(overlap_range, inside_range1, inside_range2);
					dbg!(overlapping, expected_overlapping);
					panic!(
						"Discrepancy in .overlapping() with two inside ranges detected!"
					);
				}
			}
		}
	}

	#[test]
	fn remove_overlapping_tests() {
		assert_remove_overlapping(basic(), ii(5, 5), [], basic_slice());
		assert_remove_overlapping(
			basic(),
			uu(),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			],
			[],
		);
		assert_remove_overlapping(
			basic(),
			ii(6, 7),
			[(ee(5, 7), true), (ii(7, 7), false)],
			[(ui(4), false), (ie(14, 16), true)],
		);
		assert_remove_overlapping(
			basic(),
			iu(6),
			[(ee(5, 7), true), (ii(7, 7), false), (ie(14, 16), true)],
			[(ui(4), false)],
		);
	}
	fn assert_remove_overlapping<const N: usize, const Y: usize>(
		mut before: DiscreteRangeMap<i8, InclusiveInterval<i8>, bool>,
		to_remove: InclusiveInterval<i8>,
		result: [(InclusiveInterval<i8>, bool); N],
		after: [(InclusiveInterval<i8>, bool); Y],
	) {
		assert_eq!(
			before.remove_overlapping(to_remove).collect::<Vec<_>>(),
			result
		);
		assert_eq!(before, DiscreteRangeMap::from_slice_strict(after).unwrap())
	}

	#[test]
	fn cut_tests() {
		assert_cut(
			basic(),
			ii(50, 60),
			[],
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			],
		);
		assert_cut(
			basic(),
			uu(),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			],
			[],
		);
		assert_cut(
			basic(),
			ui(6),
			[(ui(4), false), (ei(5, 6), true)],
			[(ii(7, 7), false), (ie(14, 16), true)],
		);
		assert_cut(
			basic(),
			iu(6),
			[(ie(6, 7), true), (ii(7, 7), false), (ie(14, 16), true)],
			[(ui(4), false)],
		);
	}
	fn assert_cut<const N: usize, const Y: usize>(
		mut before: DiscreteRangeMap<i8, InclusiveInterval<i8>, bool>,
		to_cut: InclusiveInterval<i8>,
		result: [(InclusiveInterval<i8>, bool); Y],
		after: [(InclusiveInterval<i8>, bool); N],
	) {
		assert_eq!(before.cut(to_cut).collect::<Vec<_>>(), result);
		assert_eq!(before, DiscreteRangeMap::from_slice_strict(after).unwrap());
	}

	#[test]
	fn gaps_tests() {
		assert_gaps(basic(), ii(50, 60), [ii(50, 60)]);
		assert_gaps(basic(), iu(50), [iu(50)]);
		assert_gaps(basic(), ee(3, 16), [ei(4, 5), ee(7, 14)]);
		assert_gaps(basic(), ei(3, 16), [ei(4, 5), ee(7, 14), ii(16, 16)]);
		assert_gaps(basic(), ue(5), []);
		assert_gaps(basic(), ui(3), []);
		assert_gaps(basic(), ii(5, 5), [ii(5, 5)]);
		assert_gaps(basic(), ii(6, 6), []);
		assert_gaps(basic(), ii(7, 7), []);
		assert_gaps(basic(), ii(8, 8), [ii(8, 8)]);

		assert_gaps(
			basic(),
			ii(i8::MIN, i8::MAX),
			[ei(4, 5), ee(7, 14), ii(16, i8::MAX)],
		);
		assert_eq!(
			DiscreteRangeMap::from_slice_strict([(
				ii(i8::MIN, i8::MAX),
				false
			)])
			.unwrap()
			.gaps(uu())
			.collect::<Vec<_>>(),
			[]
		);
	}
	fn assert_gaps<const N: usize>(
		map: DiscreteRangeMap<i8, InclusiveInterval<i8>, bool>,
		outer_range: InclusiveInterval<i8>,
		result: [InclusiveInterval<i8>; N],
	) {
		assert_eq!(map.gaps(outer_range).collect::<Vec<_>>(), result);
	}

	#[test]
	fn insert_merge_touching_tests() {
		assert_insert_merge_touching(
			basic(),
			(ii(0, 4), false),
			Err(OverlapError),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			],
		);
		assert_insert_merge_touching(
			basic(),
			(ee(7, 10), false),
			Ok(ie(7, 10)),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ie(7, 10), false),
				(ie(14, 16), true),
			],
		);
		assert_insert_merge_touching(
			basic(),
			(ee(7, 11), true),
			Ok(ie(7, 11)),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ie(7, 11), true),
				(ie(14, 16), true),
			],
		);
		assert_insert_merge_touching(
			basic(),
			(ee(7, 14), false),
			Ok(ie(7, 16)),
			[(ui(4), false), (ee(5, 7), true), (ie(7, 16), false)],
		);
	}
	fn assert_insert_merge_touching<const N: usize>(
		mut before: DiscreteRangeMap<i8, InclusiveInterval<i8>, bool>,
		to_insert: (InclusiveInterval<i8>, bool),
		result: Result<InclusiveInterval<i8>, OverlapError>,
		after: [(InclusiveInterval<i8>, bool); N],
	) {
		assert_eq!(
			before.insert_merge_touching(to_insert.0, to_insert.1),
			result
		);
		assert_eq!(before, DiscreteRangeMap::from_slice_strict(after).unwrap())
	}
	#[test]
	fn insert_merge_touching_if_values_equal_tests() {
		assert_insert_merge_touching_if_values_equal(
			basic(),
			(ii(0, 4), false),
			Err(OverlapError),
			basic_slice(),
		);
		dbg!("hererere");
		assert_insert_merge_touching_if_values_equal(
			basic(),
			(ee(7, 10), false),
			Ok(ie(7, 10)),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ie(7, 10), false),
				(ie(14, 16), true),
			],
		);
		assert_insert_merge_touching_if_values_equal(
			basic(),
			(ee(7, 11), true),
			Ok(ee(7, 11)),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ee(7, 11), true),
				(ie(14, 16), true),
			],
		);
		assert_insert_merge_touching_if_values_equal(
			basic(),
			(ee(7, 14), false),
			Ok(ie(7, 14)),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ie(7, 14), false),
				(ie(14, 16), true),
			],
		);
	}
	fn assert_insert_merge_touching_if_values_equal<const N: usize>(
		mut before: DiscreteRangeMap<i8, InclusiveInterval<i8>, bool>,
		to_insert: (InclusiveInterval<i8>, bool),
		result: Result<InclusiveInterval<i8>, OverlapError>,
		after: [(InclusiveInterval<i8>, bool); N],
	) {
		assert_eq!(
			before.insert_merge_touching_if_values_equal(
				to_insert.0,
				to_insert.1
			),
			result
		);
		assert_eq!(before, DiscreteRangeMap::from_slice_strict(after).unwrap())
	}

	#[test]
	fn insert_merge_overlapping_tests() {
		assert_insert_merge_overlapping(
			basic(),
			(ii(0, 2), true),
			ui(4),
			[
				(ui(4), true),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			],
		);
		assert_insert_merge_overlapping(
			basic(),
			(ie(14, 16), false),
			ie(14, 16),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), false),
			],
		);
		assert_insert_merge_overlapping(
			basic(),
			(ii(6, 11), false),
			ei(5, 11),
			[(ui(4), false), (ei(5, 11), false), (ie(14, 16), true)],
		);
		assert_insert_merge_overlapping(
			basic(),
			(ii(15, 18), true),
			ii(14, 18),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ii(14, 18), true),
			],
		);
		assert_insert_merge_overlapping(
			basic(),
			(uu(), false),
			uu(),
			[(uu(), false)],
		);
	}
	fn assert_insert_merge_overlapping<const N: usize>(
		mut before: DiscreteRangeMap<i8, InclusiveInterval<i8>, bool>,
		to_insert: (InclusiveInterval<i8>, bool),
		result: InclusiveInterval<i8>,
		after: [(InclusiveInterval<i8>, bool); N],
	) {
		assert_eq!(
			before.insert_merge_overlapping(to_insert.0, to_insert.1),
			result
		);
		assert_eq!(before, DiscreteRangeMap::from_slice_strict(after).unwrap())
	}

	#[test]
	fn insert_merge_touching_or_overlapping_tests() {
		assert_insert_merge_touching_or_overlapping(
			DiscreteRangeMap::from_slice_strict([(ie(1, 4), false)]).unwrap(),
			(ie(0, 1), true),
			ie(0, 4),
			[(ie(0, 4), true)],
		);

		//copied from insert_merge_overlapping_tests
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(ii(0, 2), true),
			ui(4),
			[
				(ui(4), true),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			],
		);
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(ie(14, 16), false),
			ie(14, 16),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), false),
			],
		);
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(ii(6, 11), false),
			ei(5, 11),
			[(ui(4), false), (ei(5, 11), false), (ie(14, 16), true)],
		);
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(ii(15, 18), true),
			ii(14, 18),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ii(14, 18), true),
			],
		);
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(uu(), false),
			uu(),
			[(uu(), false)],
		);
		//the only difference from the insert_merge_overlapping
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(ii(7, 14), false),
			ee(5, 16),
			[(ui(4), false), (ee(5, 16), false)],
		);
	}
	fn assert_insert_merge_touching_or_overlapping<const N: usize>(
		mut before: DiscreteRangeMap<i8, InclusiveInterval<i8>, bool>,
		to_insert: (InclusiveInterval<i8>, bool),
		result: InclusiveInterval<i8>,
		after: [(InclusiveInterval<i8>, bool); N],
	) {
		assert_eq!(
			before
				.insert_merge_touching_or_overlapping(to_insert.0, to_insert.1),
			result
		);
		assert_eq!(before, DiscreteRangeMap::from_slice_strict(after).unwrap())
	}

	#[test]
	fn config_tests() {
		assert_eq!(config(ie(1, 4), ie(6, 8)), Config::LeftFirstNonOverlapping);
		assert_eq!(config(ie(1, 4), ie(2, 8)), Config::LeftFirstPartialOverlap);
		assert_eq!(config(ie(1, 4), ie(2, 3)), Config::LeftContainsRight);

		assert_eq!(
			config(ie(6, 8), ie(1, 4)),
			Config::RightFirstNonOverlapping
		);
		assert_eq!(
			config(ie(2, 8), ie(1, 4)),
			Config::RightFirstPartialOverlap
		);
		assert_eq!(config(ie(2, 3), ie(1, 4)), Config::RightContainsLeft);
	}

	#[test]
	fn overlaps_tests() {
		for range1 in all_valid_test_bounds() {
			for range2 in all_valid_test_bounds() {
				let our_answer = overlaps(range1, range2);

				let mathematical_definition_of_overlap =
					NUMBERS_DOMAIN.iter().any(|x| {
						contains_point(range1, *x) && contains_point(range2, *x)
					});

				if our_answer != mathematical_definition_of_overlap {
					dbg!(range1, range2);
					dbg!(mathematical_definition_of_overlap, our_answer);
					panic!("Discrepancy in overlaps() detected!");
				}
			}
		}
	}

	#[test]
	fn cut_range_tests() {
		for base in all_valid_test_bounds() {
			for cut in all_valid_test_bounds() {
				let cut_result @ CutResult {
					before_cut: b,
					inside_cut: i,
					after_cut: a,
				} = cut_range(base, cut);

				let mut on_left = true;

				// The definition of a cut is: A && NOT B
				for x in NUMBERS_DOMAIN {
					let base_contains = contains_point(base, *x);
					let cut_contains = contains_point(cut, *x);

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
	fn con(x: Option<InclusiveInterval<i8>>, point: &i8) -> bool {
		match x {
			Some(y) => contains_point(y, *point),
			None => false,
		}
	}
	#[test]
	fn cut_range_bounds_should_return_valid_ranges() {
		let result: CutResult<i8> = cut_range(ie(3, 8), ie(5, 8));
		if let Some(x) = result.before_cut {
			assert!(is_valid_range(x));
		}
		if let Some(x) = result.inside_cut {
			assert!(is_valid_range(x));
		}
		if let Some(x) = result.after_cut {
			assert!(is_valid_range(x));
		}

		let result = cut_range(ie(3, 8), ie(3, 5));
		if let Some(x) = result.before_cut {
			assert!(is_valid_range(x));
		}
		if let Some(x) = result.inside_cut {
			assert!(is_valid_range(x));
		}
		if let Some(x) = result.after_cut {
			assert!(is_valid_range(x));
		}
	}

	#[test]
	fn test_intersection() {
		let input = InclusiveInterval { start: 5, end: 10 };
		assert_eq!(
			input.intersect(&InclusiveInterval { start: 8, end: 13 }),
			Some(InclusiveInterval { start: 8, end: 10 })
		);
		assert_eq!(
			input.intersect(&InclusiveInterval { start: 10, end: 13 }),
			Some(InclusiveInterval { start: 10, end: 10 })
		);
		assert_eq!(
			input.intersect(&InclusiveInterval { start: 11, end: 13 }),
			None
		);
	}

	#[test]
	fn test_translate() {
		let input = InclusiveInterval { start: 5, end: 10 };
		assert_eq!(input.translate(3), InclusiveInterval { start: 8, end: 13 });
		assert_eq!(input.translate(-2), InclusiveInterval { start: 3, end: 8 });
	}

	#[test]
	fn test_size() {
		assert_eq!(InclusiveInterval { start: 5, end: 10 }.size(), 6);
		assert_eq!(InclusiveInterval { start: 6, end: 6 }.size(), 1);
	}

	// Test Helper Functions
	//======================
	fn all_non_overlapping_test_bound_entries()
	-> Vec<(InclusiveInterval<i8>, InclusiveInterval<i8>)> {
		let mut output = Vec::new();
		for test_bounds1 in all_valid_test_bounds() {
			for test_bounds2 in all_valid_test_bounds() {
				if !overlaps(test_bounds1, test_bounds2) {
					output.push((test_bounds1, test_bounds2));
				}
			}
		}

		return output;
	}

	fn all_valid_test_bounds() -> Vec<InclusiveInterval<i8>> {
		let mut output = Vec::new();
		for i in NUMBERS {
			for j in NUMBERS {
				if i <= j {
					output.push(InclusiveInterval { start: *i, end: *j });
				}
			}
		}
		return output;
	}
}
