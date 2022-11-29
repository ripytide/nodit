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

use std::ops::RangeBounds;

use crate::range_bounds_map::RangeBoundsMap;

/// An ordered set of [`RangeBounds`] based on [`BTreeSet`]
///
/// # Examples
/// ```
/// use range_bounds_map::RangeBoundsSet;
///
/// // Make a set with some ranges
/// let visits = RangeBoundsSet::try_from([4..8, 8..18, 20..100]).unwrap();
///
/// // Check if a point is contained in the set
/// if visits.contains_point(&0) {
///     println!("No visit at the beginning ;(");
/// }
///
/// // Iterate over the ranges overlapping another range
/// for visit in visits.overlapping(&(2..=8)) {
///     println!("{visit:?}");
/// }
/// ```
/// Example using a custom [`RangeBounds`] type:
/// ```
/// use std::ops::Bound;
/// use std::ops::RangeBounds;
/// use ordered_float::NotNan;
///
/// use range_bounds_map::RangeBoundsSet;
///
/// // An Exlusive-Exlusive range of [`f32`]s not provided by any
/// // std::ops ranges
/// // We use [`ordered_float::NotNan`]s as the inner type must be Ord
/// // similar to a normal [`BTreeSet`]
/// struct ExEx {
///     start: NotNan<f32>,
///     end: NotNan<f32>,
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
///     fn start_bound(&self) -> Bound<&NotNan<f32>> {
///         Bound::Excluded(&self.start)
///     }
///     fn end_bound(&self) -> Bound<&NotNan<f32>> {
///         Bound::Excluded(&self.end)
///     }
/// }
///
/// // Now we can make a [`RangeBoundsSet`] of [`ExEx`]s
/// let mut set = RangeBoundsSet::new();
///
/// set.insert(ExEx::new(0.0, 5.0)).unwrap();
/// set.insert(ExEx::new(5.0, 7.5)).unwrap();
///
/// assert_eq!(set.contains_point(&(NotNan::new(5.0).unwrap())), false);
/// assert_eq!(set.contains_point(&(NotNan::new(7.0).unwrap())), true);
/// assert_eq!(set.contains_point(&(NotNan::new(7.5).unwrap())), false);
/// ```
///
/// [`RangeBounds`]: https://doc.rust-lang.org/std/collections/struct.BTreeSet.html
/// [`BTreeSet`]: https://doc.rust-lang.org/std/collections/struct.BTreeSet.html
pub struct RangeBoundsSet<I, K> {
	map: RangeBoundsMap<I, K, ()>,
}

impl<I, K> RangeBoundsSet<I, K>
where
	K: RangeBounds<I>,
	I: Ord + Clone,
{
	/// Makes a new, empty `RangeBoundsSet`.
	///
	/// # Examples
	/// ```
	/// use std::ops::Range;
	/// use range_bounds_map::RangeBoundsSet;
	///
	/// let range_bounds_set: RangeBoundsSet<u8, Range<u8>> = RangeBoundsSet::new();
	/// ```
	pub fn new() -> Self {
		RangeBoundsSet {
			map: RangeBoundsMap::new(),
		}
	}

	/// Returns the number of `RangeBounds` in the set.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsSet;
	///
	/// let mut range_bounds_set = RangeBoundsSet::new();
	///
	/// assert_eq!(range_bounds_set.len(), 0);
	/// range_bounds_set.insert(0..1).unwrap();
	/// assert_eq!(range_bounds_set.len(), 1);
	/// ```
	pub fn len(&self) -> usize {
		self.map.len()
	}

	/// Adds a new `RangeBounds` to the set.
	///
	/// If the new `RangeBounds` overlaps one or more `RangeBounds`
	/// already in the set then `Err(())` is returned and the set is
	/// not updated.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsSet;
	///
	/// let mut range_bounds_set = RangeBoundsSet::new();
	///
	/// assert_eq!(range_bounds_set.insert(5..10), Ok(()));
	/// assert_eq!(range_bounds_set.insert(5..10), Err(()));
	/// assert_eq!(range_bounds_set.len(), 1);
	/// ```
	pub fn insert(&mut self, range_bounds: K) -> Result<(), ()> {
		self.map.insert(range_bounds, ())
	}

	/// Returns `true` if the given `RangeBounds` overlaps any of the
	/// `RangeBounds` in the set.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsSet;
	///
	/// let mut range_bounds_set = RangeBoundsSet::new();
	///
	/// range_bounds_set.insert(5..10);
	///
	/// assert_eq!(range_bounds_set.overlaps(&(1..=3)), false);
	/// assert_eq!(range_bounds_set.overlaps(&(4..5)), false);
	///
	/// assert_eq!(range_bounds_set.overlaps(&(4..=5)), true);
	/// assert_eq!(range_bounds_set.overlaps(&(4..6)), true);
	/// ```
	pub fn overlaps<Q>(&self, search_range_bounds: &Q) -> bool
	where
		Q: RangeBounds<I>,
	{
		self.map.overlaps(search_range_bounds)
	}

	/// Returns an iterator over every `RangeBounds` in the set which
	/// overlaps the given `search_range_bounds` in ascending order.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsSet;
	///
	/// let range_bounds_set = RangeBoundsSet::try_from([1..4, 4..8, 8..100]).unwrap();
	///
	/// let mut overlapping = range_bounds_set.overlapping(&(2..8));
	///
	/// assert_eq!(overlapping.next(), Some(&(1..4)));
	/// assert_eq!(overlapping.next(), Some(&(4..8)));
	/// assert_eq!(overlapping.next(), None);
	/// ```
	pub fn overlapping<Q>(
		&self,
		search_range_bounds: &Q,
	) -> impl Iterator<Item = &K>
	where
		Q: RangeBounds<I>,
	{
		self.map
			.overlapping(search_range_bounds)
			.map(|(key, _)| key)
	}

	/// Returns a reference to the `RangeBounds` in the set that
	/// overlaps the given point, if any.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsSet;
	///
	/// let range_bounds_set = RangeBoundsSet::try_from([1..4, 4..8, 8..100]).unwrap();
	///
	/// assert_eq!(range_bounds_set.get_at_point(&3), Some(&(1..4)));
	/// assert_eq!(range_bounds_set.get_at_point(&4), Some(&(4..8)));
	/// assert_eq!(range_bounds_set.get_at_point(&101), None);
	/// ```
	pub fn get_at_point(&self, point: &I) -> Option<&K> {
		self.map.get_key_value_at_point(point).map(|(key, _)| key)
	}

	/// Returns `true` if the set contains a `RangeBounds` that
	/// overlaps a given point, and `false` if not.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsSet;
	///
	/// let range_bounds_set = RangeBoundsSet::try_from([1..4, 4..8, 8..100]).unwrap();
	///
	/// assert_eq!(range_bounds_set.contains_point(&3), true);
	/// assert_eq!(range_bounds_set.contains_point(&4), true);
	/// assert_eq!(range_bounds_set.contains_point(&101), false);
	/// ```
	pub fn contains_point(&self, point: &I) -> bool {
		self.map.contains_point(point)
	}

	/// Returns an iterator over every `RangeBouns` in the set in
	/// ascending order.
	///
	/// # Examples
	/// ```
	/// use range_bounds_map::RangeBoundsSet;
	///
	/// let range_bounds_set = RangeBoundsSet::try_from([1..4, 4..8, 8..100]).unwrap();
	///
	/// let mut iter = range_bounds_set.overlapping(&(2..8));
	///
	/// assert_eq!(iter.next(), Some(&(1..4)));
	/// assert_eq!(iter.next(), Some(&(4..8)));
	/// assert_eq!(iter.next(), None);
	/// ```
	pub fn iter(&self) -> impl Iterator<Item = &K> {
		self.map.iter().map(|(key, _)| key)
	}
}

impl<const N: usize, I, K> TryFrom<[K; N]> for RangeBoundsSet<I, K>
where
	K: RangeBounds<I>,
	I: Ord + Clone,
{
	type Error = ();
	fn try_from(range_bounds: [K; N]) -> Result<Self, Self::Error> {
		let mut range_bounds_set = RangeBoundsSet::new();
		for range_bounds in range_bounds {
			range_bounds_set.insert(range_bounds)?;
		}

		return Ok(range_bounds_set);
	}
}
