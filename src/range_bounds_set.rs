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
/// let mut visits = RangeBoundsSet::new();
///
/// // Add some ranges
/// visits.insert(4..8);
/// visits.insert(8..18);
/// visits.insert(20..100);
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
    /// Makes a new, empty `RangeBoundsSet`
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
    /// range_bounds_set.insert(5..10);
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
    /// assert_eq!(range_bounds_set.overlaps(4..6), false);
    ///
    ///
    /// assert_eq!(range_bounds_set.overlaps(4..6), true);
    /// ```
	pub fn overlaps<Q>(&self, search_range_bounds: &Q) -> bool
	where
		Q: RangeBounds<I>,
	{
		self.map.overlaps(search_range_bounds)
	}

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

	pub fn get_at_point(&self, point: &I) -> Option<&K> {
		self.map.get_key_value_at_point(point).map(|(key, _)| key)
	}

	pub fn contains_point(&self, point: &I) -> bool {
		self.map.contains_point(point)
	}

	pub fn iter(&self) -> impl Iterator<Item = &K> {
		self.map.iter().map(|(key, _)| key)
	}
}
