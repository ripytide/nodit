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
use std::ops::Bound;

use labels::{parent_tested, tested, trivial};
use serde::{Deserialize, Serialize};

/// An Ord newtype of [`Bound`] specific to [`start_bound()`].
///
/// This type is used to circumvent [`BTreeMap`]s (and rust collections
/// in general) lack of methods for searching with custom
/// [`comparator`] functions and/or it's lack of a [`Cursor`]-like
/// API
///
/// [`start_bound()`]: https://doc.rust-lang.org/std/ops/trait.RangeBounds.html#tymethod.start_bound
/// [`BTreeMap`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
/// [`comparator`]: https://stackoverflow.com/q/34028324
/// [`Cursor`]: https://github.com/rust-lang/rfcs/issues/1778
#[derive(Debug, Serialize, Deserialize, PartialEq, Clone)]
pub(crate) enum StartBound<T> {
	/// Mirror of [`Bound::Included`]
	Included(T),
	/// Mirror of [`Bound::Excluded`]
	Excluded(T),
	/// Mirror of [`Bound::Unbounded`]
	Unbounded,
	/// Workaround type used to represent [`Bound::Excluded`] in [`end_bound()`] in meta-bound
	/// [`BTreeMap::range`] searches in [`crate::RangeBoundsMap::overlapping()`]
	///
	/// [`end_bound()`]: https://doc.rust-lang.org/std/ops/trait.RangeBounds.html#tymethod.end_bound
	/// [`BTreeMap::range`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html#method.range
	ReverseExcluded(T),
	/// Workaround type used to represent [`Bound::Unbounded`] in [`end_bound()`] in meta-bound
	/// [`BTreeMap::range`] searches in [`crate::RangeBoundsMap::overlapping()`]
	///
	/// [`end_bound()`]: https://doc.rust-lang.org/std/ops/trait.RangeBounds.html#tymethod.end_bound
	/// [`BTreeMap::range`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html#method.range
	ReverseUnbounded,
}

impl<T> StartBound<T> {
	/// Converts the [`StartBound`] to the appropriate type for use as
	/// an [`end_bound()`] in a range search
	///
	/// [`end_bound()`]: https://doc.rust-lang.org/std/ops/trait.RangeBounds.html#tymethod.end_bound
	#[trivial]
	pub(crate) fn into_end_bound(self) -> StartBound<T> {
		match self {
			//flipping is unnecessary
			StartBound::Included(point) => StartBound::Included(point),
			//flip to Reverses
			StartBound::Excluded(point) => StartBound::ReverseExcluded(point),
			StartBound::Unbounded => StartBound::ReverseUnbounded,
			_ => panic!("unsuitable operation"),
		}
	}
}

impl<T> Eq for StartBound<T> where T: PartialEq {}

/// The [`PartialOrd`] implementaion with the goal of allowing the use
/// of [`BTreeMap::range`] on [`StartBound`]s
///
/// [`BTreeMap::range`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html#method.range
#[rustfmt::skip]
impl<T> PartialOrd for StartBound<T>
where
	T: PartialOrd,
{
    #[tested]
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		match (self, other) {
			(StartBound::Included(start1), StartBound::Included(start2)) => start1.partial_cmp(start2),
			(StartBound::Included(start1), StartBound::Excluded(start2)) => partial_cmp_with_priority(start1, start2, true),
			(StartBound::Included(start1), StartBound::ReverseExcluded(start2)) => partial_cmp_with_priority(start1, start2, false),
			(StartBound::Included(_), StartBound::ReverseUnbounded) => Some(Ordering::Less),
			(StartBound::Included(_), StartBound::Unbounded) => Some(Ordering::Greater),

			(StartBound::Excluded(start1), StartBound::Excluded(start2)) => start1.partial_cmp(start2),
			(StartBound::Excluded(start1), StartBound::Included(start2)) => partial_cmp_with_priority(start1, start2, false),
			(StartBound::Excluded(start1), StartBound::ReverseExcluded(start2)) => partial_cmp_with_priority(start1, start2, false),
			(StartBound::Excluded(_), StartBound::Unbounded) => Some(Ordering::Greater),
			(StartBound::Excluded(_), StartBound::ReverseUnbounded) => Some(Ordering::Less),

            (StartBound::Unbounded, StartBound::Included(_)) => Some(Ordering::Less),
            (StartBound::Unbounded, StartBound::Excluded(_)) => Some(Ordering::Less),
            (StartBound::Unbounded, StartBound::ReverseExcluded(_)) => Some(Ordering::Less),
			(StartBound::Unbounded, StartBound::Unbounded) => Some(Ordering::Equal),
			(StartBound::Unbounded, StartBound::ReverseUnbounded) => Some(Ordering::Less),

			(StartBound::ReverseExcluded(start1), StartBound::ReverseExcluded(start2)) => start1.partial_cmp(start2),
			(StartBound::ReverseExcluded(start1), StartBound::Included(start2)) => partial_cmp_with_priority(start1, start2, true),
			(StartBound::ReverseExcluded(start1), StartBound::Excluded(start2)) => partial_cmp_with_priority(start1, start2, true),
			(StartBound::ReverseExcluded(_), StartBound::Unbounded) => Some(Ordering::Greater),
			(StartBound::ReverseExcluded(_), StartBound::ReverseUnbounded) => Some(Ordering::Less),

            (StartBound::ReverseUnbounded, StartBound::Included(_)) => Some(Ordering::Greater),
            (StartBound::ReverseUnbounded, StartBound::Excluded(_)) => Some(Ordering::Greater),
            (StartBound::ReverseUnbounded, StartBound::ReverseExcluded(_)) => Some(Ordering::Greater),
			(StartBound::ReverseUnbounded, StartBound::ReverseUnbounded) => Some(Ordering::Equal),
			(StartBound::ReverseUnbounded, StartBound::Unbounded) => Some(Ordering::Greater),
		}
	}
}

//if they are equal say the item with priority is larger
//where false means left has priority and true means right
#[parent_tested]
fn partial_cmp_with_priority<T>(
	left: &T,
	right: &T,
	priority: bool,
) -> Option<Ordering>
where
	T: PartialOrd,
{
	let result = left.partial_cmp(right)?;

	Some(match result {
		Ordering::Equal => match priority {
			false => Ordering::Greater,
			true => Ordering::Less,
		},
		x => x,
	})
}

impl<T> Ord for StartBound<T>
where
	T: PartialOrd,
{
	#[trivial]
	fn cmp(&self, other: &Self) -> Ordering {
		self.partial_cmp(other).unwrap()
	}
}

impl<T> From<Bound<T>> for StartBound<T> {
	#[trivial]
	fn from(bound: Bound<T>) -> Self {
		match bound {
			Bound::Included(point) => StartBound::Included(point),
			Bound::Excluded(point) => StartBound::Excluded(point),
			Bound::Unbounded => StartBound::Unbounded,
		}
	}
}
impl<T> From<StartBound<T>> for Bound<T> {
	#[trivial]
	fn from(start_bound: StartBound<T>) -> Bound<T> {
		match start_bound {
			StartBound::Included(point) => Bound::Included(point),
			StartBound::Excluded(point) => Bound::Excluded(point),
			StartBound::Unbounded => Bound::Unbounded,
			_ => panic!("unsuitable operation"),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[rustfmt::skip]
	#[test]
	fn mass_start_bound_partial_ord_test() {
        //Included
		assert!(StartBound::Included(2) == StartBound::Included(2));
		assert!(StartBound::Included(2) <= StartBound::Included(2));
		assert!(StartBound::Included(2) >= StartBound::Included(2));
		assert!(StartBound::Included(0) < StartBound::Included(2));
		assert!(StartBound::Included(2) > StartBound::Included(0));

		assert!(StartBound::Included(2) < StartBound::Excluded(2));
		assert!(StartBound::Included(0) < StartBound::Excluded(2));
		assert!(StartBound::Included(2) > StartBound::Excluded(0));

		assert!(StartBound::Included(2) > StartBound::Unbounded);

		assert!(StartBound::Included(2) > StartBound::ReverseExcluded(2));
		assert!(StartBound::Included(0) < StartBound::ReverseExcluded(2));
		assert!(StartBound::Included(2) > StartBound::ReverseExcluded(0));

		assert!(StartBound::Included(2) < StartBound::ReverseUnbounded);

        //Exluded
		assert!(StartBound::Excluded(2) == StartBound::Excluded(2));
		assert!(StartBound::Excluded(2) <= StartBound::Excluded(2));
		assert!(StartBound::Excluded(2) >= StartBound::Excluded(2));
		assert!(StartBound::Excluded(0) < StartBound::Excluded(2));
		assert!(StartBound::Excluded(2) > StartBound::Excluded(0));

		assert!(StartBound::Excluded(2) > StartBound::Unbounded);

		assert!(StartBound::Excluded(2) > StartBound::ReverseExcluded(2));
		assert!(StartBound::Excluded(2) > StartBound::ReverseExcluded(0));
		assert!(StartBound::Excluded(0) < StartBound::ReverseExcluded(2));

		assert!(StartBound::Excluded(2) < StartBound::ReverseUnbounded);

        //Unbounded
		assert!(StartBound::Unbounded::<u8> == StartBound::Unbounded);
		assert!(StartBound::Unbounded::<u8> <= StartBound::Unbounded);
		assert!(StartBound::Unbounded::<u8> >= StartBound::Unbounded);

		assert!(StartBound::Unbounded < StartBound::ReverseExcluded(2));

		assert!(StartBound::Unbounded::<u8> < StartBound::ReverseUnbounded);

        //ReverseExcluded
		assert!(StartBound::ReverseExcluded(2) == StartBound::ReverseExcluded(2));
		assert!(StartBound::ReverseExcluded(2) <= StartBound::ReverseExcluded(2));
		assert!(StartBound::ReverseExcluded(2) >= StartBound::ReverseExcluded(2));
		assert!(StartBound::ReverseExcluded(0) < StartBound::ReverseExcluded(2));
		assert!(StartBound::ReverseExcluded(2) > StartBound::ReverseExcluded(0));

        //ReverseUnbounded
		assert!(StartBound::ReverseUnbounded::<u8> == StartBound::ReverseUnbounded);
		assert!(StartBound::ReverseUnbounded::<u8> <= StartBound::ReverseUnbounded);
		assert!(StartBound::ReverseUnbounded::<u8> >= StartBound::ReverseUnbounded);
	}
}
