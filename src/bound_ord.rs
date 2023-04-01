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
use std::ops::Bound;

use labels::{parent_tested, tested, trivial};
use serde::{Deserialize, Serialize};

/// An newtype of [`Bound`] to implement [`Ord`].
///
/// This type is used to circumvent [`BTreeMap`]s (and rust collections
/// in general) lack of methods for searching with custom
/// [`comparator`] functions and/or it's lack of a [`Cursor`]-like
/// API.
///
/// [`start_bound()`]: https://doc.rust-lang.org/std/ops/trait.RangeBounds.html#tymethod.start_bound
/// [`BTreeMap`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
/// [`comparator`]: https://stackoverflow.com/q/34028324
/// [`Cursor`]: https://github.com/rust-lang/rfcs/issues/1778
#[derive(Debug, Serialize, Deserialize, Clone)]
pub(crate) enum BoundOrd<T> {
	/// Mirror of [`Bound::Included`]
	/// There is no need for different Start and End variations as the
	/// Ord implementations are equivalent.
	Included(T),
	/// [`Bound::Excluded`] specific to Start bounds.
	StartExcluded(T),
	/// [`Bound::Unbounded`] specific to Start bounds.
	StartUnbounded,
	/// [`Bound::Excluded`] specific to End bounds.
	EndExcluded(T),
	/// [`Bound::Unbounded`] specific to End bounds.
	EndUnbounded,
}

impl<T> BoundOrd<T> {
	#[trivial]
	pub(crate) fn start(bound: Bound<T>) -> Self {
		match bound {
			Bound::Included(point) => BoundOrd::Included(point),
			Bound::Excluded(point) => BoundOrd::StartExcluded(point),
			Bound::Unbounded => BoundOrd::StartUnbounded,
		}
	}
	#[trivial]
	pub(crate) fn end(bound: Bound<T>) -> Self {
		match bound {
			Bound::Included(point) => BoundOrd::Included(point),
			Bound::Excluded(point) => BoundOrd::EndExcluded(point),
			Bound::Unbounded => BoundOrd::EndUnbounded,
		}
	}

	#[trivial]
	pub fn as_ref(&self) -> BoundOrd<&T> {
		//I can't believe this is neccessary but apparently so
		match self {
			BoundOrd::Included(x) => BoundOrd::Included(x),
			BoundOrd::StartExcluded(x) => BoundOrd::StartExcluded(x),
			BoundOrd::StartUnbounded => BoundOrd::StartUnbounded,
			BoundOrd::EndExcluded(x) => BoundOrd::EndExcluded(x),
			BoundOrd::EndUnbounded => BoundOrd::EndUnbounded,
		}
	}
}

impl<T> Ord for BoundOrd<T>
where
	T: Ord,
{
	#[rustfmt::skip]
    #[tested]
	fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (BoundOrd::Included(start1), BoundOrd::Included(start2)) => start1.cmp(start2),
            (BoundOrd::Included(start1), BoundOrd::StartExcluded(start2)) => cmp_with_priority(start1, start2, true),
            (BoundOrd::Included(start1), BoundOrd::EndExcluded(start2)) => cmp_with_priority(start1, start2, false),
            (BoundOrd::Included(_), BoundOrd::EndUnbounded) => Ordering::Less,
            (BoundOrd::Included(_), BoundOrd::StartUnbounded) => Ordering::Greater,

            (BoundOrd::StartExcluded(start1), BoundOrd::StartExcluded(start2)) => start1.cmp(start2),
            (BoundOrd::StartExcluded(start1), BoundOrd::Included(start2)) => cmp_with_priority(start1, start2, false),
            (BoundOrd::StartExcluded(start1), BoundOrd::EndExcluded(start2)) => cmp_with_priority(start1, start2, false),
            (BoundOrd::StartExcluded(_), BoundOrd::StartUnbounded) => Ordering::Greater,
            (BoundOrd::StartExcluded(_), BoundOrd::EndUnbounded) => Ordering::Less,

            (BoundOrd::StartUnbounded, BoundOrd::Included(_)) => Ordering::Less,
            (BoundOrd::StartUnbounded, BoundOrd::StartExcluded(_)) => Ordering::Less,
            (BoundOrd::StartUnbounded, BoundOrd::EndExcluded(_)) => Ordering::Less,
            (BoundOrd::StartUnbounded, BoundOrd::StartUnbounded) => Ordering::Equal,
            (BoundOrd::StartUnbounded, BoundOrd::EndUnbounded) => Ordering::Less,

            (BoundOrd::EndExcluded(start1), BoundOrd::EndExcluded(start2)) => start1.cmp(start2),
            (BoundOrd::EndExcluded(start1), BoundOrd::Included(start2)) => cmp_with_priority(start1, start2, true),
            (BoundOrd::EndExcluded(start1), BoundOrd::StartExcluded(start2)) => cmp_with_priority(start1, start2, true),
            (BoundOrd::EndExcluded(_), BoundOrd::StartUnbounded) => Ordering::Greater,
            (BoundOrd::EndExcluded(_), BoundOrd::EndUnbounded) => Ordering::Less,

            (BoundOrd::EndUnbounded, BoundOrd::Included(_)) => Ordering::Greater,
            (BoundOrd::EndUnbounded, BoundOrd::StartExcluded(_)) => Ordering::Greater,
            (BoundOrd::EndUnbounded, BoundOrd::EndExcluded(_)) => Ordering::Greater,
            (BoundOrd::EndUnbounded, BoundOrd::EndUnbounded) => Ordering::Equal,
            (BoundOrd::EndUnbounded, BoundOrd::StartUnbounded) => Ordering::Greater,
        }
}
}

impl<T> PartialOrd for BoundOrd<T>
where
	T: Ord,
{
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl<T> PartialEq for BoundOrd<T>
where
	T: Ord,
{
	fn eq(&self, other: &Self) -> bool {
		self.cmp(&other).is_eq()
	}
}

impl<T> Eq for BoundOrd<T> where T: Ord {}

/// If they are equal say the item with priority is larger
/// where false means left has priority and true means right.
#[parent_tested]
fn cmp_with_priority<T>(left: &T, right: &T, priority: bool) -> Ordering
where
	T: Ord,
{
	let result = left.cmp(right);

	match result {
		Ordering::Equal => match priority {
			false => Ordering::Greater,
			true => Ordering::Less,
		},
		x => x,
	}
}

impl<T> From<BoundOrd<T>> for Bound<T> {
	#[trivial]
	fn from(start_bound: BoundOrd<T>) -> Bound<T> {
		match start_bound {
			BoundOrd::Included(point) => Bound::Included(point),
			BoundOrd::StartExcluded(point) => Bound::Excluded(point),
			BoundOrd::StartUnbounded => Bound::Unbounded,
			BoundOrd::EndExcluded(point) => Bound::Excluded(point),
			BoundOrd::EndUnbounded => Bound::Unbounded,
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn mass_start_bound_partial_ord_test() {
		//Included
		assert!(BoundOrd::Included(2) == BoundOrd::Included(2));
		assert!(BoundOrd::Included(2) <= BoundOrd::Included(2));
		assert!(BoundOrd::Included(2) >= BoundOrd::Included(2));
		assert!(BoundOrd::Included(0) < BoundOrd::Included(2));
		assert!(BoundOrd::Included(2) > BoundOrd::Included(0));

		assert!(BoundOrd::Included(2) < BoundOrd::StartExcluded(2));
		assert!(BoundOrd::Included(0) < BoundOrd::StartExcluded(2));
		assert!(BoundOrd::Included(2) > BoundOrd::StartExcluded(0));

		assert!(BoundOrd::Included(2) > BoundOrd::StartUnbounded);

		assert!(BoundOrd::Included(2) > BoundOrd::EndExcluded(2));
		assert!(BoundOrd::Included(0) < BoundOrd::EndExcluded(2));
		assert!(BoundOrd::Included(2) > BoundOrd::EndExcluded(0));

		assert!(BoundOrd::Included(2) < BoundOrd::EndUnbounded);

		//StartExcluded
		assert!(BoundOrd::StartExcluded(2) == BoundOrd::StartExcluded(2));
		assert!(BoundOrd::StartExcluded(2) <= BoundOrd::StartExcluded(2));
		assert!(BoundOrd::StartExcluded(2) >= BoundOrd::StartExcluded(2));
		assert!(BoundOrd::StartExcluded(0) < BoundOrd::StartExcluded(2));
		assert!(BoundOrd::StartExcluded(2) > BoundOrd::StartExcluded(0));

		assert!(BoundOrd::StartExcluded(2) > BoundOrd::StartUnbounded);

		assert!(BoundOrd::StartExcluded(2) > BoundOrd::EndExcluded(2));
		assert!(BoundOrd::StartExcluded(2) > BoundOrd::EndExcluded(0));
		assert!(BoundOrd::StartExcluded(0) < BoundOrd::EndExcluded(2));

		assert!(BoundOrd::StartExcluded(2) < BoundOrd::EndUnbounded);

		//StartUnbounded
		assert!(BoundOrd::StartUnbounded::<u8> == BoundOrd::StartUnbounded);
		assert!(BoundOrd::StartUnbounded::<u8> <= BoundOrd::StartUnbounded);
		assert!(BoundOrd::StartUnbounded::<u8> >= BoundOrd::StartUnbounded);

		assert!(BoundOrd::StartUnbounded < BoundOrd::EndExcluded(2));

		assert!(BoundOrd::StartUnbounded::<u8> < BoundOrd::EndUnbounded);

		//EndExcluded
		assert!(BoundOrd::EndExcluded(2) == BoundOrd::EndExcluded(2));
		assert!(BoundOrd::EndExcluded(2) <= BoundOrd::EndExcluded(2));
		assert!(BoundOrd::EndExcluded(2) >= BoundOrd::EndExcluded(2));
		assert!(BoundOrd::EndExcluded(0) < BoundOrd::EndExcluded(2));
		assert!(BoundOrd::EndExcluded(2) > BoundOrd::EndExcluded(0));

		//EndUnbounded
		assert!(BoundOrd::EndUnbounded::<u8> == BoundOrd::EndUnbounded);
		assert!(BoundOrd::EndUnbounded::<u8> <= BoundOrd::EndUnbounded);
		assert!(BoundOrd::EndUnbounded::<u8> >= BoundOrd::EndUnbounded);
	}
}
