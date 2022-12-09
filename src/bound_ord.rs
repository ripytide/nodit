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
#[derive(Debug, Serialize, Deserialize, PartialEq, Clone)]
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
	pub(crate) fn start(bound: Bound<T>) -> Self {
		match bound {
			Bound::Included(point) => BoundOrd::Included(point),
			Bound::Excluded(point) => BoundOrd::StartExcluded(point),
			Bound::Unbounded => BoundOrd::StartUnbounded,
		}
	}
	pub(crate) fn end(bound: Bound<T>) -> Self {
		match bound {
			Bound::Included(point) => BoundOrd::Included(point),
			Bound::Excluded(point) => BoundOrd::EndExcluded(point),
			Bound::Unbounded => BoundOrd::EndUnbounded,
		}
	}
}

impl<T> Eq for BoundOrd<T> where T: PartialEq {}

#[rustfmt::skip]
impl<T> PartialOrd for BoundOrd<T>
where
	T: PartialOrd,
{
    #[tested]
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		match (self, other) {
			(BoundOrd::Included(start1), BoundOrd::Included(start2)) => start1.partial_cmp(start2),
			(BoundOrd::Included(start1), BoundOrd::StartExcluded(start2)) => partial_cmp_with_priority(start1, start2, true),
			(BoundOrd::Included(start1), BoundOrd::EndExcluded(start2)) => partial_cmp_with_priority(start1, start2, false),
			(BoundOrd::Included(_), BoundOrd::EndUnbounded) => Some(Ordering::Less),
			(BoundOrd::Included(_), BoundOrd::StartUnbounded) => Some(Ordering::Greater),

			(BoundOrd::StartExcluded(start1), BoundOrd::StartExcluded(start2)) => start1.partial_cmp(start2),
			(BoundOrd::StartExcluded(start1), BoundOrd::Included(start2)) => partial_cmp_with_priority(start1, start2, false),
			(BoundOrd::StartExcluded(start1), BoundOrd::EndExcluded(start2)) => partial_cmp_with_priority(start1, start2, false),
			(BoundOrd::StartExcluded(_), BoundOrd::StartUnbounded) => Some(Ordering::Greater),
			(BoundOrd::StartExcluded(_), BoundOrd::EndUnbounded) => Some(Ordering::Less),

            (BoundOrd::StartUnbounded, BoundOrd::Included(_)) => Some(Ordering::Less),
            (BoundOrd::StartUnbounded, BoundOrd::StartExcluded(_)) => Some(Ordering::Less),
            (BoundOrd::StartUnbounded, BoundOrd::EndExcluded(_)) => Some(Ordering::Less),
			(BoundOrd::StartUnbounded, BoundOrd::StartUnbounded) => Some(Ordering::Equal),
			(BoundOrd::StartUnbounded, BoundOrd::EndUnbounded) => Some(Ordering::Less),

			(BoundOrd::EndExcluded(start1), BoundOrd::EndExcluded(start2)) => start1.partial_cmp(start2),
			(BoundOrd::EndExcluded(start1), BoundOrd::Included(start2)) => partial_cmp_with_priority(start1, start2, true),
			(BoundOrd::EndExcluded(start1), BoundOrd::StartExcluded(start2)) => partial_cmp_with_priority(start1, start2, true),
			(BoundOrd::EndExcluded(_), BoundOrd::StartUnbounded) => Some(Ordering::Greater),
			(BoundOrd::EndExcluded(_), BoundOrd::EndUnbounded) => Some(Ordering::Less),

            (BoundOrd::EndUnbounded, BoundOrd::Included(_)) => Some(Ordering::Greater),
            (BoundOrd::EndUnbounded, BoundOrd::StartExcluded(_)) => Some(Ordering::Greater),
            (BoundOrd::EndUnbounded, BoundOrd::EndExcluded(_)) => Some(Ordering::Greater),
			(BoundOrd::EndUnbounded, BoundOrd::EndUnbounded) => Some(Ordering::Equal),
			(BoundOrd::EndUnbounded, BoundOrd::StartUnbounded) => Some(Ordering::Greater),
		}
	}
}

/// If they are equal say the item with priority is larger
/// where false means left has priority and true means right.
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

impl<T> Ord for BoundOrd<T>
where
	T: PartialOrd,
{
	#[trivial]
	fn cmp(&self, other: &Self) -> Ordering {
		self.partial_cmp(other).unwrap()
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

	#[rustfmt::skip]
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
