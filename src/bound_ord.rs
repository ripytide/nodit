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

use serde::{Deserialize, Serialize};

use crate::stepable::Stepable;

/// An newtype of [`Bound`] to implement [`Ord`] on types that
/// implement [`Step`].
///
/// [`Step`]: std::iter::Step
#[derive(Debug, Serialize, Deserialize, Clone)]
pub(crate) enum DiscreteBoundOrd<T> {
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

impl<T> DiscreteBoundOrd<T> {
	pub(crate) fn start(bound: Bound<T>) -> Self {
		match bound {
			Bound::Included(point) => DiscreteBoundOrd::Included(point),
			Bound::Excluded(point) => DiscreteBoundOrd::StartExcluded(point),
			Bound::Unbounded => DiscreteBoundOrd::StartUnbounded,
		}
	}
	pub(crate) fn end(bound: Bound<T>) -> Self {
		match bound {
			Bound::Included(point) => DiscreteBoundOrd::Included(point),
			Bound::Excluded(point) => DiscreteBoundOrd::EndExcluded(point),
			Bound::Unbounded => DiscreteBoundOrd::EndUnbounded,
		}
	}
}

impl<T> Ord for DiscreteBoundOrd<T>
where
	T: Ord + Stepable,
{
	#[rustfmt::skip]
	fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (DiscreteBoundOrd::Included(start1), DiscreteBoundOrd::Included(start2)) => start1.cmp(start2),
            (DiscreteBoundOrd::Included(start1), DiscreteBoundOrd::StartExcluded(start2)) => start1.cmp(&start2.up().unwrap()),
            (DiscreteBoundOrd::Included(start1), DiscreteBoundOrd::EndExcluded(start2)) => start1.cmp(&start2.down().unwrap()),
            (DiscreteBoundOrd::Included(_), DiscreteBoundOrd::EndUnbounded) => Ordering::Less,
            (DiscreteBoundOrd::Included(_), DiscreteBoundOrd::StartUnbounded) => Ordering::Greater,

            (DiscreteBoundOrd::StartExcluded(start1), DiscreteBoundOrd::StartExcluded(start2)) => start1.cmp(start2),
            (DiscreteBoundOrd::StartExcluded(start1), DiscreteBoundOrd::Included(start2)) => start1.up().unwrap().cmp(start2),
            (DiscreteBoundOrd::StartExcluded(start1), DiscreteBoundOrd::EndExcluded(start2)) => start1.up().unwrap().cmp(&start2.down().unwrap()),
            (DiscreteBoundOrd::StartExcluded(_), DiscreteBoundOrd::StartUnbounded) => Ordering::Greater,
            (DiscreteBoundOrd::StartExcluded(_), DiscreteBoundOrd::EndUnbounded) => Ordering::Less,

            (DiscreteBoundOrd::StartUnbounded, DiscreteBoundOrd::Included(_)) => Ordering::Less,
            (DiscreteBoundOrd::StartUnbounded, DiscreteBoundOrd::StartExcluded(_)) => Ordering::Less,
            (DiscreteBoundOrd::StartUnbounded, DiscreteBoundOrd::EndExcluded(_)) => Ordering::Less,
            (DiscreteBoundOrd::StartUnbounded, DiscreteBoundOrd::StartUnbounded) => Ordering::Equal,
            (DiscreteBoundOrd::StartUnbounded, DiscreteBoundOrd::EndUnbounded) => Ordering::Less,

            (DiscreteBoundOrd::EndExcluded(start1), DiscreteBoundOrd::EndExcluded(start2)) => start1.cmp(start2),
            (DiscreteBoundOrd::EndExcluded(start1), DiscreteBoundOrd::Included(start2)) => start1.down().unwrap().cmp(&start2),
            (DiscreteBoundOrd::EndExcluded(start1), DiscreteBoundOrd::StartExcluded(start2)) => start1.down().unwrap().cmp(&start2.up().unwrap()),
            (DiscreteBoundOrd::EndExcluded(_), DiscreteBoundOrd::StartUnbounded) => Ordering::Greater,
            (DiscreteBoundOrd::EndExcluded(_), DiscreteBoundOrd::EndUnbounded) => Ordering::Less,

            (DiscreteBoundOrd::EndUnbounded, DiscreteBoundOrd::Included(_)) => Ordering::Greater,
            (DiscreteBoundOrd::EndUnbounded, DiscreteBoundOrd::StartExcluded(_)) => Ordering::Greater,
            (DiscreteBoundOrd::EndUnbounded, DiscreteBoundOrd::EndExcluded(_)) => Ordering::Greater,
            (DiscreteBoundOrd::EndUnbounded, DiscreteBoundOrd::EndUnbounded) => Ordering::Equal,
            (DiscreteBoundOrd::EndUnbounded, DiscreteBoundOrd::StartUnbounded) => Ordering::Greater,
        }
}
}

impl<T> PartialOrd for DiscreteBoundOrd<T>
where
	T: Ord + Stepable,
{
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl<T> PartialEq for DiscreteBoundOrd<T>
where
	T: Ord + Stepable,
{
	fn eq(&self, other: &Self) -> bool {
		self.cmp(other).is_eq()
	}
}

impl<T> Eq for DiscreteBoundOrd<T> where T: Ord + Stepable {}

impl<T> From<DiscreteBoundOrd<T>> for Bound<T> {
	fn from(start_bound: DiscreteBoundOrd<T>) -> Bound<T> {
		match start_bound {
			DiscreteBoundOrd::Included(point) => Bound::Included(point),
			DiscreteBoundOrd::StartExcluded(point) => Bound::Excluded(point),
			DiscreteBoundOrd::StartUnbounded => Bound::Unbounded,
			DiscreteBoundOrd::EndExcluded(point) => Bound::Excluded(point),
			DiscreteBoundOrd::EndUnbounded => Bound::Unbounded,
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn mass_start_bound_partial_ord_test() {
		//Included
		assert!(DiscreteBoundOrd::Included(2) == DiscreteBoundOrd::Included(2));
		assert!(DiscreteBoundOrd::Included(2) <= DiscreteBoundOrd::Included(2));
		assert!(DiscreteBoundOrd::Included(2) >= DiscreteBoundOrd::Included(2));
		assert!(DiscreteBoundOrd::Included(0) < DiscreteBoundOrd::Included(2));
		assert!(DiscreteBoundOrd::Included(2) > DiscreteBoundOrd::Included(0));

		assert!(
			DiscreteBoundOrd::Included(2) < DiscreteBoundOrd::StartExcluded(2)
		);
		assert!(
			DiscreteBoundOrd::Included(0) < DiscreteBoundOrd::StartExcluded(2)
		);
		assert!(
			DiscreteBoundOrd::Included(2) > DiscreteBoundOrd::StartExcluded(0)
		);

		assert!(
			DiscreteBoundOrd::Included(2) > DiscreteBoundOrd::StartUnbounded
		);

		assert!(
			DiscreteBoundOrd::Included(2) > DiscreteBoundOrd::EndExcluded(2)
		);
		assert!(
			DiscreteBoundOrd::Included(0) < DiscreteBoundOrd::EndExcluded(2)
		);
		assert!(
			DiscreteBoundOrd::Included(2) > DiscreteBoundOrd::EndExcluded(0)
		);

		assert!(DiscreteBoundOrd::Included(2) < DiscreteBoundOrd::EndUnbounded);

		//StartExcluded
		assert!(
			DiscreteBoundOrd::StartExcluded(2)
				== DiscreteBoundOrd::StartExcluded(2)
		);
		assert!(
			DiscreteBoundOrd::StartExcluded(2)
				<= DiscreteBoundOrd::StartExcluded(2)
		);
		assert!(
			DiscreteBoundOrd::StartExcluded(2)
				>= DiscreteBoundOrd::StartExcluded(2)
		);
		assert!(
			DiscreteBoundOrd::StartExcluded(0)
				< DiscreteBoundOrd::StartExcluded(2)
		);
		assert!(
			DiscreteBoundOrd::StartExcluded(2)
				> DiscreteBoundOrd::StartExcluded(0)
		);

		assert!(
			DiscreteBoundOrd::StartExcluded(2)
				> DiscreteBoundOrd::StartUnbounded
		);

		assert!(
			DiscreteBoundOrd::StartExcluded(2)
				> DiscreteBoundOrd::EndExcluded(2)
		);
		assert!(
			DiscreteBoundOrd::StartExcluded(2)
				> DiscreteBoundOrd::EndExcluded(0)
		);
		assert!(
			DiscreteBoundOrd::StartExcluded(0)
				< DiscreteBoundOrd::EndExcluded(2)
		);

		assert!(
			DiscreteBoundOrd::StartExcluded(2) < DiscreteBoundOrd::EndUnbounded
		);

		//StartUnbounded
		assert!(
			DiscreteBoundOrd::StartUnbounded::<i8>
				== DiscreteBoundOrd::StartUnbounded
		);
		assert!(
			DiscreteBoundOrd::StartUnbounded::<i8>
				<= DiscreteBoundOrd::StartUnbounded
		);
		assert!(
			DiscreteBoundOrd::StartUnbounded::<i8>
				>= DiscreteBoundOrd::StartUnbounded
		);

		assert!(
			DiscreteBoundOrd::StartUnbounded < DiscreteBoundOrd::EndExcluded(2)
		);

		assert!(
			DiscreteBoundOrd::StartUnbounded::<i8>
				< DiscreteBoundOrd::EndUnbounded
		);

		//EndExcluded
		assert!(
			DiscreteBoundOrd::EndExcluded(2)
				== DiscreteBoundOrd::EndExcluded(2)
		);
		assert!(
			DiscreteBoundOrd::EndExcluded(2)
				<= DiscreteBoundOrd::EndExcluded(2)
		);
		assert!(
			DiscreteBoundOrd::EndExcluded(2)
				>= DiscreteBoundOrd::EndExcluded(2)
		);
		assert!(
			DiscreteBoundOrd::EndExcluded(0) < DiscreteBoundOrd::EndExcluded(2)
		);
		assert!(
			DiscreteBoundOrd::EndExcluded(2) > DiscreteBoundOrd::EndExcluded(0)
		);

		//EndUnbounded
		assert!(
			DiscreteBoundOrd::EndUnbounded::<i8>
				== DiscreteBoundOrd::EndUnbounded
		);
		assert!(
			DiscreteBoundOrd::EndUnbounded::<i8>
				<= DiscreteBoundOrd::EndUnbounded
		);
		assert!(
			DiscreteBoundOrd::EndUnbounded::<i8>
				>= DiscreteBoundOrd::EndUnbounded
		);
	}
}
