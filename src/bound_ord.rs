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

use serde::{Deserialize, Serialize};

use crate::discrete_bounds::DiscreteBound;
use crate::stepable::Stepable;

/// An newtype of [`Bound`] to implement [`Ord`] on types that
/// implement [`Step`].
///
/// [`Step`]: std::iter::Step
#[derive(Debug, Serialize, Deserialize, Clone)]
pub(crate) enum DiscreteBoundOrd<T> {
	Included(T),
	StartUnbounded,
	EndUnbounded,
}

impl<I> DiscreteBoundOrd<I> {
	pub(crate) fn start(discrete_bound: DiscreteBound<I>) -> Self {
		match discrete_bound {
			DiscreteBound::Included(point) => DiscreteBoundOrd::Included(point),
			DiscreteBound::Unbounded => DiscreteBoundOrd::StartUnbounded,
		}
	}
	pub(crate) fn end(discrete_bound: DiscreteBound<I>) -> Self {
		match discrete_bound {
			DiscreteBound::Included(point) => DiscreteBoundOrd::Included(point),
			DiscreteBound::Unbounded => DiscreteBoundOrd::EndUnbounded,
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
            (DiscreteBoundOrd::Included(_), DiscreteBoundOrd::EndUnbounded) => Ordering::Less,
            (DiscreteBoundOrd::Included(_), DiscreteBoundOrd::StartUnbounded) => Ordering::Greater,

            (DiscreteBoundOrd::StartUnbounded, DiscreteBoundOrd::Included(_)) => Ordering::Less,
            (DiscreteBoundOrd::StartUnbounded, DiscreteBoundOrd::StartUnbounded) => Ordering::Equal,
            (DiscreteBoundOrd::StartUnbounded, DiscreteBoundOrd::EndUnbounded) => Ordering::Less,

            (DiscreteBoundOrd::EndUnbounded, DiscreteBoundOrd::Included(_)) => Ordering::Greater,
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
			DiscreteBoundOrd::Included(2) > DiscreteBoundOrd::StartUnbounded
		);

		assert!(DiscreteBoundOrd::Included(2) < DiscreteBoundOrd::EndUnbounded);

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
			DiscreteBoundOrd::StartUnbounded::<i8>
				< DiscreteBoundOrd::EndUnbounded
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
