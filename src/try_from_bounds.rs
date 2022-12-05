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

use std::ops::{
	Bound, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo,
	RangeToInclusive,
};

/// A "newtype" trait to copy [`TryFrom`].
///
/// I am forced to use this "newtype" instead of [`TryFrom`] because
/// [`Range`] and friends don't implement `TryFrom<(Bound, Bound)>`
///
/// I personally think they should since then I wouldn't have to make
/// a trait just for this. I have made a post about it here should you
/// wish to comment your view.
/// <https://internals.rust-lang.org/t/range-should-impl-tryfrom-bound-bound>
///
/// [`TryFrom`]: https://doc.rust-lang.org/std/convert/trait.TryFrom.html
/// [`Range`]: https://doc.rust-lang.org/std/ops/struct.Range.html
pub trait TryFromBounds<I> {
	fn try_from_bounds(
		start_bound: Bound<I>,
		end_bound: Bound<I>,
	) -> Option<Self>
	where
		Self: Sized;
}

impl<I> TryFromBounds<I> for (Bound<I>, Bound<I>) {
	fn try_from_bounds(
		start_bound: Bound<I>,
		end_bound: Bound<I>,
	) -> Option<Self> {
		Some((start_bound, end_bound))
	}
}

impl<I> TryFromBounds<I> for Range<I> {
	fn try_from_bounds(
		start_bound: Bound<I>,
		end_bound: Bound<I>,
	) -> Option<Self> {
		match (start_bound, end_bound) {
			(Bound::Included(start), Bound::Excluded(end)) => Some(start..end),
			_ => None,
		}
	}
}

impl<I> TryFromBounds<I> for RangeInclusive<I> {
	fn try_from_bounds(
		start_bound: Bound<I>,
		end_bound: Bound<I>,
	) -> Option<Self> {
		match (start_bound, end_bound) {
			(Bound::Included(start), Bound::Included(end)) => Some(start..=end),
			_ => None,
		}
	}
}

impl<I> TryFromBounds<I> for RangeFrom<I> {
	fn try_from_bounds(
		start_bound: Bound<I>,
		end_bound: Bound<I>,
	) -> Option<Self> {
		match (start_bound, end_bound) {
			(Bound::Included(start), Bound::Unbounded) => Some(start..),
			_ => None,
		}
	}
}

impl<I> TryFromBounds<I> for RangeTo<I> {
	fn try_from_bounds(
		start_bound: Bound<I>,
		end_bound: Bound<I>,
	) -> Option<Self> {
		match (start_bound, end_bound) {
			(Bound::Unbounded, Bound::Excluded(end)) => Some(..end),
			_ => None,
		}
	}
}

impl<I> TryFromBounds<I> for RangeToInclusive<I> {
	fn try_from_bounds(
		start_bound: Bound<I>,
		end_bound: Bound<I>,
	) -> Option<Self> {
		match (start_bound, end_bound) {
			(Bound::Unbounded, Bound::Included(end)) => Some(..=end),
			_ => None,
		}
	}
}

impl<I> TryFromBounds<I> for RangeFull {
	fn try_from_bounds(
		start_bound: Bound<I>,
		end_bound: Bound<I>,
	) -> Option<Self> {
		match (start_bound, end_bound) {
			(Bound::Unbounded, Bound::Unbounded) => Some(..),
			_ => None,
		}
	}
}
