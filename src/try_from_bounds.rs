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

use std::ops::{
	Bound, Range, RangeBounds, RangeFrom, RangeFull, RangeInclusive, RangeTo,
	RangeToInclusive,
};

use labels::{not_a_fn, trivial};

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
	#[not_a_fn]
	fn try_from_bounds(
		start_bound: Bound<I>,
		end_bound: Bound<I>,
	) -> Option<Self>
	where
		Self: Sized;
	// optimisation: make this non-implemented so the trait impls can
	// define them more efficiently
	#[not_a_fn]
	fn is_valid<Q>(range_bounds: &Q) -> bool
	where
		Q: RangeBounds<I>,
		Self: Sized,
		I: Clone,
	{
		Self::try_from_bounds(
			range_bounds.start_bound().cloned(),
			range_bounds.end_bound().cloned(),
		)
		.is_some()
	}
}

impl<I> TryFromBounds<I> for (Bound<I>, Bound<I>) {
	#[trivial]
	fn try_from_bounds(
		start_bound: Bound<I>,
		end_bound: Bound<I>,
	) -> Option<Self> {
		Some((start_bound, end_bound))
	}
}

impl<I> TryFromBounds<I> for Range<I> {
	#[trivial]
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
	#[trivial]
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
	#[trivial]
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
	#[trivial]
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
	#[trivial]
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
	#[trivial]
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
