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
use std::ops::RangeBounds;

use crate::bound_ord::BoundOrd;

pub enum CustomRangeBoundsOrdWrapper<I, K> {
	BoundOrd(BoundOrd<I>),
	RangeBounds(K),
}

impl<I, K> Ord for CustomRangeBoundsOrdWrapper<I, K>
where
	I: Ord,
	K: RangeBounds<I>,
{
	fn cmp(&self, other: &Self) -> Ordering {
		match (self, other) {
			(
				CustomRangeBoundsOrdWrapper::RangeBounds(range_bounds),
				CustomRangeBoundsOrdWrapper::BoundOrd(bound_ord),
			) => cmp_range_bounds_with_bound_ord(
				range_bounds,
				bound_ord.as_ref(),
			),
			(
				CustomRangeBoundsOrdWrapper::BoundOrd(bound_ord),
				CustomRangeBoundsOrdWrapper::RangeBounds(range_bounds),
			) => cmp_range_bounds_with_bound_ord(
				range_bounds,
				bound_ord.as_ref(),
			)
			.reverse(),
			_ => {
				panic!(
					"Must have ONE of each real RangeBounds and non-real BoundOrd!"
				);
			}
		}
	}
}

fn cmp_range_bounds_with_bound_ord<I, K>(
	range_bounds: &K,
	bound_ord: BoundOrd<&I>,
) -> Ordering
where
	I: Ord,
	K: RangeBounds<I>,
{
	//optimisation remove cloning here and all trait bounds that are
	//reliant on this
	let start_bound_ord = BoundOrd::start(range_bounds.start_bound());
	let end_bound_ord = BoundOrd::end(range_bounds.end_bound());

	if bound_ord < start_bound_ord {
		Ordering::Greater
	} else if bound_ord > end_bound_ord {
		Ordering::Less
	} else {
		Ordering::Equal
	}
}

impl<I, K> PartialOrd for CustomRangeBoundsOrdWrapper<I, K>
where
	I: Ord,
	K: RangeBounds<I>,
{
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl<I, K> Eq for CustomRangeBoundsOrdWrapper<I, K>
where
	I: Ord,
	K: RangeBounds<I>,
{
}

impl<I, K> PartialEq for CustomRangeBoundsOrdWrapper<I, K>
where
	I: Ord,
	K: RangeBounds<I>,
{
	fn eq(&self, other: &Self) -> bool {
		self.cmp(other).is_eq()
	}
}
