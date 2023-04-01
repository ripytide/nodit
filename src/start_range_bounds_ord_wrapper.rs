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
use std::marker::PhantomData;
use std::ops::RangeBounds;

use crate::bound_ord::BoundOrd;

#[derive(Debug, Clone)]
pub struct StartRangeBoundsOrdWrapper<I, K> {
	phantom: PhantomData<I>,
	inner: K,
}

impl<I, K> Ord for StartRangeBoundsOrdWrapper<I, K>
where
	I: Ord,
	K: RangeBounds<I>,
{
	fn cmp(&self, other: &Self) -> Ordering {
		BoundOrd::start(self.inner.start_bound())
			.cmp(&BoundOrd::start(other.inner.start_bound()))
	}
}
impl<I, K> PartialOrd for StartRangeBoundsOrdWrapper<I, K>
where
	I: Ord,
	K: RangeBounds<I>,
{
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(&other))
	}
}
impl<I, K> PartialEq for StartRangeBoundsOrdWrapper<I, K>
where
	I: Ord,
	K: RangeBounds<I>,
{
	fn eq(&self, other: &Self) -> bool {
		self.cmp(&other).is_eq()
	}
}
impl<I, K> Eq for StartRangeBoundsOrdWrapper<I, K>
where
	I: Ord,
	K: RangeBounds<I>,
{
}
