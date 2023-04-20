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

use std::ops::{Bound, RangeBounds};

use crate::bound_ord::DiscreteBoundOrd;
use crate::stepable::Stepable;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DiscreteBounds<I> {
	start: DiscreteBound<I>,
	end: DiscreteBound<I>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiscreteBound<I> {
	Included(I),
	Unbounded,
}

impl<I> DiscreteBound<I>
where
	I: Stepable,
{
	pub fn start(bound: Bound<I>) -> Self {
		match bound {
			Bound::Included(x) => DiscreteBound::Included(x),
			Bound::Excluded(x) => DiscreteBound::Included(x.up().unwrap()),
			Bound::Unbounded => DiscreteBound::Unbounded,
		}
	}
	pub fn end(bound: Bound<I>) -> Self {
		match bound {
			Bound::Included(x) => DiscreteBound::Included(x),
			Bound::Excluded(x) => DiscreteBound::Included(x.down().unwrap()),
			Bound::Unbounded => DiscreteBound::Unbounded,
		}
	}

	pub fn up_if_finite(&self) -> DiscreteBound<I> {
		match self {
			DiscreteBound::Included(x) => DiscreteBound::Included(x.up().unwrap()),
			DiscreteBound::Unbounded => DiscreteBound::Unbounded,
		}
	}
	pub fn down_if_finite(&self) -> DiscreteBound<I> {
		match self {
			DiscreteBound::Included(x) => DiscreteBound::Included(x.down().unwrap()),
			DiscreteBound::Unbounded => DiscreteBound::Unbounded,
		}
	}
}

impl<I> From<DiscreteBoundOrd<I>> for DiscreteBound<I> {
	fn from(discrete_bound_ord: DiscreteBoundOrd<I>) -> Self {
		match discrete_bound_ord {
			DiscreteBoundOrd::Included(x) => DiscreteBound::Included(x),
			DiscreteBoundOrd::StartUnbounded => DiscreteBound::Unbounded,
			DiscreteBoundOrd::EndUnbounded => DiscreteBound::Unbounded,
		}
	}
}

impl<I> RangeBounds<I> for DiscreteBounds<I> {
	fn start_bound(&self) -> Bound<&I> {
		match self.start {
			DiscreteBound::Included(ref x) => Bound::Included(x),
			DiscreteBound::Unbounded => Bound::Unbounded,
		}
	}
	fn end_bound(&self) -> Bound<&I> {
		match self.start {
			DiscreteBound::Included(ref x) => Bound::Included(x),
			DiscreteBound::Unbounded => Bound::Unbounded,
		}
	}
}
