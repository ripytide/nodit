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

use crate::range_bounds_map::FiniteRange;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DiscreteFiniteBounds<I> {
	//both are always included
	pub start: I,
	pub end: I,
}

impl<I> RangeBounds<I> for DiscreteFiniteBounds<I> {
	fn start_bound(&self) -> Bound<&I> {
		Bound::Included(&self.start)
	}
	fn end_bound(&self) -> Bound<&I> {
		Bound::Included(&self.end)
	}
}

impl<I> FiniteRange<I> for DiscreteFiniteBounds<I>
where
	I: Copy,
{
	fn start(&self) -> I {
		self.start
	}

	fn end(&self) -> I {
		self.end
	}
}
