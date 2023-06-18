/*
Copyright 2022,2023 James Forster

This file is part of discrete_range_map.

discrete_range_map is free software: you can redistribute it and/or
modify it under the terms of the GNU Affero General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

discrete_range_map is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with discrete_range_map. If not, see <https://www.gnu.org/licenses/>.
*/

use std::ops::{Bound, RangeBounds};

use serde::{Deserialize, Serialize};

use crate::discrete_range_map::InclusiveRange;
use crate::DiscreteFinite;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct InclusiveInterval<I> {
	pub start: I,
	pub end: I,
}

impl<I> InclusiveInterval<I> where I: Ord + DiscreteFinite + Copy {}

impl<I> RangeBounds<I> for InclusiveInterval<I>
where
	I: Copy,
{
	fn start_bound(&self) -> Bound<&I> {
		Bound::Included(&self.start)
	}

	fn end_bound(&self) -> Bound<&I> {
		Bound::Included(&self.end)
	}
}

impl<I> InclusiveRange<I> for InclusiveInterval<I>
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
