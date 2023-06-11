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

use crate::discrete_range_map::FiniteRange;
use crate::DiscreteFinite;

///both ends are always included
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval<I> {
	pub start: I,
	pub end: I,
}

impl<I> Interval<I>
where
	I: Ord + DiscreteFinite + Copy,
{
	pub fn contains(&self, point: I) -> bool {
		point >= self.start && point <= self.end
	}

	///requires that self comes before other and they don't overlap
	pub fn touches_ordered(&self, other: &Self) -> bool {
		self.end == other.start.down().unwrap()
	}

	///requires that self comes before other
	pub fn overlaps_ordered(&self, other: &Self) -> bool {
		self.contains(other.start) || self.contains(other.end)
	}

	///requires that self comes before other
	pub fn merge_ordered(self, other: &Self) -> Self {
		Interval {
			start: self.start,
			end: other.end,
		}
	}
}

impl<I> FiniteRange<I> for Interval<I>
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
