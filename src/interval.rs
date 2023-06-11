/*
Copyright 2022 James Forster

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

///both ends are always included
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval<I> {
	pub start: I,
	pub end: I,
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
