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

use std::iter::Step;

pub trait Discrete {
    const MIN: Self;
    const MAX: Self;

	fn up(self) -> Option<Self>
	where
		Self: Sized;
	fn down(self) -> Option<Self>
	where
		Self: Sized;
}

impl<T> Discrete for T
where
	T: Sized + Step,
{
	fn up(self) -> Option<Self> {
		<T as Step>::forward_checked(self, 1)
	}
	fn down(self) -> Option<Self> {
		<T as Step>::backward_checked(self, 1)
	}
}
