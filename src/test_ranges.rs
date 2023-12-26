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

//! A collection of helper functions for making [`InclusiveInterval`]s from `i8`'s used for testing
//! and example purposes.

use crate::{DiscreteFinite, InclusiveInterval};

/// An unbounded-unbounded interval
pub fn uu() -> InclusiveInterval<i8> {
	InclusiveInterval {
		start: i8::MIN,
		end: i8::MAX,
	}
}
/// An unbounded-included interval
pub fn ui(x: i8) -> InclusiveInterval<i8> {
	InclusiveInterval {
		start: i8::MIN,
		end: x,
	}
}
/// An unbounded-excluded interval
pub fn ue(x: i8) -> InclusiveInterval<i8> {
	InclusiveInterval {
		start: i8::MIN,
		end: x.down().unwrap(),
	}
}
/// An included-unbounded interval
pub fn iu(x: i8) -> InclusiveInterval<i8> {
	InclusiveInterval {
		start: x,
		end: i8::MAX,
	}
}
/// An excluded-unbounded interval
pub fn eu(x: i8) -> InclusiveInterval<i8> {
	InclusiveInterval {
		start: x.up().unwrap(),
		end: i8::MAX,
	}
}
/// An included-included interval
pub fn ii(x1: i8, x2: i8) -> InclusiveInterval<i8> {
	InclusiveInterval { start: x1, end: x2 }
}
/// An included-excluded interval
pub fn ie(x1: i8, x2: i8) -> InclusiveInterval<i8> {
	InclusiveInterval {
		start: x1,
		end: x2.down().unwrap(),
	}
}
/// An excluded-included interval
pub fn ei(x1: i8, x2: i8) -> InclusiveInterval<i8> {
	InclusiveInterval {
		start: x1.up().unwrap(),
		end: x2,
	}
}
/// An excluded-excluded interval
pub fn ee(x1: i8, x2: i8) -> InclusiveInterval<i8> {
	InclusiveInterval {
		start: x1.up().unwrap(),
		end: x2.down().unwrap(),
	}
}
