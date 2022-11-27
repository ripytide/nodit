/*
Copyright 2022 James Forster

This file is part of range_bounds_map.

range_bounds_map is free software: you can redistribute it and/or
modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

range_bounds_map is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with range_bounds_map. If not, see <https://www.gnu.org/licenses/>.
*/

#![feature(is_some_and)]
#![feature(let_chains)]
pub(crate) mod bounds;
pub mod range_bounds_ext;
pub mod range_bounds_map;
pub mod range_bounds_set;

#[cfg(test)]
pub(crate) mod test_helpers;

pub use crate::range_bounds_map::RangeBoundsMap;
pub use crate::range_bounds_set::RangeBoundsSet;
