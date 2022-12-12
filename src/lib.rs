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

//! todo

#![feature(is_some_and)]
#![feature(let_chains)]
#![allow(clippy::tabs_in_doc_comments)]
#![allow(clippy::needless_return)]
pub(crate) mod bound_ord;
pub mod range_bounds_map;
pub mod range_bounds_set;
pub mod try_from_bounds;

pub use crate::range_bounds_map::{
	OverlapError, OverlapOrTryFromBoundsError, RangeBoundsMap,
	TryFromBoundsError,
};
pub use crate::range_bounds_set::RangeBoundsSet;
pub use crate::try_from_bounds::TryFromBounds;
