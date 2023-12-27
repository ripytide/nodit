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

//! A module containing [`InclusiveInterval`] and its constructors.
//!
//! The constructors are not associated functions as then you must write
//! `InclusiveInterval` before it every time you want create an interval
//! which is a bit annoying as you can't import associated function in rust
//! yet. If you would still like the associated versions I would be happy to
//! add them as well, just open a PR/Issue.

use core::ops::{Bound, Range, RangeBounds, RangeInclusive};

use serde::{Deserialize, Serialize};

use crate::discrete_range_map::invalid_range_panic;
use crate::{InclusiveRange, PointType};

/// An inclusive interval, only valid intervals can be constructed.
///
/// This interval struct is used throughout this crate for the examples and
/// tests but can also be used by library users if they don't wish to create
/// their own interval types.
///
/// To create an `InclusiveInterval` use one of the various contrutor
/// functions which will all panic if you try to create an invalid range.
/// See [`Invalid
/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
/// for more details.
///
/// ```
/// use discrete_range_map::inclusive_interval::{ee, ii};
///
/// let inclusive_interval = ii(4, 4);
/// let exclusive_interval = ee(3, 5);
///
/// assert_eq!(inclusive_interval, exclusive_interval);
/// ```
///
/// ```should_panic
/// use discrete_range_map::inclusive_interval::ee;
///
/// let invalid_interval = ee(4, 4);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct InclusiveInterval<I> {
	/// The start of the interval, inclusive.
	pub(crate) start: I,
	/// The end of the interval, inclusive.
	pub(crate) end: I,
}
impl<I> InclusiveInterval<I>
where
	I: PointType,
{
	/// The start of the range, inclusive.
	///
	/// ```
	/// use discrete_range_map::inclusive_interval::ii;
	///
	/// assert_eq!(ii(2, 4).start(), 2);
	/// ```
	pub fn start(&self) -> I {
		self.start
	}
	/// The end of the range, inclusive.
	///
	/// ```
	/// use discrete_range_map::inclusive_interval::ii;
	///
	/// assert_eq!(ii(2, 4).end(), 4);
	/// ```
	pub fn end(&self) -> I {
		self.end
	}
}

impl<I> RangeBounds<I> for InclusiveInterval<I>
where
	I: PointType,
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
	I: PointType,
{
	fn start(&self) -> I {
		self.start
	}

	fn end(&self) -> I {
		self.end
	}
}
impl<I> From<InclusiveInterval<I>> for RangeInclusive<I> {
	fn from(value: InclusiveInterval<I>) -> Self {
		value.start..=value.end
	}
}
impl<I> From<RangeInclusive<I>> for InclusiveInterval<I>
where
	I: PointType,
{
	fn from(value: RangeInclusive<I>) -> Self {
		ii(*value.start(), *value.end())
	}
}
impl<I> From<InclusiveInterval<I>> for Range<I>
where
	I: PointType,
{
	fn from(value: InclusiveInterval<I>) -> Self {
		value.start..value.end.up().unwrap()
	}
}
impl<I> From<Range<I>> for InclusiveInterval<I>
where
	I: PointType,
{
	fn from(value: Range<I>) -> Self {
		ie(value.start, value.end)
	}
}

/// Create an new Unbounded-Unbounded interval.
///
/// # Panics
///
/// Panics if the range is an invalid range. See [`Invalid
/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
/// for more details.
///
/// ```
/// use discrete_range_map::inclusive_interval::uu;
/// use discrete_range_map::InclusiveInterval;
///
/// let interval1: InclusiveInterval<u8> = uu();
/// let interval2: InclusiveInterval<u8> = uu();
///
/// assert_eq!(interval1, interval2)
/// ```
pub fn uu<I>() -> InclusiveInterval<I>
where
	I: PointType,
{
	let interval = InclusiveInterval {
		start: I::MIN,
		end: I::MAX,
	};

	invalid_range_panic(interval);

	interval
}
/// Create an new Unbounded-Included interval.
///
/// # Panics
///
/// Panics if the range is an invalid range. See [`Invalid
/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
/// for more details.
///
/// ```
/// use discrete_range_map::inclusive_interval::ui;
///
/// let interval1 = ui(1);
/// let interval2 = ui(4);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn ui<I>(x: I) -> InclusiveInterval<I>
where
	I: PointType,
{
	let interval = InclusiveInterval {
		start: I::MIN,
		end: x,
	};

	invalid_range_panic(interval);

	interval
}
/// Create an new Unbounded-Excluded interval.
///
/// # Panics
///
/// Panics if the range is an invalid range. See [`Invalid
/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
/// for more details.
///
/// ```
/// use discrete_range_map::inclusive_interval::ue;
///
/// let interval1 = ue(1);
/// let interval2 = ue(4);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn ue<I>(x: I) -> InclusiveInterval<I>
where
	I: PointType,
{
	let interval = InclusiveInterval {
		start: I::MIN,
		end: x.down().unwrap(),
	};

	invalid_range_panic(interval);

	interval
}
/// Create an new Included-Unbounded interval.
///
/// # Panics
///
/// Panics if the range is an invalid range. See [`Invalid
/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
/// for more details.
///
/// ```
/// use discrete_range_map::inclusive_interval::iu;
///
/// let interval1 = iu(1);
/// let interval2 = iu(4);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn iu<I>(x: I) -> InclusiveInterval<I>
where
	I: PointType,
{
	let interval = InclusiveInterval {
		start: x,
		end: I::MAX,
	};

	invalid_range_panic(interval);

	interval
}
/// Create an new Excluded-Unbounded interval.
///
/// # Panics
///
/// Panics if the range is an invalid range. See [`Invalid
/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
/// for more details.
///
/// ```
/// use discrete_range_map::inclusive_interval::eu;
///
/// let interval1 = eu(1);
/// let interval2 = eu(4);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn eu<I>(x: I) -> InclusiveInterval<I>
where
	I: PointType,
{
	let interval = InclusiveInterval {
		start: x.up().unwrap(),
		end: I::MAX,
	};

	invalid_range_panic(interval);

	interval
}
/// Create an new Included-Included interval.
///
/// # Panics
///
/// Panics if the range is an invalid range. See [`Invalid
/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
/// for more details.
///
/// ```
/// use discrete_range_map::inclusive_interval::ii;
///
/// let interval1 = ii(0, 4);
/// let interval2 = ii(2, 6);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn ii<I>(x1: I, x2: I) -> InclusiveInterval<I>
where
	I: PointType,
{
	let interval = InclusiveInterval { start: x1, end: x2 };

	invalid_range_panic(interval);

	interval
}
/// Create an new Included-Excluded interval.
///
/// # Panics
///
/// Panics if the range is an invalid range. See [`Invalid
/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
/// for more details.
///
/// ```
/// use discrete_range_map::inclusive_interval::ie;
///
/// let interval1 = ie(0, 4);
/// let interval2 = ie(2, 6);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn ie<I>(x1: I, x2: I) -> InclusiveInterval<I>
where
	I: PointType,
{
	let interval = InclusiveInterval {
		start: x1,
		end: x2.down().unwrap(),
	};

	invalid_range_panic(interval);

	interval
}
/// Create an new Excluded-Included interval.
///
/// # Panics
///
/// Panics if the range is an invalid range. See [`Invalid
/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
/// for more details.
///
/// ```
/// use discrete_range_map::inclusive_interval::ei;
///
/// let interval1 = ei(0, 4);
/// let interval2 = ei(2, 6);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn ei<I>(x1: I, x2: I) -> InclusiveInterval<I>
where
	I: PointType,
{
	let interval = InclusiveInterval {
		start: x1.up().unwrap(),
		end: x2,
	};

	invalid_range_panic(interval);

	interval
}
/// Create an new Excluded-Excluded interval.
///
/// # Panics
///
/// Panics if the range is an invalid range. See [`Invalid
/// Ranges`](https://docs.rs/discrete_range_map/latest/discrete_range_map/index.html#invalid-ranges)
/// for more details.
///
/// ```
/// use discrete_range_map::inclusive_interval::ee;
///
/// let interval1 = ee(0, 4);
/// let interval2 = ee(2, 6);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn ee<I>(x1: I, x2: I) -> InclusiveInterval<I>
where
	I: PointType,
{
	let interval = InclusiveInterval {
		start: x1.up().unwrap(),
		end: x2.down().unwrap(),
	};

	invalid_range_panic(interval);

	interval
}
