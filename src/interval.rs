//! A module containing [`Interval`] and [`InclusiveInterval`].
//!
//! The constructors are not associated functions as then you must write
//! `InclusiveInterval` before it every time you want create an interval
//! which is a bit annoying as you can't import associated function in rust
//! yet. If you would still like the associated versions I would be happy to
//! add them as well, just open a PR/Issue.

use core::ops::{Bound, Range, RangeBounds, RangeInclusive};

use crate::utils::{invalid_interval_panic, sorted_config, SortedConfig};
use crate::{IntervalType, PointType};

/// An inclusive interval, only valid intervals can be constructed.
///
/// This interval struct is used throughout this crate for the examples and
/// tests but can also be used by library users if they don't wish to create
/// their own interval types.
///
/// To create an `InclusiveInterval` use one of the various contrutor
/// functions which will all panic if you try to create an invalid interval.
/// See [`Invalid
/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
/// for more details.
///
/// ```
/// use nodit::interval::{ee, ii};
///
/// let inclusive_interval = ii(4, 4);
/// let exclusive_interval = ee(3, 5);
///
/// assert_eq!(inclusive_interval, exclusive_interval);
/// ```
///
/// ```should_panic
/// use nodit::interval::ee;
///
/// let invalid_interval = ee(4, 4);
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Interval<I> {
	/// The start of the interval, inclusive.
	pub(crate) start: I,
	/// The end of the interval, inclusive.
	pub(crate) end: I,
}
impl<I> Interval<I>
where
	I: PointType,
{
	/// The start of the interval, inclusive.
	///
	/// ```
	/// use nodit::interval::ii;
	///
	/// assert_eq!(ii(2, 4).start(), &2);
	/// ```
	pub fn start(&self) -> &I {
		&self.start
	}
	/// The end of the interval, inclusive.
	///
	/// ```
	/// use nodit::interval::ii;
	///
	/// assert_eq!(ii(2, 4).end(), &4);
	/// ```
	pub fn end(&self) -> &I {
		&self.end
	}
}

impl<I> RangeBounds<I> for Interval<I>
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
impl<I> InclusiveInterval<I> for Interval<I>
where
	I: PointType,
{
	fn start(&self) -> &I {
		&self.start
	}

	fn end(&self) -> &I {
		&self.end
	}
}
impl<I> From<Interval<I>> for RangeInclusive<I> {
	fn from(value: Interval<I>) -> Self {
		value.start..=value.end
	}
}
impl<I> From<RangeInclusive<I>> for Interval<I>
where
	I: PointType,
{
	fn from(value: RangeInclusive<I>) -> Self {
		ii_by_ref(value.start(), value.end())
	}
}
impl<I> From<Interval<I>> for Range<I>
where
	I: PointType,
{
	fn from(value: Interval<I>) -> Self {
		value.start..value.end.up().unwrap()
	}
}
impl<I> From<Range<I>> for Interval<I>
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
/// Panics if the interval is an invalid interval. See [`Invalid
/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
/// for more details.
///
/// ```
/// use nodit::interval::uu;
/// use nodit::{InclusiveInterval, Interval};
///
/// let interval1: Interval<u8> = uu();
/// let interval2: Interval<u8> = uu();
///
/// assert_eq!(interval1, interval2)
/// ```
pub fn uu<I>() -> Interval<I>
where
	I: PointType,
{
	let interval = Interval {
		start: I::MIN,
		end: I::MAX,
	};

	invalid_interval_panic(&interval);

	interval
}

/// Create an new Unbounded-Unbounded interval by references.
pub fn uu_by_ref<I>() -> Interval<I>
where
	I: PointType,
{
	let interval = Interval {
		start: I::MIN,
		end: I::MAX,
	};

	invalid_interval_panic(&interval);

	interval
}

/// Create an new Unbounded-Included interval.
///
/// # Panics
///
/// Panics if the interval is an invalid interval. See [`Invalid
/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
/// for more details.
///
/// ```
/// use nodit::interval::ui;
///
/// let interval1 = ui(1);
/// let interval2 = ui(4);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn ui<I>(end: I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval { start: I::MIN, end };

	invalid_interval_panic(&interval);

	interval
}

/// Create an new Unbounded-Included interval by reference.
pub fn ui_by_ref<I>(end: &I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval { start: I::MIN, end: end.clone() };

	invalid_interval_panic(&interval);

	interval
}
/// Create an new Unbounded-Excluded interval.
///
/// # Panics
///
/// Panics if the interval is an invalid interval. See [`Invalid
/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
/// for more details.
///
/// ```
/// use nodit::interval::ue;
///
/// let interval1 = ue(1);
/// let interval2 = ue(4);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn ue<I>(end: I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval {
		start: I::MIN,
		end: end.down().unwrap(),
	};

	invalid_interval_panic(&interval);

	interval
}

/// Create an new Unbounded-Excluded interval by reference.
pub fn ue_by_ref<I>(end: &I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval {
		start: I::MIN,
		end: end.down().unwrap(),
	};

	invalid_interval_panic(&interval);

	interval
}
/// Create an new Included-Unbounded interval.
///
/// # Panics
///
/// Panics if the interval is an invalid interval. See [`Invalid
/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
/// for more details.
///
/// ```
/// use nodit::interval::iu;
///
/// let interval1 = iu(1);
/// let interval2 = iu(4);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn iu<I>(start: I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval { start, end: I::MAX };

	invalid_interval_panic(&interval);

	interval
}

/// Create an new Included-Unbounded interval by reference.
pub fn iu_by_ref<I>(start: &I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval { start: start.clone(), end: I::MAX };

	invalid_interval_panic(&interval);

	interval
}

/// Create an new Excluded-Unbounded interval.
///
/// # Panics
///
/// Panics if the interval is an invalid interval. See [`Invalid
/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
/// for more details.
///
/// ```
/// use nodit::interval::eu;
///
/// let interval1 = eu(1);
/// let interval2 = eu(4);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn eu<I>(start: I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval {
		start: start.up().unwrap(),
		end: I::MAX,
	};

	invalid_interval_panic(&interval);

	interval
}

/// Create an new Excluded-Unbounded interval by reference.
pub fn eu_by_ref<I>(start: &I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval {
		start: start.up().unwrap(),
		end: I::MAX,
	};

	invalid_interval_panic(&interval);

	interval
}

/// Create an new Included-Included interval.
///
/// # Panics
///
/// Panics if the interval is an invalid interval. See [`Invalid
/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
/// for more details.
///
/// ```
/// use nodit::interval::ii;
///
/// let interval1 = ii(0, 4);
/// let interval2 = ii(2, 6);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn ii<I>(start: I, end: I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval { start, end };

	invalid_interval_panic(&interval);

	interval
}

/// Create an new Included-Included interval by reference.
pub fn ii_by_ref<I>(start: &I, end: &I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval { start: start.clone(), end: end.clone() };

	invalid_interval_panic(&interval);

	interval
}

/// Create an new Included-Excluded interval.
///
/// # Panics
///
/// Panics if the interval is an invalid interval. See [`Invalid
/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
/// for more details.
///
/// ```
/// use nodit::interval::ie;
///
/// let interval1 = ie(0, 4);
/// let interval2 = ie(2, 6);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn ie<I>(start: I, end: I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval {
		start,
		end: end.down().unwrap(),
	};

	invalid_interval_panic(&interval);

	interval
}

/// Create an new Included-Excluded interval by reference.
pub fn ie_by_ref<I>(start: &I, end: &I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval {
		start: start.clone(),
		end: end.down().unwrap(),
	};

	invalid_interval_panic(&interval);

	interval
}

/// Create an new Excluded-Included interval.
///
/// # Panics
///
/// Panics if the interval is an invalid interval. See [`Invalid
/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
/// for more details.
///
/// ```
/// use nodit::interval::ei;
///
/// let interval1 = ei(0, 4);
/// let interval2 = ei(2, 6);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn ei<I>(start: I, end: I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval {
		start: start.up().unwrap(),
		end,
	};

	invalid_interval_panic(&interval);

	interval
}

/// Create an new Excluded-Included interval by reference.
pub fn ei_by_ref<I>(start: &I, end: &I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval {
		start: start.up().unwrap(),
		end: end.clone(),
	};

	invalid_interval_panic(&interval);

	interval
}

/// Create an new Excluded-Excluded interval.
///
/// # Panics
///
/// Panics if the interval is an invalid interval. See [`Invalid
/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
/// for more details.
///
/// ```
/// use nodit::interval::ee;
///
/// let interval1 = ee(0, 4);
/// let interval2 = ee(2, 6);
///
/// assert_ne!(interval1, interval2)
/// ```
pub fn ee<I>(start: I, end: I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval {
		start: start.up().unwrap(),
		end: end.down().unwrap(),
	};

	invalid_interval_panic(&interval);

	interval
}

/// Create an new Excluded-Excluded interval by reference.
pub fn ee_by_ref<I>(start: &I, end: &I) -> Interval<I>
where
	I: PointType,
{
	let interval = Interval {
		start: start.up().unwrap(),
		end: end.down().unwrap(),
	};

	invalid_interval_panic(&interval);

	interval
}

/// A interval that has **Inclusive** end-points.
pub trait InclusiveInterval<I>: Clone + From<Interval<I>> {
	/// The start of `self`, inclusive.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ie, ii};
	/// use nodit::InclusiveInterval;
	///
	/// assert_eq!(ii(3, 4).start(), &3);
	/// assert_eq!(ii(4, 5).start(), &4);
	/// assert_eq!(ie(5, 6).start(), &5);
	/// ```
	fn start(&self) -> &I;
	/// The end of `self`, inclusive.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ei, ii};
	/// use nodit::InclusiveInterval;
	///
	/// assert_eq!(ii(3, 4).end(), &4);
	/// assert_eq!(ii(4, 5).end(), &5);
	/// assert_eq!(ei(5, 6).end(), &6);
	/// ```
	fn end(&self) -> &I;

	/// Does `self` contain the given point?
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ie, ii};
	/// use nodit::InclusiveInterval;
	///
	/// assert_eq!(ii(4, 5).contains_point(3), false);
	/// assert_eq!(ii(4, 5).contains_point(4), true);
	/// assert_eq!(ii(4, 5).contains_point(5), true);
	/// assert_eq!(ii(4, 5).contains_point(6), false);
	/// ```
	fn contains_point(&self, point: I) -> bool
	where
		I: PointType,
	{
		&point >= self.start() && &point <= self.end()
	}

	/// Does `self` contain the given point by referrence?
	fn contains_point_by_ref(&self, point: &I) -> bool
	where
		I: PointType,
	{
		point >= self.start() && point <= self.end()
	}

	/// Does `self` contain the given interval?
	///
	/// This means all points of the given interval must also be contained within `self`.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ie, ii};
	/// use nodit::InclusiveInterval;
	///
	/// assert_eq!(ii(4, 5).contains_interval(&ii(4, 4)), true);
	/// assert_eq!(ii(4, 5).contains_interval(&ii(5, 5)), true);
	/// assert_eq!(ii(4, 5).contains_interval(&ii(4, 6)), false);
	/// assert_eq!(ii(4, 5).contains_interval(&ii(4, 5)), true);
	/// ```
	fn contains_interval<Q>(&self, interval: &Q) -> bool
	where
		I: PointType,
		Q: IntervalType<I>,
	{
		self.start() <= interval.start() && self.end() >= interval.end()
	}

	/// Is `self` valid?
	///
	/// This uses this crates definition of valid intervals which means `start()` <= `end()`.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ie, ii};
	/// use nodit::InclusiveInterval;
	///
	/// assert_eq!(ii(4, 4).is_valid(), true);
	/// assert_eq!(ii(4, 5).is_valid(), true);
	/// assert_eq!(ie(4, 5).is_valid(), true);
	/// ```
	fn is_valid(&self) -> bool
	where
		I: PointType,
	{
		self.start() <= self.end()
	}

	/// Is `self` an interval over a single point?
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ie, ii};
	/// use nodit::InclusiveInterval;
	///
	/// assert_eq!(ii(4, 4).is_singular(), true);
	/// assert_eq!(ii(4, 5).is_singular(), false);
	/// assert_eq!(ie(4, 5).is_singular(), true);
	/// ```
	fn is_singular(&self) -> bool
	where
		I: PointType,
	{
		self.start() == self.end()
	}

	/// Returns the intersection between `self` and `other` if there is any.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ee, ie, ii};
	/// use nodit::InclusiveInterval;
	///
	/// assert_eq!(ii(4, 6).intersection(&ie(6, 8)), Some(ii(6, 6)));
	/// assert_eq!(ii(4, 6).intersection(&ee(6, 8)), None);
	/// ```
	fn intersection<Q>(&self, other: &Q) -> Option<Self>
	where
		I: PointType,
		Q: IntervalType<I>,
		Self: From<Interval<I>>,
	{
		let intersect_start = I::max(self.start().clone(), other.start().clone());
		let intersect_end = I::min(self.end().clone(), other.end().clone());
		if intersect_start <= intersect_end {
			Some(Self::from(Interval {
				start: intersect_start,
				end: intersect_end,
			}))
		} else {
			None
		}
	}

	/// Returns true if the `self` and `other` overlap and false if they do not.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ee, ie, ii};
	/// use nodit::InclusiveInterval;
	///
	/// assert_eq!(ii(4, 6).overlaps(&ii(6, 8)), true);
	/// assert_eq!(ii(4, 6).overlaps(&ii(8, 10)), false);
	/// ```
	fn overlaps<Q>(&self, other: &Q) -> bool
	where
		I: PointType,
		Q: IntervalType<I>,
	{
		!matches!(
			sorted_config( (*self).clone(), (*other).clone()),
			SortedConfig::NonOverlapping(_, _)
		)
	}

	/// Move `self` by the given `delta` amount upwards.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ee, ie, ii};
	/// use nodit::InclusiveInterval;
	///
	/// assert_eq!(ii(4, 6).translate(8), ii(12, 14));
	/// assert_eq!(ee(4, 6).translate(-4), ee(0, 2));
	/// ```
	fn translate(&self, delta: I) -> Self
	where
		I: PointType,
		I: core::ops::Add<Output = I>,
		Self: From<Interval<I>>,
	{
		Self::from(Interval {
			start: self.start().clone() + delta.clone(),
			end: self.end().clone() + delta,
		})
	}

	/// Move `self` by the given `delta` amount upwards by reference to delta.
	fn translate_by_ref(&self, delta: &I) -> Self
	where
		I: PointType,
		I: core::ops::Add<Output = I>,
		Self: From<Interval<I>>,
	{
		Self::from(Interval {
			start: self.start().clone() + delta.clone(),
			end: self.end().clone() + delta.clone(),
		})
	}

	/// The amount from the start to the end of the `self`.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ee, ei, ie, ii};
	/// use nodit::InclusiveInterval;
	///
	/// assert_eq!(ii(4, 6).width(), 2);
	/// assert_eq!(ie(4, 6).width(), 1);
	/// assert_eq!(ei(4, 6).width(), 1);
	/// assert_eq!(ee(4, 6).width(), 0);
	/// ```
	fn width(&self) -> I
	where
		I: PointType,
		I: core::ops::Sub<Output = I>,
	{
		self.end().clone().clone() - self.start().clone()
	}
}
