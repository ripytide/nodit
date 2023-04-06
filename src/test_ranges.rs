use std::ops::{Bound, RangeBounds};

use crate::{TryFromBounds, TryFromBoundsError};

pub type AnyRange = (Bound<i8>, Bound<i8>);

pub fn uu() -> AnyRange {
	(Bound::Unbounded, Bound::Unbounded)
}
pub fn ui(x: i8) -> AnyRange {
	(Bound::Unbounded, Bound::Included(x))
}
pub fn ue(x: i8) -> AnyRange {
	(Bound::Unbounded, Bound::Excluded(x))
}
pub fn iu(x: i8) -> AnyRange {
	(Bound::Included(x), Bound::Unbounded)
}
//fn eu(x: i8) -> TestBounds {
//(Bound::Excluded(x), Bound::Unbounded)
//}
pub fn ii(x1: i8, x2: i8) -> AnyRange {
	(Bound::Included(x1), Bound::Included(x2))
}
pub fn ie(x1: i8, x2: i8) -> AnyRange {
	(Bound::Included(x1), Bound::Excluded(x2))
}
pub fn ei(x1: i8, x2: i8) -> AnyRange {
	(Bound::Excluded(x1), Bound::Included(x2))
}
pub fn ee(x1: i8, x2: i8) -> AnyRange {
	(Bound::Excluded(x1), Bound::Excluded(x2))
}

pub fn u() -> Bound<i8> {
	Bound::Unbounded
}

/// a..b Inclusive-Exclusive range struct
/// since the builtin range isn't Copy for some reason
#[allow(dead_code)]
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct InExRange {
	start: i8,
	end: i8,
}

pub fn ie_strict(start: i8, end: i8) -> InExRange {
	InExRange { start, end }
}

impl RangeBounds<i8> for InExRange {
	fn start_bound(&self) -> Bound<&i8> {
		Bound::Included(&self.start)
	}
	fn end_bound(&self) -> Bound<&i8> {
		Bound::Excluded(&self.end)
	}
}

impl TryFromBounds<i8> for InExRange {
	fn try_from_bounds(
		start_bound: Bound<i8>,
		end_bound: Bound<i8>,
	) -> Result<Self, crate::TryFromBoundsError>
	where
		Self: Sized,
	{
		match (start_bound, end_bound) {
			(Bound::Included(start), Bound::Excluded(end)) => {
				Ok(InExRange { start, end })
			}
			_ => Err(TryFromBoundsError),
		}
	}
}
