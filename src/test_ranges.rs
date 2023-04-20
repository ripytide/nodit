use std::ops::{Bound, RangeBounds};

use crate::discrete_bounds::{DiscreteBound, DiscreteBounds};
use crate::stepable::Stepable;
use crate::{TryFromDiscreteBounds, TryFromDiscreteBoundsError};

pub fn uu() -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Unbounded,
		end: DiscreteBound::Unbounded,
	}
}
pub fn ui(x: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Unbounded,
		end: DiscreteBound::Included(x),
	}
}
pub fn ue(x: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Unbounded,
		end: DiscreteBound::Included(x.down().unwrap()),
	}
}
pub fn iu(x: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Included(x),
		end: DiscreteBound::Unbounded,
	}
}
//fn eu(x: i8) -> TestBounds {
//(Bound::Excluded(x), Bound::Unbounded)
//}
pub fn ii(x1: i8, x2: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Included(x1),
		end: DiscreteBound::Included(x2),
	}
}
pub fn ie(x1: i8, x2: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Included(x1),
		end: DiscreteBound::Included(x2.down().unwrap()),
	}
}
pub fn ei(x1: i8, x2: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Included(x1.up().unwrap()),
		end: DiscreteBound::Included(x2),
	}
}
pub fn ee(x1: i8, x2: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Included(x1.up().unwrap()),
		end: DiscreteBound::Included(x2.down().unwrap()),
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IEStrict {
	start: i8,
	end: i8,
}

pub fn ie_strict(start: i8, end: i8) -> IEStrict {
	IEStrict { start, end }
}

impl RangeBounds<i8> for IEStrict {
	fn start_bound(&self) -> std::ops::Bound<&i8> {
		Bound::Included(&self.start)
	}
	fn end_bound(&self) -> Bound<&i8> {
		Bound::Excluded(&self.end)
	}
}

impl TryFromDiscreteBounds<i8> for IEStrict {
	fn try_from_discrete_bounds(
		discrete_bounds: DiscreteBounds<i8>,
	) -> Result<Self, TryFromDiscreteBoundsError>
	where
		Self: Sized,
	{
		match (discrete_bounds.start, discrete_bounds.end) {
			(DiscreteBound::Included(start), DiscreteBound::Included(end)) => Ok(IEStrict {
				start,
				end: end.checked_add(1).ok_or(TryFromDiscreteBoundsError)?,
			}),
			_ => Err(TryFromDiscreteBoundsError),
		}
	}
}
