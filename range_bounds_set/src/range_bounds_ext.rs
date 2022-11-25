use std::cmp::Ordering;
use std::ops::{Bound, RangeBounds};

trait BoundExt<T> {
	fn inner(&self) -> Option<T>;
}

pub trait RangeBoundsExt<T>
where
	Self: RangeBounds<T>,
	T: PartialOrd,
{
	fn dummy(start_bound: Bound<T>, end_bound: Bound<T>) -> Self;
	fn overlaps(&self, other: &Self) -> bool {
		let (left_most, right_most) = match StartBound::from(self.start_bound())
			.cmp(&StartBound::from(other.start_bound()))
		{
			Ordering::Less => (self, other),
			Ordering::Greater => (other, self),
			Ordering::Equal => return true,
		};

		match (left_most.end_bound(), right_most.start_bound()) {
			(Bound::Included(end), Bound::Included(start)) => end >= start,

			(Bound::Excluded(end), Bound::Excluded(start)) => end > start,
			(Bound::Included(end), Bound::Excluded(start)) => end > start,
			(Bound::Excluded(end), Bound::Included(start)) => end > start,

			(Bound::Unbounded, _) => true,

			(_, Bound::Unbounded) => unreachable!(),
		}
	}
}

use std::ops::{
	Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
};

use crate::bounds::StartBound;

impl<T> RangeBoundsExt<T> for (Bound<T>, Bound<T>)
where
	T: PartialOrd,
{
	fn dummy(start_bound: Bound<T>, end_bound: Bound<T>) -> Self {
		(Bound::from(start_bound), Bound::from(end_bound))
	}
}
impl<T> RangeBoundsExt<T> for Range<T>
where
	T: PartialOrd,
{
	fn dummy(start_bound: Bound<T>, end_bound: Bound<T>) -> Self {
		if let Bound::Included(start) = start_bound {
			if let Bound::Excluded(end) = end_bound {
				return Range { start, end };
			} else {
				panic!("The end of a Range must be Excluded(_)")
			}
		} else {
			panic!("The start of a Range must be Included(_)")
		}
	}
}
impl<T> RangeBoundsExt<T> for RangeFrom<T>
where
	T: PartialOrd,
{
	fn dummy(start_bound: Bound<T>, end_bound: Bound<T>) -> Self {
		if let Bound::Included(start) = start_bound {
			if let Bound::Unbounded = end_bound {
				return RangeFrom { start };
			} else {
				panic!("The end of a RangeFrom must be Unbounded")
			}
		} else {
			panic!("The start of a RangeFrom must be Included(_)")
		}
	}
}
impl<T> RangeBoundsExt<T> for RangeFull
where
	T: PartialOrd,
{
	fn dummy(start_bound: Bound<T>, end_bound: Bound<T>) -> Self {
		if let Bound::Unbounded = start_bound {
			if let Bound::Unbounded = end_bound {
				return RangeFull {};
			} else {
				panic!("The end of a RangeFull must be Unbounded")
			}
		} else {
			panic!("The start of a RangeFull must be Unbounded")
		}
	}
}
impl<T> RangeBoundsExt<T> for RangeInclusive<T>
where
	T: PartialOrd,
{
	fn dummy(start_bound: Bound<T>, end_bound: Bound<T>) -> Self {
		if let Bound::Included(start) = start_bound {
			if let Bound::Included(end) = end_bound {
				return RangeInclusive::new(start, end);
			} else {
				panic!("The end of a RangeInclusive must be Included(_)")
			}
		} else {
			panic!("The start of a RangeInclusive must be Included(_)")
		}
	}
}
impl<T> RangeBoundsExt<T> for RangeTo<T>
where
	T: PartialOrd,
{
	fn dummy(start_bound: Bound<T>, end_bound: Bound<T>) -> Self {
		if let Bound::Unbounded = start_bound {
			if let Bound::Excluded(end) = end_bound {
				return RangeTo { end };
			} else {
				panic!("The end of a RangeTo must be Excluded(_)")
			}
		} else {
			panic!("The start of a RangeTo must be Unbounded")
		}
	}
}
impl<T> RangeBoundsExt<T> for RangeToInclusive<T>
where
	T: PartialOrd,
{
	fn dummy(start_bound: Bound<T>, end_bound: Bound<T>) -> Self {
		if let Bound::Unbounded = start_bound {
			if let Bound::Included(end) = end_bound {
				return RangeToInclusive { end };
			} else {
				panic!("The end of a RangeToInclusive must be Included(_)")
			}
		} else {
			panic!("The start of a RangeToInclusive must be Unbounded")
		}
	}
}
