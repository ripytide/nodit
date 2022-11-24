use crate::bounds::{EndBound, StartBound};

pub trait RangeBounds<T>
where
	T: PartialOrd,
{
	fn start_bound(&self) -> StartBound<&T>;
	fn end_bound(&self) -> EndBound<&T>;
	fn dummy(start_bound: StartBound<T>, end_bound: EndBound<T>) -> Self;

	fn get_pair(&self) -> (StartBound<&T>, EndBound<&T>) {
		(self.start_bound(), self.end_bound())
	}
	fn contains(&self, item: &T) -> bool {
		(match self.start_bound() {
			StartBound::Included(start) => start <= item,
			StartBound::Excluded(start) => start < item,
			StartBound::Unbounded => true,
		}) && (match self.end_bound() {
			EndBound::Included(end) => item <= end,
			EndBound::Excluded(end) => item < end,
			EndBound::Unbounded => true,
		})
	}
	fn overlaps(&self, other: &Self) -> bool {
		let self_start_contained = self
			.start_bound()
			.inner()
			.is_some_and(|start| other.contains(*start));
		let self_end_contained = self
			.end_bound()
			.inner()
			.is_some_and(|end| other.contains(*end));
		let other_start_contained = other
			.start_bound()
			.inner()
			.is_some_and(|start| self.contains(*start));
		let other_end_contained = other
			.end_bound()
			.inner()
			.is_some_and(|end| self.contains(*end));
		let double_unbounded = self.start_bound().is_unbounded()
			&& self.end_bound().is_unbounded()
			&& other.start_bound().is_unbounded()
			&& other.end_bound().is_unbounded();
		let same_exclusive = match (self.get_pair(), other.get_pair()) {
			(
				(StartBound::Excluded(start1), EndBound::Excluded(end1)),
				(StartBound::Excluded(start2), EndBound::Excluded(end2)),
			) if start1 == start2 && end1 == end2 => true,
			_ => false,
		};

		self_start_contained
			|| self_end_contained
			|| other_start_contained
			|| other_end_contained
			|| double_unbounded
			|| same_exclusive
	}
}

use std::ops::{
	Bound, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo,
	RangeToInclusive,
};

impl<T> RangeBounds<T> for (Bound<T>, Bound<T>)
where
	T: PartialOrd,
{
	//todo use Froms and AsRef stuff and functions to do this instead of bare
	//matching
	fn start_bound(&self) -> StartBound<&T> {
		match self.0 {
			Bound::Included(ref point) => StartBound::Included(point),
			Bound::Excluded(ref point) => StartBound::Excluded(point),
			Bound::Unbounded => StartBound::Unbounded,
		}
	}
	fn end_bound(&self) -> EndBound<&T> {
		match self.1 {
			Bound::Included(ref point) => EndBound::Included(point),
			Bound::Excluded(ref point) => EndBound::Excluded(point),
			Bound::Unbounded => EndBound::Unbounded,
		}
	}
	fn dummy(start_bound: StartBound<T>, end_bound: EndBound<T>) -> Self {
		(Bound::from(start_bound), Bound::from(end_bound))
	}
}
impl<T> RangeBounds<T> for Range<T>
where
	T: PartialOrd,
{
	fn start_bound(&self) -> StartBound<&T> {
		StartBound::Included(&self.start)
	}
	fn end_bound(&self) -> EndBound<&T> {
		EndBound::Excluded(&self.end)
	}
	fn dummy(start_bound: StartBound<T>, end_bound: EndBound<T>) -> Self {
		if let StartBound::Included(start) = start_bound {
			if let EndBound::Excluded(end) = end_bound {
				return Range { start, end };
			} else {
				panic!("The end of a Range must be Excluded(_)")
			}
		} else {
			panic!("The start of a Range must be Included(_)")
		}
	}
}
impl<T> RangeBounds<T> for RangeFrom<T>
where
	T: PartialOrd,
{
	fn start_bound(&self) -> StartBound<&T> {
		StartBound::Included(&self.start)
	}
	fn end_bound(&self) -> EndBound<&T> {
		EndBound::Unbounded
	}
	fn dummy(start_bound: StartBound<T>, end_bound: EndBound<T>) -> Self {
		if let StartBound::Included(start) = start_bound {
			if let EndBound::Unbounded = end_bound {
				return RangeFrom { start };
			} else {
				panic!("The end of a RangeFrom must be Unbounded")
			}
		} else {
			panic!("The start of a RangeFrom must be Included(_)")
		}
	}
}
impl<T> RangeBounds<T> for RangeFull
where
	T: PartialOrd,
{
	fn start_bound(&self) -> StartBound<&T> {
		StartBound::Unbounded
	}
	fn end_bound(&self) -> EndBound<&T> {
		EndBound::Unbounded
	}
	fn dummy(start_bound: StartBound<T>, end_bound: EndBound<T>) -> Self {
		if let StartBound::Unbounded = start_bound {
			if let EndBound::Unbounded = end_bound {
				return RangeFull {};
			} else {
				panic!("The end of a RangeFull must be Unbounded")
			}
		} else {
			panic!("The start of a RangeFull must be Unbounded")
		}
	}
}
impl<T> RangeBounds<T> for RangeInclusive<T>
where
	T: PartialOrd,
{
	fn start_bound(&self) -> StartBound<&T> {
		StartBound::Included(self.start())
	}
	fn end_bound(&self) -> EndBound<&T> {
		EndBound::Included(self.end())
	}
	fn dummy(start_bound: StartBound<T>, end_bound: EndBound<T>) -> Self {
		if let StartBound::Included(start) = start_bound {
			if let EndBound::Included(end) = end_bound {
				return RangeInclusive::new(start, end);
			} else {
				panic!("The end of a RangeInclusive must be Included(_)")
			}
		} else {
			panic!("The start of a RangeInclusive must be Included(_)")
		}
	}
}
impl<T> RangeBounds<T> for RangeTo<T>
where
	T: PartialOrd,
{
	fn start_bound(&self) -> StartBound<&T> {
		StartBound::Unbounded
	}
	fn end_bound(&self) -> EndBound<&T> {
		EndBound::Excluded(&self.end)
	}
	fn dummy(start_bound: StartBound<T>, end_bound: EndBound<T>) -> Self {
		if let StartBound::Unbounded = start_bound {
			if let EndBound::Excluded(end) = end_bound {
				return RangeTo { end };
			} else {
				panic!("The end of a RangeTo must be Excluded(_)")
			}
		} else {
			panic!("The start of a RangeTo must be Unbounded")
		}
	}
}
impl<T> RangeBounds<T> for RangeToInclusive<T>
where
	T: PartialOrd,
{
	fn start_bound(&self) -> StartBound<&T> {
		StartBound::Unbounded
	}
	fn end_bound(&self) -> EndBound<&T> {
		EndBound::Included(&self.end)
	}
	fn dummy(start_bound: StartBound<T>, end_bound: EndBound<T>) -> Self {
		if let StartBound::Unbounded = start_bound {
			if let EndBound::Included(end) = end_bound {
				return RangeToInclusive { end };
			} else {
				panic!("The end of a RangeToInclusive must be Included(_)")
			}
		} else {
			panic!("The start of a RangeToInclusive must be Unbounded")
		}
	}
}
