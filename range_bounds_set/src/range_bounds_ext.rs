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

#[cfg(test)]
mod tests {
	use ranges::GenericRange;

	use super::*;
	use crate::test_helpers::all_valid_test_bounds;

	//we test our function against GenericRange's is_overlapping()
	//which we trust cuz y not lel
	#[test]
	fn mass_overlaps_test() {
		for range_bounds1 in all_valid_test_bounds() {
			for range_bounds2 in all_valid_test_bounds() {
				let mut trusted_answer = GenericRange::from(range_bounds1)
					.is_overlapping(&GenericRange::from(range_bounds2));

				let our_answer = range_bounds1.overlaps(&range_bounds2);

				//the only thing the "trusted" answer get wrong --__--
                if let (Bound::Included(start1), Bound::Included(end1)) = range_bounds1 &&
                   let (Bound::Included(start2), Bound::Included(end2)) = range_bounds2 &&
                   (start1 == end1) && (start2 == end2) && (end1 == start2)
                {
                    trusted_answer = true;
                }

				if our_answer != trusted_answer {
					dbg!(range_bounds1, range_bounds2);
					dbg!(trusted_answer, our_answer);
					panic!("Discrepency in .overlaps() detected!");
				}
			}
		}
	}
}
