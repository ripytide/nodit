use std::ops::{Bound, RangeBounds};

use crate::bound_ext::BoundExt;

pub trait RangeBoundsExt<T> {
	fn overlaps(&self, other: &Self) -> bool;
	fn get_pair(&self) -> (Bound<&T>, Bound<&T>);
}

impl<T, K> RangeBoundsExt<T> for K
where
	K: RangeBounds<T>,
	T: PartialOrd,
{
	fn get_pair(&self) -> (Bound<&T>, Bound<&T>) {
		(self.start_bound(), self.end_bound())
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
				(Bound::Excluded(start1), Bound::Excluded(end1)),
				(Bound::Excluded(start2), Bound::Excluded(end2)),
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
