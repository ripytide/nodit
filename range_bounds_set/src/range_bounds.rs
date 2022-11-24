use crate::bounds::{EndBound, StartBound};

pub trait RangeBounds<T>
where
	T: PartialOrd,
{
	fn start_bound(&self) -> StartBound<&T>;
	fn end_bound(&self) -> EndBound<&T>;
	fn get_pair(&self) -> (StartBound<&T>, EndBound<&T>) {
		(self.start_bound(), self.end_bound())
	}
	fn dummy(start_bound: StartBound<T>, end_bound: EndBound<T>) -> Self;
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
