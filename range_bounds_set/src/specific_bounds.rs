use std::cmp::Ordering;
use std::ops::{Bound, RangeBounds};

use crate::bound_ext::BoundExt;

pub enum EndBound<T> {
	Included(T),
	Excluded(T),
	Unbounded,
}

impl<T> PartialEq for EndBound<T>
where
	T: PartialEq,
{
	fn eq(&self, other: &Self) -> bool {
		match (self.inner(), other.inner()) {
			(Some(start1), Some(start2)) => start1 == start2,
			(None, None) => true,
			_ => false,
		}
	}
}

impl<T> Eq for EndBound<T> where T: PartialEq {}

impl<T> PartialOrd for EndBound<T>
where
	T: PartialOrd,
{
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		match (self.inner(), other.inner()) {
			//todo fix meh
			(Some(start1), Some(start2)) => start1.partial_cmp(start2),
			(None, Some(_)) => Some(Ordering::Less),
			(Some(_), None) => Some(Ordering::Greater),
			(None, None) => Some(Ordering::Equal),
		}
	}
}

impl<T> Ord for EndBound<T>
where
	T: PartialOrd,
{
	fn cmp(&self, other: &Self) -> Ordering {
		self.partial_cmp(other).unwrap()
	}
}

impl<T> RangeBounds<EndBound<T>> for (EndBound<T>, EndBound<T>) {
	fn start_bound(&self) -> Bound<&EndBound<T>> {
		self.0
	}
	fn end_bound(&self) -> Bound<&EndBound<T>> {
		self.1
	}
}

impl<T> BoundExt<T> for EndBound<T> {
	fn inner(&self) -> Option<&T> {
		match self {
			EndBound::Included(inner) => Some(inner),
			EndBound::Excluded(inner) => Some(inner),
			EndBound::Unbounded => None,
		}
	}

	fn is_unbounded(&self) -> bool {
		match self {
			EndBound::Unbounded => true,
			_ => false,
		}
	}
}

impl<T> From<Bound<T>> for EndBound<T> {
	fn from(value: Bound<T>) -> Self {
		match value {
			Bound::Included(item) => EndBound::Included(item),
			Bound::Excluded(item) => EndBound::Excluded(item),
			Bound::Unbounded => Self::Unbounded,
		}
	}
}
