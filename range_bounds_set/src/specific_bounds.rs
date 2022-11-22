use std::cmp::Ordering;

use crate::bound_ext::BoundExt;

pub enum StartBound<T> {
	Included(T),
	Excluded(T),
	Unbounded,
}

impl<T> PartialEq for StartBound<T>
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

impl<T> PartialOrd for StartBound<T>
where
	T: PartialOrd,
{
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		match (self.inner(), other.inner()) {
			(Some(start1), Some(start2)) => start1.partial_cmp(start2),
			(None, Some(_)) => Some(Ordering::Less),
			(Some(_), None) => Some(Ordering::Greater),
			(None, None) => Some(Ordering::Equal),
		}
	}
}

impl<T> BoundExt<T> for StartBound<T> {
	fn inner(&self) -> Option<&T> {
		match self {
			StartBound::Included(inner) => Some(inner),
			StartBound::Excluded(inner) => Some(inner),
			StartBound::Unbounded => None,
		}
	}

	fn is_unbounded(&self) -> bool {
		match self {
			StartBound::Unbounded => true,
			_ => false,
		}
	}
}

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

impl<T> PartialOrd for EndBound<T>
where
	T: PartialOrd,
{
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		match (self.inner(), other.inner()) {
			(Some(start1), Some(start2)) => start1.partial_cmp(start2),
			(None, Some(_)) => Some(Ordering::Less),
			(Some(_), None) => Some(Ordering::Greater),
			(None, None) => Some(Ordering::Equal),
		}
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
