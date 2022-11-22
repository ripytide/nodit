use std::ops::Bound;

pub trait BoundExt<T> {
	fn inner(&self) -> Option<&T>;
	fn is_unbounded(&self) -> bool;
}

impl<T> BoundExt<T> for Bound<T> {
	fn inner(&self) -> Option<&T> {
		match self {
			Bound::Included(inner) => Some(inner),
			Bound::Excluded(inner) => Some(inner),
			Bound::Unbounded => None,
		}
	}

	fn is_unbounded(&self) -> bool {
		match self {
			Bound::Unbounded => true,
			_ => false,
		}
	}
}
