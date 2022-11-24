use std::cmp::Ordering;
use std::ops::Bound;

pub enum StartBound<T> {
	Included(T),
	Excluded(T),
	Unbounded,
}

impl<T> StartBound<T> {
	pub fn inner(&self) -> Option<&T> {
		match self {
			StartBound::Included(inner) => Some(inner),
			StartBound::Excluded(inner) => Some(inner),
			StartBound::Unbounded => None,
		}
	}

	pub fn is_unbounded(&self) -> bool {
		match self {
			StartBound::Unbounded => true,
			_ => false,
		}
	}

	pub fn as_ref(&self) -> StartBound<&T> {
		match self {
			StartBound::Included(point) => StartBound::Included(point),
			StartBound::Excluded(point) => StartBound::Excluded(point),
			StartBound::Unbounded => StartBound::Unbounded,
		}
	}
}
impl<T> StartBound<&T>
where
	T: Clone,
{
	pub fn cloned(&self) -> StartBound<T> {
		match self {
			StartBound::Included(point) => StartBound::Included((*point).clone()),
			StartBound::Excluded(point) => StartBound::Excluded((*point).clone()),
			StartBound::Unbounded => StartBound::Unbounded,
		}
	}
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

impl<T> Eq for StartBound<T> where T: PartialEq {}

impl<T> PartialOrd for StartBound<T>
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

impl<T> Ord for StartBound<T>
where
	T: PartialOrd,
{
	fn cmp(&self, other: &Self) -> Ordering {
		self.partial_cmp(other).unwrap()
	}
}

impl<T> From<EndBound<T>> for StartBound<T> {
	fn from(end_bound: EndBound<T>) -> Self {
		match end_bound {
			EndBound::Included(point) => StartBound::Included(point),
			EndBound::Excluded(point) => StartBound::Excluded(point),
			EndBound::Unbounded => StartBound::Unbounded,
		}
	}
}
impl<T> From<Bound<T>> for StartBound<T> {
	fn from(bound: Bound<T>) -> Self {
		match bound {
			Bound::Included(point) => StartBound::Included(point),
			Bound::Excluded(point) => StartBound::Excluded(point),
			Bound::Unbounded => StartBound::Unbounded,
		}
	}
}
impl<T> From<StartBound<T>> for Bound<T> {
	fn from(start_bound: StartBound<T>) -> Bound<T> {
		match start_bound {
			StartBound::Included(point) => Bound::Included(point),
			StartBound::Excluded(point) => Bound::Excluded(point),
			StartBound::Unbounded => Bound::Unbounded,
		}
	}
}

pub enum EndBound<T> {
	Included(T),
	Excluded(T),
	Unbounded,
}

impl<T> EndBound<T> {
	pub fn inner(&self) -> Option<&T> {
		match self {
			EndBound::Included(inner) => Some(inner),
			EndBound::Excluded(inner) => Some(inner),
			EndBound::Unbounded => None,
		}
	}

	pub fn is_unbounded(&self) -> bool {
		match self {
			EndBound::Unbounded => true,
			_ => false,
		}
	}

	pub fn as_ref(&self) -> EndBound<&T> {
		match self {
			EndBound::Included(point) => EndBound::Included(point),
			EndBound::Excluded(point) => EndBound::Excluded(point),
			EndBound::Unbounded => EndBound::Unbounded,
		}
	}
}
impl<T> EndBound<&T>
where
	T: Clone,
{
	pub fn cloned(&self) -> EndBound<T> {
		match self {
			EndBound::Included(point) => EndBound::Included((*point).clone()),
			EndBound::Excluded(point) => EndBound::Excluded((*point).clone()),
			EndBound::Unbounded => EndBound::Unbounded,
		}
	}
}

impl<T> PartialEq for EndBound<T>
where
	T: PartialEq,
{
	fn eq(&self, other: &Self) -> bool {
		match (self.inner(), other.inner()) {
			(Some(end1), Some(end2)) => end1 == end2,
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
			(Some(end1), Some(end2)) => end1.partial_cmp(end2),
			(None, Some(_)) => Some(Ordering::Greater),
			(Some(_), None) => Some(Ordering::Less),
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

impl<T> From<StartBound<T>> for EndBound<T> {
	fn from(start_bound: StartBound<T>) -> Self {
		match start_bound {
			StartBound::Included(point) => EndBound::Included(point),
			StartBound::Excluded(point) => EndBound::Excluded(point),
			StartBound::Unbounded => EndBound::Unbounded,
		}
	}
}
impl<T> From<Bound<T>> for EndBound<T> {
	fn from(bound: Bound<T>) -> Self {
		match bound {
			Bound::Included(point) => EndBound::Included(point),
			Bound::Excluded(point) => EndBound::Excluded(point),
			Bound::Unbounded => EndBound::Unbounded,
		}
	}
}
impl<T> From<EndBound<T>> for Bound<T> {
	fn from(end_bound: EndBound<T>) -> Bound<T> {
		match end_bound {
			EndBound::Included(point) => Bound::Included(point),
			EndBound::Excluded(point) => Bound::Excluded(point),
			EndBound::Unbounded => Bound::Unbounded,
		}
	}
}
