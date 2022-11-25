use std::cmp::Ordering;
use std::ops::Bound;

pub enum StartBound<T> {
	Included(T),
	Excluded(T),
	Unbounded,
	//a workaround type used only for allowing bounded-unbounded range searches
	//in overlapping()
	ReverseUnbounded,
}

impl<T> StartBound<T> {
	pub fn inner(&self) -> Option<&T> {
		match self {
			StartBound::Included(inner) => Some(inner),
			StartBound::Excluded(inner) => Some(inner),
			_ => None,
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
			StartBound::ReverseUnbounded => StartBound::ReverseUnbounded,
		}
	}

	//when using this as an end value in a range search
	pub fn as_end_value(self) -> StartBound<T> {
		match self {
			StartBound::Included(point) => StartBound::Included(point),
			StartBound::Excluded(point) => StartBound::Excluded(point),
			//flip Unbounded with ReverseUnbounded
			StartBound::Unbounded => StartBound::ReverseUnbounded,
			StartBound::ReverseUnbounded => panic!("unsuitable operation"),
		}
	}
}
impl<T> StartBound<&T>
where
	T: Clone,
{
	pub fn cloned(&self) -> StartBound<T> {
		match self {
			StartBound::Included(point) => {
				StartBound::Included((*point).clone())
			}
			StartBound::Excluded(point) => {
				StartBound::Excluded((*point).clone())
			}
			StartBound::Unbounded => StartBound::Unbounded,
			StartBound::ReverseUnbounded => StartBound::ReverseUnbounded,
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

#[rustfmt::skip]
impl<T> PartialOrd for StartBound<T>
where
	T: PartialOrd,
{
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		match (self, other) {
			(StartBound::Included(start1), StartBound::Included(start2)) => start1.partial_cmp(start2),
			(StartBound::Excluded(start1), StartBound::Excluded(start2)) => start1.partial_cmp(start2),

			(StartBound::Included(start1), StartBound::Excluded(start2)) => partial_cmp_with_priority(start1, start2, true),
			(StartBound::Excluded(start1), StartBound::Included(start2)) => partial_cmp_with_priority(start1, start2, false),

			(StartBound::Included(_), StartBound::Unbounded) => Some(Ordering::Greater),
			(StartBound::Excluded(_), StartBound::Unbounded) => Some(Ordering::Greater),
            (StartBound::Unbounded, StartBound::Included(_)) => Some(Ordering::Less),
            (StartBound::Unbounded, StartBound::Excluded(_)) => Some(Ordering::Less),

			(StartBound::Included(_), StartBound::ReverseUnbounded) => Some(Ordering::Less),
			(StartBound::Excluded(_), StartBound::ReverseUnbounded) => Some(Ordering::Less),
            (StartBound::ReverseUnbounded, StartBound::Included(_)) => Some(Ordering::Greater),
            (StartBound::ReverseUnbounded, StartBound::Excluded(_)) => Some(Ordering::Greater),


			(StartBound::Unbounded, StartBound::Unbounded) => Some(Ordering::Equal),
			(StartBound::ReverseUnbounded, StartBound::ReverseUnbounded) => Some(Ordering::Equal),

			(StartBound::Unbounded, StartBound::ReverseUnbounded) => Some(Ordering::Less),
			(StartBound::ReverseUnbounded, StartBound::Unbounded) => Some(Ordering::Greater),
		}
	}
}

//if they are equal say the item with priority is larger
//where false means left has priority and true means right
fn partial_cmp_with_priority<T>(
	left: &T,
	right: &T,
	priority: bool,
) -> Option<Ordering>
where
	T: PartialOrd,
{
	let result = left.partial_cmp(right)?;

	Some(match result {
		Ordering::Equal => match priority {
			false => Ordering::Greater,
			true => Ordering::Less,
		},
		x => x,
	})
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
			EndBound::ReverseUnbounded => panic!("unsuitable operation"),
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
			StartBound::ReverseUnbounded => panic!("unsuitable operation"),
		}
	}
}

pub enum EndBound<T> {
	Included(T),
	Excluded(T),
	Unbounded,
	//a workaround type used only for allowing bounded-unbounded range searches
	//in overlapping()
	ReverseUnbounded,
}

impl<T> EndBound<T> {
	pub fn inner(&self) -> Option<&T> {
		match self {
			EndBound::Included(inner) => Some(inner),
			EndBound::Excluded(inner) => Some(inner),
			_ => None,
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
			EndBound::ReverseUnbounded => EndBound::ReverseUnbounded,
		}
	}

	//when using this as an start value in a range search
	pub fn as_start_value(self) -> EndBound<T> {
		match self {
			EndBound::Included(point) => EndBound::Included(point),
			EndBound::Excluded(point) => EndBound::Excluded(point),
			//flip Unbounded with ReverseUnbounded
			EndBound::Unbounded => EndBound::ReverseUnbounded,
			EndBound::ReverseUnbounded => EndBound::ReverseUnbounded,
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
			EndBound::ReverseUnbounded => EndBound::ReverseUnbounded,
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

#[rustfmt::skip]
impl<T> PartialOrd for EndBound<T>
where
	T: PartialOrd,
{
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		match (self, other) {
			(EndBound::Included(end1), EndBound::Included(end2)) => end1.partial_cmp(end2),
			(EndBound::Excluded(end1), EndBound::Excluded(end2)) => end1.partial_cmp(end2),

			(EndBound::Included(end1), EndBound::Excluded(end2)) => partial_cmp_with_priority(end1, end2, false),
			(EndBound::Excluded(end1), EndBound::Included(end2)) => partial_cmp_with_priority(end1, end2, true),

			(EndBound::Included(_), EndBound::Unbounded) => Some(Ordering::Less),
			(EndBound::Excluded(_), EndBound::Unbounded) => Some(Ordering::Less),
            (EndBound::Unbounded, EndBound::Included(_)) => Some(Ordering::Greater),
            (EndBound::Unbounded, EndBound::Excluded(_)) => Some(Ordering::Greater),

			(EndBound::Included(_), EndBound::ReverseUnbounded) => Some(Ordering::Greater),
			(EndBound::Excluded(_), EndBound::ReverseUnbounded) => Some(Ordering::Greater),
            (EndBound::ReverseUnbounded, EndBound::Included(_)) => Some(Ordering::Less),
            (EndBound::ReverseUnbounded, EndBound::Excluded(_)) => Some(Ordering::Less),


			(EndBound::Unbounded, EndBound::Unbounded) => Some(Ordering::Equal),
			(EndBound::ReverseUnbounded, EndBound::ReverseUnbounded) => Some(Ordering::Equal),

			(EndBound::Unbounded, EndBound::ReverseUnbounded) => Some(Ordering::Greater),
			(EndBound::ReverseUnbounded, EndBound::Unbounded) => Some(Ordering::Less),
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
			StartBound::ReverseUnbounded => EndBound::ReverseUnbounded,
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
			EndBound::ReverseUnbounded => {
				panic!("You can't convert SpecialErg to a Bound")
			}
		}
	}
}
