use std::cmp::Ordering;
use std::ops::Bound;

#[derive(PartialEq)]
pub enum StartBound<T> {
	Included(T),
	Excluded(T),
	Unbounded,
	//a workaround type used only for allowing bounded-unbounded range searches
	//in overlapping()
	ReverseUnbounded,
}

impl<T> StartBound<T> {
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
