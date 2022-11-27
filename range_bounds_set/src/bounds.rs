use std::cmp::Ordering;
use std::ops::Bound;

#[derive(PartialEq, Debug)]
pub(crate) enum StartBound<T> {
	Included(T),
	Excluded(T),
	Unbounded,
	//workaround types used only as ends_bounds in meta-bound
	//StartBound range searches in overlapping() (non need for
	//reverseIncluded as it would be equivalent to normal included)
	ReverseExcluded(T),
	ReverseUnbounded,
}

impl<T> StartBound<T> {
	//when using this as an end value in a range search
	pub(crate) fn as_end_bound(self) -> StartBound<T> {
		match self {
			//flipping is unnecessary
			StartBound::Included(point) => StartBound::Included(point),
			//flip to Reverses
			StartBound::Excluded(point) => StartBound::ReverseExcluded(point),
			StartBound::Unbounded => StartBound::ReverseUnbounded,
			_ => panic!("unsuitable operation"),
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
			(StartBound::Included(start1), StartBound::Excluded(start2)) => partial_cmp_with_priority(start1, start2, true),
			(StartBound::Included(start1), StartBound::ReverseExcluded(start2)) => partial_cmp_with_priority(start1, start2, false),
			(StartBound::Included(_), StartBound::ReverseUnbounded) => Some(Ordering::Less),
			(StartBound::Included(_), StartBound::Unbounded) => Some(Ordering::Greater),

			(StartBound::Excluded(start1), StartBound::Excluded(start2)) => start1.partial_cmp(start2),
			(StartBound::Excluded(start1), StartBound::Included(start2)) => partial_cmp_with_priority(start1, start2, false),
			(StartBound::Excluded(start1), StartBound::ReverseExcluded(start2)) => partial_cmp_with_priority(start1, start2, false),
			(StartBound::Excluded(_), StartBound::Unbounded) => Some(Ordering::Greater),
			(StartBound::Excluded(_), StartBound::ReverseUnbounded) => Some(Ordering::Less),

            (StartBound::Unbounded, StartBound::Included(_)) => Some(Ordering::Less),
            (StartBound::Unbounded, StartBound::Excluded(_)) => Some(Ordering::Less),
            (StartBound::Unbounded, StartBound::ReverseExcluded(_)) => Some(Ordering::Less),
			(StartBound::Unbounded, StartBound::Unbounded) => Some(Ordering::Equal),
			(StartBound::Unbounded, StartBound::ReverseUnbounded) => Some(Ordering::Less),

			(StartBound::ReverseExcluded(start1), StartBound::ReverseExcluded(start2)) => start1.partial_cmp(start2),
			(StartBound::ReverseExcluded(start1), StartBound::Included(start2)) => partial_cmp_with_priority(start1, start2, true),
			(StartBound::ReverseExcluded(start1), StartBound::Excluded(start2)) => partial_cmp_with_priority(start1, start2, true),
			(StartBound::ReverseExcluded(_), StartBound::Unbounded) => Some(Ordering::Greater),
			(StartBound::ReverseExcluded(_), StartBound::ReverseUnbounded) => Some(Ordering::Less),

            (StartBound::ReverseUnbounded, StartBound::Included(_)) => Some(Ordering::Greater),
            (StartBound::ReverseUnbounded, StartBound::Excluded(_)) => Some(Ordering::Greater),
            (StartBound::ReverseUnbounded, StartBound::ReverseExcluded(_)) => Some(Ordering::Greater),
			(StartBound::ReverseUnbounded, StartBound::ReverseUnbounded) => Some(Ordering::Equal),
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
			_ => panic!("unsuitable operation"),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[rustfmt::skip]
	#[test]
	fn mass_start_bound_partial_ord_test() {
        //Included
		assert!(StartBound::Included(2) == StartBound::Included(2));
		assert!(StartBound::Included(2) <= StartBound::Included(2));
		assert!(StartBound::Included(2) >= StartBound::Included(2));
		assert!(StartBound::Included(0) < StartBound::Included(2));
		assert!(StartBound::Included(2) > StartBound::Included(0));

		assert!(StartBound::Included(2) < StartBound::Excluded(2));
		assert!(StartBound::Included(0) < StartBound::Excluded(2));
		assert!(StartBound::Included(2) > StartBound::Excluded(0));

		assert!(StartBound::Included(2) > StartBound::Unbounded);

		assert!(StartBound::Included(2) > StartBound::ReverseExcluded(2));
		assert!(StartBound::Included(0) < StartBound::ReverseExcluded(2));
		assert!(StartBound::Included(2) > StartBound::ReverseExcluded(0));

		assert!(StartBound::Included(2) < StartBound::ReverseUnbounded);

        //Exluded
		assert!(StartBound::Excluded(2) == StartBound::Excluded(2));
		assert!(StartBound::Excluded(2) <= StartBound::Excluded(2));
		assert!(StartBound::Excluded(2) >= StartBound::Excluded(2));
		assert!(StartBound::Excluded(0) < StartBound::Excluded(2));
		assert!(StartBound::Excluded(2) > StartBound::Excluded(0));

		assert!(StartBound::Excluded(2) > StartBound::Unbounded);

		assert!(StartBound::Excluded(2) > StartBound::ReverseExcluded(2));
		assert!(StartBound::Excluded(2) > StartBound::ReverseExcluded(0));
		assert!(StartBound::Excluded(0) < StartBound::ReverseExcluded(2));

		assert!(StartBound::Excluded(2) < StartBound::ReverseUnbounded);

        //Unbounded
		assert!(StartBound::Unbounded::<u8> == StartBound::Unbounded);
		assert!(StartBound::Unbounded::<u8> <= StartBound::Unbounded);
		assert!(StartBound::Unbounded::<u8> >= StartBound::Unbounded);

		assert!(StartBound::Unbounded < StartBound::ReverseExcluded(2));

		assert!(StartBound::Unbounded::<u8> < StartBound::ReverseUnbounded);

        //ReverseExcluded
		assert!(StartBound::ReverseExcluded(2) == StartBound::ReverseExcluded(2));
		assert!(StartBound::ReverseExcluded(2) <= StartBound::ReverseExcluded(2));
		assert!(StartBound::ReverseExcluded(2) >= StartBound::ReverseExcluded(2));
		assert!(StartBound::ReverseExcluded(0) < StartBound::ReverseExcluded(2));
		assert!(StartBound::ReverseExcluded(2) > StartBound::ReverseExcluded(0));

        //ReverseUnbounded
		assert!(StartBound::ReverseUnbounded::<u8> == StartBound::ReverseUnbounded);
		assert!(StartBound::ReverseUnbounded::<u8> <= StartBound::ReverseUnbounded);
		assert!(StartBound::ReverseUnbounded::<u8> >= StartBound::ReverseUnbounded);
	}
}
