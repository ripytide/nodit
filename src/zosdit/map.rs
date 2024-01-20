//! A module containing [`ZosditMap`].

use core::cmp::Ordering;
use core::marker::PhantomData;

use btree_monstrousity::btree_map::SearchBoundCustom;
use btree_monstrousity::BTreeMap;

use crate::{IntervalType, PointType};

/// A Zero Overlap Sequential Discrete Interval Tree Map Data-Structure based off [`NoditMap`] and
/// [`SmallVec`]
///
/// `I` is the generic type parameter for the [`Ord`] type the `K`
/// type is a interval over.
///
/// `K` is the generic type parameter for the interval type stored as the
/// keys in the map.
///
/// `V` is the generic type parameter for the values associated with the
/// keys in the map.
///
/// Phrasing it another way: `I` is the point type, `K` is the interval type, and `V` is the value type.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ZosditMap<I, K, V> {
	inner: BTreeMap<K, V>,
	phantom: PhantomData<I>,
}

/// The error returned when inserting a interval that non-zero-overlaps another interval when it
/// should not have. Contains the value that was not inserted.
#[derive(PartialEq, Debug)]
pub struct NonZeroOverlapError<V> {
	/// The value which was not inserted, because of the overlap error.
	pub value: V,
}

impl<I, K, V> ZosditMap<I, K, V>
where
	I: PointType,
	K: IntervalType<I>,
{
	/// Makes a new, empty `ZosditMap`.
	///
	/// # Examples
	/// ```
	/// use nodit::{Interval, ZosditMap};
	///
	/// let map: ZosditMap<i8, Interval<i8>, bool> = ZosditMap::new();
	/// ```
	pub fn new() -> Self {
		ZosditMap {
			inner: BTreeMap::new(),
			phantom: PhantomData,
		}
	}

	/// Adds a new entry to the map without modifying other entries.
	///
	/// If the given interval non-zero-overlaps one or more intervals already in the
	/// map, then an [`NonzeroOverlapError`] is returned and the map is not
	/// updated.
	///
	/// If a zero-overlap is encountered *and* the given interval is singular
	/// ([`InclusiveInterval::is_singular()`]), the intervals value is pushed back onto the
	/// internal `SmallVec` for that entry.
	pub fn insert_push_back(
		&mut self,
		interval: I,
		value: V,
	) -> Result<(), NonZeroOverlapError<V>> {
		todo!()
	}

	/// Returns `true` if the given interval zero-overlaps the intervals in
	/// the map, and `false` if not.
	pub fn is_zero_overlap(&self, interval: K) -> bool {
		//i had to draw all the different combinations of intervals on a piece of paper to find
		//this elegant solution, there are a surprising amount of different scenarios when you
		//start considering zero-sized intervals and things

		let comp_generator = |point, extraneous_result| {
			move |inner_interval: &K| {
				if point == inner_interval.start()
					&& point == inner_interval.end()
				{
					extraneous_result
				} else if point <= inner_interval.start() {
					Ordering::Less
				} else if point >= inner_interval.end() {
					Ordering::Greater
				} else {
					Ordering::Equal
				}
			}
		};

		let start_bound = SearchBoundCustom::Included;
		let end_bound = SearchBoundCustom::Included;

		self.inner
			.range(
				comp_generator(interval.start(), Ordering::Greater),
				start_bound,
				comp_generator(interval.end(), Ordering::Less),
				end_bound,
			)
			.next()
			.is_none()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::interval::ii;
	use crate::utils::double_comp;

	#[test]
	fn is_nonzero_overlap_tests() {
		let test_cases = [
			((4, 10), vec![], true),
			((4, 10), vec![(3, 5)], false),
			((4, 10), vec![(3, 11)], false),
			((4, 10), vec![(3, 4)], true),
			((4, 10), vec![(4, 5)], false),
			((4, 10), vec![(10, 11)], true),
			((4, 10), vec![(9, 10)], false),
			((4, 10), vec![(3, 11)], false),
			((4, 10), vec![(4, 10)], false),
			((4, 10), vec![(5, 9)], false),
			((4, 10), vec![(3, 5), (9, 11)], false),
			((4, 10), vec![(4, 5), (9, 10)], false),
			((4, 10), vec![(3, 4), (10, 11)], true),
			//zero sized search
			((4, 4), vec![(3, 3)], true),
			((4, 4), vec![(4, 4)], true),
			((4, 4), vec![(5, 5)], true),
			((4, 4), vec![(3, 4)], true),
			((4, 4), vec![(4, 5)], true),
			((4, 4), vec![(3, 5)], false),
		];

		for ((start, end), map_intervals, expected) in test_cases {
			let mut map = ZosditMap::new();
			for (mi_start, mi_end) in map_intervals.clone() {
				map.inner.insert(ii(mi_start, mi_end), (), double_comp());
			}

			let search_interval = ii(start, end);

			let result = map.is_zero_overlap(search_interval);

			if result != expected {
				dbg!(&search_interval, map_intervals);
				panic!("result not equal to expected")
			}
		}
	}
}
