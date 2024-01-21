//! A module containing [`ZosditMap`].

use alloc::boxed::Box;
use core::cmp::Ordering;
use core::marker::PhantomData;

use btree_monstrousity::btree_map::SearchBoundCustom;
use btree_monstrousity::BTreeMap;
use smallvec::SmallVec;

use crate::utils::{double_comp, invalid_interval_panic};
use crate::{IntervalType, PointType};

type ValueStore<V> = SmallVec<[V; 2]>;

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
///
/// # Examples
/// ```
/// use nodit::interval::ie;
/// use nodit::ZosditMap;
///
/// // Make a map of intervals to booleans
/// let mut map = ZosditMap::from_slice_push_back([
/// 	(ie(4, 8), false),
/// 	(ie(8, 18), true),
/// 	(ie(20, 100), false),
/// ])
/// .unwrap();
///
/// // Iterate over the entries in the map
/// for (interval, value) in map.iter() {
/// 	println!("{interval:?}, {value:?}");
/// }
/// ```
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ZosditMap<I, K, V> {
	inner: BTreeMap<K, ValueStore<V>>,
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

	/// Appends the value to the `SmallVec` corresponding to the interval.
	///
	/// If the given interval non-zero-overlaps one or more intervals already in the
	/// map, then an [`NonzeroOverlapError`] is returned and the map is not
	/// updated.
	///
	/// If the given interval is singular and there is an identical singular interval entry already
	/// in the map then the value is appended to the back on the internal `SmallVec`.
	///
	/// # Panics
	///
	/// Panics if the given interval is an invalid interval. See [`Invalid
	/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ii;
	/// use nodit::ZosditMap;
	///
	/// let mut map = ZosditMap::new();
	///
	/// assert_eq!(map.insert_push_back(ii(0, 10), true), Ok(()));
	/// assert_eq!(map.insert_push_back(ii(10, 10), true), Ok(()));
	/// assert_eq!(map.insert_push_back(ii(10, 10), false), Ok(()));
	///
	/// assert_eq!(
	/// 	map.into_iter().collect::<Vec<_>>(),
	/// 	[(ii(0, 10), true), (ii(10, 10), true), (ii(10, 10), false)]
	/// );
	/// ```
	pub fn insert_push_back(
		&mut self,
		interval: K,
		value: V,
	) -> Result<(), NonZeroOverlapError<V>> {
		invalid_interval_panic(interval);

		if !self.is_zero_overlap(interval) {
			Err(NonZeroOverlapError { value })
		} else {
			self.inner
				.entry(interval, double_comp())
				.or_default()
				.push(value);

			Ok(())
		}
	}

	/// Returns `true` if the given interval zero-overlaps the intervals in
	/// the map, and `false` if not.
	///
	/// # Panics
	///
	/// Panics if the given interval is an invalid interval. See [`Invalid
	/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ii;
	/// use nodit::ZosditMap;
	///
	/// let mut map = ZosditMap::new();
	///
	/// assert_eq!(map.insert_push_back(ii(0, 10), true), Ok(()));
	/// assert_eq!(map.insert_push_back(ii(10, 10), true), Ok(()));
	/// assert_eq!(map.insert_push_back(ii(10, 10), false), Ok(()));
	///
	/// assert_eq!(map.is_zero_overlap(ii(0, 0)), true);
	/// assert_eq!(map.is_zero_overlap(ii(10, 10)), true);
	/// assert_eq!(map.is_zero_overlap(ii(10, 12)), true);
	/// assert_eq!(map.is_zero_overlap(ii(10, 12)), true);
	///
	/// assert_eq!(map.is_zero_overlap(ii(0, 2)), false);
	/// assert_eq!(map.is_zero_overlap(ii(4, 4)), false);
	/// assert_eq!(map.is_zero_overlap(ii(4, 12)), false);
	/// ```
	pub fn is_zero_overlap(&self, interval: K) -> bool {
		invalid_interval_panic(interval);

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

	/// Returns an iterator over every entry in the map in ascending
	/// order.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ie;
	/// use nodit::ZosditMap;
	///
	/// let map = ZosditMap::from_slice_push_back([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// let mut iter = map.iter();
	///
	/// assert_eq!(iter.next(), Some((&ie(1, 4), &false)));
	/// assert_eq!(iter.next(), Some((&ie(4, 8), &true)));
	/// assert_eq!(iter.next(), Some((&ie(8, 100), &false)));
	/// assert_eq!(iter.next(), None);
	/// ```
	pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
		self.inner.iter().flat_map(|(interval, value_store)| {
			value_store.iter().map(move |value| (interval, value))
		})
	}

	/// Allocates a `ZosditMap` and moves the given entries from the given
	/// slice into the map using [`ZosditMap::insert_push_back()`].
	///
	/// May return an `Err` while inserting. See
	/// [`NoditMap::insert_strict()`] for details.
	///
	/// # Panics
	///
	/// Panics if the given interval is an invalid interval. See [`Invalid
	/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ie;
	/// use nodit::ZosditMap;
	///
	/// let map = ZosditMap::from_slice_push_back([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	/// ```
	pub fn from_slice_push_back<const N: usize>(
		slice: [(K, V); N],
	) -> Result<ZosditMap<I, K, V>, NonZeroOverlapError<V>> {
		ZosditMap::from_iter_push_back(slice.into_iter())
	}

	/// Collects a `ZosditMap` from an iterator of (interval,
	/// value) tuples using [`Zosdit::insert_push_back()`].
	///
	/// May return an `Err` while inserting. See
	/// [`NoditMap::insert_push_back()`] for details.
	///
	/// # Panics
	///
	/// Panics if the given interval is an invalid interval. See [`Invalid
	/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ie;
	/// use nodit::ZosditMap;
	///
	/// let slice =
	/// 	[(ie(1, 4), false), (ie(4, 8), true), (ie(8, 100), false)];
	///
	/// let map: ZosditMap<_, _, _> = ZosditMap::from_iter_push_back(
	/// 	slice
	/// 		.into_iter()
	/// 		.filter(|(interval, _)| interval.start() > 2),
	/// )
	/// .unwrap();
	/// ```
	pub fn from_iter_push_back(
		iter: impl Iterator<Item = (K, V)>,
	) -> Result<ZosditMap<I, K, V>, NonZeroOverlapError<V>> {
		let mut map = ZosditMap::new();
		for (interval, value) in iter {
			map.insert_push_back(interval, value)?;
		}
		return Ok(map);
	}
}

impl<I, K, V> IntoIterator for ZosditMap<I, K, V>
where
	I: PointType,
	K: IntervalType<I> + 'static,
	V: 'static,
{
	type Item = (K, V);
	type IntoIter = Box<dyn Iterator<Item = (K, V)>>;

	fn into_iter(self) -> Self::IntoIter {
		Box::new(self.inner.into_iter().flat_map(|(interval, value_store)| {
			value_store.into_iter().map(move |value| (interval, value))
		}))
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
				map.inner.insert(
					ii(mi_start, mi_end),
					SmallVec::<[(); 2]>::new(),
					double_comp(),
				);
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
