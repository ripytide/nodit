//! A module containing [`ZosditMap`].

use alloc::boxed::Box;
use core::cmp::Ordering;
use core::fmt;
use core::marker::PhantomData;

use btree_monstrousity::btree_map::SearchBoundCustom;
use serde::de::{SeqAccess, Visitor};
use serde::ser::SerializeSeq;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use smallvec::SmallVec;

use crate::utils::{
	exclusive_comp_generator, inclusive_comp_generator, invalid_interval_panic,
};
use crate::{IntervalType, NoditMap, PointType};

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
/// let mut map = ZosditMap::from_slice_strict_back([
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ZosditMap<I, K, V> {
	nodit_map: NoditMap<I, K, ValueStore<V>>,
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
			nodit_map: NoditMap::new(),
		}
	}

	/// See [`NoditMap::len()`] for more details.
	pub fn len(&self) -> usize {
		self.nodit_map.len()
	}
	/// See [`NoditMap::is_empty()`] for more details.
	pub fn is_empty(&self) -> bool {
		self.nodit_map.is_empty()
	}

	/// Returns the first key-value pair in the map.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ii;
	/// use nodit::ZosditMap;
	///
	/// let map = ZosditMap::from_slice_strict_back([
	/// 	(ii(0, 4), -2),
	/// 	(ii(4, 4), -4),
	/// 	(ii(4, 4), -8),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(
	/// 	map.first_key_value(),
	/// 	Some((&ii(4, 4), &-2))
	/// );
	pub fn first_key_value(&self) -> Option<(&K, &V)> {
		let (key, value_store) = self.nodit_map.first_entry()?;

		let first_value = value_store.first()?;

		Some((key, first_value))
	}

	/// Returns the last key-value pair in the map.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ii;
	/// use nodit::ZosditMap;
	///
	/// let map = ZosditMap::from_slice_strict_back([
	/// 	(ii(0, 4), -2),
	/// 	(ii(4, 4), -4),
	/// 	(ii(4, 4), -8),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(
	/// 	map.last_key_value(),
	/// 	Some((&ii(4, 4), &-8))
	/// );
	pub fn last_key_value(&self) -> Option<(&K, &V)> {
		let (key, value_store) = self.nodit_map.last_entry()?;

		let last_value = value_store.last()?;

		Some((key, last_value))
	}

	/// Gets the last value stored in the `SmallVec` for the interval(s)
	/// that contain that point.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ii;
	/// use nodit::ZosditMap;
	///
	/// let map = ZosditMap::from_slice_strict_back([
	/// 	(ii(0, 4), -2),
	/// 	(ii(4, 4), -4),
	/// 	(ii(4, 4), -8),
	/// 	(ii(4, 8), -10),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(map.get_last_value_at_point(0), Some(&-2));
	/// assert_eq!(map.get_last_value_at_point(4), Some(&-10));
	/// assert_eq!(map.get_last_value_at_point(10), None);
	/// ```
	pub fn get_last_value_at_point(&self, point: I) -> Option<&V> {
		self.nodit_map
			.inner
			.lower_bound(
				exclusive_comp_generator(point, Ordering::Greater),
				SearchBoundCustom::Included,
			)
			.value()
			.and_then(|x| x.last())
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
	/// assert_eq!(map.insert_strict_back(ii(0, 10), -2), Ok(()));
	/// assert_eq!(map.insert_strict_back(ii(10, 10), -4), Ok(()));
	/// assert_eq!(map.insert_strict_back(ii(10, 10), -6), Ok(()));
	///
	/// assert_eq!(
	/// 	map.into_iter().collect::<Vec<_>>(),
	/// 	[(ii(0, 10), -2), (ii(10, 10), -4), (ii(10, 10), -6)]
	/// );
	/// ```
	pub fn insert_strict_back(
		&mut self,
		interval: K,
		value: V,
	) -> Result<(), NonZeroOverlapError<V>> {
		invalid_interval_panic(interval);

		if !self.is_zero_overlap(interval) {
			Err(NonZeroOverlapError { value })
		} else {
			self.nodit_map
				.inner
				.entry(interval, |inner_interval, new_interval| {
					let start_result = exclusive_comp_generator(
						new_interval.start(),
						Ordering::Greater,
					)(inner_interval);
					let end_result = exclusive_comp_generator(
						new_interval.end(),
						Ordering::Less,
					)(inner_interval);

					match (start_result, end_result) {
						(Ordering::Greater, Ordering::Less) => Ordering::Equal,
						(Ordering::Less, Ordering::Less) => Ordering::Less,
						(Ordering::Greater, Ordering::Greater) => {
							Ordering::Greater
						}

						//not possible with non-zero-overlap
						(Ordering::Less, Ordering::Greater) => unreachable!(),
						(Ordering::Equal, Ordering::Less) => unreachable!(),
						(Ordering::Greater, Ordering::Equal) => unreachable!(),
						(Ordering::Equal, Ordering::Greater) => unreachable!(),
						(Ordering::Equal, Ordering::Equal) => unreachable!(),
						(Ordering::Less, Ordering::Equal) => unreachable!(),
					}
				})
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
	/// assert_eq!(map.insert_strict_back(ii(0, 10), -2), Ok(()));
	/// assert_eq!(map.insert_strict_back(ii(10, 10), -4), Ok(()));
	/// assert_eq!(map.insert_strict_back(ii(10, 10), -6), Ok(()));
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
	pub fn is_zero_overlap<Q>(&self, interval: Q) -> bool
	where
		Q: IntervalType<I>,
	{
		invalid_interval_panic(interval);

		//i had to draw all the different combinations of intervals on a piece of paper to find
		//this elegant solution, there are a surprising amount of different scenarios when you
		//start considering zero-sized intervals and things

		self.nodit_map
			.inner
			.range(
				exclusive_comp_generator(interval.start(), Ordering::Greater),
				SearchBoundCustom::Included,
				exclusive_comp_generator(interval.end(), Ordering::Less),
				SearchBoundCustom::Included,
			)
			.next()
			.is_none()
	}

	/// The same as [`NoditMap::cut()`] except it flattens the `SmallVec`s of values into the
	/// returned iterator.
	///
	/// See [`NoditMap::cut()`] for more details.
	///
	/// # Panics
	///
	/// Panics if the given interval is an invalid interval. See [`Invalid
	/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ee, ii};
	/// use nodit::ZosditMap;
	///
	/// let mut base = ZosditMap::from_slice_strict_back([
	/// 	(ii(0, 4), -2),
	/// 	(ii(4, 4), -4),
	/// 	(ii(4, 4), -6),
	/// 	(ii(4, 8), -8),
	/// ])
	/// .unwrap();
	///
	/// let after_cut = ZosditMap::from_slice_strict_back([
	/// 	(ii(0, 2), -2),
	/// 	(ii(6, 8), -8),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(
	/// 	base.cut(ee(2, 6)).collect::<Vec<_>>(),
	/// 	[
	/// 		(ii(3, 4), -2),
	/// 		(ii(4, 4), -4),
	/// 		(ii(4, 4), -6),
	/// 		(ii(4, 5), -8)
	/// 	]
	/// );
	/// assert_eq!(base, after_cut);
	/// ```
	pub fn cut<'a, Q>(&'a mut self, interval: Q) -> impl Iterator<Item = (K, V)>
	where
		Q: IntervalType<I> + 'a,
		V: Clone,
	{
		invalid_interval_panic(interval);

		let cut = self.nodit_map.cut(interval);

		cut.flat_map(|(interval, value_store)| {
			value_store.into_iter().map(move |value| (interval, value))
		})
	}

	/// The same as [`NoditMap::overlapping()`] except it flattens the `SmallVec`s of values into
	/// the returned iterator.
	///
	/// See [`NoditMap::overlapping()`] for more details.
	///
	/// # Panics
	///
	/// Panics if the given interval is an invalid interval. See [`Invalid
	/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ee, ii};
	/// use nodit::ZosditMap;
	///
	/// let mut base = ZosditMap::from_slice_strict_back([
	/// 	(ii(0, 4), -2),
	/// 	(ii(4, 4), -4),
	/// 	(ii(4, 4), -6),
	/// 	(ii(4, 8), -8),
	/// 	(ii(8, 12), -10),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(
	/// 	base.overlapping(ii(4, 4)).collect::<Vec<_>>(),
	/// 	[
	/// 		(&ii(0, 4), &-2),
	/// 		(&ii(4, 4), &-4),
	/// 		(&ii(4, 4), &-6),
	/// 		(&ii(4, 8), &-8),
	/// 	]
	/// );
	/// ```
	pub fn overlapping<Q>(&self, interval: Q) -> impl Iterator<Item = (&K, &V)>
	where
		Q: IntervalType<I>,
	{
		invalid_interval_panic(interval);

		let overlapping = self.nodit_map.inner.range(
			inclusive_comp_generator(interval.start(), Ordering::Less),
			SearchBoundCustom::Included,
			inclusive_comp_generator(interval.end(), Ordering::Greater),
			SearchBoundCustom::Included,
		);

		overlapping.flat_map(|(interval, value_store)| {
			value_store.iter().map(move |value| (interval, value))
		})
	}

	/// Returns an iterator over every entry in the map in ascending
	/// order.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ie;
	/// use nodit::ZosditMap;
	///
	/// let map = ZosditMap::from_slice_strict_back([
	/// 	(ie(1, 4), -2),
	/// 	(ie(4, 8), -4),
	/// 	(ie(8, 100), -6),
	/// ])
	/// .unwrap();
	///
	/// let mut iter = map.iter();
	///
	/// assert_eq!(iter.next(), Some((&ie(1, 4), &-2)));
	/// assert_eq!(iter.next(), Some((&ie(4, 8), &-4)));
	/// assert_eq!(iter.next(), Some((&ie(8, 100), &-6)));
	/// assert_eq!(iter.next(), None);
	/// ```
	pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&K, &V)> {
		self.nodit_map.iter().flat_map(|(interval, value_store)| {
			value_store.iter().map(move |value| (interval, value))
		})
	}

	/// Allocates a `ZosditMap` and moves the given entries from the given
	/// slice into the map using [`ZosditMap::insert_strict_back()`].
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
	/// let map = ZosditMap::from_slice_strict_back([
	/// 	(ie(1, 4), -2),
	/// 	(ie(4, 8), -4),
	/// 	(ie(8, 100), -6),
	/// ])
	/// .unwrap();
	/// ```
	pub fn from_slice_strict_back<const N: usize>(
		slice: [(K, V); N],
	) -> Result<ZosditMap<I, K, V>, NonZeroOverlapError<V>> {
		ZosditMap::from_iter_strict_back(slice.into_iter())
	}

	/// Collects a `ZosditMap` from an iterator of (interval,
	/// value) tuples using [`Zosdit::insert_strict_back()`].
	///
	/// May return an `Err` while inserting. See
	/// [`NoditMap::insert_strict_back()`] for details.
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
	/// let slice = [(ie(1, 4), -2), (ie(4, 8), -4), (ie(8, 100), -6)];
	///
	/// let map: ZosditMap<_, _, _> = ZosditMap::from_iter_strict_back(
	/// 	slice
	/// 		.into_iter()
	/// 		.filter(|(interval, _)| interval.start() > 2),
	/// )
	/// .unwrap();
	/// ```
	pub fn from_iter_strict_back(
		iter: impl Iterator<Item = (K, V)>,
	) -> Result<ZosditMap<I, K, V>, NonZeroOverlapError<V>> {
		let mut map = ZosditMap::new();
		for (interval, value) in iter {
			map.insert_strict_back(interval, value)?;
		}
		return Ok(map);
	}
}

impl<I, K, V> Default for ZosditMap<I, K, V> {
	fn default() -> Self {
		ZosditMap {
			nodit_map: NoditMap::default(),
		}
	}
}

impl<I, K, V> IntoIterator for ZosditMap<I, K, V>
where
	I: PointType + 'static,
	K: IntervalType<I> + 'static,
	V: 'static,
{
	type Item = (K, V);
	type IntoIter = Box<dyn Iterator<Item = (K, V)>>;

	fn into_iter(self) -> Self::IntoIter {
		Box::new(self.nodit_map.into_iter().flat_map(
			|(interval, value_store)| {
				value_store.into_iter().map(move |value| (interval, value))
			},
		))
	}
}

impl<I, K, V> Serialize for ZosditMap<I, K, V>
where
	I: PointType,
	K: IntervalType<I> + Serialize,
	V: Serialize,
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let mut seq = serializer.serialize_seq(Some(self.len()))?;
		for (interval, value) in self.iter() {
			seq.serialize_element(&(interval, value))?;
		}
		seq.end()
	}
}

impl<'de, I, K, V> Deserialize<'de> for ZosditMap<I, K, V>
where
	I: PointType,
	K: IntervalType<I> + Deserialize<'de>,
	V: Deserialize<'de>,
{
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		deserializer.deserialize_seq(ZosditMapVisitor {
			i: PhantomData,
			k: PhantomData,
			v: PhantomData,
		})
	}
}

struct ZosditMapVisitor<I, K, V> {
	i: PhantomData<I>,
	k: PhantomData<K>,
	v: PhantomData<V>,
}

impl<'de, I, K, V> Visitor<'de> for ZosditMapVisitor<I, K, V>
where
	I: PointType,
	K: IntervalType<I> + Deserialize<'de>,
	V: Deserialize<'de>,
{
	type Value = ZosditMap<I, K, V>;

	fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
		formatter.write_str("a ZosditMap")
	}

	fn visit_seq<A>(self, mut access: A) -> Result<Self::Value, A::Error>
	where
		A: SeqAccess<'de>,
	{
		let mut map = ZosditMap::new();
		while let Some((interval, value)) = access.next_element()? {
			map.insert_strict_back(interval, value).or(Err(
				serde::de::Error::custom("intervals non-zero-overlap"),
			))?;
		}
		Ok(map)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::interval::ii;

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
				map.insert_strict_back(ii(mi_start, mi_end), ()).unwrap();
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
