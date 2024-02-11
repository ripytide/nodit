//! A module containing [`NoditMap`].

use alloc::vec::Vec;
use core::marker::PhantomData;

use btree_monstrousity::btree_map::{
	IntoIter as BTreeMapIntoIter, SearchBoundCustom,
};
use btree_monstrousity::BTreeMap;
use itertools::Itertools;

use crate::utils::{
	cut_interval, invalid_interval_panic, overlapping_comp, starts_comp,
	touching_end_comp, touching_start_comp,
};
use crate::{DiscreteFinite, InclusiveInterval, Interval};

/// An ordered map of non-overlapping intervals based on [`BTreeMap`].
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
/// use nodit::NoditMap;
///
/// // Make a map of intervals to booleans
/// let mut map = NoditMap::from_slice_strict([
/// 	(ie(4, 8), false),
/// 	(ie(8, 18), true),
/// 	(ie(20, 100), false),
/// ])
/// .unwrap();
///
/// // Change a value in the map
/// *map.get_at_point_mut(7).unwrap() = true;
///
/// if map.contains_point(99) {
/// 	println!("Map contains value at 99 :)");
/// }
///
/// // Iterate over the entries in the map
/// for (interval, value) in map.iter() {
/// 	println!("{interval:?}, {value:?}");
/// }
/// ```
///
/// [`BTreeMap`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NoditMap<I, K, V> {
	pub(crate) inner: BTreeMap<K, V>,
	phantom: PhantomData<I>,
}

/// The error returned when inserting a interval that overlaps another interval when
/// it should not have. Contains the value that was not inserted.
#[derive(PartialEq, Debug)]
pub struct OverlapError<V> {
	/// The value which was not inserted, because of the overlap error.
	pub value: V,
}

/// The marker trait for valid point types, a blanket implementation is provided for all types
/// which implement this traits' super-traits so you shouln't need to implement this yourself.
pub trait PointType: Ord + Copy + DiscreteFinite {}
impl<I> PointType for I where I: Ord + Copy + DiscreteFinite {}

/// The marker trait for valid interval types, a blanket implementation is provided for all types
/// which implement this traits' super-traits so you shouln't need to implement this yourself.
pub trait IntervalType<I>: InclusiveInterval<I> {}
impl<I, K> IntervalType<I> for K
where
	I: PointType,
	K: InclusiveInterval<I> + Copy + From<Interval<I>>,
{
}

impl<I, K, V> NoditMap<I, K, V>
where
	I: PointType,
	K: IntervalType<I>,
{
	/// Returns `true` if the given interval overlaps any of the
	/// intervals in the map, and `false` if not.
	///
	/// # Panics
	///
	/// Panics if the given interval is an invalid interval. See [`Invalid
	/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ie, ii};
	/// use nodit::NoditMap;
	///
	/// let mut map = NoditMap::new();
	///
	/// map.insert_strict(ie(5, 10), false);
	///
	/// assert_eq!(map.overlaps(ii(1, 3)), false);
	/// assert_eq!(map.overlaps(ie(4, 5)), false);
	///
	/// assert_eq!(map.overlaps(ii(4, 5)), true);
	/// assert_eq!(map.overlaps(ie(4, 6)), true);
	/// ```
	pub fn overlaps<Q>(&self, interval: Q) -> bool
	where
		Q: IntervalType<I>,
	{
		invalid_interval_panic(interval);

		self.overlapping(interval).next().is_some()
	}

	/// Returns an iterator over every entry in the map that overlaps
	/// the given interval in ascending order.
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
	/// use nodit::NoditMap;
	///
	/// let map = NoditMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// let mut overlapping = map.overlapping(ie(2, 8));
	///
	/// assert_eq!(
	/// 	overlapping.collect::<Vec<_>>(),
	/// 	[(&ie(1, 4), &false), (&ie(4, 8), &true)]
	/// );
	/// ```
	pub fn overlapping<Q>(
		&self,
		interval: Q,
	) -> impl DoubleEndedIterator<Item = (&K, &V)>
	where
		Q: IntervalType<I>,
	{
		invalid_interval_panic(interval);

		self.inner.range(
			overlapping_comp(interval.start()),
			SearchBoundCustom::Included,
			overlapping_comp(interval.end()),
			SearchBoundCustom::Included,
		)
	}

	/// Returns an mutable iterator over every entry in the map that
	/// overlaps the given interval in ascending order.
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
	/// use nodit::NoditMap;
	///
	/// let mut map = NoditMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// for (interval, value) in map.overlapping_mut(ie(3, 7)) {
	/// 	if *interval == ie(4, 8) {
	/// 		*value = false
	/// 	} else {
	/// 		*value = true
	/// 	}
	/// }
	/// ```
	pub fn overlapping_mut<Q>(
		&mut self,
		interval: Q,
	) -> impl DoubleEndedIterator<Item = (&K, &mut V)>
	where
		Q: IntervalType<I>,
	{
		invalid_interval_panic(interval);

		self.inner.range_mut(
			overlapping_comp(interval.start()),
			SearchBoundCustom::Included,
			overlapping_comp(interval.end()),
			SearchBoundCustom::Included,
		)
	}

	/// Returns a reference to the value corresponding to the interval in
	/// the map that overlaps the given point, if any.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ie;
	/// use nodit::NoditMap;
	///
	/// let map = NoditMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(map.get_at_point(3), Some(&false));
	/// assert_eq!(map.get_at_point(4), Some(&true));
	/// assert_eq!(map.get_at_point(101), None);
	/// ```
	pub fn get_at_point(&self, point: I) -> Option<&V> {
		self.get_key_value_at_point(point)
			.map(|(_, value)| value)
			.ok()
	}

	/// Returns a mutable reference to the value corresponding to the
	/// interval that overlaps the given point, if any.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ie;
	/// use nodit::NoditMap;
	/// let mut map =
	/// 	NoditMap::from_slice_strict([(ie(1, 4), false)]).unwrap();
	///
	/// if let Some(x) = map.get_at_point_mut(2) {
	/// 	*x = true;
	/// }
	///
	/// assert_eq!(map.get_at_point(1), Some(&true));
	/// ```
	pub fn get_at_point_mut(&mut self, point: I) -> Option<&mut V> {
		self.inner.get_mut(overlapping_comp(point))
	}

	/// Returns `true` if the map contains a interval that overlaps the
	/// given point, and `false` if not.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ie;
	/// use nodit::NoditMap;
	///
	/// let map = NoditMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(map.contains_point(3), true);
	/// assert_eq!(map.contains_point(4), true);
	/// assert_eq!(map.contains_point(101), false);
	/// ```
	pub fn contains_point(&self, point: I) -> bool {
		self.get_key_value_at_point(point).is_ok()
	}

	/// Returns the entry corresponding to the interval that
	/// overlaps the given point, if any.
	///
	/// If there is no interval that overlaps the given point the
	/// maximally-sized gap at the given point is returned.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ie, iu};
	/// use nodit::NoditMap;
	///
	/// let map = NoditMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 6), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(
	/// 	map.get_key_value_at_point(3),
	/// 	Ok((&ie(1, 4), &false))
	/// );
	/// assert_eq!(map.get_key_value_at_point(5), Ok((&ie(4, 6), &true)));
	/// assert_eq!(map.get_key_value_at_point(7), Err(ie(6, 8)));
	/// assert_eq!(map.get_key_value_at_point(101), Err(iu(100)));
	/// ```
	pub fn get_key_value_at_point(&self, point: I) -> Result<(&K, &V), K> {
		self.inner
			.get_key_value(overlapping_comp(point))
			.ok_or_else(|| K::from(self.get_gap_at_raw(point)))
	}
	fn get_gap_at_raw(&self, point: I) -> Interval<I> {
		let lower = self
			.inner
			.upper_bound(overlapping_comp(point), SearchBoundCustom::Included);
		let upper = self
			.inner
			.lower_bound(overlapping_comp(point), SearchBoundCustom::Included);

		Interval {
			start: lower
				.key()
				.map_or(I::MIN, |lower| lower.end().up().unwrap()),
			end: upper
				.key()
				.map_or(I::MAX, |upper| upper.start().down().unwrap()),
		}
	}

	/// Removes every entry in the map which overlaps the given interval
	/// and returns them in an iterator in ascending order.
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
	/// use nodit::NoditMap;
	///
	/// let mut map = NoditMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// let mut removed = map.remove_overlapping(ie(2, 8));
	///
	/// assert_eq!(
	/// 	removed.collect::<Vec<_>>(),
	/// 	[(ie(1, 4), false), (ie(4, 8), true)]
	/// );
	///
	/// assert_eq!(
	/// 	map.into_iter().collect::<Vec<_>>(),
	/// 	[(ie(8, 100), false)]
	/// );
	/// ```
	pub fn remove_overlapping<'a, Q>(
		&'a mut self,
		interval: Q,
	) -> impl Iterator<Item = (K, V)>
	where
		Q: IntervalType<I> + 'a,
	{
		invalid_interval_panic(interval);

		let mut result = Vec::new();

		let mut cursor = self.inner.lower_bound_mut(
			overlapping_comp(interval.start()),
			SearchBoundCustom::Included,
		);

		while cursor
			.key()
			.is_some_and(|inner_interval| interval.overlaps(inner_interval))
		{
			result.push(cursor.remove_current().unwrap());
		}

		return result.into_iter();
	}

	/// Cuts a given interval out of the map and returns an iterator of the full or
	/// partial intervals with their values that were cut in ascending order.
	///
	/// `V` must implement `Clone` as if you try to cut out the center
	/// of a interval in the map it will split into two different entries
	/// using `Clone`. Or if you partially cut a interval then
	/// `V` must be cloned to be returned in the iterator.
	///
	/// # Panics
	///
	/// Panics if the given interval is an invalid interval. See [`Invalid
	/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ie, ii};
	/// use nodit::NoditMap;
	///
	/// let mut base = NoditMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// let after_cut = NoditMap::from_slice_strict([
	/// 	(ie(1, 2), false),
	/// 	(ie(40, 100), false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(
	/// 	base.cut(ie(2, 40)).collect::<Vec<_>>(),
	/// 	[(ie(2, 4), false), (ie(4, 8), true), (ie(8, 40), false),]
	/// );
	/// assert_eq!(base, after_cut);
	/// ```
	pub fn cut<'a, Q>(&'a mut self, interval: Q) -> impl Iterator<Item = (K, V)>
	where
		Q: IntervalType<I> + 'a,
		V: Clone,
	{
		invalid_interval_panic(interval);

		let mut result = Vec::new();

		let mut cursor = self.inner.lower_bound_mut(
			overlapping_comp(interval.start()),
			SearchBoundCustom::Included,
		);

		while let Some(key) = cursor.key() {
			if !key.overlaps(&interval) {
				break;
			}

			let (key, value) = cursor.remove_current().unwrap();

			let cut_result = cut_interval(key, interval);

			if let Some(before_cut) = cut_result.before_cut {
				cursor.insert_before(K::from(before_cut), value.clone());
			}
			if let Some(after_cut) = cut_result.after_cut {
				cursor.insert_before(K::from(after_cut), value.clone());
			}

			result.push((K::from(cut_result.inside_cut.unwrap()), value));
		}

		result.into_iter()
	}

	/// Returns an iterator of all the gaps in the map that overlap the given
	/// `interval` in ascending order.
	///
	/// See [`NoditMap::gaps_trimmed()`] if you require the returned
	/// gaps to be trimmed to be fully contained within given `interval`.
	///
	/// # Panics
	///
	/// Panics if the given interval is an invalid interval. See [`Invalid
	/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ie, ii, iu};
	/// use nodit::NoditMap;
	///
	/// let map = NoditMap::from_slice_strict([
	/// 	(ie(1, 3), false),
	/// 	(ie(5, 7), true),
	/// 	(ie(9, 100), false),
	/// ])
	/// .unwrap();
	///
	/// let mut gaps = map.gaps_untrimmed(ii(4, 120));
	///
	/// assert_eq!(
	/// 	gaps.collect::<Vec<_>>(),
	/// 	[ie(3, 5), ie(7, 9), iu(100)]
	/// );
	/// ```
	pub fn gaps_untrimmed<'a, Q>(
		&'a self,
		interval: Q,
	) -> impl Iterator<Item = K> + '_
	where
		Q: IntervalType<I> + 'a,
	{
		invalid_interval_panic(interval);

		// If the start or end point of interval is not
		// contained within a interval in the map then we need to
		// generate the gaps.
		let start_gap =
			(!self.inner.contains_key(overlapping_comp(interval.start())))
				.then(|| self.get_gap_at_raw(interval.start()));
		let end_gap =
			(!self.inner.contains_key(overlapping_comp(interval.end())))
				.then(|| self.get_gap_at_raw(interval.end()));

		let (start_gap, end_gap) = match (start_gap, end_gap) {
			(Some(start_gap), Some(end_gap)) => {
				if start_gap.start() == end_gap.start() {
					//it's the same gap
					(Some(start_gap), None)
				} else {
					//it's different gaps
					(Some(start_gap), Some(end_gap))
				}
			}
			(Some(start_gap), None) => (Some(start_gap), None),
			(None, Some(end_gap)) => (None, Some(end_gap)),
			(None, None) => (None, None),
		};

		let overlapping = self
			.overlapping(interval)
			.map(|(key, _)| (key.start(), key.end()));

		let inner_gaps = overlapping
			.tuple_windows()
			.map(|(first, second)| {
				K::from(Interval {
					start: first.1.up().unwrap(),
					end: second.0.down().unwrap(),
				})
			})
			.filter(|interval| interval.is_valid());

		//possibly add the trimmed start and end gaps
		start_gap
			.map(K::from)
			.into_iter()
			.chain(inner_gaps)
			.chain(end_gap.map(K::from))
	}

	/// Returns an iterator of all the gaps in the map that overlap the given
	/// `interval` that are also trimmed so they are all fully contained within the
	/// given `interval`, in ascending order.
	///
	/// See [`NoditMap::gaps_untrimmed()`] if you do not want the
	/// returned gaps to be trimmed.
	///
	/// # Panics
	///
	/// Panics if the given interval is an invalid interval. See [`Invalid
	/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::{ie, ii, iu};
	/// use nodit::NoditMap;
	///
	/// let map = NoditMap::from_slice_strict([
	/// 	(ie(1, 3), false),
	/// 	(ie(5, 7), true),
	/// 	(ie(9, 100), false),
	/// ])
	/// .unwrap();
	///
	/// let mut gaps = map.gaps_trimmed(ii(4, 120));
	///
	/// assert_eq!(
	/// 	gaps.collect::<Vec<_>>(),
	/// 	[ie(4, 5), ie(7, 9), ii(100, 120)]
	/// );
	/// ```
	pub fn gaps_trimmed<'a, Q>(
		&'a self,
		interval: Q,
	) -> impl Iterator<Item = K> + '_
	where
		Q: IntervalType<I> + 'a,
	{
		invalid_interval_panic(interval);

		// If the start or end point of interval is not
		// contained within a interval in the map then we need to
		// generate the gaps.
		let start_gap =
			(!self.inner.contains_key(overlapping_comp(interval.start())))
				.then(|| self.get_gap_at_raw(interval.start()));
		let end_gap =
			(!self.inner.contains_key(overlapping_comp(interval.end())))
				.then(|| self.get_gap_at_raw(interval.end()));

		let (trimmed_start_gap, trimmed_end_gap) = match (start_gap, end_gap) {
			(Some(mut start_gap), Some(mut end_gap)) => {
				if start_gap.start() == end_gap.start() {
					//it's the same gap
					start_gap.start = interval.start();
					start_gap.end = interval.end();

					(Some(start_gap), None)
				} else {
					//it's different gaps
					start_gap.start = interval.start();
					end_gap.end = interval.end();

					(Some(start_gap), Some(end_gap))
				}
			}
			(Some(mut start_gap), None) => {
				start_gap.start = interval.start();
				(Some(start_gap), None)
			}
			(None, Some(mut end_gap)) => {
				end_gap.end = interval.end();
				(None, Some(end_gap))
			}
			(None, None) => (None, None),
		};

		let overlapping = self
			.overlapping(interval)
			.map(|(key, _)| (key.start(), key.end()));

		let inner_gaps = overlapping
			.tuple_windows()
			.map(|(first, second)| {
				K::from(Interval {
					start: first.1.up().unwrap(),
					end: second.0.down().unwrap(),
				})
			})
			.filter(|interval| interval.is_valid());

		//possibly add the trimmed start and end gaps
		trimmed_start_gap
			.map(K::from)
			.into_iter()
			.chain(inner_gaps)
			.chain(trimmed_end_gap.map(K::from))
	}

	/// Returns `true` if the map covers every point in the given
	/// interval, and `false` if it does not.
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
	/// use nodit::NoditMap;
	///
	/// let map = NoditMap::from_slice_strict([
	/// 	(ie(1, 3), false),
	/// 	(ie(5, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(map.contains_interval(ie(1, 3)), true);
	/// assert_eq!(map.contains_interval(ie(2, 6)), false);
	/// assert_eq!(map.contains_interval(ie(6, 100)), true);
	/// ```
	pub fn contains_interval<Q>(&self, interval: Q) -> bool
	where
		Q: IntervalType<I>,
	{
		invalid_interval_panic(interval);

		// Soooo clean and mathematical!
		self.gaps_untrimmed(interval).next().is_none()
	}

	/// Adds a new entry to the map without modifying other entries.
	///
	/// If the given interval overlaps one or more intervals already in the
	/// map, then an [`OverlapError`] is returned and the map is not
	/// updated.
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
	/// use nodit::{NoditMap, OverlapError};
	///
	/// let mut map = NoditMap::new();
	///
	/// assert_eq!(map.insert_strict(ie(5, 10), 9), Ok(()));
	/// assert_eq!(
	/// 	map.insert_strict(ie(5, 10), 2),
	/// 	Err(OverlapError { value: 2 })
	/// );
	/// assert_eq!(map.len(), 1);
	/// ```
	pub fn insert_strict(
		&mut self,
		interval: K,
		value: V,
	) -> Result<(), OverlapError<V>> {
		invalid_interval_panic(interval);

		if self.overlaps(interval) {
			return Err(OverlapError { value });
		}

		self.insert_unchecked(interval, value);

		Ok(())
	}
	fn insert_unchecked(&mut self, interval: K, value: V) {
		self.inner.insert(interval, value, starts_comp());
	}

	fn insert_merge_with_comps<G1, G2, R1, R2>(
		&mut self,
		interval: K,
		value: V,
		get_start: G1,
		get_end: G2,
		remove_start: R1,
		remove_end: R2,
	) -> K
	where
		G1: FnOnce(&Self, &V) -> Option<K>,
		G2: FnOnce(&Self, &V) -> Option<K>,
		R1: FnOnce(&mut Self, &V),
		R2: FnOnce(&mut Self, &V),
	{
		invalid_interval_panic(interval);

		let matching_start = get_start(self, &value);
		let matching_end = get_end(self, &value);

		let returning = match (matching_start, matching_end) {
			(Some(matching_start), Some(matching_end)) => K::from(Interval {
				start: matching_start.start(),
				end: matching_end.end(),
			}),
			(Some(matching_start), None) => K::from(Interval {
				start: matching_start.start(),
				end: interval.end(),
			}),
			(None, Some(matching_end)) => K::from(Interval {
				start: interval.start(),
				end: matching_end.end(),
			}),
			(None, None) => interval,
		};

		let _ = self.remove_overlapping(interval);

		remove_start(self, &value);
		remove_end(self, &value);

		self.insert_unchecked(returning, value);

		returning
	}

	/// Adds a new entry to the map and merges into other intervals in
	/// the map which touch it.
	///
	/// The value of the merged-together interval is set to the value given for
	/// this insertion.
	///
	/// If successful then the newly inserted (possibly merged) interval is
	/// returned.
	///
	/// If the given interval overlaps one or more intervals already in the
	/// map, then an [`OverlapError`] is returned and the map is not
	/// updated.
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
	/// use nodit::{NoditMap, OverlapError};
	///
	/// let mut map = NoditMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(6, 8), true),
	/// ])
	/// .unwrap();
	///
	/// // Touching
	/// assert_eq!(
	/// 	map.insert_merge_touching(ie(4, 6), true),
	/// 	Ok(ie(1, 8))
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching(ie(4, 8), false),
	/// 	Err(OverlapError { value: false }),
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching(ie(10, 16), false),
	/// 	Ok(ie(10, 16))
	/// );
	///
	/// assert_eq!(
	/// 	map.into_iter().collect::<Vec<_>>(),
	/// 	[(ie(1, 8), true), (ie(10, 16), false)]
	/// );
	/// ```
	pub fn insert_merge_touching(
		&mut self,
		interval: K,
		value: V,
	) -> Result<K, OverlapError<V>> {
		invalid_interval_panic(interval);

		if self.overlaps(interval) {
			return Err(OverlapError { value });
		}

		Ok(self.insert_merge_with_comps(
			interval,
			value,
			|selfy, _| {
				selfy
					.inner
					.get_key_value(touching_start_comp(interval.start()))
					.map(|(key, _)| key)
					.copied()
			},
			|selfy, _| {
				selfy
					.inner
					.get_key_value(touching_end_comp(interval.end()))
					.map(|(key, _)| key)
					.copied()
			},
			|selfy, _| {
				selfy.inner.remove(touching_start_comp(interval.start()));
			},
			|selfy, _| {
				selfy.inner.remove(touching_end_comp(interval.end()));
			},
		))
	}

	/// Adds a new entry to the map and merges into other intervals in
	/// the map which touch it if the touching intervals' values are
	/// equal to the value being inserted.
	///
	/// If successful then the newly inserted (possibly merged) interval is
	/// returned.
	///
	/// If the given interval overlaps one or more intervals already in the
	/// map, then an [`OverlapError`] is returned and the map is not
	/// updated.
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
	/// use nodit::{NoditMap, OverlapError};
	///
	/// let mut map = NoditMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(6, 8), true),
	/// ])
	/// .unwrap();
	///
	/// // Touching
	/// assert_eq!(
	/// 	map.insert_merge_touching_if_values_equal(ie(4, 6), true),
	/// 	Ok(ie(4, 8))
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching_if_values_equal(ie(4, 8), false),
	/// 	Err(OverlapError { value: false }),
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching_if_values_equal(ie(10, 16), false),
	/// 	Ok(ie(10, 16))
	/// );
	///
	/// assert_eq!(
	/// 	map.into_iter().collect::<Vec<_>>(),
	/// 	[(ie(1, 4), false), (ie(4, 8), true), (ie(10, 16), false)]
	/// );
	/// ```
	pub fn insert_merge_touching_if_values_equal(
		&mut self,
		interval: K,
		value: V,
	) -> Result<K, OverlapError<V>>
	where
		V: Eq,
	{
		invalid_interval_panic(interval);

		if self.overlaps(interval) {
			return Err(OverlapError { value });
		}

		let get_start = |selfy: &Self, value: &V| {
			selfy
				.inner
				.get_key_value(touching_start_comp(interval.start()))
				.filter(|(_, start_touching_value)| {
					*start_touching_value == value
				})
				.map(|(key, _)| key)
				.copied()
		};
		let get_end = |selfy: &Self, value: &V| {
			selfy
				.inner
				.get_key_value(touching_end_comp(interval.end()))
				.filter(|(_, start_touching_value)| {
					*start_touching_value == value
				})
				.map(|(key, _)| key)
				.copied()
		};

		Ok(self.insert_merge_with_comps(
			interval,
			value,
			get_start,
			get_end,
			|selfy, value| {
				if get_start(selfy, value).is_some() {
					selfy.inner.remove(touching_start_comp(interval.start()));
				}
			},
			|selfy, value| {
				if get_end(selfy, value).is_some() {
					selfy.inner.remove(touching_end_comp(interval.end()));
				}
			},
		))
	}

	/// Adds a new entry to the map and merges into other intervals in
	/// the map which overlap it.
	///
	/// The value of the merged-together interval is set to the value given for
	/// this insertion.
	///
	/// The newly inserted (possibly merged) interval is returned.
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
	/// use nodit::{NoditMap, OverlapError};
	///
	/// let mut map = NoditMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(6, 8), true),
	/// ])
	/// .unwrap();
	///
	/// // Touching
	/// assert_eq!(
	/// 	map.insert_merge_overlapping(ie(4, 6), true),
	/// 	ie(4, 6)
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_overlapping(ie(4, 8), false),
	/// 	ie(4, 8)
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_overlapping(ie(10, 16), false),
	/// 	ie(10, 16)
	/// );
	///
	/// assert_eq!(
	/// 	map.into_iter().collect::<Vec<_>>(),
	/// 	[(ie(1, 4), false), (ie(4, 8), false), (ie(10, 16), false)]
	/// );
	/// ```
	pub fn insert_merge_overlapping(&mut self, interval: K, value: V) -> K {
		invalid_interval_panic(interval);

		self.insert_merge_with_comps(
			interval,
			value,
			|selfy, _| {
				selfy
					.inner
					.get_key_value(overlapping_comp(interval.start()))
					.map(|(key, _)| key)
					.copied()
			},
			|selfy, _| {
				selfy
					.inner
					.get_key_value(overlapping_comp(interval.end()))
					.map(|(key, _)| key)
					.copied()
			},
			|_, _| {},
			|_, _| {},
		)
	}

	/// Adds a new entry to the map and merges into other intervals in
	/// the map which touch or overlap it.
	///
	/// The value of the merged-together interval is set to the value given for
	/// this insertion.
	///
	/// The newly inserted (possibly merged) interval is returned.
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
	/// use nodit::{NoditMap, OverlapError};
	///
	/// let mut map = NoditMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(6, 8), true),
	/// ])
	/// .unwrap();
	///
	/// // Touching
	/// assert_eq!(
	/// 	map.insert_merge_touching_or_overlapping(ie(4, 6), true),
	/// 	ie(1, 8)
	/// );
	///
	/// // Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching_or_overlapping(ie(4, 8), false),
	/// 	ie(1, 8)
	/// );
	///
	/// // Neither Touching or Overlapping
	/// assert_eq!(
	/// 	map.insert_merge_touching_or_overlapping(ie(10, 16), false),
	/// 	ie(10, 16)
	/// );
	///
	/// assert_eq!(
	/// 	map.into_iter().collect::<Vec<_>>(),
	/// 	[(ie(1, 8), false), (ie(10, 16), false)]
	/// );
	/// ```
	pub fn insert_merge_touching_or_overlapping(
		&mut self,
		interval: K,
		value: V,
	) -> K {
		invalid_interval_panic(interval);

		self.insert_merge_with_comps(
			interval,
			value,
			|selfy, _| {
				selfy
					.inner
					.get_key_value(touching_start_comp(interval.start()))
					.map(|(key, _)| key)
					.or(selfy
						.inner
						.get_key_value(overlapping_comp(interval.start()))
						.map(|(key, _)| key))
					.copied()
			},
			|selfy, _| {
				selfy
					.inner
					.get_key_value(touching_end_comp(interval.end()))
					.map(|(key, _)| key)
					.or(selfy
						.inner
						.get_key_value(overlapping_comp(interval.end()))
						.map(|(key, _)| key))
					.copied()
			},
			|selfy, _| {
				selfy.inner.remove(touching_start_comp(interval.start()));
			},
			|selfy, _| {
				selfy.inner.remove(touching_end_comp(interval.end()));
			},
		)
	}

	/// Adds a new entry to the map and overwrites any other intervals
	/// that overlap the new interval.
	///
	/// Returns an iterator over the full or partial cut entries in
	/// ascending order.
	///
	/// This is equivalent to using [`NoditMap::cut()`]
	/// followed by [`NoditMap::insert_strict()`]. Hence the
	/// same `V: Clone` trait bound applies.
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
	/// use nodit::NoditMap;
	///
	/// let mut map =
	/// 	NoditMap::from_slice_strict([(ie(2, 8), false)]).unwrap();
	///
	/// map.insert_overwrite(ie(4, 6), true);
	///
	/// assert_eq!(
	/// 	map.into_iter().collect::<Vec<_>>(),
	/// 	[(ie(2, 4), false), (ie(4, 6), true), (ie(6, 8), false)]
	/// );
	/// ```
	pub fn insert_overwrite(
		&mut self,
		interval: K,
		value: V,
	) -> impl Iterator<Item = (K, V)>
	where
		V: Clone,
	{
		invalid_interval_panic(interval);

		let cut = self.cut(interval);
		self.insert_unchecked(interval, value);
		cut
	}

	/// Allocates a `NoditMap` and moves the given entries from
	/// the given slice into the map using
	/// [`NoditMap::insert_strict()`].
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
	/// use nodit::NoditMap;
	///
	/// let map = NoditMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	/// ```
	pub fn from_slice_strict<const N: usize>(
		slice: [(K, V); N],
	) -> Result<NoditMap<I, K, V>, OverlapError<V>> {
		NoditMap::from_iter_strict(slice.into_iter())
	}

	/// Collects a `NoditMap` from an iterator of (interval,
	/// value) tuples using [`NoditMap::insert_strict()`].
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
	/// use nodit::NoditMap;
	///
	/// let slice =
	/// 	[(ie(1, 4), false), (ie(4, 8), true), (ie(8, 100), false)];
	///
	/// let map: NoditMap<_, _, _> = NoditMap::from_iter_strict(
	/// 	slice
	/// 		.into_iter()
	/// 		.filter(|(interval, _)| interval.start() > 2),
	/// )
	/// .unwrap();
	/// ```
	pub fn from_iter_strict(
		iter: impl Iterator<Item = (K, V)>,
	) -> Result<NoditMap<I, K, V>, OverlapError<V>> {
		let mut map = NoditMap::new();
		for (interval, value) in iter {
			map.insert_strict(interval, value)?;
		}
		Ok(map)
	}
}

impl<I, K, V> NoditMap<I, K, V> {
	/// Makes a new, empty [`NoditMap`].
	///
	/// # Examples
	/// ```
	/// use nodit::{Interval, NoditMap};
	///
	/// let map: NoditMap<i8, Interval<i8>, bool> = NoditMap::new();
	/// ```
	pub fn new() -> Self {
		Self::default()
	}

	/// Returns the number of intervals in the map.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ie;
	/// use nodit::NoditMap;
	///
	/// let mut map = NoditMap::new();
	///
	/// assert_eq!(map.len(), 0);
	/// map.insert_strict(ie(0, 1), false).unwrap();
	/// assert_eq!(map.len(), 1);
	/// ```
	pub fn len(&self) -> usize {
		self.inner.len()
	}

	/// Returns `true` if the map contains no intervals, and
	/// `false` if it does.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ie;
	/// use nodit::NoditMap;
	///
	/// let mut map = NoditMap::new();
	///
	/// assert_eq!(map.is_empty(), true);
	/// map.insert_strict(ie(0, 1), false).unwrap();
	/// assert_eq!(map.is_empty(), false);
	/// ```
	pub fn is_empty(&self) -> bool {
		self.inner.is_empty()
	}

	/// Returns an iterator over every entry in the map in ascending
	/// order.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ie;
	/// use nodit::NoditMap;
	///
	/// let map = NoditMap::from_slice_strict([
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
	pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&K, &V)> {
		self.inner.iter()
	}

	/// Returns an mutable iterator over every entry in the map in
	/// ascending order.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ie;
	/// use nodit::NoditMap;
	///
	/// let mut map = NoditMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// for (interval, value) in map.iter_mut() {
	/// 	if *interval == ie(4, 8) {
	/// 		*value = false
	/// 	} else {
	/// 		*value = true
	/// 	}
	/// }
	/// ```
	pub fn iter_mut(
		&mut self,
	) -> impl DoubleEndedIterator<Item = (&K, &mut V)> {
		self.inner.iter_mut()
	}

	/// Returns the first entry in the map, if any.
	///
	/// # Examples
	/// ```
	/// use nodit::interval::ie;
	/// use nodit::NoditMap;
	///
	/// let map = NoditMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(map.first_key_value(), Some((&ie(1, 4), &false)));
	/// ```
	pub fn first_key_value(&self) -> Option<(&K, &V)> {
		self.inner.first_key_value()
	}

	/// Returns the last entry in the map, if any.
	///
	/// # Examples
	/// ```
	/// use nodit::NoditMap;
	/// use nodit::interval::ie;
	///
	/// let map = NoditMap::from_slice_strict([
	/// 	(ie(1, 4), false),
	/// 	(ie(4, 8), true),
	/// 	(ie(8, 100), false),
	/// ])
	/// .unwrap();
	///
	/// assert_eq!(
	/// 	map.last_key_value(),
	/// 	Some((&ie(8, 100), &false))
	/// );
	pub fn last_key_value(&self) -> Option<(&K, &V)> {
		self.inner.last_key_value()
	}
}

// Trait Impls ==========================

impl<I, K, V> IntoIterator for NoditMap<I, K, V> {
	type Item = (K, V);
	type IntoIter = IntoIter<I, K, V>;
	fn into_iter(self) -> Self::IntoIter {
		IntoIter {
			inner: self.inner.into_iter(),
			phantom: PhantomData,
		}
	}
}
/// An owning iterator over the entries of a [`NoditMap`].
///
/// This `struct` is created by the [`into_iter`] method on
/// [`NoditMap`] (provided by the [`IntoIterator`] trait). See
/// its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
pub struct IntoIter<I, K, V> {
	inner: BTreeMapIntoIter<K, V>,
	phantom: PhantomData<I>,
}
impl<I, K, V> Iterator for IntoIter<I, K, V> {
	type Item = (K, V);
	fn next(&mut self) -> Option<Self::Item> {
		self.inner.next()
	}
}

impl<I, K, V> Default for NoditMap<I, K, V> {
	fn default() -> Self {
		NoditMap {
			inner: BTreeMap::default(),
			phantom: PhantomData,
		}
	}
}

#[cfg(feature = "serde")]
mod serde {
	use core::marker::PhantomData;

	use serde::de::{SeqAccess, Visitor};
	use serde::ser::SerializeSeq;
	use serde::{Deserialize, Deserializer, Serialize, Serializer};

	use crate::{IntervalType, NoditMap, PointType};

	impl<I, K, V> Serialize for NoditMap<I, K, V>
	where
		K: Serialize,
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

	impl<'de, I, K, V> Deserialize<'de> for NoditMap<I, K, V>
	where
		I: PointType,
		K: IntervalType<I> + Deserialize<'de>,
		V: Deserialize<'de>,
	{
		fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
		where
			D: Deserializer<'de>,
		{
			deserializer.deserialize_seq(NoditMapVisitor {
				i: PhantomData,
				k: PhantomData,
				v: PhantomData,
			})
		}
	}

	struct NoditMapVisitor<I, K, V> {
		i: PhantomData<I>,
		k: PhantomData<K>,
		v: PhantomData<V>,
	}

	impl<'de, I, K, V> Visitor<'de> for NoditMapVisitor<I, K, V>
	where
		I: PointType,
		K: IntervalType<I> + Deserialize<'de>,
		V: Deserialize<'de>,
	{
		type Value = NoditMap<I, K, V>;

		fn expecting(
			&self,
			formatter: &mut alloc::fmt::Formatter,
		) -> alloc::fmt::Result {
			formatter.write_str("a NoditMap")
		}

		fn visit_seq<A>(self, mut access: A) -> Result<Self::Value, A::Error>
		where
			A: SeqAccess<'de>,
		{
			let mut map = NoditMap::new();
			while let Some((interval, value)) = access.next_element()? {
				map.insert_strict(interval, value)
					.or(Err(serde::de::Error::custom("intervals overlap")))?;
			}
			Ok(map)
		}
	}
}

#[cfg(test)]
mod tests {
	use pretty_assertions::assert_eq;

	use super::*;
	use crate::interval::{ee, ei, ie, ii, iu, ue, ui, uu};
	use crate::utils::{config, contains_point, Config, CutResult};

	//only every other number to allow mathematical_overlapping_definition
	//to test between bounds in finite using smaller intervalled finite
	pub(crate) const NUMBERS: &[i8] = &[2, 4, 6, 8, 10];
	//go a bit around on either side to compensate for Unbounded
	pub(crate) const NUMBERS_DOMAIN: &[i8] =
		&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

	fn basic() -> NoditMap<i8, Interval<i8>, bool> {
		NoditMap::from_slice_strict([
			(ui(4), false),
			(ee(5, 7), true),
			(ii(7, 7), false),
			(ie(14, 16), true),
		])
		.unwrap()
	}
	fn basic_slice() -> [(Interval<i8>, bool); 4] {
		[
			(ui(4), false),
			(ee(5, 7), true),
			(ii(7, 7), false),
			(ie(14, 16), true),
		]
	}

	#[test]
	fn insert_strict_tests() {
		assert_insert_strict(
			basic(),
			(ii(0, 4), false),
			Err(OverlapError { value: false }),
			basic_slice(),
		);
		assert_insert_strict(
			basic(),
			(ii(5, 6), false),
			Err(OverlapError { value: false }),
			basic_slice(),
		);
		assert_insert_strict(
			basic(),
			(ii(4, 5), true),
			Err(OverlapError { value: true }),
			basic_slice(),
		);
		assert_insert_strict(
			basic(),
			(ei(4, 5), true),
			Ok(()),
			[
				(ui(4), false),
				(ei(4, 5), true),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			],
		);
	}
	fn assert_insert_strict<const N: usize>(
		mut before: NoditMap<i8, Interval<i8>, bool>,
		to_insert: (Interval<i8>, bool),
		result: Result<(), OverlapError<bool>>,
		after: [(Interval<i8>, bool); N],
	) {
		assert_eq!(before.insert_strict(to_insert.0, to_insert.1), result);
		assert_eq!(before, NoditMap::from_slice_strict(after).unwrap())
	}

	#[test]
	fn overlapping_tests() {
		//case zero
		for overlap_interval in all_valid_test_bounds() {
			//you can't overlap nothing
			assert!(
				NoditMap::<i8, Interval<i8>, ()>::new()
					.overlapping(overlap_interval)
					.next()
					.is_none()
			);
		}

		//case one
		for overlap_interval in all_valid_test_bounds() {
			for inside_interval in all_valid_test_bounds() {
				let mut map = NoditMap::new();
				map.insert_strict(inside_interval, ()).unwrap();

				let mut expected_overlapping = Vec::new();
				if overlap_interval.overlaps(&inside_interval) {
					expected_overlapping.push(inside_interval);
				}

				let overlapping = map
					.overlapping(overlap_interval)
					.map(|(key, _)| key)
					.copied()
					.collect::<Vec<_>>();

				if overlapping != expected_overlapping {
					dbg!(overlap_interval, inside_interval);
					dbg!(overlapping, expected_overlapping);
					panic!(
						"Discrepancy in .overlapping() with single inside interval detected!"
					);
				}
			}
		}

		//case two
		for overlap_interval in all_valid_test_bounds() {
			for (inside_interval1, inside_interval2) in
				all_non_overlapping_test_bound_entries()
			{
				let mut map = NoditMap::new();
				map.insert_strict(inside_interval1, ()).unwrap();
				map.insert_strict(inside_interval2, ()).unwrap();

				let mut expected_overlapping = Vec::new();
				if overlap_interval.overlaps(&inside_interval1) {
					expected_overlapping.push(inside_interval1);
				}
				if overlap_interval.overlaps(&inside_interval2) {
					expected_overlapping.push(inside_interval2);
				}
				//make our expected_overlapping the correct order
				if expected_overlapping.len() > 1
					&& expected_overlapping[0].start()
						> expected_overlapping[1].start()
				{
					expected_overlapping.swap(0, 1);
				}

				let overlapping = map
					.overlapping(overlap_interval)
					.map(|(key, _)| key)
					.copied()
					.collect::<Vec<_>>();

				if overlapping != expected_overlapping {
					dbg!(overlap_interval, inside_interval1, inside_interval2);
					dbg!(overlapping, expected_overlapping);
					panic!(
						"Discrepancy in .overlapping() with two inside intervals detected!"
					);
				}
			}
		}
	}

	#[test]
	fn remove_overlapping_tests() {
		assert_remove_overlapping(basic(), ii(5, 5), [], basic_slice());
		assert_remove_overlapping(
			basic(),
			uu(),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			],
			[],
		);
		assert_remove_overlapping(
			basic(),
			ii(6, 7),
			[(ee(5, 7), true), (ii(7, 7), false)],
			[(ui(4), false), (ie(14, 16), true)],
		);
		assert_remove_overlapping(
			basic(),
			iu(6),
			[(ee(5, 7), true), (ii(7, 7), false), (ie(14, 16), true)],
			[(ui(4), false)],
		);
	}
	fn assert_remove_overlapping<const N: usize, const Y: usize>(
		mut before: NoditMap<i8, Interval<i8>, bool>,
		to_remove: Interval<i8>,
		result: [(Interval<i8>, bool); N],
		after: [(Interval<i8>, bool); Y],
	) {
		assert_eq!(
			before.remove_overlapping(to_remove).collect::<Vec<_>>(),
			result
		);
		assert_eq!(before, NoditMap::from_slice_strict(after).unwrap())
	}

	#[test]
	fn cut_tests() {
		assert_cut(
			basic(),
			ii(50, 60),
			[],
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			],
		);
		assert_cut(
			basic(),
			uu(),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			],
			[],
		);
		assert_cut(
			basic(),
			ui(6),
			[(ui(4), false), (ei(5, 6), true)],
			[(ii(7, 7), false), (ie(14, 16), true)],
		);
		assert_cut(
			basic(),
			iu(6),
			[(ie(6, 7), true), (ii(7, 7), false), (ie(14, 16), true)],
			[(ui(4), false)],
		);
	}
	fn assert_cut<const N: usize, const Y: usize>(
		mut before: NoditMap<i8, Interval<i8>, bool>,
		to_cut: Interval<i8>,
		result: [(Interval<i8>, bool); Y],
		after: [(Interval<i8>, bool); N],
	) {
		assert_eq!(before.cut(to_cut).collect::<Vec<_>>(), result);
		assert_eq!(before, NoditMap::from_slice_strict(after).unwrap());
	}

	#[test]
	fn gaps_untrimmed_tests() {
		assert_gaps_untrimmed(basic(), ii(50, 60), [iu(16)]);
		assert_gaps_untrimmed(basic(), iu(50), [iu(16)]);
		assert_gaps_untrimmed(basic(), ee(3, 16), [ei(4, 5), ee(7, 14)]);
		assert_gaps_untrimmed(
			basic(),
			ei(3, 16),
			[ei(4, 5), ee(7, 14), iu(16)],
		);
		assert_gaps_untrimmed(basic(), ue(5), []);
		assert_gaps_untrimmed(basic(), ui(3), []);
		assert_gaps_untrimmed(basic(), ii(5, 5), [ii(5, 5)]);
		assert_gaps_untrimmed(basic(), ii(6, 6), []);
		assert_gaps_untrimmed(basic(), ii(7, 7), []);
		assert_gaps_untrimmed(basic(), ii(8, 8), [ii(8, 13)]);

		assert_gaps_untrimmed(
			basic(),
			ii(i8::MIN, i8::MAX),
			[ei(4, 5), ee(7, 14), ii(16, i8::MAX)],
		);
		assert_eq!(
			NoditMap::from_slice_strict([(ii(i8::MIN, i8::MAX), false)])
				.unwrap()
				.gaps_trimmed(uu())
				.collect::<Vec<_>>(),
			[]
		);
	}
	fn assert_gaps_untrimmed<const N: usize>(
		map: NoditMap<i8, Interval<i8>, bool>,
		interval: Interval<i8>,
		result: [Interval<i8>; N],
	) {
		assert_eq!(map.gaps_untrimmed(interval).collect::<Vec<_>>(), result);
	}

	#[test]
	fn gaps_trimmed_tests() {
		assert_gaps_trimmed(basic(), ii(50, 60), [ii(50, 60)]);
		assert_gaps_trimmed(basic(), iu(50), [iu(50)]);
		assert_gaps_trimmed(basic(), ee(3, 16), [ei(4, 5), ee(7, 14)]);
		assert_gaps_trimmed(
			basic(),
			ei(3, 16),
			[ei(4, 5), ee(7, 14), ii(16, 16)],
		);
		assert_gaps_trimmed(basic(), ue(5), []);
		assert_gaps_trimmed(basic(), ui(3), []);
		assert_gaps_trimmed(basic(), ii(5, 5), [ii(5, 5)]);
		assert_gaps_trimmed(basic(), ii(6, 6), []);
		assert_gaps_trimmed(basic(), ii(7, 7), []);
		assert_gaps_trimmed(basic(), ii(8, 8), [ii(8, 8)]);

		assert_gaps_trimmed(
			basic(),
			ii(i8::MIN, i8::MAX),
			[ei(4, 5), ee(7, 14), ii(16, i8::MAX)],
		);
		assert_eq!(
			NoditMap::from_slice_strict([(ii(i8::MIN, i8::MAX), false)])
				.unwrap()
				.gaps_trimmed(uu())
				.collect::<Vec<_>>(),
			[]
		);
	}
	fn assert_gaps_trimmed<const N: usize>(
		map: NoditMap<i8, Interval<i8>, bool>,
		interval: Interval<i8>,
		result: [Interval<i8>; N],
	) {
		assert_eq!(map.gaps_trimmed(interval).collect::<Vec<_>>(), result);
	}

	#[test]
	fn insert_merge_touching_tests() {
		assert_insert_merge_touching(
			basic(),
			(ii(0, 4), false),
			Err(OverlapError { value: false }),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			],
		);
		assert_insert_merge_touching(
			basic(),
			(ee(7, 10), false),
			Ok(ie(7, 10)),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ie(7, 10), false),
				(ie(14, 16), true),
			],
		);
		assert_insert_merge_touching(
			basic(),
			(ee(7, 11), true),
			Ok(ie(7, 11)),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ie(7, 11), true),
				(ie(14, 16), true),
			],
		);
		assert_insert_merge_touching(
			basic(),
			(ee(7, 14), false),
			Ok(ie(7, 16)),
			[(ui(4), false), (ee(5, 7), true), (ie(7, 16), false)],
		);
	}
	fn assert_insert_merge_touching<const N: usize>(
		mut before: NoditMap<i8, Interval<i8>, bool>,
		to_insert: (Interval<i8>, bool),
		result: Result<Interval<i8>, OverlapError<bool>>,
		after: [(Interval<i8>, bool); N],
	) {
		assert_eq!(
			before.insert_merge_touching(to_insert.0, to_insert.1),
			result
		);
		assert_eq!(before, NoditMap::from_slice_strict(after).unwrap())
	}
	#[test]
	fn insert_merge_touching_if_values_equal_tests() {
		assert_insert_merge_touching_if_values_equal(
			basic(),
			(ii(0, 4), false),
			Err(OverlapError { value: false }),
			basic_slice(),
		);
		dbg!("hererere");
		assert_insert_merge_touching_if_values_equal(
			basic(),
			(ee(7, 10), false),
			Ok(ie(7, 10)),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ie(7, 10), false),
				(ie(14, 16), true),
			],
		);
		assert_insert_merge_touching_if_values_equal(
			basic(),
			(ee(7, 11), true),
			Ok(ee(7, 11)),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ee(7, 11), true),
				(ie(14, 16), true),
			],
		);
		assert_insert_merge_touching_if_values_equal(
			basic(),
			(ee(7, 14), false),
			Ok(ie(7, 14)),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ie(7, 14), false),
				(ie(14, 16), true),
			],
		);
	}
	fn assert_insert_merge_touching_if_values_equal<const N: usize>(
		mut before: NoditMap<i8, Interval<i8>, bool>,
		to_insert: (Interval<i8>, bool),
		result: Result<Interval<i8>, OverlapError<bool>>,
		after: [(Interval<i8>, bool); N],
	) {
		assert_eq!(
			before.insert_merge_touching_if_values_equal(
				to_insert.0,
				to_insert.1
			),
			result
		);
		assert_eq!(before, NoditMap::from_slice_strict(after).unwrap())
	}

	#[test]
	fn insert_merge_overlapping_tests() {
		assert_insert_merge_overlapping(
			basic(),
			(ii(0, 2), true),
			ui(4),
			[
				(ui(4), true),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			],
		);
		assert_insert_merge_overlapping(
			basic(),
			(ie(14, 16), false),
			ie(14, 16),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), false),
			],
		);
		assert_insert_merge_overlapping(
			basic(),
			(ii(6, 11), false),
			ei(5, 11),
			[(ui(4), false), (ei(5, 11), false), (ie(14, 16), true)],
		);
		assert_insert_merge_overlapping(
			basic(),
			(ii(15, 18), true),
			ii(14, 18),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ii(14, 18), true),
			],
		);
		assert_insert_merge_overlapping(
			basic(),
			(uu(), false),
			uu(),
			[(uu(), false)],
		);
	}
	fn assert_insert_merge_overlapping<const N: usize>(
		mut before: NoditMap<i8, Interval<i8>, bool>,
		to_insert: (Interval<i8>, bool),
		result: Interval<i8>,
		after: [(Interval<i8>, bool); N],
	) {
		assert_eq!(
			before.insert_merge_overlapping(to_insert.0, to_insert.1),
			result
		);
		assert_eq!(before, NoditMap::from_slice_strict(after).unwrap())
	}

	#[test]
	fn insert_merge_touching_or_overlapping_tests() {
		assert_insert_merge_touching_or_overlapping(
			NoditMap::from_slice_strict([(ie(1, 4), false)]).unwrap(),
			(ie(0, 1), true),
			ie(0, 4),
			[(ie(0, 4), true)],
		);

		//copied from insert_merge_overlapping_tests
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(ii(0, 2), true),
			ui(4),
			[
				(ui(4), true),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), true),
			],
		);
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(ie(14, 16), false),
			ie(14, 16),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ie(14, 16), false),
			],
		);
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(ii(6, 11), false),
			ei(5, 11),
			[(ui(4), false), (ei(5, 11), false), (ie(14, 16), true)],
		);
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(ii(15, 18), true),
			ii(14, 18),
			[
				(ui(4), false),
				(ee(5, 7), true),
				(ii(7, 7), false),
				(ii(14, 18), true),
			],
		);
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(uu(), false),
			uu(),
			[(uu(), false)],
		);
		//the only difference from the insert_merge_overlapping
		assert_insert_merge_touching_or_overlapping(
			basic(),
			(ii(7, 14), false),
			ee(5, 16),
			[(ui(4), false), (ee(5, 16), false)],
		);
	}
	fn assert_insert_merge_touching_or_overlapping<const N: usize>(
		mut before: NoditMap<i8, Interval<i8>, bool>,
		to_insert: (Interval<i8>, bool),
		result: Interval<i8>,
		after: [(Interval<i8>, bool); N],
	) {
		assert_eq!(
			before
				.insert_merge_touching_or_overlapping(to_insert.0, to_insert.1),
			result
		);
		assert_eq!(before, NoditMap::from_slice_strict(after).unwrap())
	}

	#[test]
	fn config_tests() {
		assert_eq!(config(ie(1, 4), ie(6, 8)), Config::LeftFirstNonOverlapping);
		assert_eq!(config(ie(1, 4), ie(2, 8)), Config::LeftFirstPartialOverlap);
		assert_eq!(config(ie(1, 4), ie(2, 3)), Config::LeftContainsRight);

		assert_eq!(
			config(ie(6, 8), ie(1, 4)),
			Config::RightFirstNonOverlapping
		);
		assert_eq!(
			config(ie(2, 8), ie(1, 4)),
			Config::RightFirstPartialOverlap
		);
		assert_eq!(config(ie(2, 3), ie(1, 4)), Config::RightContainsLeft);
	}

	#[test]
	fn overlaps_tests() {
		for interval1 in all_valid_test_bounds() {
			for interval2 in all_valid_test_bounds() {
				let our_answer = interval1.overlaps(&interval2);

				let mathematical_definition_of_overlap =
					NUMBERS_DOMAIN.iter().any(|x| {
						contains_point(interval1, *x)
							&& contains_point(interval2, *x)
					});

				if our_answer != mathematical_definition_of_overlap {
					dbg!(interval1, interval2);
					dbg!(mathematical_definition_of_overlap, our_answer);
					panic!("Discrepancy in overlaps() detected!");
				}
			}
		}
	}

	#[test]
	fn cut_interval_tests() {
		for base in all_valid_test_bounds() {
			for cut in all_valid_test_bounds() {
				let cut_result @ CutResult {
					before_cut: b,
					inside_cut: i,
					after_cut: a,
				} = cut_interval(base, cut);

				let mut on_left = true;

				// The definition of a cut is: A && NOT B
				for x in NUMBERS_DOMAIN {
					let base_contains = contains_point(base, *x);
					let cut_contains = contains_point(cut, *x);

					if cut_contains {
						on_left = false;
					}

					let invariant = match (base_contains, cut_contains) {
						(false, _) => !con(b, x) && !con(i, x) && !con(a, x),
						(true, false) => {
							if on_left {
								con(b, x) && !con(i, x) && !con(a, x)
							} else {
								!con(b, x) && !con(i, x) && con(a, x)
							}
						}
						(true, true) => !con(b, x) && con(i, x) && !con(a, x),
					};

					if !invariant {
						dbg!(base_contains);
						dbg!(cut_contains);

						dbg!(on_left);

						dbg!(base);
						dbg!(cut);
						dbg!(cut_result);

						dbg!(x);

						panic!("Invariant Broken!");
					}
				}
			}
		}
	}
	fn con(x: Option<Interval<i8>>, point: &i8) -> bool {
		match x {
			Some(y) => contains_point(y, *point),
			None => false,
		}
	}
	#[test]
	fn cut_interval_should_return_valid_intervals() {
		let result: CutResult<i8> = cut_interval(ie(3, 8), ie(5, 8));
		if let Some(x) = result.before_cut {
			assert!(x.is_valid());
		}
		if let Some(x) = result.inside_cut {
			assert!(x.is_valid());
		}
		if let Some(x) = result.after_cut {
			assert!(x.is_valid());
		}

		let result = cut_interval(ie(3, 8), ie(3, 5));
		if let Some(x) = result.before_cut {
			assert!(x.is_valid());
		}
		if let Some(x) = result.inside_cut {
			assert!(x.is_valid());
		}
		if let Some(x) = result.after_cut {
			assert!(x.is_valid());
		}
	}

	#[test]
	fn test_intersection() {
		let input = Interval { start: 5, end: 10 };
		assert_eq!(
			input.intersection(&Interval { start: 8, end: 13 }),
			Some(Interval { start: 8, end: 10 })
		);
		assert_eq!(
			input.intersection(&Interval { start: 10, end: 13 }),
			Some(Interval { start: 10, end: 10 })
		);
		assert_eq!(input.intersection(&Interval { start: 11, end: 13 }), None);
	}

	#[test]
	fn test_translate() {
		let input = Interval { start: 5, end: 10 };
		assert_eq!(input.translate(3), Interval { start: 8, end: 13 });
		assert_eq!(input.translate(-2), Interval { start: 3, end: 8 });
	}

	// Test Helper Functions
	//======================
	fn all_non_overlapping_test_bound_entries()
	-> Vec<(Interval<i8>, Interval<i8>)> {
		let mut output = Vec::new();
		for test_bounds1 in all_valid_test_bounds() {
			for test_bounds2 in all_valid_test_bounds() {
				if !test_bounds1.overlaps(&test_bounds2) {
					output.push((test_bounds1, test_bounds2));
				}
			}
		}

		output
	}

	fn all_valid_test_bounds() -> Vec<Interval<i8>> {
		let mut output = Vec::new();
		for i in NUMBERS {
			for j in NUMBERS {
				if i <= j {
					output.push(Interval { start: *i, end: *j });
				}
			}
		}
		output
	}
}
