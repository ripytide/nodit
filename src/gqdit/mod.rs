//! A module containing the `gqdit` data-structure.
//!
//! `gqdit` stands for Gap Query Discrete Interval Tree

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use itertools::Itertools;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::interval::{ii, iu, ui, uu};
use crate::utils::invalid_interval_panic;
use crate::{Interval, IntervalType, NoditMap, PointType};

/// The marker trait for valid id types, a blanket implementation is provided for all types
/// which implement this traits' super-traits so you shouln't need to implement this yourself.
pub trait IdType: Eq + Ord + Copy {}
impl<D> IdType for D where D: Eq + Ord + Copy {}

/// The [`Gqdit`] is a Gap Query Discrete Interval Tree, it is designed for the storage of multiple
/// sets of discrete non-overlapping intervalts with each set assigned a unique identifier. Then
/// once this data-structure is created it can be gap-queried to find gaps between all the sets
/// efficiently. Optionally, you can also search for gaps with an identifier which sort of ignores
/// any intervals associated with that identifier when doing the gap-search which is often useful.
///
/// Importantly, overlapping is allowed between different identifiers' intervals but not within the
/// intervals of the same identifier.
///
/// `I` is the generic type parameter for the [`Ord`] type the `K`
/// type is a interval over.
///
/// `K` is the generic type parameter for the interval type stored in the data-structure.
///
/// `D` is the generic type parameter for the identifiers associated with the
/// interval sets in the data-structure.
///
/// Phrasing it another way: `I` is the point type, `K` is the interval type, and `D` is the identifier type.
///
/// Developed for the paper (includes more in depth description of how this data-structure is
/// implemented):
/// ```text
/// Guaranteed, Predictable, Polynomial AGV Time-Pathing
/// James Forster
/// October 2023
/// https://doi.org/10.48550/arXiv.2310.12006
/// https://arxiv.org/abs/2310.12006
/// ```
///
/// # Examples
/// ```
/// use std::collections::BTreeSet;
///
/// use nodit::interval::{ii, iu};
/// use nodit::Gqdit;
///
/// let mut map = Gqdit::new();
///
/// map.insert(BTreeSet::from([0_u8]), ii(0, 4));
/// map.insert(BTreeSet::from([2_u8]), ii(2, 6));
/// map.insert(BTreeSet::from([4_u8]), ii(10, 40));
///
/// assert_eq!(
/// 	map.gaps_no_identifier(ii(0, 100)),
/// 	[ii(7, 9), iu(41)]
/// );
/// ```
#[derive(Clone, Debug)]
pub struct Gqdit<I, K, D> {
	inner: NoditMap<I, K, BTreeSet<D>>,
}

impl<I, K, D> Gqdit<I, K, D>
where
	I: PointType,
	K: IntervalType<I>,
	D: IdType,
{
	/// Makes a new, empty [`Gqdit`].
	///
	/// # Examples
	/// ```
	/// use nodit::{Gqdit, Interval};
	///
	/// let map: Gqdit<i8, Interval<i8>, u8> = Gqdit::new();
	/// ```
	pub fn new() -> Self {
		Self::default()
	}

	/// Returns a [`Vec`] of intervals which are equivalent to those found
	/// by finding the gaps in the discrete interval tree formed by the
	/// intersection of all the intervals associated with every identifier
	/// inside the structure except the given identifier whose intervals
	/// are ignored.
	///
	/// See [`Gqdit::gaps_no_identifier`] to not ignore any identifiers.
	///
	/// # Panics
	///
	/// Panics if the given interval is an invalid interval. See [`Invalid
	/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use std::collections::BTreeSet;
	///
	/// use nodit::interval::{ii, iu};
	/// use nodit::Gqdit;
	///
	/// let mut map = Gqdit::new();
	///
	/// map.insert(BTreeSet::from([0_u8]), ii(0, 4));
	/// map.insert(BTreeSet::from([2_u8]), ii(2, 6));
	/// map.insert(BTreeSet::from([4_u8]), ii(10, 40));
	///
	/// assert_eq!(
	/// 	map.gaps_no_identifier(ii(0, 100)),
	/// 	[ii(7, 9), iu(41)]
	/// );
	/// ```
	pub fn gaps_no_identifier<Q>(&self, interval: Q) -> Vec<K>
	where
		Q: IntervalType<I>,
	{
		invalid_interval_panic(interval);

		self.inner
			.overlapping(interval)
			.filter_map(|(inner_interval, other_specifiers)| {
				if other_specifiers.is_empty() {
					Some(inner_interval)
				} else {
					None
				}
			})
			.copied()
			.collect()
	}

	/// Returns a [`Vec`] of intervals which are equivalent to those found
	/// by finding the gaps in the discrete interval tree formed by the
	/// intersection of all the intervals associated with every identifier
	/// inside the structure.
	///
	/// See [`Gqdit::gaps_with_identifier`] to ignore intervals from a
	/// specific identifier.
	///
	/// # Panics
	///
	/// Panics if the given interval is an invalid interval. See [`Invalid
	/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use std::collections::BTreeSet;
	///
	/// use nodit::interval::{ii, iu};
	/// use nodit::Gqdit;
	///
	/// let mut map = Gqdit::new();
	///
	/// map.insert(BTreeSet::from([0_u8]), ii(0, 4));
	/// map.insert(BTreeSet::from([2_u8]), ii(2, 6));
	/// map.insert(BTreeSet::from([4_u8]), ii(10, 40));
	///
	/// assert_eq!(
	/// 	map.gaps_with_identifier(2_u8, ii(0, 100)),
	/// 	[ii(5, 9), iu(41)]
	/// );
	/// ```
	pub fn gaps_with_identifier<Q>(&self, identifier: D, interval: Q) -> Vec<K>
	where
		Q: IntervalType<I>,
	{
		invalid_interval_panic(interval);

		let valid_gaps = self
			.inner
			.overlapping(interval)
			.filter_map(move |(inner_interval, other_identifiers)| {
				if valid_identifier(Some(identifier), other_identifiers) {
					Some(inner_interval)
				} else {
					None
				}
			})
			.copied();
		//we don't want end ones as they are
		//handled separately
		let non_end_gaps = valid_gaps.filter(|gap| {
			!gap.contains_point(interval.start()) && !gap.contains_point(interval.end())
		});

		//instead of using possibly-partial end gaps we will
		//replace them with completely_iterated gaps
		//expanded on both sides outwardly only not inwardly
		let mut left_gap =
			self.expand_gaps_at_point_left(identifier, interval.start());
		let mut right_gap =
			self.expand_gaps_at_point_right(identifier, interval.end());
		//if they refer to the save gap then merge them
		if let (Some(left), Some(right)) = (left_gap.as_mut(), right_gap) {
			if overlaps_ordered(*left, right) {
				*left = K::from(merge_ordered(*left, right));
				right_gap = None;
			}
		}

		//then we need to chain these iterators together and
		//progressively merge touching gaps
		let all_non_merged_gaps =
			left_gap.into_iter().chain(non_end_gaps).chain(right_gap);

		//the final proper merged result
		all_non_merged_gaps
			.coalesce(|x, y| {
				if touches_ordered(x, y) {
					Ok(K::from(merge_ordered(x, y)))
				} else {
					Err((x, y))
				}
			})
			.collect()
	}

	/// Cuts the given `interval` out of all the interval sets associated with the given
	/// `identifiers`.
	///
	/// Cutting an interval with no identifiers is a no-op.
	///
	/// # Examples
	/// ```
	/// use std::collections::BTreeSet;
	///
	/// use nodit::interval::{ii, iu};
	/// use nodit::Gqdit;
	///
	/// let mut map = Gqdit::new();
	///
	/// map.insert(BTreeSet::from([0_u8]), ii(0, 4));
	/// map.insert(BTreeSet::from([2_u8]), ii(2, 6));
	/// map.insert(BTreeSet::from([4_u8]), ii(10, 40));
	///
	/// map.cut_with_identifiers(BTreeSet::from([2, 4]), ii(0, 20));
	///
	/// assert_eq!(
	/// 	map.gaps_no_identifier(ii(0, 100)),
	/// 	[ii(5, 20), iu(41)]
	/// );
	/// ```
	///
	/// # Panics
	///
	/// Panics if the given interval is an invalid interval. See [`Invalid
	/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
	/// for more details.
	pub fn cut_with_identifiers<Q>(
		&mut self,
		identifiers: BTreeSet<D>,
		interval: Q,
	) where
		Q: IntervalType<I>,
	{
		invalid_interval_panic(interval);

		if identifiers.is_empty() {
			return;
		}

		for (cut_interval, mut cut_identifiers) in self
			.inner
			.cut(interval)
			//to soothe the borrow checker
			.collect::<Vec<_>>()
		{
			cut_identifiers.retain(|i| !identifiers.contains(i));

			self.inner
				.insert_merge_touching_if_values_equal(
					cut_interval,
					cut_identifiers,
				)
				.unwrap_or_else(|_| panic!());
		}
	}

	/// Cuts the given `interval` out of all interval sets in the structure.
	///
	/// # Examples
	/// ```
	/// use std::collections::BTreeSet;
	///
	/// use nodit::interval::{ii, iu};
	/// use nodit::Gqdit;
	///
	/// let mut map = Gqdit::new();
	///
	/// map.insert(BTreeSet::from([0_u8]), ii(0_u8, 4));
	/// map.insert(BTreeSet::from([2_u8]), ii(2, 6));
	/// map.insert(BTreeSet::from([4_u8]), ii(10, 40));
	///
	/// map.cut_all_identifiers(ii(0, 20));
	///
	/// assert_eq!(
	/// 	map.gaps_no_identifier(ii(0, 100)),
	/// 	[ii(0, 20), iu(41)]
	/// );
	/// ```
	///
	/// # Panics
	///
	/// Panics if the given interval is an invalid interval. See [`Invalid
	/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
	/// for more details.
	pub fn cut_all_identifiers<Q>(&mut self, interval: Q)
	where
		Q: IntervalType<I>,
	{
		invalid_interval_panic(interval);

		for (cut_interval, mut cut_identifiers) in self
			.inner
			.cut(interval)
			//to soothe the borrow checker
			.collect::<Vec<_>>()
		{
			cut_identifiers.clear();

			self.inner
				.insert_merge_touching_if_values_equal(
					cut_interval,
					cut_identifiers,
				)
				.unwrap_or_else(|_| panic!());
		}
	}

	/// Inserts an interval into the structure assigned to the given
	/// identifiers.
	///
	/// How overlapping/touching intervals of the same specificer are
	/// stored internally is unspecificed since only the gaps are able to
	/// be queried and regardless of how they are stored the gaps will be
	/// the same.
	///
	/// Inserting an interval with no identifiers is a no-op.
	///
	/// # Panics
	///
	/// Panics if the given interval is an invalid interval. See [`Invalid
	/// Intervals`](https://docs.rs/nodit/latest/nodit/index.html#invalid-intervals)
	/// for more details.
	///
	/// # Examples
	/// ```
	/// use std::collections::BTreeSet;
	///
	/// use nodit::interval::ii;
	/// use nodit::Gqdit;
	///
	/// let mut map = Gqdit::new();
	///
	/// map.insert(BTreeSet::from([0_u8]), ii(0, 4));
	/// ```
	pub fn insert(&mut self, identifiers: BTreeSet<D>, interval: K) {
		invalid_interval_panic(interval);

		if identifiers.is_empty() {
			return;
		}

		//first we extend the overlapping partial
		//intervals with the
		//other_specifiers and then insert them
		//back into the data_structure with
		//insert_merge_touching_if_values_equal to prevent
		//fragmentation
		//
		//optimisation: do this without cutting and re-inserting
		//using overlapping_mut or something
		let cut = self
			.inner
			.cut(interval)
			//to soothe the borrow checker
			.collect::<Vec<_>>()
			.into_iter();

		let extended_cut = cut.map(|(cut_interval, mut cut_identifiers)| {
			cut_identifiers.extend(identifiers.clone());
			(cut_interval, cut_identifiers)
		});

		for (extended_interval, extended_identifiers) in extended_cut {
			self.inner
				.insert_merge_touching_if_values_equal(
					extended_interval,
					extended_identifiers,
				)
				.unwrap_or_else(|_| panic!());
		}
	}

	/// Appends all the intervals from `other` to `self`.
	///
	/// # Examples
	/// ```
	/// use std::collections::BTreeSet;
	///
	/// use nodit::interval::ii;
	/// use nodit::Gqdit;
	///
	/// let mut map = Gqdit::new();
	/// map.insert(BTreeSet::from([0_u8]), ii(0, 4));
	///
	/// let mut other = Gqdit::new();
	/// other.insert(BTreeSet::from([0_u8]), ii(6, 10));
	///
	/// map.append(&mut other);
	///
	/// assert_eq!(map.gaps_no_identifier(ii(0, 10)), [ii(5, 5)]);
	/// ```
	pub fn append(&mut self, other: &mut Self) {
		for (interval, identifiers) in other.inner.remove_overlapping(uu()) {
			self.insert(identifiers, interval);
		}
	}

	/// Return all the identifiers with intervals overlapping the given
	/// `point`.
	///
	/// # Examples
	/// ```
	/// use std::collections::BTreeSet;
	///
	/// use nodit::interval::ii;
	/// use nodit::Gqdit;
	///
	/// let mut map = Gqdit::new();
	/// map.insert(BTreeSet::from([0_u8]), ii(2, 6));
	/// map.insert(BTreeSet::from([1_u8]), ii(4, 8));
	///
	/// assert_eq!(map.identifiers_at_point(0), BTreeSet::from([]));
	/// assert_eq!(map.identifiers_at_point(2), BTreeSet::from([0]));
	/// assert_eq!(map.identifiers_at_point(5), BTreeSet::from([0, 1]));
	/// assert_eq!(map.identifiers_at_point(8), BTreeSet::from([1]));
	/// assert_eq!(map.identifiers_at_point(10), BTreeSet::from([]));
	/// ```
	pub fn identifiers_at_point(&self, point: I) -> BTreeSet<D> {
		self.inner
			.get_at_point(point)
			.cloned()
			.unwrap_or(BTreeSet::new())
	}

	fn expand_gaps_at_point_right(&self, identifier: D, point: I) -> Option<K> {
		let overlapping_right = self.inner.overlapping(iu(point));

		overlapping_right
			.take_while(|(_, other_identifiers)| {
				valid_identifier(Some(identifier), other_identifiers)
			})
			.map(|(x, _)| *x)
			.coalesce(|x, y| {
				//since there are no gaps we know they will always
				//touch
				Ok(K::from(merge_ordered(x, y)))
			})
			.next()
	}
	fn expand_gaps_at_point_left(&self, identifier: D, point: I) -> Option<K> {
		//we are going in reverse since we are going left
		let overlapping_left = self.inner.overlapping(ui(point)).rev();

		overlapping_left
			.take_while(|(_, other_identifiers)| {
				valid_identifier(Some(identifier), other_identifiers)
			})
			.map(|(x, _)| *x)
			.coalesce(|x, y| {
				//since we are going from right to left these will
				//be reversed too
				//
				//since there are no gaps we know they will always
				//touch
				Ok(K::from(merge_ordered(y, x)))
			})
			.next()
	}
}

fn valid_identifier<I>(
	with_identifier: Option<I>,
	other_identifiers: &BTreeSet<I>,
) -> bool
where
	I: Eq + Ord,
{
	match with_identifier {
		Some(identifier) => {
			other_identifiers.is_empty()
				|| (other_identifiers.len() == 1
					&& other_identifiers.contains(&identifier))
		}
		None => other_identifiers.is_empty(),
	}
}
/// Requires that self comes before other
fn merge_ordered<I, A, B>(a: A, b: B) -> Interval<I>
where
	I: PointType,
	A: IntervalType<I>,
	B: IntervalType<I>,
{
	ii(a.start(), b.end())
}
/// Requires that self comes before other
fn overlaps_ordered<I, A, B>(a: A, b: B) -> bool
where
	I: PointType,
	A: IntervalType<I>,
	B: IntervalType<I>,
{
	a.contains_point(b.start()) || a.contains_point(b.end())
}
/// Requires that self comes before other
fn touches_ordered<I, A, B>(a: A, b: B) -> bool
where
	I: PointType,
	A: IntervalType<I>,
	B: IntervalType<I>,
{
	a.end() == b.start().down().unwrap()
}

impl<I, K, D> PartialEq for Gqdit<I, K, D>
where
	I: PartialEq,
	K: PartialEq,
	BTreeSet<D>: PartialEq,
{
	fn eq(&self, other: &Self) -> bool {
		self.inner.eq(&other.inner)
	}
}

impl<I, K, D> Default for Gqdit<I, K, D>
where
	I: PointType,
	K: IntervalType<I>,
{
	fn default() -> Self {
		let mut map = NoditMap::new();
		map.insert_strict(K::from(uu()), BTreeSet::new())
			.unwrap_or_else(|_| panic!());
		Self { inner: map }
	}
}

impl<I, K, D> Serialize for Gqdit<I, K, D>
where
	I: PointType,
	K: IntervalType<I> + Serialize,
	D: IdType,
	BTreeSet<D>: Serialize,
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		self.inner.serialize(serializer)
	}
}

impl<'de, I, K, D> Deserialize<'de> for Gqdit<I, K, D>
where
	I: PointType,
	K: IntervalType<I> + Deserialize<'de>,
	D: IdType,
	BTreeSet<D>: Deserialize<'de>,
{
	fn deserialize<De>(deserializer: De) -> Result<Self, De::Error>
	where
		De: Deserializer<'de>,
	{
		NoditMap::deserialize(deserializer).map(|x| Gqdit { inner: x })
	}
}
