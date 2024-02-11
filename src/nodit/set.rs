//! A module containing [`NoditSet`].
//!
//! Since [`NoditSet`] is just a wrapper around
//! [`NoditMap`], most of the methods' docs will point towards the
//! equivalent method's docs on [`NoditMap`] to prevent
//! inconsistency.

use crate::nodit::map::IntoIter as NoditMapIntoIter;
use crate::{IntervalType, NoditMap, OverlapError, PointType};

/// An ordered set of non-overlapping intervals based on [`NoditMap`].
///
/// `I` is the generic type parameter for the [`Ord`] type the `K`
/// type is interval over.
///
/// `K` is the generic type parameter for the interval implementing type
/// in the set.
///
/// Phrasing it another way: `I` is the point type and `K` is the interval type.
///
/// See [`NoditMap`] for more details.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NoditSet<I, K> {
	inner: NoditMap<I, K, ()>,
}

impl<I, K> NoditSet<I, K>
where
	I: PointType,
	K: IntervalType<I>,
{
	/// See [`NoditMap::overlaps()`] for more details.
	pub fn overlaps<Q>(&self, interval: Q) -> bool
	where
		Q: IntervalType<I>,
	{
		self.inner.overlaps(interval)
	}
	/// See [`NoditMap::overlapping()`] for more details.
	pub fn overlapping<Q>(
		&self,
		interval: Q,
	) -> impl DoubleEndedIterator<Item = &K>
	where
		Q: IntervalType<I>,
	{
		self.inner.overlapping(interval).map(first)
	}
	/// See [`NoditMap::get_key_value_at_point()`] for more details.
	pub fn get_at_point(&self, point: I) -> Result<&K, K> {
		self.inner.get_key_value_at_point(point).map(first)
	}
	/// See [`NoditMap::contains_point()`] for more details.
	pub fn contains_point(&self, point: I) -> bool {
		self.inner.contains_point(point)
	}
	/// See [`NoditMap::remove_overlapping()`] for more details.
	pub fn remove_overlapping<'a, Q>(
		&'a mut self,
		interval: Q,
	) -> impl Iterator<Item = K>
	where
		Q: IntervalType<I> + 'a,
	{
		self.inner.remove_overlapping(interval).map(first)
	}
	/// See [`NoditMap::cut()`] for more details.
	pub fn cut<'a, Q>(&'a mut self, interval: Q) -> impl Iterator<Item = K>
	where
		Q: IntervalType<I> + 'a,
	{
		self.inner.cut(interval).map(first)
	}
	/// See [`NoditMap::gaps_untrimmed()`] for more details.
	pub fn gaps_untrimmed<'a, Q>(
		&'a self,
		interval: Q,
	) -> impl Iterator<Item = K> + '_
	where
		Q: IntervalType<I> + 'a,
	{
		self.inner.gaps_untrimmed(interval)
	}
	/// See [`NoditMap::gaps_trimmed()`] for more details.
	pub fn gaps_trimmed<'a, Q>(
		&'a self,
		interval: Q,
	) -> impl Iterator<Item = K> + '_
	where
		Q: IntervalType<I> + 'a,
	{
		self.inner.gaps_trimmed(interval)
	}
	/// See [`NoditMap::contains_interval()`] for more details.
	pub fn contains_interval<Q>(&self, interval: Q) -> bool
	where
		Q: IntervalType<I>,
	{
		self.inner.contains_interval(interval)
	}
	/// See [`NoditMap::insert_strict()`] for more details.
	pub fn insert_strict(
		&mut self,
		interval: K,
	) -> Result<(), OverlapError<()>> {
		self.inner.insert_strict(interval, ())
	}
	/// See [`NoditMap::insert_merge_touching()`] for more details.
	pub fn insert_merge_touching(
		&mut self,
		interval: K,
	) -> Result<K, OverlapError<()>> {
		self.inner.insert_merge_touching(interval, ())
	}
	/// See [`NoditMap::insert_merge_overlapping()`] for more details.
	pub fn insert_merge_overlapping(&mut self, interval: K) -> K {
		self.inner.insert_merge_overlapping(interval, ())
	}
	/// See [`NoditMap::insert_merge_touching_or_overlapping()`] for more details.
	pub fn insert_merge_touching_or_overlapping(&mut self, interval: K) -> K {
		self.inner
			.insert_merge_touching_or_overlapping(interval, ())
	}
	/// See [`NoditMap::insert_overwrite()`] for more details.
	pub fn insert_overwrite(&mut self, interval: K) -> impl Iterator<Item = K> {
		self.inner.insert_overwrite(interval, ()).map(first)
	}
	/// See [`NoditMap::from_slice_strict()`] for more details.
	pub fn from_slice_strict<const N: usize>(
		slice: [K; N],
	) -> Result<NoditSet<I, K>, OverlapError<()>> {
		let mut set = NoditSet::new();
		for interval in slice {
			set.insert_strict(interval)?;
		}
		return Ok(set);
	}
	/// See [`NoditMap::from_iter_strict()`] for more details.
	pub fn from_iter_strict(
		iter: impl Iterator<Item = K>,
	) -> Result<NoditSet<I, K>, OverlapError<()>> {
		let mut set = NoditSet::new();
		for interval in iter {
			set.insert_strict(interval)?;
		}
		return Ok(set);
	}
}

impl<I, K> NoditSet<I, K> {
	/// See [`NoditMap::new()`] for more details.
	pub fn new() -> Self {
		NoditSet {
			inner: NoditMap::new(),
		}
	}
	/// See [`NoditMap::len()`] for more details.
	pub fn len(&self) -> usize {
		self.inner.len()
	}
	/// See [`NoditMap::is_empty()`] for more details.
	pub fn is_empty(&self) -> bool {
		self.inner.is_empty()
	}
	/// See [`NoditMap::iter()`] for more details.
	pub fn iter(&self) -> impl DoubleEndedIterator<Item = &K> {
		self.inner.iter().map(first)
	}
	/// See [`NoditMap::first_key_value()`] for more details.
	pub fn first(&self) -> Option<&K> {
		self.inner.first_key_value().map(first)
	}
	/// See [`NoditMap::last_key_value()`] for more details.
	pub fn last(&self) -> Option<&K> {
		self.inner.last_key_value().map(first)
	}
}

// Helper Functions ==========================

fn first<A, B>((a, _): (A, B)) -> A {
	a
}

// Trait Impls ==========================

impl<I, K> IntoIterator for NoditSet<I, K> {
	type Item = K;
	type IntoIter = IntoIter<I, K>;
	fn into_iter(self) -> Self::IntoIter {
		return IntoIter {
			inner: self.inner.into_iter(),
		};
	}
}
/// An owning iterator over the entries of a [`NoditSet`].
///
/// This `struct` is created by the [`into_iter`] method on
/// [`NoditSet`] (provided by the [`IntoIterator`] trait). See
/// its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
pub struct IntoIter<I, K> {
	inner: NoditMapIntoIter<I, K, ()>,
}
impl<I, K> Iterator for IntoIter<I, K> {
	type Item = K;
	fn next(&mut self) -> Option<Self::Item> {
		self.inner.next().map(first)
	}
}

impl<I, K> Default for NoditSet<I, K>
where
	I: PointType,
{
	fn default() -> Self {
		NoditSet {
			inner: NoditMap::default(),
		}
	}
}

#[cfg(feature = "serde")]
mod serde {
	use core::marker::PhantomData;

	use serde::de::{SeqAccess, Visitor};
	use serde::ser::SerializeSeq;
	use serde::{Deserialize, Deserializer, Serialize, Serializer};

	use crate::{IntervalType, NoditSet, PointType};

	impl<I, K> Serialize for NoditSet<I, K>
	where
		K: Serialize,
	{
		fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
		where
			S: Serializer,
		{
			let mut seq = serializer.serialize_seq(Some(self.len()))?;
			for interval in self.iter() {
				seq.serialize_element(&interval)?;
			}
			seq.end()
		}
	}

	impl<'de, I, K> Deserialize<'de> for NoditSet<I, K>
	where
		I: PointType,
		K: IntervalType<I> + Deserialize<'de>,
	{
		fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
		where
			D: Deserializer<'de>,
		{
			deserializer.deserialize_seq(NoditSetVisitor {
				i: PhantomData,
				k: PhantomData,
			})
		}
	}

	struct NoditSetVisitor<I, K> {
		i: PhantomData<I>,
		k: PhantomData<K>,
	}

	impl<'de, I, K> Visitor<'de> for NoditSetVisitor<I, K>
	where
		I: PointType,
		K: IntervalType<I> + Deserialize<'de>,
	{
		type Value = NoditSet<I, K>;

		fn expecting(
			&self,
			formatter: &mut alloc::fmt::Formatter,
		) -> alloc::fmt::Result {
			formatter.write_str("a NoditSet")
		}

		fn visit_seq<A>(self, mut access: A) -> Result<Self::Value, A::Error>
		where
			A: SeqAccess<'de>,
		{
			let mut set = NoditSet::new();
			while let Some(interval) = access.next_element()? {
				set.insert_strict(interval).map_err(|_| {
					serde::de::Error::custom("intervals overlap")
				})?;
			}
			Ok(set)
		}
	}
}
