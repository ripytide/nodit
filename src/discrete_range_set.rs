/*
Copyright 2022,2023 James Forster

This file is part of discrete_range_map.

discrete_range_map is free software: you can redistribute it and/or
modify it under the terms of the GNU Affero General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

discrete_range_map is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with discrete_range_map. If not, see <https://www.gnu.org/licenses/>.
*/

//! The module containing [`DiscreteRangeSet`] and related types. Since
//! [`DiscreteRangeSet`] is just a wrapper around [`DiscreteRangeMap`], most of
//! the methods' docs will point towards the equivalent method's docs on
//! [`DiscreteRangeMap`] to prevent inconsistency.

use core::fmt;
use core::marker::PhantomData;

use serde::de::{SeqAccess, Visitor};
use serde::ser::SerializeSeq;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::discrete_range_map::IntoIter as DiscreteRangeMapIntoIter;
use crate::{DiscreteRangeMap, OverlapError, PointType, RangeType};

/// An ordered set of non-overlapping ranges based on [`DiscreteRangeMap`].
///
/// `I` is the generic type parameter for the [`Ord`] type the `K`
/// type is range over.
///
/// `K` is the generic type parameter for the range implementing type
/// in the set.
///
/// Phrasing it another way: `I` is the point type and `K` is the range type.
///
/// See [`DiscreteRangeMap`] for more details.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiscreteRangeSet<I, K> {
	inner: DiscreteRangeMap<I, K, ()>,
}

impl<I, K> DiscreteRangeSet<I, K>
where
	I: PointType,
	K: RangeType<I>,
{
	/// See [`DiscreteRangeMap::overlaps()`] for more details.
	pub fn overlaps<Q>(&self, range: Q) -> bool
	where
		Q: RangeType<I>,
	{
		self.inner.overlaps(range)
	}
	/// See [`DiscreteRangeMap::overlapping()`] for more details.
	pub fn overlapping<Q>(
		&self,
		range: Q,
	) -> impl DoubleEndedIterator<Item = &K>
	where
		Q: RangeType<I>,
	{
		self.inner.overlapping(range).map(first)
	}
	/// See [`DiscreteRangeMap::get_entry_at_point()`] for more details.
	pub fn get_at_point(&self, point: I) -> Result<&K, K> {
		self.inner.get_entry_at_point(point).map(first)
	}
	/// See [`DiscreteRangeMap::contains_point()`] for more details.
	pub fn contains_point(&self, point: I) -> bool {
		self.inner.contains_point(point)
	}
	/// See [`DiscreteRangeMap::remove_overlapping()`] for more details.
	pub fn remove_overlapping<'a, Q>(
		&'a mut self,
		range: Q,
	) -> impl Iterator<Item = K> + '_
	where
		Q: RangeType<I> + 'a,
	{
		self.inner.remove_overlapping(range).map(first)
	}
	/// See [`DiscreteRangeMap::cut()`] for more details.
	pub fn cut<'a, Q>(&'a mut self, range: Q) -> impl Iterator<Item = K> + '_
	where
		Q: RangeType<I> + 'a,
	{
		self.inner.cut(range).map(first)
	}
	/// See [`DiscreteRangeMap::gaps()`] for more details.
	pub fn gaps<'a, Q>(&'a self, range: Q) -> impl Iterator<Item = K> + '_
	where
		Q: RangeType<I> + 'a,
	{
		self.inner.gaps(range)
	}
	/// See [`DiscreteRangeMap::contains_range()`] for more details.
	pub fn contains_range<Q>(&self, range: Q) -> bool
	where
		Q: RangeType<I>,
	{
		self.inner.contains_range(range)
	}
	/// See [`DiscreteRangeMap::insert_strict()`] for more details.
	pub fn insert_strict(&mut self, range: K) -> Result<(), OverlapError> {
		self.inner.insert_strict(range, ())
	}
	/// See [`DiscreteRangeMap::insert_merge_touching()`] for more details.
	pub fn insert_merge_touching(
		&mut self,
		range: K,
	) -> Result<K, OverlapError> {
		self.inner.insert_merge_touching(range, ())
	}
	/// See [`DiscreteRangeMap::insert_merge_overlapping()`] for more details.
	pub fn insert_merge_overlapping(&mut self, range: K) -> K {
		self.inner.insert_merge_overlapping(range, ())
	}
	/// See [`DiscreteRangeMap::insert_merge_touching_or_overlapping()`] for more details.
	pub fn insert_merge_touching_or_overlapping(&mut self, range: K) -> K {
		self.inner.insert_merge_touching_or_overlapping(range, ())
	}
	/// See [`DiscreteRangeMap::insert_overwrite()`] for more details.
	pub fn insert_overwrite(&mut self, range: K) {
		self.inner.insert_overwrite(range, ())
	}
	/// See [`DiscreteRangeMap::from_slice_strict()`] for more details.
	pub fn from_slice_strict<const N: usize>(
		slice: [K; N],
	) -> Result<DiscreteRangeSet<I, K>, OverlapError> {
		let mut set = DiscreteRangeSet::new();
		for range in slice {
			set.insert_strict(range)?;
		}
		return Ok(set);
	}
	/// See [`DiscreteRangeMap::from_iter_strict()`] for more details.
	pub fn from_iter_strict(
		iter: impl Iterator<Item = K>,
	) -> Result<DiscreteRangeSet<I, K>, OverlapError> {
		let mut set = DiscreteRangeSet::new();
		for range in iter {
			set.insert_strict(range)?;
		}
		return Ok(set);
	}
}

impl<I, K> DiscreteRangeSet<I, K> {
	/// See [`DiscreteRangeMap::new()`] for more details.
	pub fn new() -> Self {
		DiscreteRangeSet {
			inner: DiscreteRangeMap::new(),
		}
	}
	/// See [`DiscreteRangeMap::len()`] for more details.
	pub fn len(&self) -> usize {
		self.inner.len()
	}
	/// See [`DiscreteRangeMap::is_empty()`] for more details.
	pub fn is_empty(&self) -> bool {
		self.inner.is_empty()
	}
	/// See [`DiscreteRangeMap::iter()`] for more details.
	pub fn iter(&self) -> impl DoubleEndedIterator<Item = &K> {
		self.inner.iter().map(first)
	}
	/// See [`DiscreteRangeMap::first_entry()`] for more details.
	pub fn first(&self) -> Option<&K> {
		self.inner.first_entry().map(first)
	}
	/// See [`DiscreteRangeMap::last_entry()`] for more details.
	pub fn last(&self) -> Option<&K> {
		self.inner.last_entry().map(first)
	}
}

// Helper Functions ==========================

fn first<A, B>((a, _): (A, B)) -> A {
	a
}

// Trait Impls ==========================

impl<I, K> IntoIterator for DiscreteRangeSet<I, K> {
	type Item = K;
	type IntoIter = IntoIter<I, K>;
	fn into_iter(self) -> Self::IntoIter {
		return IntoIter {
			inner: self.inner.into_iter(),
		};
	}
}
/// An owning iterator over the entries of a [`DiscreteRangeSet`].
///
/// This `struct` is created by the [`into_iter`] method on
/// [`DiscreteRangeSet`] (provided by the [`IntoIterator`] trait). See
/// its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
pub struct IntoIter<I, K> {
	inner: DiscreteRangeMapIntoIter<I, K, ()>,
}
impl<I, K> Iterator for IntoIter<I, K> {
	type Item = K;
	fn next(&mut self) -> Option<Self::Item> {
		self.inner.next().map(first)
	}
}

impl<I, K> Default for DiscreteRangeSet<I, K>
where
	I: PointType,
{
	fn default() -> Self {
		DiscreteRangeSet {
			inner: DiscreteRangeMap::default(),
		}
	}
}

impl<I, K> Serialize for DiscreteRangeSet<I, K>
where
	K: Serialize,
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		let mut seq = serializer.serialize_seq(Some(self.len()))?;
		for range_bounds in self.iter() {
			seq.serialize_element(&range_bounds)?;
		}
		seq.end()
	}
}

impl<'de, I, K> Deserialize<'de> for DiscreteRangeSet<I, K>
where
	I: PointType,
	K: RangeType<I> + Deserialize<'de>,
{
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		deserializer.deserialize_seq(DiscreteRangeSetVisitor {
			i: PhantomData,
			k: PhantomData,
		})
	}
}

struct DiscreteRangeSetVisitor<I, K> {
	i: PhantomData<I>,
	k: PhantomData<K>,
}

impl<'de, I, K> Visitor<'de> for DiscreteRangeSetVisitor<I, K>
where
	I: PointType,
	K: RangeType<I> + Deserialize<'de>,
{
	type Value = DiscreteRangeSet<I, K>;

	fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
		formatter.write_str("a DiscreteRangeSet")
	}

	fn visit_seq<A>(self, mut access: A) -> Result<Self::Value, A::Error>
	where
		A: SeqAccess<'de>,
	{
		let mut set = DiscreteRangeSet::new();
		while let Some(range_bounds) = access.next_element()? {
			set.insert_strict(range_bounds)
				.map_err(|_| serde::de::Error::custom("ranges overlap"))?;
		}
		Ok(set)
	}
}
