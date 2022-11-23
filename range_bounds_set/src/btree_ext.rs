use std::collections::btree_map::Range as MapRange;
use std::collections::btree_set::Range as SetRange;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Bound;

pub trait BTreeSetExt<T> {
	fn next_above_lower_bound(&self, lower_bound: Bound<&T>) -> Option<&T>;
	fn next_below_upper_bound(&self, upper_bound: Bound<&T>) -> Option<&T>;
	fn above_lower_bound(&self, lower_bound: Bound<&T>) -> SetRange<T>;
	fn above_upper_bound(&self, upper_bound: Bound<&T>) -> SetRange<T>;
}

impl<T> BTreeSetExt<T> for BTreeSet<T>
where
	T: Ord,
{
	fn next_above_lower_bound(&self, lower_bound: Bound<&T>) -> Option<&T> {
		self.range((lower_bound, Bound::Unbounded)).next_back()
	}
	fn next_below_upper_bound(&self, upper_bound: Bound<&T>) -> Option<&T> {
		self.range((Bound::Unbounded, upper_bound)).next_back()
	}
	fn above_lower_bound(&self, lower_bound: Bound<&T>) -> SetRange<T> {
		self.range((lower_bound, Bound::Unbounded))
	}
	fn above_upper_bound(&self, upper_bound: Bound<&T>) -> SetRange<T> {
		self.range((upper_bound, Bound::Unbounded))
	}
}

pub trait BTreeMapExt<K, V> {
	fn next_above_lower_bound(
		&self,
		lower_bound: Bound<&K>,
	) -> Option<(&K, &V)>;
	fn next_below_upper_bound(
		&self,
		upper_bound: Bound<&K>,
	) -> Option<(&K, &V)>;
	fn above_lower_bound(&self, lower_bound: Bound<&K>) -> MapRange<K, V>;
	fn above_upper_bound(&self, upper_bound: Bound<&K>) -> MapRange<K, V>;
}

impl<K, V> BTreeMapExt<K, V> for BTreeMap<K, V>
where
	K: Ord,
{
	fn next_above_lower_bound(
		&self,
		lower_bound: Bound<&K>,
	) -> Option<(&K, &V)> {
		self.range((lower_bound, Bound::Unbounded)).next_back()
	}
	fn next_below_upper_bound(
		&self,
		upper_bound: Bound<&K>,
	) -> Option<(&K, &V)> {
		self.range((Bound::Unbounded, upper_bound)).next_back()
	}
	fn above_lower_bound(&self, lower_bound: Bound<&K>) -> MapRange<K, V> {
		self.range((lower_bound, Bound::Unbounded))
	}
	fn above_upper_bound(&self, upper_bound: Bound<&K>) -> MapRange<K, V> {
		self.range((upper_bound, Bound::Unbounded))
	}
}
