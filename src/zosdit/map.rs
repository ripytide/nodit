use crate::{IntervalType, NoditMap, OverlapError, PointType};
use serde::{Deserialize, Serialize};

/// A Zero Overlap Sequential Discrete Interval Tree Map Data-Structure based off [`NoditMap`] and
/// [`SmallVec`]
///
/// See the top-level crate documentation for details on how to use this Data-Structure.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ZosditMap<I, K, V> {
	#[serde(bound(
		deserialize = "I: PointType, K: IntervalType<I> + Deserialize<'de>, V: Deserialize<'de>,"
	))]
	inner: NoditMap<I, K, V>,
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
	/// use nodit::Interval;
	/// use zosdit::ZosditMap;
	///
	/// let map: ZosditMap<i8, Interval<i8>, bool> = ZosditMap::new();
	/// ```
	pub fn new() -> Self {
		ZosditMap {
			inner: NoditMap::new(),
		}
	}

	/// Inserts
	pub fn insert_push_back(
		&mut self,
		interval: I,
		value: V,
	) -> Result<(), OverlapError<V>> {
		self.inner.insert_strict(k, p)
	}

	pub fn is_zero_overlap(&self, interval: K) -> bool {
        let start = interval.start();
        let end = interval.end();
		let mut overlapping = self.inner.overlapping(interval);
        match (overlapping.next(), overlapping.next_back()) {
            (Some(_), Some(_)) => todo!(),
            (Some(_), None) => todo!(),
            (None, Some(_)) => todo!(),
            (None, None) => todo!(),
        }
	}
}
