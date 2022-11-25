use std::collections::BTreeMap;
use std::iter::once;
use std::ops::Bound;

use either::Either;

use crate::bounds::StartBound;
use crate::range_bounds_ext::RangeBoundsExt;

pub struct RangeBoundsMap<I, K, V> {
	starts: BTreeMap<StartBound<I>, (K, V)>,
}

impl<I, K, V> RangeBoundsMap<I, K, V>
where
	K: RangeBoundsExt<I>,
	I: Ord + Clone,
{
	pub fn new() -> Self {
		RangeBoundsMap {
			starts: BTreeMap::new(),
		}
	}

	//returns Err(()) if the given range overlaps another range
	//does not coalesce ranges if they touch
	pub fn insert(&mut self, range_bounds: K, value: V) -> Result<(), ()> {
		if self.overlaps(&range_bounds) {
			return Err(());
		}

		//todo panic on invalid inputs

		self.starts.insert(
			StartBound::from(range_bounds.start_bound().cloned()),
			(range_bounds, value),
		);

		return Ok(());
	}

	pub fn contains_point(&self, point: &I) -> bool {
		self.get(point).is_some()
	}

	pub fn overlaps(&self, search_range_bounds: &K) -> bool {
		self.overlapping(search_range_bounds).next().is_some()
	}

	pub fn overlapping(
		&self,
		search_range_bounds: &K,
	) -> impl Iterator<Item = (&K, &V)> {
		let start_range_bounds = (
			//Included is lossless regarding meta-bounds searches
			Bound::Included(StartBound::from(
				search_range_bounds.start_bound().cloned(),
			)),
			Bound::Included(
				StartBound::from(search_range_bounds.end_bound().cloned())
					.as_end_value(),
			),
		);
		//this range will hold all the ranges we want except possibly
		//the first RangeBound in the range
		let most_range_bounds = self.starts.range(start_range_bounds);

		if let Some(missing_entry @ (_, (possible_missing_range_bounds, _))) =
			//Excluded is lossless regarding meta-bounds searches
			//because we don't want equal bound as they would have be
			//coverded in the previous step
			self.starts
					.range((
						Bound::Unbounded,
						Bound::Excluded(
							//optimisation fix this without cloning
							//todo should probably use .as_end_value()
							StartBound::from(
								search_range_bounds.start_bound().cloned(),
							),
						),
					))
					.next()
		{
			if possible_missing_range_bounds.overlaps(&search_range_bounds) {
				return Either::Left(
					once(missing_entry)
						.chain(most_range_bounds)
						.map(|(_, (key, value))| (key, value)),
				);
			}
		}

		return Either::Right(
			most_range_bounds.map(|(_, (key, value))| (key, value)),
		);
	}

	pub fn get(&self, point: &I) -> Option<&V> {
		self.get_key_value(point).map(|(_, value)| value)
	}

	pub fn get_key_value(&self, point: &I) -> Option<(&K, &V)> {
		//a zero-range included-included range is equivalent to a point
		return self
			.overlapping(&K::dummy(
				Bound::Included(point.clone()),
				Bound::Included(point.clone()),
			))
			.next();
	}

	pub fn get_mut(&mut self, point: &I) -> Option<&mut V> {
		if let Some(overlapping_start_bound) =
			self.get_key_value(point).map(|(key, _)| key.start_bound())
		{
			return self
				.starts
				//optimisation fix this without cloning
				.get_mut(&StartBound::from(overlapping_start_bound.cloned()))
				.map(|(_, value)| value);
		}
		return None;
	}

	pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
		self.starts.iter().map(|(_, (key, value))| (key, value))
	}
}
