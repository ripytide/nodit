use std::collections::BTreeMap;
use std::fmt::Debug;
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
	K: RangeBoundsExt<I> + Debug,
	I: Ord + Clone + Debug,
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
		let start =
			StartBound::from(search_range_bounds.start_bound().cloned());

		let end = StartBound::from(search_range_bounds.end_bound().cloned())
			.as_end_bound();

		dbg!(&start);
		dbg!(&end);
		let start_range_bounds = (
			//Included is lossless regarding meta-bounds searches
			//which is what we want
			Bound::Included(start),
			Bound::Included(end),
		);
		//this range will hold all the ranges we want except possibly
		//the first RangeBound in the range
		let most_range_bounds = self.starts.range(start_range_bounds);

		//then we check for this possibly missing range_bounds
		if let Some(missing_entry @ (_, (possible_missing_range_bounds, _))) =
			//Excluded is lossless regarding meta-bounds searches
			//because we don't want equal bounds as they would have be
			//covered in the previous step and we don't want duplicates
			self.starts
					.range((
						Bound::Unbounded,
						Bound::Excluded(
							//optimisation fix this without cloning
							StartBound::from(
								search_range_bounds.start_bound().cloned(),
							)
							.as_end_bound(),
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

#[cfg(test)]
mod tests {
	//all the functions in range_bounds_map rely upon overlapping so
	//if that works everything is likely to work so there are only
	//tests for overlapping()

	use std::ops::RangeBounds;

	use crate::bounds::StartBound;
	use crate::range_bounds_ext::RangeBoundsExt;
	use crate::test_helpers::{all_valid_test_bounds, TestBounds};
	use crate::RangeBoundsSet;

	#[test]
	fn mass_overlapping_test() {
		//case zero
		for overlap_range in all_valid_test_bounds() {
			//you can't overlap nothing
			assert!(
				RangeBoundsSet::new()
					.overlapping(&overlap_range)
					.next()
					.is_none()
			);
		}

		//case one
		for overlap_range in all_valid_test_bounds() {
			for inside_range in all_valid_test_bounds() {
				let mut range_bounds_set = RangeBoundsSet::new();
				range_bounds_set.insert(inside_range).unwrap();

				let mut expected_overlapping = Vec::new();
				if overlap_range.overlaps(&inside_range) {
					expected_overlapping.push(inside_range);
				}

				let overlapping = range_bounds_set
					.overlapping(&overlap_range)
					.copied()
					.collect::<Vec<_>>();

				if overlapping != expected_overlapping {
					dbg!(overlap_range, inside_range);
					dbg!(overlapping, expected_overlapping);
					panic!(
						"Discrepency in .overlapping() with single inside range detected!"
					);
				}
			}
		}

		//case two
		for overlap_range in all_valid_test_bounds() {
			for (inside_range1, inside_range2) in
				all_non_overlapping_test_bound_pairs()
			{
				let mut range_bounds_set = RangeBoundsSet::new();
				range_bounds_set.insert(inside_range1).unwrap();
				range_bounds_set.insert(inside_range2).unwrap();

				let mut expected_overlapping = Vec::new();
				if overlap_range.overlaps(&inside_range1) {
					expected_overlapping.push(inside_range1);
				}
				if overlap_range.overlaps(&inside_range2) {
					expected_overlapping.push(inside_range2);
				}
				//make our expected_overlapping the correct order
				if expected_overlapping.len() > 1 {
					if StartBound::from(expected_overlapping[0].start_bound())
						> StartBound::from(
							expected_overlapping[1].start_bound(),
						) {
						expected_overlapping.swap(0, 1);
					}
				}

				let overlapping = range_bounds_set
					.overlapping(&overlap_range)
					.copied()
					.collect::<Vec<_>>();

				if overlapping != expected_overlapping {
					dbg!(overlap_range, inside_range1, inside_range2);
					dbg!(overlapping, expected_overlapping);
					panic!(
						"Discrepency in .overlapping() with two inside ranges detected!"
					);
				}
			}
		}
	}

	fn all_non_overlapping_test_bound_pairs() -> Vec<(TestBounds, TestBounds)> {
		let mut output = Vec::new();
		for test_bounds1 in all_valid_test_bounds() {
			for test_bounds2 in all_valid_test_bounds() {
				if !test_bounds1.overlaps(&test_bounds2) {
					output.push((test_bounds1, test_bounds2));
				}
			}
		}

		return output;
	}
}
