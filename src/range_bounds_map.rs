/*
Copyright 2022 James Forster

This file is part of range_bounds_map.

range_bounds_map is free software: you can redistribute it and/or
modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

range_bounds_map is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with range_bounds_map. If not, see <https://www.gnu.org/licenses/>.
*/

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::iter::once;
use std::ops::{Bound, RangeBounds};

use either::Either;

use crate::bounds::StartBound;

pub struct RangeBoundsMap<I, K, V> {
	starts: BTreeMap<StartBound<I>, (K, V)>,
}

impl<I, K, V> RangeBoundsMap<I, K, V>
where
	K: RangeBounds<I>,
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
			//optimisation fix this without cloning
			StartBound::from(range_bounds.start_bound().cloned()),
			(range_bounds, value),
		);

		return Ok(());
	}

	pub fn contains_point(&self, point: &I) -> bool {
		self.get(point).is_some()
	}

	pub fn overlaps<Q>(&self, search_range_bounds: &Q) -> bool
	where
		Q: RangeBounds<I>,
	{
		self.overlapping(search_range_bounds).next().is_some()
	}

	pub fn overlapping<Q>(
		&self,
		search_range_bounds: &Q,
	) -> impl Iterator<Item = (&K, &V)>
	where
		Q: RangeBounds<I>,
	{
		//optimisation fix this without cloning
		let start =
			StartBound::from(search_range_bounds.start_bound().cloned());
		//optimisation fix this without cloning
		let end = StartBound::from(search_range_bounds.end_bound().cloned())
			.as_end_bound();

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
						Bound::Excluded(StartBound::from(
							//optimisation fix this without cloning
							search_range_bounds.start_bound().cloned(),
						)),
					))
					.next_back()
		{
			if overlaps(possible_missing_range_bounds, search_range_bounds) {
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
			.overlapping(&(
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

fn overlaps<I, A, B>(a: &A, b: &B) -> bool
where
	A: RangeBounds<I>,
	B: RangeBounds<I>,
	I: PartialOrd,
{
	let a_start = a.start_bound();
	let a_end = a.end_bound();

	let b_start = b.start_bound();
	let b_end = b.end_bound();

	let (left_end, right_start) =
		match StartBound::from(a_start).cmp(&StartBound::from(b_start)) {
			Ordering::Less => (a_end, b_start),
			Ordering::Greater => (b_end, a_start),
			Ordering::Equal => return true,
		};

	match (left_end, right_start) {
		(Bound::Included(end), Bound::Included(start)) => end >= start,

		(Bound::Excluded(end), Bound::Excluded(start)) => end > start,
		(Bound::Included(end), Bound::Excluded(start)) => end > start,
		(Bound::Excluded(end), Bound::Included(start)) => end > start,

		(Bound::Unbounded, _) => true,

		(_, Bound::Unbounded) => unreachable!(),
	}
}

#[cfg(test)]
mod tests {
	use std::ops::{Bound, Range, RangeBounds};

	use super::overlaps;
	use crate::bounds::StartBound;
	use crate::RangeBoundsSet;

	type TestBounds = (Bound<u8>, Bound<u8>);

	//only every other number to allow mathematical_overlapping_definition
	//to test between bounds in finite using smaller intervalled finite
	pub(crate) const NUMBERS: &'static [u8] = &[2, 4, 6, 8, 10];
	//go a bit around on either side to compensate for Unbounded
	pub(crate) const NUMBERS_DOMAIN: &'static [u8] =
		&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

	#[test]
	fn mass_overlaps_test() {
		for range_bounds1 in all_valid_test_bounds() {
			for range_bounds2 in all_valid_test_bounds() {
				let our_answer = overlaps(&range_bounds1, &range_bounds2);

				let mathematical_definition_of_overlap =
					NUMBERS_DOMAIN.iter().any(|x| {
						range_bounds1.contains(x) && range_bounds2.contains(x)
					});

				if our_answer != mathematical_definition_of_overlap {
					dbg!(range_bounds1, range_bounds2);
					dbg!(mathematical_definition_of_overlap, our_answer);
					panic!("Discrepency in .overlaps() detected!");
				}
			}
		}
	}

	#[test]
	fn mass_overlapping_test() {
		//case zero
		for overlap_range in all_valid_test_bounds() {
			//you can't overlap nothing
			assert!(
				RangeBoundsSet::<u8, Range<u8>>::new()
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
				if overlaps(&overlap_range, &inside_range) {
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
				if overlaps(&overlap_range, &inside_range1) {
					expected_overlapping.push(inside_range1);
				}
				if overlaps(&overlap_range, &inside_range2) {
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
				if !overlaps(&test_bounds1, &test_bounds2) {
					output.push((test_bounds1, test_bounds2));
				}
			}
		}

		return output;
	}

	fn all_valid_test_bounds() -> Vec<TestBounds> {
		let mut output = Vec::new();

		//bounded-bounded
		output.append(&mut all_finite_bounded_pairs());
		//bounded-unbounded
		for start_bound in all_finite_bounded() {
			output.push((start_bound, Bound::Unbounded));
		}
		//unbounded-bounded
		for end_bound in all_finite_bounded() {
			output.push((Bound::Unbounded, end_bound));
		}
		//unbounded-unbounded
		output.push((Bound::Unbounded, Bound::Unbounded));

		return output;
	}

	fn all_finite_bounded_pairs() -> Vec<(Bound<u8>, Bound<u8>)> {
		let mut output = Vec::new();
		for i in NUMBERS {
			for j in NUMBERS {
				for i_ex in [false, true] {
					for j_ex in [false, true] {
						if j > i || (j == i && !i_ex && !j_ex) {
							output.push((
								finite_bound(*i, i_ex),
								finite_bound(*j, j_ex),
							));
						}
					}
				}
			}
		}
		return output;
	}

	fn all_finite_bounded() -> Vec<Bound<u8>> {
		let mut output = Vec::new();
		for i in NUMBERS {
			for j in 0..=1 {
				output.push(finite_bound(*i, j == 1));
			}
		}
		return output;
	}

	fn finite_bound(x: u8, included: bool) -> Bound<u8> {
		match included {
			false => Bound::Included(x),
			true => Bound::Excluded(x),
		}
	}
}
