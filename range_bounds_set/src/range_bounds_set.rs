use std::collections::{BTreeSet, HashMap, BTreeMap};
use std::marker::PhantomData;

use derive_new::new;

use crate::bounds::{EndBound, StartBound};
use crate::range_bounds::RangeBounds;
use crate::StdBound;

type Id = u128;

//todo switch to slot map thingy
#[derive(new)]
pub struct RangeBoundsSet<T, I> {
	#[new(value="BTreeMap::new()")]
	starts: BTreeMap<StartBound<I>, T>,

	#[new(default)]
	id: u128,
}

impl<T, I> RangeBoundsSet<T, I>
where
	T: RangeBounds<I>,
	I: Ord + Clone,
{
	//returns Err(()) if the inserting the given range overlaps another range
	//coalesces ranges if they touch
	pub fn insert(&mut self, range_bounds: T) -> Result<(), ()> {
		Ok(())
	}

	pub fn raw_insert(&mut self, range_bounds: T) {}

	pub fn overlapping(&self, range_bounds: T) {
		let start_range_bounds = (
			//we require the EndBound:Ord imlementation to work with
			//the Included range only
			StdBound::Included(range_bounds.start_bound().cloned()),
			StdBound::Included(StartBound::from(range_bounds.end_bound().cloned())),
		);
		//this range will hold all the ranges we want except possibly
		//the last RangeBounds
		let ends_range = self.starts.range(start_range_bounds);

        let possible_missing_range_bounds = self.starts.
	}

	pub fn get(&self, point: &I) {}
}

#[cfg(test)]
mod tests {
	//use pretty_assertions::assert_eq;

	use super::*;

	// So there are a lot of permutations for overlaps checks: like 100's even
	// for less than 3 ranges inside the see my picture in
	// notes/ for an idea
	// Hence the strategy since I want thorough testing at least for
	// T = { 0, 1, 2 } where T is the number of ranges in the rangeset
	// upon query, and I want every valid (maintains invariant of no
	// overlaps (only relevant for T=2)) permutation of query to
	// interval set to have it's own test.
	//
	// This strategy is open-ended if anyone feels like manually
	// inputing the T=3 cases ;p
	//
	// And so rather than figuring all the valid cases manually I
	// wrote a script to do it for me, and then I also wrote a helper
	// script to streamline the manual input process. The script
	// essentially enumerates all of the generated cases and asks me
	// to input the expected
	//
	//
	//
	//
	//
	//
	//
	//
	//
	//
	// Rusts Bounds types are overly ambiguous in RangeBouns, it
	// should return StartBound and EndBound so that you can
	// implement Ord on them
}
