use std::collections::{BTreeSet, HashMap};
use std::marker::PhantomData;
use std::ops::{Bound, RangeBounds};

use derive_new::new;

use crate::specific_bounds::{EndBound, StartBound};

type Id = u128;

//todo switch to slot map thingy
#[derive(Default, new)]
pub struct RangeBoundsSet<T, I> {
	#[new(default)]
	ranges: HashMap<Id, T>,
	#[new(default)]
	starts: BTreeSet<StartBound<I>>,
	#[new(default)]
	ends: BTreeSet<EndBound<I>>,
	phantom_data: PhantomData<I>,

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
	pub fn insert(&mut self, range: T) -> Result<(), ()> {
		Ok(())
	}

	pub fn raw_insert(&mut self, range: T) {}

	pub fn overlapping(&self, range: T) {
		let end_bounds_range = (
			EndBound::from(range.start_bound().cloned()),
			EndBound::from(range.end_bound().cloned()),
		);
		self.ends.range(end_bounds_range);
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
