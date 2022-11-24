#[cfg(test)]
mod tests {
	use crate::range_bounds_map::RangeBoundsMap;
	// So there are a lot of permutations for overlaps checks: like 100's even
	// for less than 3 ranges inside the range_bounds_map
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
	// wrote a script to do it for me, and then I also wrote a cli
	// prorgram to ask me what the answer should be for each case
	// then the script generated the rust tests you see below

	// GENERATED
	// ==========================================================
}
