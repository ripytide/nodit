use std::ops::Bound;

pub type TestBounds = (Bound<u8>, Bound<u8>);

pub fn all_valid_test_bounds() -> Vec<TestBounds> {
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

pub const NUMBERS: &'static [u8] = &[2, 4, 6, 8, 10];
//go a bit around on either side to compensate for Unbounded
pub const NUMBERS_DOMAIN: &'static [u8] =
	&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

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
