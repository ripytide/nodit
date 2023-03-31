#![feature(test)]

extern crate test;
use test::Bencher;

extern crate range_bounds_map;
use range_bounds_map::*;

/// linear multiplier for work done by benchmarks
const REPEAT: usize = 120;

#[bench]
fn bench_insert_strict(b: &mut Bencher) {
	b.iter(|| {
		let mut map = RangeBoundsMap::new();
		for i in 0..REPEAT {
			let r = i..=i;
			map.insert_strict(r, i).expect("insert failed");
		}
	});
}

#[bench]
fn bench_insert_merge_touching(b: &mut Bencher) {
	b.iter(|| {
		let mut map = RangeBoundsMap::new();
		for i in 0..REPEAT / 2 {
			let r1 = (10 * i)..(10 * i + 1);
			let r2 = (10 * i + 1)..(10 * i + 2);
			map.insert_merge_touching(r1, true)
				.expect("Failed to insert");
			map.insert_merge_touching(r2, true)
				.expect("Failed to insert");
		}
	})
}

#[bench]
fn bench_insert_merge_overlapping(b: &mut Bencher) {
	b.iter(|| {
		let mut map = RangeBoundsMap::new();
		for i in 0..REPEAT / 2 {
			let r1 = (10 * i)..(10 * i + 1);
			let r2 = (10 * i)..(10 * i + 2);
			map.insert_merge_overlapping(r1, true)
				.expect("Failed to insert");
			map.insert_merge_overlapping(r2, true)
				.expect("Failed to insert");
		}
	})
}

#[bench]
fn bench_insert_merge_touching_or_overlapping(b: &mut Bencher) {
	b.iter(|| {
		let mut map = RangeBoundsMap::new();
		for i in 0..REPEAT / 2 {
			let r1 = (10 * i + 1)..(10 * i + 2);
			let r2 = (10 * i)..(10 * i + 4);
			map.insert_merge_touching_or_overlapping(r1, 1)
				.expect("Failed to insert");
			map.insert_merge_touching_or_overlapping(r2, 2)
				.expect("Failed to insert");
		}
	})
}

#[bench]
fn bench_insert_overwrite(b: &mut Bencher) {
	b.iter(|| {
		let mut map = RangeBoundsMap::new();
		for i in 0..REPEAT {
			let r = i..i + 2;
			map.insert_overwrite(r, i).expect("insert failed");
		}
	});
}
