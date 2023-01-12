#![feature(test)]

extern crate test;
use test::Bencher;

extern crate range_bounds_map;
use range_bounds_map::*;

/// linear multiplier for work done by benchmarks
const REPEAT: usize = 120;

#[bench]
fn bench_insert_platonic(b: &mut Bencher) {
	b.iter(|| {
		let mut map = RangeBoundsMap::new();
		for i in 0..REPEAT {
			let r = i..=i;
			if let Err(OverlapError) = map.insert_platonic(r, i) {
				panic!("Failed to insert");
			}
		}
	});
}

#[bench]
fn bench_insert_coalesce_touching(b: &mut Bencher) {
	b.iter(|| {
		let mut map = RangeBoundsMap::new();
		for i in 0..REPEAT / 2 {
			let r1 = (10 * i)..(10 * i + 1);
			let r2 = (10 * i + 1)..(10 * i + 2);
			if let Err(e) = map.insert_coalesce_touching(r1, true) {
				panic!("Failed to insert: {:?}", e)
			}
			if let Err(e) = map.insert_coalesce_touching(r2, true) {
				panic!("Failed to insert: {:?}", e)
			}
		}
	})
}

#[bench]
fn bench_insert_coalesce_overlapping(b: &mut Bencher) {
	b.iter(|| {
		let mut map = RangeBoundsMap::new();
		for i in 0..REPEAT / 2 {
			let r1 = (10 * i)..(10 * i + 1);
			let r2 = (10 * i)..(10 * i + 2);
			if let Err(e) = map.insert_coalesce_overlapping(r1, true) {
				panic!("Failed to insert: {:?}", e)
			}
			if let Err(e) = map.insert_coalesce_overlapping(r2, true) {
				panic!("Failed to insert: {:?}", e)
			}
		}
	})
}

#[bench]
fn bench_insert_coalesce_touching_or_overlapping(b: &mut Bencher) {
	b.iter(|| {
		let mut map = RangeBoundsMap::new();
		for i in 0..REPEAT / 2 {
			let r1 = (10 * i + 1)..(10 * i + 2);
			let r2 = (10 * i)..(10 * i + 4);
			if let Err(e) = map.insert_coalesce_touching_or_overlapping(r1, 1) {
				panic!("Failed to insert: {:?}", e)
			}
			if let Err(e) = map.insert_coalesce_touching_or_overlapping(r2, 2) {
				panic!("Failed to insert: {:?}", e)
			}
		}
	})
}
