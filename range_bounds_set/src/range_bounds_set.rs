use crate::range_bounds_ext::RangeBoundsExt;
use crate::range_bounds_map::RangeBoundsMap;

pub struct RangeBoundsSet<I, K> {
	map: RangeBoundsMap<I, K, ()>,
}

impl<I, K> RangeBoundsSet<I, K>
where
	K: RangeBoundsExt<I> + std::fmt::Debug,
	I: Ord + Clone + std::fmt::Debug,
{
	pub fn new() -> Self {
		RangeBoundsSet {
			map: RangeBoundsMap::new(),
		}
	}

	//returns Err(()) if the given range overlaps another range
	//does not coalesce ranges if they touch
	pub fn insert(&mut self, range_bounds: K) -> Result<(), ()> {
		self.map.insert(range_bounds, ())
	}

	pub fn overlaps(&self, search_range_bounds: &K) -> bool {
		self.map.overlaps(search_range_bounds)
	}

	pub fn overlapping(
		&self,
		search_range_bounds: &K,
	) -> impl Iterator<Item = &K> {
		self.map
			.overlapping(search_range_bounds)
			.map(|(key, _)| key)
	}

	pub fn get(&self, point: &I) -> Option<&K> {
		self.map.get_key_value(point).map(|(key, _)| key)
	}

	pub fn contains_point(&self, point: &I) -> bool {
		self.map.contains_point(point)
	}

	pub fn iter(&self) -> impl Iterator<Item = &K> {
		self.map.iter().map(|(key, _)| key)
	}
}
