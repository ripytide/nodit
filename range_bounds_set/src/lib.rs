#![feature(is_some_and)]
#![feature(let_chains)]
pub mod bounds;
pub mod range_bounds_ext;
pub mod range_bounds_map;
pub mod range_bounds_set;

#[cfg(test)]
pub mod test_helpers;

pub use crate::range_bounds_map::RangeBoundsMap;
pub use crate::range_bounds_set::RangeBoundsSet;
