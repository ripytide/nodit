#![feature(is_some_and)]
#![feature(let_chains)]
pub(crate) mod bounds;
pub mod range_bounds_ext;
pub mod range_bounds_map;
pub mod range_bounds_set;

#[cfg(test)]
pub(crate) mod test_helpers;

pub use crate::range_bounds_map::RangeBoundsMap;
pub use crate::range_bounds_set::RangeBoundsSet;
