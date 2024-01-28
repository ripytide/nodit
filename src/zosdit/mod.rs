//! A module containing the `zosdit` data-structures.
//!
//! `zosdit` stands for Zero-Overlap Sequential Discrete Interval Tree.
//!
//! These data-structures are very similar to the `nodit` data-structures, except where in `zosdit`
//! no overlapping at all is allowed within the data-structure, `zosdit` is slightly more relaxed
//! in that you are allowed overlaps as long as they are "zero-overlaps".
//!
//! ## Zero-Overlap
//!
//! In this crate, zero-overlap is the term used to describe when intervals have zero-width
//! overlap, for example the intervals `0..=4` and `4..=10` overlap since they both contain the
//! point `4`, however, they are also deemed to have zero-overlap as the width of their
//! intersection (4..=4) is zero (4 - 4 = 0).
//!
//! However, there is another restriction to our definition of zero-overlap, and that is that
//! singular intervals (like 4..=4) cannot be completely inside other intervals. For example,
//! (4..=8) and (6..=6) despite having zero-width intersection are deemed to still not be classed
//! as having zero-overlap.
//!
//! These two restrictions then give natural zero-overlap sequences of intervals such as [`0..=4`,
//! `4..=4`, `4..=4`, `4..=4`, `4..=6`, `6..=10`]. This is where the sequential part comes in as
//! when inserting a new interval into the data-structure those three `4..=4` intervals are
//! inserted to the back of the same intervals (if using `insert_strict_back()`).
//!
//! The main use-case for these data-structures at the moment is for time-traversal of a graph. So
//! if you wanted to describe the time-taken when walking along a graph with perhaps some
//! zero-sized and some non-zero-sized edges losslessly and efficiently then this is the sort of
//! data-structure you might want to use.

pub mod map;
