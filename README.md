# range_bounds_map

# What

This is a library that provides two main data structures,
`RangeBoundsMap` and `RangeBoundsSet`. `RangeBoundsMap` is similar to
`BTreeMap` except `RangeBoundsMap` uses any type that implements
`RangeBounds` as keys, while maintaining two invariants: no two
keys map overlap, and a keys `start_bound()` >= its `end_bound()`.
In the same fashion, `RangeBoundSet` is similar to `BTreeSet` except
it stores any type that implements `RangeBounds`.

# Examples

# Why

Chances are most people reading this will know why they might or might
not need this data structure. However, if you are not one of those
people see the above example for a small subset of the functionality
this crate provides.

# How

# Caveats

There are a few issues I can think of with this implementation, each
of them are documented as GitHub Issues. But to summarise:

- No coalescing insert functions, yet.
- No `gaps()` iterator function, yet.
- Sub-optimal use of unnecessary `cloned()` just to placate the borrow checker.
- Requirement for `dummy()` trait function needed to implement some of
  the internal functions that wouldn't be neccessary if `BTreeMap` had
  either a Cursor API or a Comparator API (google for the respective
  rust-lang issues) However the `dummy()` trait function would be
  unavoidable for the `gaps()` function if you wanted an iterator over
  your same key type.

# Improvements

# Credit

I orignally come up with the `StartBound`: `Ord` bodge on my
own, however, I later stumbled across `rangemap` which also used a
`StartBound`: `Ord` bodge. `rangemap` then became my main soure of
inspiration. The aim for my library was to become a more generic
superset of `rangemap`, following from
(this issue)[https://github.com/jeffparsons/rangemap/issues/56] and
(this pull request)[https://github.com/jeffparsons/rangemap/pull/57]
in which I changed `rangemap`'s `RangeMap` to use `RangeBounds`'s as
keys before I realized it might be easier and simpler to just write it
all from scratch. Which ended up working really well with some
simplifications I made which ended up resulting in much less code
(~600 lines over `rangemap`'s ~2700)

# Similar Crates

Here are some relevant crates I found whilst searching around the
topic area:

- (rangemap)[https://docs.rs/ranges]
  Very similar to this crate but can only use `Range`s and
  `RangeInclusive` as keys in it's `map` and `set` structs (separately).
- (ranges)[https://docs.rs/ranges]
  Cool library for fully-generic ranges (unlike std::ops ranges), along
  with a `Ranges` datastructure for storing them (Vec-based
  unfortunately)
- (intervaltree)[https://docs.rs/intervaltree]
  Allows overlapping intervals but is immutable unfortunately
- (nonoverlappingintervaltree)[https://docs.rs/nonoverlapping_interval_tree]
  Very similar to rangemap except without a `gaps()` function and only
  for Range's and not RangeInclusive's. And also no fancy coalescing
  functions.
- (unbounded_interval_tree)[https://docs.rs/unbounded-interval-tree]
  A data structure based off of a 2007 published paper! It supports any
  RangeBounds as keys too, except it is implemented with a non-balancing
  Box<Node> based tree, however it also supports overlapping
  RangeBounds which my library does not.
- (rangetree)[https://docs.rs/rangetree]
  I'm not entirely sure what this library is or isn't, but it looks like
  a custom red-black tree/BTreeImplementation used specifically for a
  Range Tree. Interesting but also quite old (5 years) and uses
  unsafe.

add optimisation comments on all cloned() uses
add documentation to EVERYTHING
test cargo docs
add issues to github for all the caveats and cloned() optimisations
add caveat and gh#issue for dummy() and documentation for it too ;P
add examples for all functions in rust doc comments and test them with cargo doc-test
add some actual rust example files in an example folder
convert README to cool format using links to docs
add github badges including lib.rs
make logo
fix todo for checking insert reverse ranges
use it in robot_Sweet_graph for a bit before publishing
add CI
