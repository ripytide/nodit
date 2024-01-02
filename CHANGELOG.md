# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

<!-- next-header -->

## Unreleased - ReleaseDate

### Added

- Added a missing implementation of `DiscreteFinite` for `usize`, #54
- Added implementations for:
  - `From<InclusiveInterval> for std::ops::Range`
  - `From<std::ops::Range> for InclusiveInterval`
  - `From<InclusiveInterval> for std::ops::RangeInclusive`
  - `From<std::ops::RangeInclusive> for InclusiveInterval`

### Changed

- `InclusiveInterval` has now been given generic constructors and proper
  documentation for use by end-users, #56
- `insert_overwrite()` now returns the cut entries, #51
- Renamed `gaps()` to `gaps_trimmed()` and added a `gaps_untrimmed()` method
- Mass replaced renamed from the word "range" to the word "interval" all code
  items, docs.

### Fixed

- The now generic constructors for `InclusiveInterval` will all now panic on
  creation of an invalid interval to propagate errors earlier in users' code for
  a better debugging experience.
- Documentation has been heavily worked to make it better and more up to date
  with more examples

## 0.6.2 - 2023-12-26

### Added

- Documentation now added to every item in the crate by
  enforcing `missing_docs = "deny"`

### Changed

- `OverlapError` now returns the value that was attempted to be inserted to
  match up with `BTreeMap` and other `std` rust insert methods, #43

## 0.6.1 - 2023-12-06

### Added

- Added intersection and translation methods to the `InclusiveRange` trait, #46

## 0.6.0 - 2023-12-03

### Added

- `no_std` is now supported

### Fixed

- Refactored trait bounds into single `PointType` and `RangeType` marker
  traits

## 0.5.2 - 2023-09-11

### Added

- Added a `from_iter_stric()` method to the map and set.

## 0.5.1 - 2023-07-01

### Fixed

- Updated dependencies to fix a compile error

## 0.5.0 - 2023-07-01

### Added

- Added new `InclusiveRange` trait
- Renamed lots of items to make them more consistent

## 0.4.3 - 2023-06-03

### Changed

- Removed lots of unnecessary bounds for many functions and the Serialize trait

## 0.4.2 - 2023-06-11

### Changed

- Renamed `DiscreteFiniteBounds` to `Interval` and gave it some utility
  functions

## 0.4.1 - 2023-04-16

### Fixed

- Improved the performance of `remove_overlapping()` and all functions which use
  it internally in #44

## 0.4.0 - 2023-04-24

### Changed

- The crate was renamed from `range_bounds_map` to `discrete_range_map` in #41
- The behaviour of the crate was switched from continuous to discrete intervals
  in #41
- The behaviour of the crate was switched from possibly unbounded intervals to
  assumed Finite intervals in #41

## 0.3.2 - 2023-04-19

### Changed

- Made `gaps()` return a `DoubleEndedIterator`, #32

## 0.3.1 - 2023-04-19

### Changed

- Changed return type of `get_entry_at_point()` and `get_at_point()` to a
  `Result` instead of an `Option` to return the gap interval if no
  entry is found, #31

## 0.3.0 - 2023-04-18

### Added

- Added `insert_merge_touching_if_values_equal()` method to `RangeBoundsMap`, #30

## 0.2.2 - 2023-04-10

### Added

- Added `get_at_point()` back to `RangeBoundsSet`

## 0.2.1 - 2023-04-09

### Added

- Added basic trait derives to the set

## 0.2.0 - 2023-04-07

### Changed

- Renamed all instances of the word `coalesce` with the word `merge` in #12
- Renamed `overwrite` to `insert_overwrite` in #13
- Renamed `insert_platonic` to `insert_strict` in #14
- Reverted "Remove Implementations of `FromIterator` and other
  `From<other_collection>` traits" in #17
- BTree Monstrousity Implementation in #26

### Fixed

- Better Panic Messages in #28

### Added

- Added `Panics` sections to the documentation where applicable in #15
- Added `append_*` functions for all the associated `insert_*` functions in #19
- Added \_mut methods in #27

### Removed

- Removed Implementations of `FromIterator` and other
  `From<other_collection>` traits in #16
- Removed Implementations of `FromIterator` and other
  `From<other_collection>` traits (PR 2) in #18

## 0.1.1 - 2023-03-31

### Changed

- Added method `trimmed_overlapping()` in #2
