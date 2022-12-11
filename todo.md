# refactor

- try to fix all the uses of cloned() in the library
- make a StartBoundWrapper that uses StartBound to implement ord and
  use that instead of storing the startbound twice
- make a range_bounds configuration: NonOverlapping, A contained in B,
  A partial overlap B, with A before B. And use it to simplify all the
  logic based RangeBounds functions
- make an expand function to go RangeBounds -> (Bound, Bound) rather
  than doing it manually everywhere

# features

- make specifc RangeMap, RangeSet, RangeInclusiveMap... types for signature
  simplification
- alternatively add just the one generic SafeRangeBoundsMap + Set that
  just add unwraps everywhere to simplify signatures on known-"Safe"
  symmetric types such as Range

- make gaps() DoubleEndedIterator
- make all iterators cutsom types as is standardised in libraries for
  some reason

- add coalesce if same-value otherwise overwrite) function to make
  finally make range_bounds_map a superset of rangemap

- make cut() return and Ok(Iterator((Bound, Bound))) like gaps()
- add gaps_same() and cut_same() which are gaps().map(to K) and
  cut().map(to K) using TryFromBounds
- update the TryFromBoundsError with examples of new gaps() and cut()

# time based

- use it in robot_Sweet_graph for a bit before publishing

# final checks

- remove most rustfmt::skips and cargo fmt
- check toml meta-data, github meta-data and readme opener
- copy map to set again
- copy readme to lib.rs docs again
- take a look around idiomatic rust for a bit first
- run is_labelled again and check they are accurate
- review method parameter names for all public functions
- update lines of code figures on docs
- add issues to github for all the caveats
- review caveats again
- run and fix cargo clippy

- PUBLISH

# after publish tasks

- add links to [`RangeBoundsSet`] and map after docs.rs is live with
  the docs, and generally check for dead links on docs and readme
- tell people in issues of other rangemap libraries about my library
  stonks advertising
