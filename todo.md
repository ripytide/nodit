# refactor

- try to remove unnecessary uses of cloned()
- use expand, expand_cloned and cloned_bounds everywhere
- replace instances of |(key, \_)| with fn first()
- rename insert_overwrite to insert_forceful
- make all iterators cutsom types as is standardised in libraries for
  some reason(?)
- take a look around idiomatic rust for a bit
- review method parameter names for all public functions
- make try_from_bounds trait return TryFromBoundsError rather than
  mapping the option all the time

# optimisations

- make a StartBoundWrapper that uses BoundOrd to implement ord and
  use that instead of storing the startbound twice

# Documentation

- replace `RangeBounds` with `K` where applicatble in docs
- replace rust types URL links with direct rust links
- normalize the description of the project beteen:
  - the first line of the crate levele docs/readme
  - the description meta-data section on github
  - the descriptio meta-data field in the Cargo.toml

# features

- make specifc RangeMap, RangeSet, RangeInclusiveMap... types for signature
  simplification - alternatively add just the one generic SafeRangeBoundsMap + Set that
  just add unwraps everywhere to simplify signatures on known-"Safe"
  symmetric types such as Range
- add rangemap's insert function to finally make range_bounds_map a superset of rangemap

- add remove_at_point(), clear(), etc..

- add a multi-dimentional version of RandBounds{Map,Set} by compositing Normal 1D RangeBoundsSets together in a big Vec or something.

# open questions

- should we implement FromIterator? If so which insert should we use?
  (At the moment we do implement it using insert_strict())
- should append\_\* functions not change the base if they fail half way?


#### PUBLISH

# after publish tasks

- add links to [`RangeBoundsSet`] and map after docs.rs is live with
  the docs, and generally check for dead links on docs and readme
- tell people in issues of other rangemap libraries about my library
  stonks advertising



# new todos

- the docs annoy me with sometimes including "Basic usage:" and
  sometimes not, this may not be unique just the btree_cursors
  function docs though.
- no examples in the docs for Cursors and CursorsMut unlike Entry docs
  for some other collections which have nice docs.
- remove unused dependencies
- update cut docs to say they just return (K, V) now
- same with gaps docs except with I instead of &I now

- grep for docs on doubleiterator and change to single now
