#![doc = include_str!("../README.md")]
#![allow(clippy::tabs_in_doc_comments)]
#![allow(clippy::needless_return)]
#![no_std]

extern crate alloc;

pub(crate) mod utils;

pub mod discrete_finite;
pub mod gqdit;
pub mod interval;
pub mod nodit;
pub mod zosdit;

pub use crate::discrete_finite::DiscreteFinite;
pub use crate::gqdit::{Gqdit, IdType};
pub use crate::interval::{InclusiveInterval, Interval};
pub use crate::nodit::map::{IntervalType, NoditMap, OverlapError, PointType};
pub use crate::nodit::set::NoditSet;
pub use crate::zosdit::map::{NonZeroOverlapError, ZosditMap};
