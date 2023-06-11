use crate::discrete_finite::DiscreteFinite;
use crate::interval::Interval;

pub fn uu() -> Interval<i8> {
	Interval {
		start: i8::MIN,
		end: i8::MAX,
	}
}
pub fn ui(x: i8) -> Interval<i8> {
	Interval {
		start: i8::MIN,
		end: x,
	}
}
pub fn ue(x: i8) -> Interval<i8> {
	Interval {
		start: i8::MIN,
		end: x.down().unwrap(),
	}
}
pub fn iu(x: i8) -> Interval<i8> {
	Interval {
		start: x,
		end: i8::MAX,
	}
}
//fn eu(x: i8) -> TestBounds {
//(Bound::Excluded(x), Bound::Unbounded)
//}
pub fn ii(x1: i8, x2: i8) -> Interval<i8> {
	Interval { start: x1, end: x2 }
}
pub fn ie(x1: i8, x2: i8) -> Interval<i8> {
	Interval {
		start: x1,
		end: x2.down().unwrap(),
	}
}
pub fn ei(x1: i8, x2: i8) -> Interval<i8> {
	Interval {
		start: x1.up().unwrap(),
		end: x2,
	}
}
pub fn ee(x1: i8, x2: i8) -> Interval<i8> {
	Interval {
		start: x1.up().unwrap(),
		end: x2.down().unwrap(),
	}
}
