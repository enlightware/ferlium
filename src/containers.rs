use std::cmp;

pub type SmallVec1<T> = smallvec::SmallVec<[T; 1]>;
pub type SmallVec2<T> = smallvec::SmallVec<[T; 2]>;

/// A struct that holds an optional first item of an iterator.
pub struct First<T>(pub Option<T>);

impl<T> FromIterator<T> for First<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        First(iter.into_iter().next())
    }
}

pub fn compare_by<T, F>(left: &[T], right: &[T], compare: F) -> cmp::Ordering
where
    T: cmp::Ord,
    F: Fn(&T, &T) -> cmp::Ordering,
{
    let l = cmp::min(left.len(), right.len());
    let lhs = &left[..l];
    let rhs = &right[..l];

    for i in 0..l {
        match compare(&lhs[i], &rhs[i]) {
            cmp::Ordering::Equal => (),
            non_eq => return non_eq,
        }
    }

    left.len().cmp(&right.len())
}
