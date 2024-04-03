pub type SmallVec1<T> = smallvec::SmallVec<[T; 1]>;
pub type SmallVec2<T> = smallvec::SmallVec<[T; 2]>;

/// A struct that holds an optional first item of an iterator.
pub struct First<T>(pub Option<T>);

impl<T> FromIterator<T> for First<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        First(iter.into_iter().next())
    }
}
