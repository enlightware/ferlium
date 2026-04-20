use std::fmt;
use std::ops::{Index, IndexMut};

/// A doubly linked list.
pub struct List<T> {

  /// The number of elements in the list.
  size: usize,

  /// The offset of the list head.
  head_offset: usize,

  /// The offset of the list tail.
  tail_offset: usize,

  /// The position of the next free bucket in the list buffer.
  free_offset: usize,

  /// The elements in list.
  storage: Vec<Bucket<T>>,

}

impl<T> List<T> {

  /// Creates an empty list.
  pub fn new() -> Self {
    Self{
      size: 0,
      head_offset: !0,
      tail_offset: !0,
      free_offset: 0,
      storage: vec![],
    }
  }

  /// Returns `true` iff `self` is empty.
  pub fn is_empty(&self) -> bool {
    self.size == 0
  }

  /// Returns the number of elements in `self`.
  pub fn len(&self) -> usize {
    self.size
  }

  /// Returns the number of elements that can be stored in `self` without allocating new storage.
  pub fn capacity(&self) -> usize {
    self.storage.capacity()
  }

  /// Returns the position of the first element.
  pub fn first_address(&self) -> Option<Address> {
    if self.storage.is_empty() { None } else { Some(Address::new(self.head_offset)) }
  }

  /// Returns position of the last element.
  pub fn last_address(&self) -> Option<Address> {
    if self.storage.is_empty() { None } else { Some(Address::new(self.tail_offset)) }
  }

  ///s Returns the position that immediately follows `a`, if any.
  pub fn address_after(&self, a: Address) -> Option<Address> {
    assert!(self.in_bounds(a));
    if a == self.last_address() {
      None
    } else {
      Some(Address::new(self.storage[a.offset].next))
    }
  }

  /// Returns the position that immediately precedes `a`, if any.
  pub fn address_before(&self, a: Address) -> Option<Address> {
    assert!(self.in_bounds(a));
    if a == self.first_address() {
      None
    } else {
      Some(Address::new(self.storage[a.offset].previous))
    }
  }

  /// Returns an iterator over the contents of `self`.
  pub fn iter(&self) -> ListIterator<'_, T> {
    ListIterator { addresses: self.addresses() }
  }

  /// Returns an iterator over the addresses in `self`.
  pub fn addresses(&self) -> AddressIterator<'_, T> {
    AddressIterator  { base: self, position: self.first_address() }
  }

  /// Reserves enough space to store the `additional` new elements in `self` without allocating new
  /// storage.
  pub fn reserve(&mut self, k: usize) {
    let n = self.storage.len();
    let r = n - self.size;
    if k > r { self.storage.reserve(k - r); }
  }

  /// Inserts `x` at the end of `self` and returns its position.
  pub fn append(&mut self, x: T) -> Address {
    // Is the underlying storage empty?
    if self.storage.is_empty() {
      self.size = 1;
      self.head_offset = 0;
      self.tail_offset = 0;
      self.free_offset = 1;
      self.storage = vec![Bucket::new(!0, !0, x)];
      Address::new(0)
    }

    // Has the list been emptied?
    else if self.size == 0 {
      let new_offset = self.free_offset;
      self.size = 1;
      self.head_offset = self.free_offset;
      self.tail_offset = self.free_offset;
      self.free_offset = self.storage[new_offset].next;
      self.storage[new_offset].assign(!1, !1, x);
      Address::new(new_offset)
    }

    // Regular insertion.
    else {
      self.insert_after(Address::new(self.tail_offset), x)
    }
  }

  /// Inserts `x` at the start of `self` and returns its position.
  pub fn prepend(&mut self, x: T) -> Address {
    if self.is_empty() {
      self.append(x)
    } else {
      self.insert_before(Address::new(self.head_offset), x)
    }
  }

  /// Inserts `x` before the element at `a` and returns its position.
  pub fn insert_before(& mut self, a: Address, x: T) -> Address {
    assert!(self.in_bounds(a));

    // The offset of the previous bucket, if any.
    let p = self.storage[a.offset].previous;

    // Is the storage full or can we re-use a bucket that was emptied?
    let new_offset = if self.free_offset == self.storage.len() {
      self.storage.push(Bucket::new(p, a.offset, x));
      self.free_offset = self.storage.len();
      self.free_offset - 1
    } else {
      let new_offset = self.free_offset;
      self.free_offset = self.storage[self.free_offset].next;
      self.storage[new_offset].assign(p, a.offset, x);
      new_offset
    };

    // Update links.
    if a.offset == self.head_offset {
      self.head_offset = new_offset;
    } else {
      self.storage[p].next = new_offset;
    }
    self.storage[a.offset].previous = new_offset;

    // Update size.
    self.size += 1;
    Address::new(new_offset)
  }

  /// Inserts `x` after the element at `a` and returns its position.
  pub fn insert_after(&mut self, a: Address, x: T) -> Address {
    assert!(self.in_bounds(a));

    // The offset of the next bucket, if any.
    let n = self.storage[a.offset].next;

    // Is the storage full or can we re-use a bucket that was emptied?
    let new_offset = if self.free_offset == self.storage.len() {
      self.storage.push(Bucket::new(a.offset, n, x));
      self.free_offset = self.storage.len();
      self.free_offset - 1
    } else {
      let new_offset = self.free_offset;
      self.free_offset = self.storage[self.free_offset].next;
      self.storage[new_offset].assign(a.offset, n, x);
      new_offset
    };

    // Update links.
    if a.offset == self.tail_offset {
      self.tail_offset = new_offset;
    } else {
      self.storage[n].previous = new_offset;
    }
    self.storage[a.offset].next = new_offset;

    // Update size.
    self.size += 1;
    Address::new(new_offset)
  }

  /// Removes and returns the element at `a`.
  pub fn remove(&mut self, a: Address) -> T {
    assert!(self.in_bounds(a));

    let p = self.storage[a.offset].previous;
    if p != !0 { self.storage[p].next = self.storage[a.offset].next; }

    let n = self.storage[a.offset].next;
    if n != !0 { self.storage[n].previous = self.storage[a.offset].previous; }

    self.storage[a.offset].next = self.free_offset;

    self.size -= 1;
    self.free_offset = a.offset;
    if a.offset == self.head_offset { self.head_offset = n; }
    if a.offset == self.tail_offset { self.tail_offset = p; }

    self.storage[a.offset].element.take().unwrap()
  }

  /// Returns `true` iff `a` is a valid position in `self`.
  fn in_bounds(&self, a: Address) -> bool {
    a.offset < self.storage.len()
  }

}

impl<T> Index<Address> for List<T> {

  type Output = T;

  fn index(&self, a: Address) -> &T {
    assert!(self.in_bounds(a));
    self.storage[a.offset].element.as_ref().unwrap()
  }

}

impl<T> IndexMut<Address> for List<T> {

  fn index_mut(&mut self, a: Address) -> &mut T {
    assert!(self.in_bounds(a));
    self.storage[a.offset].element.as_mut().unwrap()
  }

}

impl<'a, T> IntoIterator for  &'a List<T> {

  type Item = &'a T;
  type IntoIter = ListIterator<'a, T>;

  fn into_iter(self) -> ListIterator<'a, T> {
    self.iter()
  }

}

impl<T> Extend<T> for List<T> {

  fn extend<I: IntoIterator<Item = T>>(&mut self, xs: I) {
    for x in xs {
      self.append(x);
    }
  }

}

impl<T : std::fmt::Debug> fmt::Debug for List<T> {

  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut builder = f.debug_list();

    let mut a = self.first_address();
    while let Some(b) = a {
      builder.entry(&self[b]);
      a = self.address_after(b);
    }

    builder.finish()
  }

}

/// The address of an element in a doubly linked list.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Address {

  /// The raw representation of this address.
  offset: usize,

}

impl Address {

  /// Creates a new instance with the given offset.
  fn new(offset: usize) -> Self { Address { offset } }

  /// Returns the raw value of this address.
  pub fn raw(&self) -> usize { self.offset }

}

impl PartialEq<Option<Address>> for Address {

  /// Returns `true` iff `self` is equal to the value wrapped in `other`.
  fn eq(&self, other: &Option<Address>) -> bool {
    if let Some(rhs) = other { self == rhs } else { false }
  }

}

/// An iterator over the contents of a doubly-linked list.
pub struct ListIterator<'a, T> {

  /// An iterator over the addresses of the contents produced by `self`.
  addresses: AddressIterator<'a, T>,

}

impl<'a, T> Iterator for ListIterator<'a, T> {

  type Item = &'a T;

  fn next(&mut self) -> Option<&'a T> {
    self.addresses.next().map(|a| &self.addresses.base[a])
  }

}

/// An iterator over the addresses of the elements of a doubly-linked list.
pub struct AddressIterator<'a, T> {

  /// The list whose contents is being iterated over.
  base: &'a List<T>,

  /// The current position of the iterator.
  position: Option<Address>,

}

impl<'a, T> Iterator for AddressIterator<'a, T> {

  type Item = Address;

  fn next(&mut self) -> Option<Address> {
    if let Some(a) = self.position {
      self.position = self.base.address_after(a);
      Some(a)
    } else {
      None
    }
  }

}

/// A bucket in the internal storage of a doubly linked list.
struct Bucket<T> {

  /// If the bucket is busy, this property is either the offset of the preceding bucket or `!0` if
  /// there isn't any. If the bucket is free, this property is unspecified.
  previous: usize,

  /// If the bucket is busy, this property is either the offset of the succeeding bucket or `!0` if
  /// there isn't any. If the bucket is free, this property is the offset of the next free bucket.
  next: usize,

  /// The stored element iff the bucket is busy.
  element: Option<T>,

}

impl<T> Bucket<T> {

  /// Creates a new instance with the given properties.
  fn new(previous: usize, next: usize, element: T) -> Self {
    Self { previous, next, element: Some(element) }
  }

  /// Assigns the value of `self`, assuming it is free.
  fn assign(&mut self, previous: usize, next: usize, element: T) {
    self.previous = previous;
    self.next = next;
    self.element = Some(element);
  }

}

#[cfg(test)]
mod tests {

  use super::*;

  #[test]
  fn test_is_empty() {
    let mut xs = List::<&str>::new();
    assert!(xs.is_empty());
    xs.append("a");
    assert!(!xs.is_empty());
  }

  #[test]
  fn test_len() {
    let mut xs = List::<&str>::new();
    assert_eq!(xs.len(), 0);

    let a = xs.append("a");
    assert_eq!(xs.len(), 1);

    let b = xs.append("b");
    assert_eq!(xs.len(), 2);

    xs.remove(a);
    assert_eq!(xs.len(), 1);

    xs.remove(b);
    assert_eq!(xs.len(), 0);
  }

  #[test]
  fn test_capacity() {
    let mut xs = List::<&str>::new();

    let a = xs.append("a");
    xs.extend(vec!["b", "c", "d"]);
    xs.remove(a);
    xs.reserve(48);
    assert!(xs.capacity() >= 48);
  }

  #[test]
  fn test_first_address() {
    let mut xs = List::<&str>::new();
    assert_eq!(xs.first_address(), None);

    let a = xs.append("a");
    assert_eq!(xs.first_address(), Some(a));

    let b = xs.append("b");
    assert_eq!(xs.first_address(), Some(a));
    assert_ne!(a, b);

    let c = xs.prepend("c");
    assert_eq!(xs.first_address(), Some(c));
  }

  #[test]
  fn test_last_address() {
    let mut xs = List::<&str>::new();
    assert_eq!(xs.last_address(), None);

    let a = xs.prepend("a");
    assert_eq!(xs.last_address(), Some(a));

    let b = xs.prepend("b");
    assert_eq!(xs.last_address(), Some(a));
    assert_ne!(a, b);

    let c = xs.append("c");
    assert_eq!(xs.last_address(), Some(c));
  }

  #[test]
  fn test_address_before() -> Result<(), String> {
    let mut xs = List::<&str>::new();
    xs.extend(vec!["a", "b"]);

    let b = xs.last_address().ok_or("unexpected None")?;
    let a = xs.address_before(b).ok_or("unexpected None")?;
    assert_eq!(xs[a], "a");
    assert_eq!(xs.address_before(a), None);

    Ok(())
  }

  #[test]
  fn test_address_after() -> Result<(), String> {
    let mut xs = List::<&str>::new();
    xs.extend(vec!["a", "b"]);

    let a = xs.first_address().ok_or("unexpected None")?;
    let b = xs.address_after(a).ok_or("unexpected None")?;
    assert_eq!(xs[b], "b");
    assert_eq!(xs.address_after(b), None);

    Ok(())
  }

  #[test]
  fn test_addresses() -> Result<(), String> {
    let mut xs = List::<&str>::new();
    xs.extend(vec!["a", "b"]);

    let ys = xs.addresses().map(|a| xs[a].clone());
    assert_eq!(ys, vec!["a", "b"]);
  }

  #[test]
  fn test_append() {
    let mut xs = List::<&str>::new();

    xs.append("a");
    assert!(xs.iter().eq(vec!["a"].iter()));

    let b = xs.append("b");
    assert!(xs.iter().eq(vec!["a", "b"].iter()));

    xs.append("c");
    assert!(xs.iter().eq(vec!["a", "b", "c"].iter()));

    xs.remove(b);
    xs.append("d");
    assert!(xs.iter().eq(vec!["a", "c", "d"].iter()));
  }

  #[test]
  fn test_prepend() {
    let mut xs = List::<&str>::new();

    xs.prepend("a");
    assert!(xs.iter().eq(vec!["a"].iter()));

    let b = xs.prepend("b");
    assert!(xs.iter().eq(vec!["b", "a"].iter()));

    xs.prepend("c");
    assert!(xs.iter().eq(vec!["c", "b", "a"].iter()));

    xs.remove(b);
    xs.prepend("d");
    assert!(xs.iter().eq(vec!["d", "c", "a"].iter()));
  }

  #[test]
  fn test_insert_before() {
    let mut xs = List::<&str>::new();

    let a = xs.prepend("a");
    xs.insert_before(a, "b");
    xs.insert_before(a, "c");
    assert!(xs.iter().eq(vec!["b", "c", "a"].iter()));
  }

  #[test]
  fn test_insert_after() {
    let mut xs = List::<&str>::new();

    let a = xs.prepend("a");
    xs.insert_after(a, "b");
    xs.insert_after(a, "c");
    assert!(xs.iter().eq(vec!["a", "c", "b"].iter()));
  }

}
