use nonmax::NonMaxU32;
use std::fmt;
use std::ops::{Index, IndexMut};

/// A doubly linked list.
pub struct List<T> {
    /// The number of elements in the list.
    size: usize,

    /// The address of the list head.
    head: Option<Address>,

    /// The address of the list tail.
    tail: Option<Address>,

    /// The head of the free-bucket list.
    free: Option<Address>,

    /// The elements in list.
    storage: Vec<Bucket<T>>,
}

impl<T> List<T> {
    /// Creates an empty list.
    pub fn new() -> Self {
        Self {
            size: 0,
            head: None,
            tail: None,
            free: None,
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

    /// Returns the position of the first element, if any.
    pub fn first_address(&self) -> Option<Address> {
        self.head
    }

    /// Returns position of the last element, if any.
    pub fn last_address(&self) -> Option<Address> {
        self.tail
    }

    /// Returns the position that immediately follows `a`, if any.
    pub fn address_after(&self, a: Address) -> Option<Address> {
        assert!(self.in_bounds(a));
        self.storage[a.as_index()].next
    }

    /// Returns the position that immediately precedes `a`, if any.
    pub fn address_before(&self, a: Address) -> Option<Address> {
        assert!(self.in_bounds(a));
        self.storage[a.as_index()].previous
    }

    /// Returns an iterator over the contents of `self`.
    pub fn iter(&self) -> ListIterator<'_, T> {
        ListIterator {
            addresses: self.addresses(),
        }
    }

    /// Returns an iterator over the addresses in `self`.
    pub fn addresses(&self) -> AddressIterator<'_, T> {
        AddressIterator {
            base: self,
            position: self.first_address(),
        }
    }

    /// Reserves enough space to store `k` additional elements in `self` without reallocating its
    /// storage.
    pub fn reserve(&mut self, k: usize) {
        let n = self.storage.len();
        let r = n - self.size;
        if k > r {
            let additional = k - r;
            assert!(
                additional <= Address::CAPACITY - n,
                "list address space exhausted"
            );
            self.storage.reserve(additional);
        }
    }

    /// Inserts `x` at the end of `self` and returns its position.
    pub fn append(&mut self, x: T) -> Address {
        if self.is_empty() {
            let address = self.allocate_bucket(None, None, x);
            self.size = 1;
            self.head = Some(address);
            self.tail = Some(address);
            address
        } else {
            self.insert_after(self.tail.expect("a non-empty list has a tail"), x)
        }
    }

    /// Inserts `x` at the start of `self` and returns its position.
    pub fn prepend(&mut self, x: T) -> Address {
        if self.is_empty() {
            self.append(x)
        } else {
            self.insert_before(self.head.expect("a non-empty list has a head"), x)
        }
    }

    /// Inserts `x` before the element at `a` and returns its position.
    pub fn insert_before(&mut self, a: Address, x: T) -> Address {
        assert!(self.in_bounds(a));

        let previous = self.storage[a.as_index()].previous;
        let new_address = self.allocate_bucket(previous, Some(a), x);

        // Update links.
        if let Some(previous) = previous {
            self.storage[previous.as_index()].next = Some(new_address);
        } else {
            self.head = Some(new_address);
        }
        self.storage[a.as_index()].previous = Some(new_address);

        // Update size.
        self.size += 1;
        new_address
    }

    /// Inserts `x` after the element at `a` and returns its position.
    pub fn insert_after(&mut self, a: Address, x: T) -> Address {
        assert!(self.in_bounds(a));

        let next = self.storage[a.as_index()].next;
        let new_address = self.allocate_bucket(Some(a), next, x);

        // Update links.
        if let Some(next) = next {
            self.storage[next.as_index()].previous = Some(new_address);
        } else {
            self.tail = Some(new_address);
        }
        self.storage[a.as_index()].next = Some(new_address);

        // Update size.
        self.size += 1;
        new_address
    }

    /// Removes and returns the element at `a`.
    pub fn remove(&mut self, a: Address) -> T {
        assert!(self.in_bounds(a));

        let index = a.as_index();
        let previous = self.storage[index].previous;
        let next = self.storage[index].next;

        if let Some(previous) = previous {
            self.storage[previous.as_index()].next = next;
        } else {
            self.head = next;
        }
        if let Some(next) = next {
            self.storage[next.as_index()].previous = previous;
        } else {
            self.tail = previous;
        }

        self.size -= 1;
        self.storage[index].previous = None;
        self.storage[index].next = self.free;
        self.free = Some(a);

        self.storage[index].element.take().unwrap()
    }

    /// Returns `true` iff `a` is a valid position in `self`.
    fn in_bounds(&self, a: Address) -> bool {
        self.storage
            .get(a.as_index())
            .is_some_and(|bucket| bucket.element.is_some())
    }

    /// Allocates a bucket, reusing a removed bucket when possible.
    fn allocate_bucket(
        &mut self,
        previous: Option<Address>,
        next: Option<Address>,
        element: T,
    ) -> Address {
        if let Some(address) = self.free {
            let bucket = &mut self.storage[address.as_index()];
            self.free = bucket.next;
            bucket.assign(previous, next, element);
            address
        } else {
            let address = Address::new(self.storage.len());
            self.storage.push(Bucket::new(previous, next, element));
            address
        }
    }
}

impl<T> Index<Address> for List<T> {
    type Output = T;

    fn index(&self, a: Address) -> &T {
        assert!(self.in_bounds(a));
        self.storage[a.as_index()].element.as_ref().unwrap()
    }
}

impl<T> IndexMut<Address> for List<T> {
    fn index_mut(&mut self, a: Address) -> &mut T {
        assert!(self.in_bounds(a));
        self.storage[a.as_index()].element.as_mut().unwrap()
    }
}

impl<'a, T> IntoIterator for &'a List<T> {
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

impl<T: std::fmt::Debug> fmt::Debug for List<T> {
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
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(transparent)]
pub struct Address(NonMaxU32);

impl Address {
    /// The maximum number of buckets addressable by a list.
    const CAPACITY: usize = u32::MAX as usize;

    /// Creates a new instance with the given storage index.
    fn new(offset: usize) -> Self {
        let offset = u32::try_from(offset).expect("list address space exhausted");
        Self(NonMaxU32::new(offset).expect("list address space exhausted"))
    }

    /// Returns this address as an index into a list's backing storage.
    fn as_index(self) -> usize {
        self.0.get() as usize
    }

    /// Returns the raw value of this address.
    pub fn raw(self) -> u32 {
        self.0.get()
    }
}

impl std::hash::Hash for Address {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.raw(), state);
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
    /// The preceding bucket when this bucket is occupied.
    previous: Option<Address>,

    /// The succeeding bucket when occupied, or the next free bucket when unoccupied.
    next: Option<Address>,

    /// The stored element iff the bucket is busy.
    element: Option<T>,
}

impl<T> Bucket<T> {
    /// Creates a new instance with the given properties.
    fn new(previous: Option<Address>, next: Option<Address>, element: T) -> Self {
        Self {
            previous,
            next,
            element: Some(element),
        }
    }

    /// Assigns the value of `self`, assuming it is free.
    fn assign(&mut self, previous: Option<Address>, next: Option<Address>, element: T) {
        debug_assert!(self.element.is_none());
        self.previous = previous;
        self.next = next;
        self.element = Some(element);
    }
}

impl<T> Default for List<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use std::hash::{DefaultHasher, Hash, Hasher};

    #[test]
    fn address_has_a_compact_optional_representation() {
        assert_eq!(std::mem::size_of::<Address>(), 4);
        assert_eq!(std::mem::size_of::<Option<Address>>(), 4);
    }

    #[test]
    fn address_supports_the_largest_valid_offset() {
        let address = Address::new((u32::MAX - 1) as usize);
        assert_eq!(address.raw(), u32::MAX - 1);
    }

    #[test]
    fn address_hashes_its_logical_offset() {
        let mut address_hasher = DefaultHasher::new();
        Address::new(42).hash(&mut address_hasher);
        let mut integer_hasher = DefaultHasher::new();
        42_u32.hash(&mut integer_hasher);
        assert_eq!(address_hasher.finish(), integer_hasher.finish());
    }

    #[test]
    #[should_panic(expected = "list address space exhausted")]
    fn address_rejects_the_reserved_offset() {
        Address::new(u32::MAX as usize);
    }

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

        let ys = xs.addresses().map(|a| &xs[a]);
        assert!(ys.eq(["a", "b"].iter()));

        Ok(())
    }

    #[test]
    fn test_append() {
        let mut xs = List::<&str>::new();

        xs.append("a");
        assert!(xs.iter().eq(["a"].iter()));

        let b = xs.append("b");
        assert!(xs.iter().eq(["a", "b"].iter()));

        xs.append("c");
        assert!(xs.iter().eq(["a", "b", "c"].iter()));

        xs.remove(b);
        xs.append("d");
        assert!(xs.iter().eq(["a", "c", "d"].iter()));
    }

    #[test]
    fn test_reuse_multiple_removed_buckets() {
        let mut xs = List::<&str>::new();
        let a = xs.append("a");
        let b = xs.append("b");
        xs.append("c");
        let d = xs.append("d");

        xs.remove(b);
        xs.remove(d);

        let e = xs.append("e");
        let f = xs.insert_after(a, "f");
        assert_eq!(e, d);
        assert_eq!(f, b);
        assert!(xs.iter().eq(["a", "f", "c", "e"].iter()));
    }

    #[test]
    fn test_prepend() {
        let mut xs = List::<&str>::new();

        xs.prepend("a");
        assert!(xs.iter().eq(["a"].iter()));

        let b = xs.prepend("b");
        assert!(xs.iter().eq(["b", "a"].iter()));

        xs.prepend("c");
        assert!(xs.iter().eq(["c", "b", "a"].iter()));

        xs.remove(b);
        xs.prepend("d");
        assert!(xs.iter().eq(["d", "c", "a"].iter()));
    }

    #[test]
    fn test_insert_before() {
        let mut xs = List::<&str>::new();

        let a = xs.prepend("a");
        xs.insert_before(a, "b");
        xs.insert_before(a, "c");
        assert!(xs.iter().eq(["b", "c", "a"].iter()));
    }

    #[test]
    fn test_insert_after() {
        let mut xs = List::<&str>::new();

        let a = xs.prepend("a");
        xs.insert_after(a, "b");
        xs.insert_after(a, "c");
        assert!(xs.iter().eq(["a", "c", "b"].iter()));
    }

    #[test]
    fn test_first_last_address_after_emptied() {
        let mut xs = List::<&str>::new();
        let a = xs.append("a");
        xs.remove(a);
        assert!(xs.is_empty());

        // An emptied list has no first/last element, even though its backing storage retains the
        // freed bucket. Returning the stale `!0` head/tail sentinel here yields an out-of-bounds
        // `Address`, and iterating it panics.
        assert_eq!(xs.first_address(), None);
        assert_eq!(xs.last_address(), None);
        assert_eq!(xs.iter().count(), 0);
        assert_eq!(xs.addresses().count(), 0);
    }

    #[test]
    fn test_reserve_before_first_append() {
        let mut xs = List::<&str>::new();
        xs.reserve(48);

        // Reserving capacity must survive the first append: per `reserve`'s contract the next 48
        // insertions happen "without reallocating its storage".
        xs.append("a");
        assert!(xs.capacity() >= 48);
        assert_eq!(xs[xs.first_address().unwrap()], "a");
    }

    #[test]
    fn test_append_after_emptied() {
        let mut xs = List::<&str>::new();

        let a = xs.append("a");
        xs.remove(a);
        assert!(xs.is_empty());

        // Re-using an emptied bucket must restore the `!0` neighbor sentinels so that a later
        // removal does not index out of bounds.
        let b = xs.append("b");
        assert!(xs.iter().eq(["b"].iter()));

        xs.remove(b); // crash
        assert!(xs.is_empty());
    }
}
