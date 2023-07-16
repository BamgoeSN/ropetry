use std::{
    cmp::Ordering::*,
    fmt::Debug,
    marker::PhantomData,
    mem,
    ops::RangeBounds,
    ptr::{self, NonNull},
    todo, unreachable,
};

/// A rope, which is a dynamic array which takes amortized *O*(log*n*) time for insertion and
/// removal at the middle of it. In return however, every other basic operation such as random
/// access also takes amortized *O*(log*n*) time.
///
/// The API design is similar to that of `VecDeque`, except for those related with range
/// operations.
///
/// TODO: Support cursors. API will be similar to that of `LinkedList`.
/// TODO: When `T` is `LzMonoid`, range queries can be performed on the rope.
pub struct Rope<T> {
    root: Link<T>,
    size: usize,
}

impl<T> Rope<T> {
    /// Creates an empty rope.
    pub fn new() -> Self {
        todo!();
    }

    /// Clears the rope, removing all values.
    pub fn clear(&mut self) {
        todo!();
    }

    /// Returns the number of elements in the rope.
    pub fn len(&self) -> usize {
        todo!();
    }

    /// Returns `true` if the rope is empty.
    pub fn is_empty(&self) -> bool {
        todo!();
    }

    /// Provides a reference to the element at the given index.
    /// Returns `None` if `index` is out of bounds.
    pub fn get(&mut self, index: usize) -> Option<&T> {
        todo!();
    }

    /// Provides a mutable reference to the element at the given index.
    /// Returns `None` if `index` is out of bounds.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        todo!();
    }

    /// Inserts an element at `index` within the rope.
    /// Panics if `index` is greater than the rope's length.
    pub fn insert(&mut self, index: usize, value: T) {
        todo!();
    }

    /// Removes and returns the element at `index` from the deque.
    /// Returns `None` if `index` is out of bounds.
    pub fn remove(&mut self, index: usize) -> Option<T> {
        todo!();
    }

    /// Prepends an element to the rope.
    pub fn push_front(&mut self, value: T) {
        todo!();
    }

    /// Appends an element to the rope.
    pub fn push_back(&mut self, value: T) {
        todo!();
    }

    /// Removes the first element and returns it, or `None` if the rope is empty.
    pub fn pop_front(&mut self) -> Option<T> {
        todo!();
    }

    /// Removes the last element and returns it, or `None` if the rope is empty.
    pub fn pop_back(&mut self) -> Option<T> {
        todo!();
    }

    /// Swaps elements at indices `i` and `j`. `i` and `j` may be equal.
    /// Panics if either index is out of bounds.
    pub fn swap(&mut self, i: usize, j: usize) {
        todo!()
    }

    /// Splits the rope into two at the given index, and returns a new `Rope` which reuses
    /// already allocated memory.
    /// `self` contains elements `[0, at)` after the operation, and the returned rope contains
    /// elements `[at, len)`.
    /// Panics if `at > len`.
    pub fn split_off(&mut self, at: usize) -> Rope<T> {
        todo!()
    }

    /// Takes out the elements at `range` from the rope, and returns a new `Rope` which reuses
    /// already allocated memory.
    /// Letting the start and end point of `range` as `s` and `e` respectively, `self` contains
    /// elements `[0, s)` and `[e, len)` after the operation, and the returned rope contains
    /// elements `[s, e)`.
    /// Panics if the starting point is greater than the end point, or if the end point is
    /// greater than the length of the rope.
    pub fn take_range_out(&mut self, range: impl RangeBounds<usize>) -> Rope<T> {
        todo!()
    }

    /// Appends all the elements of `other` to `self`, consuming `other`.
    pub fn append(&mut self, other: Rope<T>) {
        todo!()
    }

    /// Inserts a rope at `index` within `self`.
    pub fn insert_rope(&mut self, index: usize, other: Rope<T>) {
        todo!()
    }

    /// Rotates the rope `mid` places to the left.
    /// Panics if `mid > len`.
    pub fn rotate_left(&mut self, mid: usize) {
        todo!()
    }

    /// Rotates the rope `mid` places to the right.
    /// Panics if `mid > len`.
    pub fn rotate_right(&mut self, mid: usize) {
        todo!()
    }

    /// Returns the index `i` where `pred(self[i])` is `false` for the first time, given that
    /// `pred(self[i])` is `true` until a certain index, and `false` for every following
    /// element. If the guarantee is not met, the returned result is unspecified and
    /// meaningless.
    pub fn partition_point(&mut self, pred: impl FnMut(&T) -> bool) -> usize {
        todo!()
    }

    /// Reverses the rope.
    pub fn reverse(&mut self) {
        todo!()
    }

    /// Reverse `range` of the rope.
    /// Panics if the starting point is greater than the end point, or if the end point is
    /// greater than the length of the rope.
    pub fn reverse_range(&mut self, range: impl RangeBounds<usize>) {
        todo!()
    }
}

impl<T> Default for Rope<T> {
    fn default() -> Self {
        todo!()
    }
}

impl<T> Clone for Rope<T> {
    fn clone(&self) -> Self {
        todo!()
    }
}

impl<T> Debug for Rope<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl<T> Drop for Rope<T> {
    fn drop(&mut self) {
        todo!()
    }
}

impl<T> FromIterator<T> for Rope<T> {
    fn from_iter<S: IntoIterator<Item = T>>(iter: S) -> Self {
        todo!()
    }
}

impl<T> Extend<T> for Rope<T> {
    fn extend<S: IntoIterator<Item = T>>(&mut self, iter: S) {
        todo!()
    }
}

pub struct Iter<'a, T> {
    marker: PhantomData<&'a T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<'a, T> IntoIterator for &'a Rope<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        todo!()
    }
}

pub struct IterMut<'a, T> {
    marker: PhantomData<&'a mut T>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;
    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<'a, T> IntoIterator for &'a mut Rope<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        todo!()
    }
}

pub struct IntoIter<T> {
    marker: PhantomData<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<T> IntoIterator for Rope<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        todo!()
    }
}

//------------------------
// Helper implementations
//------------------------

struct Node<T> {
    data: T,
    subt: usize,
    l: Link<T>,
    r: Link<T>,
    p: Link<T>,
    rev: bool,
}

type Link<T> = Option<NonNull<Node<T>>>;

impl<T> Node<T> {
    fn new(data: T) -> Self {
        Self {
            data,
            subt: 1,
            l: None,
            r: None,
            p: None,
            rev: false,
        }
    }
}

#[cfg(test)]
mod test {
    use std::{assert_eq, collections::VecDeque};

    use super::*;
    #[test]
    fn insertion_removal_test() {
        let mut rope: Rope<i32> = Rope::new();
        let mut refr: VecDeque<i32> = VecDeque::new();

        // Insertion
        let queries = vec![
            (0, 3),
            (1, 2),
            (2, 9),
            (1, 20),
            (4, 30),
            (0, 1),
            (2, 4),
            (2, 10),
            (2, 5),
            (1, 6),
            (5, 7),
        ];
        for &(i, v) in queries.iter() {
            rope.insert(i, v);
            refr.insert(i, v);
            assert_eq!(rope.len(), refr.len());
            for i in 0..refr.len() {
                assert_eq!(*rope.get(i).unwrap(), *refr.get(i).unwrap());
            }
        }

        // Removal
        let queries = vec![1, 4, 2, 4, 6, 0, 99, 3, 1];
        for &i in queries.iter() {
            let a = rope.remove(i);
            let b = refr.remove(i);
            assert_eq!(a, b);
            assert_eq!(rope.len(), refr.len());
            for i in 0..refr.len() {
                assert_eq!(*rope.get(i).unwrap(), *refr.get(i).unwrap());
            }
        }
    }
}
