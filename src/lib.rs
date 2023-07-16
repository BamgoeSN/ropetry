#![allow(unused)]

use std::{
    cmp::Ordering::*,
    fmt::Debug,
    marker::PhantomData,
    mem,
    ops::RangeBounds,
    panic,
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

//------------------
// Helper functions
//------------------

// At every moment when a function is newly called, every node existing at that point are
// "updated", which means that every node satisfies the condition that even if the `update`
// function is called on any of them, there will be no change made whatsoever. If this promise
// breaks, the whole code breaks.
// This is not the case for being "propagated". The safety guarantee for it is given as comments
// for every helper function.

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
    /// Returns a new node with a given `data`.
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

    /// Propagates `rev` of `x`. Obviously `x` doesn't need to be already propagated,
    /// and this function propagates `x`.
    /// TODO: Add a support for the propagation of any lazily evaluatable operation.
    fn propagate(x: NonNull<Self>) {
        unsafe {
            let x = x.as_ptr();
            if (*x).rev {
                (*x).rev = false;
                mem::swap(&mut (*x).l, &mut (*x).r);
                if let Some(l) = (*x).l {
                    (*l.as_ptr()).rev ^= true;
                }
                if let Some(r) = (*x).r {
                    (*r.as_ptr()).rev ^= true;
                }
            }
        }
    }

    /// Updates `subt` of `x` based on its children nodes. `x` doesn't need to be already
    /// propagated, and this function doesn't propagate `x`.
    /// TODO: Add a support for the updates of any range-queriable operation.
    fn update(x: NonNull<Self>) {
        unsafe {
            let x = x.as_ptr();
            let lsize = if let Some(l) = (*x).l {
                (*l.as_ptr()).subt
            } else {
                0
            };
            let rsize = if let Some(r) = (*x).r {
                (*r.as_ptr()).subt
            } else {
                0
            };
            (*x).subt = 1 + lsize + rsize;
        }
    }

    /// Returns `None` if `x` is a root. Returns `Some((true, p))` if `x` has `p` as a parent and
    /// is a left child of `p`. Otherwise, returns `Some((false, p))` where `p` is a parent of `x`.
    /// `x` and `p` doesn't need to be propagated in advance, and they are both propagated after
    /// the function.
    fn left_parent(x: NonNull<Self>) -> Option<(bool, NonNull<Self>)> {
        unsafe {
            (*x.as_ptr()).p.map(|p| {
                Self::propagate(p);
                if (*p.as_ptr())
                    .l
                    .map_or(false, |pl| ptr::eq(x.as_ptr(), pl.as_ptr()))
                {
                    (true, p)
                } else {
                    (false, p)
                }
            })
        }
    }

    /// Returns `None` if `x` is a root. Returns `Some((true, p))` if `x` has `p` as a parent and
    /// is a left child of `p`. Otherwise, returns `Some((false, p))` where `p` is a parent of `x`.
    /// `p` is assumed to be already propagated. Breaking this assumption is UB.
    unsafe fn left_parent_unchecked(x: NonNull<Self>) -> Option<(bool, NonNull<Self>)> {
        unsafe {
            (*x.as_ptr()).p.map(|p| {
                if (*p.as_ptr())
                    .l
                    .map_or(false, |pl| ptr::eq(x.as_ptr(), pl.as_ptr()))
                {
                    (true, p)
                } else {
                    (false, p)
                }
            })
        }
    }
}

impl<T> Rope<T> {
    /// Performs a "rotation" on `x`, a.k.a. "zig" operation. `x` and `p` doesn't need to be
    /// propagated, and this function will propagate them. This function also fixes the root if it
    /// changes to another node.
    /// If `x` is already a root, then this function just propagates `x` and ends.
    /// Panics if `self` is empty. This function when `x` is not a part of `self` is very likely to
    /// trigger UB, but it won't happen in this code.
    fn rotate(&mut self, x: NonNull<Node<T>>) {
        Node::propagate(x);

        // Return if `x == self.root`
        if let Some(root) = self.root {
            if ptr::eq(root.as_ptr(), x.as_ptr()) {
                return;
            }
        }

        // Now it's guaranteed that `x != self.root`
        match Node::left_parent(x) {
            Some((is_left, p)) => {
                // Propagation has already been done for `p`
                unsafe {
                    if is_left {
                        // `p.l == x`
                        let b = (*x.as_ptr()).r;
                        // Connect p to x as a right child
                        (*p.as_ptr()).p = Some(x);
                        (*x.as_ptr()).r = Some(p);
                        // Connect b to p as a left child
                        if let Some(b) = b {
                            (*b.as_ptr()).p = Some(p);
                        }
                        (*p.as_ptr()).l = b;
                    } else {
                        // `p.r == x`
                        let b = (*x.as_ptr()).l;
                        // Connect p to x as a left child
                        (*p.as_ptr()).p = Some(x);
                        (*x.as_ptr()).l = Some(p);
                        // Connect b to p as a right child
                        if let Some(b) = b {
                            (*b.as_ptr()).p = Some(p);
                        }
                        (*p.as_ptr()).r = b;
                    }
                    // Update `p` and `x`
                    Node::update(p);
                    Node::update(x);
                }
                // If `p` was `self.root`, then the rotation has just changed the root
                if let Some(root) = self.root {
                    if ptr::eq(root.as_ptr(), p.as_ptr()) {
                        self.root = Some(x);
                    }
                }
            }
            None => {
                // If `x` is not a root but doesn't have a parent, this is a bug.
                unreachable!("`x` is not a root of `self`, but doesn't have a parent node!");
            }
        }
    }

    /// Performs a "rotation" on `x`, a.k.a. "zig" operation. `x` and `p` are assumed to be already
    /// propagated, and breaking this assumption is UB. This functionn still fixes the root if it
    /// changes to another one.
    /// If `x` is already a root, then this function does nothing.
    /// Panics if `self` is empty. This function when `x` is not a part of `self` is very likely to
    /// trigger UB, but it won't happen in this code.
    unsafe fn rotate_unchecked(&mut self, x: NonNull<Node<T>>) {
        // Return if `x == self.root`
        if let Some(root) = self.root {
            if ptr::eq(root.as_ptr(), x.as_ptr()) {
                return;
            }
        }

        // Now it's guaranteed that `x != self.root`
        match Node::left_parent_unchecked(x) {
            Some((is_left, p)) => {
                // Propagation has already been done for `p`
                unsafe {
                    if is_left {
                        // `p.l == x`
                        let b = (*x.as_ptr()).r;
                        // Connect p to x as a right child
                        (*p.as_ptr()).p = Some(x);
                        (*x.as_ptr()).r = Some(p);
                        // Connect b to p as a left child
                        if let Some(b) = b {
                            (*b.as_ptr()).p = Some(p);
                        }
                        (*p.as_ptr()).l = b;
                    } else {
                        // `p.r == x`
                        let b = (*x.as_ptr()).l;
                        // Connect p to x as a left child
                        (*p.as_ptr()).p = Some(x);
                        (*x.as_ptr()).l = Some(p);
                        // Connect b to p as a right child
                        if let Some(b) = b {
                            (*b.as_ptr()).p = Some(p);
                        }
                        (*p.as_ptr()).r = b;
                    }
                    // Update `p` and `x`
                    Node::update(p);
                    Node::update(x);
                }
                // If `p` was `self.root`, then the rotation has just changed the root
                if let Some(root) = self.root {
                    if ptr::eq(root.as_ptr(), p.as_ptr()) {
                        self.root = Some(x);
                    }
                }
            }
            None => {
                // If `x` is not a root but doesn't have a parent, this is a bug.
                unreachable!("`x` is not a root of `self`, but doesn't have a parent node!");
            }
        }
    }

    // Splays a node. None of the node needs to be propagated. Every node that was an ancestor of
    // `x` gets propagated after the function call, despite they don't stay as its ancestors
    // anymore.
    fn splay(&mut self, x: NonNull<Node<T>>) {
        if let Some(root) = self.root {
            while !ptr::eq(root.as_ptr(), x.as_ptr()) {
                if let Some((is_x_left, p)) = Node::left_parent(x) {
                    if ptr::eq(root.as_ptr(), p.as_ptr()) {
                        // `p` is a root of `self` -> rotate(x)
                        self.rotate(x);
                    } else {
                        if let Some((is_p_left, _)) = Node::left_parent(p) {
                            if is_x_left == is_p_left {
                                // zig-zig
                                self.rotate(p);
                                self.rotate(x);
                            } else {
                                // zig-zag
                                self.rotate(x);
                                self.rotate(x);
                            }
                        } else {
                            // `g` simply doesn't exist, and `x` is not a root of `self`, thus `p`
                            // should be the root. However, this branch is for the case where
                            // `p` is not the root.
                            unreachable!("`p` is not a root of `self`, but `g` doesn't exist and `x` is not a root either.");
                        }
                    }
                } else {
                    // If `x` is not a root but doesn't have a parent, this is a bug.
                    unreachable!("`x` is not a root of `self`, but doesn't have a parent node!");
                }
            }
        } else {
            unreachable!("`self` is empty, thus `x` is not in `self`.");
        }
    }

    unsafe fn splay_unchecked(&mut self, x: NonNull<Node<T>>) {
        if let Some(root) = self.root {
            while !ptr::eq(root.as_ptr(), x.as_ptr()) {
                if let Some((is_x_left, p)) = Node::left_parent_unchecked(x) {
                    if ptr::eq(root.as_ptr(), p.as_ptr()) {
                        // `p` is a root of `self` -> rotate(x)
                        self.rotate_unchecked(x);
                    } else {
                        if let Some((is_p_left, _)) = Node::left_parent_unchecked(p) {
                            if is_x_left == is_p_left {
                                // zig-zig
                                self.rotate_unchecked(p);
                                self.rotate_unchecked(x);
                            } else {
                                // zig-zag
                                self.rotate_unchecked(x);
                                self.rotate_unchecked(x);
                            }
                        } else {
                            // `g` simply doesn't exist, and `x` is not a root of `self`, thus `p`
                            // should be the root. However, this branch is for the case where
                            // `p` is not the root.
                            unreachable!("`p` is not a root of `self`, but `g` doesn't exist and `x` is not a root either.");
                        }
                    }
                } else {
                    // If `x` is not a root but doesn't have a parent, this is a bug.
                    unreachable!("`x` is not a root of `self`, but doesn't have a parent node!");
                }
            }
        } else {
            unreachable!("`self` is empty, thus `x` is not in `self`.");
        }
    }

    /// Finds the `index`-th node, splays it, and returns it. No nodes need to be propagated before the
    /// function call, and every node that *were* the ancestors of `index`-th node including itself
    /// gets propageted by this function.
    fn kth_ptr(&mut self, index: usize) -> Link<T> {
        if index >= self.len() {
            return None;
        }

        if let Some(root) = self.root {
            unsafe {
                let mut ptr = root;
                let mut rem = index;

                loop {
                    Node::propagate(ptr);
                    let lsize = if let Some(l) = (*ptr.as_ptr()).l {
                        (*l.as_ptr()).subt
                    } else {
                        0
                    };

                    match rem.cmp(&lsize) {
                        Less => {
                            ptr = if let Some(l) = (*ptr.as_ptr()).l {
                                l
                            } else {
                                break;
                            }
                        }
                        Equal => {
                            break;
                        }
                        Greater => {
                            rem -= lsize + 1;
                            ptr = if let Some(r) = (*ptr.as_ptr()).r {
                                r
                            } else {
                                break;
                            }
                        }
                    }
                }

                // It's guaranteed that every node from `self.root` to `ptr` are propagated, thus
                // it's safe to call splay_unchecked.
                self.splay_unchecked(ptr);
                Some(ptr)
            }
        } else {
            unreachable!("The len is {}, but it has no root", self.size);
        }
    }

    /// Finds the node right before `x`. This function does not splay the returned node, but
    /// propagates every node it scans through.
    fn adjacent_before(&self, x: NonNull<Node<T>>) -> Link<T> {
        Node::propagate(x);
        unsafe {
            if let Some(mut ptr) = (*x.as_ptr()).l {
                Node::propagate(ptr);
                while let Some(r) = (*ptr.as_ptr()).r {
                    ptr = r;
                    Node::propagate(ptr);
                }
                Some(ptr)
            } else {
                let mut ptr = x;
                while let Some((is_left, p)) = Node::left_parent(ptr) {
                    if is_left {
                        ptr = p;
                    } else {
                        return Some(p);
                    }
                }
                return None;
            }
        }
    }

    /// Finds the node right before `x`. This function does not splay the returned node, but
    /// propagates every node it scans through.
    fn adjacent_after(&self, x: NonNull<Node<T>>) -> Link<T> {
        Node::propagate(x);
        unsafe {
            if let Some(mut ptr) = (*x.as_ptr()).r {
                Node::propagate(ptr);
                while let Some(l) = (*ptr.as_ptr()).l {
                    ptr = l;
                    Node::propagate(ptr);
                }
                Some(ptr)
            } else {
                let mut ptr = x;
                while let Some((is_left, p)) = Node::left_parent(ptr) {
                    if !is_left {
                        ptr = p;
                    } else {
                        break;
                    }
                }
                return None;
            }
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
