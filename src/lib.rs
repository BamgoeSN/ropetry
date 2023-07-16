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
        Self::default()
    }

    /// Clears the rope, removing all values.
    pub fn clear(&mut self) {
        let drop_tree = Self {
            root: self.root,
            size: self.size,
        };
        self.root = None;
        self.size = 0;
        drop(drop_tree)
    }

    /// Returns the number of elements in the rope.
    pub fn len(&self) -> usize {
        self.size
    }

    /// Returns `true` if the rope is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Provides a reference to the element at the given index.
    /// Returns `None` if `index` is out of bounds.
    pub fn get(&mut self, index: usize) -> Option<&T> {
        unsafe {
            let p = self.kth_ptr(index)?;
            self.splay(p);
            Some(&(*p.as_ptr()).data)
        }
    }

    /// Provides a mutable reference to the element at the given index.
    /// Returns `None` if `index` is out of bounds.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        unsafe {
            let p = self.kth_ptr(index)?;
            self.splay(p);
            Some(&mut (*p.as_ptr()).data)
        }
    }

    /// Inserts an element at `index` within the rope.
    /// Panics if `index` is greater than the rope's length.
    pub fn insert(&mut self, index: usize, value: T) {
        assert!(index <= self.len());

        unsafe {
            let new_node = NonNull::new_unchecked(Box::into_raw(Box::new(Node::new(value))));

            if let Some(root) = self.root {
                // `self` is not empty
                let idx_node = self.kth_ptr(index);

                if let Some(idx_node) = idx_node {
                    // `index` is in-bounds, thus `new_node` should be placed right before
                    // `idx_node`.
                    self.naive_insert_at_left(idx_node, new_node);
                } else {
                    // `index == self.len()`, thus `new_node` should be placed at the rightmost of
                    // the rope. Set `ptr` as the current rightmost node.
                    let mut ptr = root;
                    (*ptr.as_ptr()).prop_rev();
                    while let Some(r) = (*ptr.as_ptr()).r {
                        ptr = r;
                        (*ptr.as_ptr()).prop_rev();
                    }
                    // Place `new_node` as the right child of `ptr`
                    (*new_node.as_ptr()).p = Some(ptr);
                    (*ptr.as_ptr()).r = Some(new_node);
                }

                let mut c = new_node;
                while let Some(p) = (*c.as_ptr()).p {
                    c = p;
                    (*c.as_ptr()).update_subt_norev();
                }
            } else {
                // `self` is empty
                self.root = Some(new_node);
            }

            self.splay(new_node);
            self.size += 1;
        }
    }

    /// Removes and returns the element at `index` from the deque.
    /// Returns `None` if `index` is out of bounds.
    pub fn remove(&mut self, index: usize) -> Option<T> {
        if index >= self.len() {
            return None;
        }

        let data: T = unsafe {
            if let Some(mut rt) = self.kth_ptr(index) {
                rt = self.remove_helper(rt);
                if let Some(rtp) = (*rt.as_ptr()).p {
                    self.splay(rtp);
                }
                let retr = Box::from_raw(rt.as_ptr());
                retr.data
            } else {
                unreachable!()
            }
        };

        self.size -= 1;
        Some(data)
    }

    /// Prepends an element to the rope.
    pub fn push_front(&mut self, value: T) {
        self.insert(0, value);
    }

    /// Appends an element to the rope.
    pub fn push_back(&mut self, value: T) {
        self.insert(self.len(), value);
    }

    /// Removes the first element and returns it, or `None` if the rope is empty.
    pub fn pop_front(&mut self) -> Option<T> {
        self.remove(0)
    }

    /// Removes the last element and returns it, or `None` if the rope is empty.
    pub fn pop_back(&mut self) -> Option<T> {
        self.remove(self.len().checked_sub(1)?)
    }

    /// Swaps elements at indices `i` and `j`. `i` and `j` may be equal.
    /// Panics if either index is out of bounds.
    pub fn swap(&mut self, i: usize, j: usize) {
        // Safety: The actual address of nodes are never changed while searching for nodes and
        // splaying.
        unsafe {
            let inode = self
                .kth_ptr(i)
                .expect(&format!("The len is {} but the index is {}", self.size, i));
            let jnode = self
                .kth_ptr(j)
                .expect(&format!("The len is {} but the index is {}", self.size, i));
            mem::swap(&mut (*inode.as_ptr()).data, &mut (*jnode.as_ptr()).data)
        }
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
        Self {
            root: None,
            size: 0,
        }
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
        if let Some(root) = self.root {
            unsafe {
                let mut st: Vec<*mut Node<T>> = Vec::new();
                st.push(root.as_ptr());
                while let Some(t) = st.pop() {
                    let v = Box::from_raw(t);
                    if let Some(l) = v.l {
                        st.push(l.as_ptr());
                    }
                    if let Some(r) = v.r {
                        st.push(r.as_ptr());
                    }
                    drop(v);
                }
            }
        }
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

    fn left_size_norev(&self) -> usize {
        unsafe { self.l.map_or(0, |l| (*l.as_ptr()).subt) }
    }
    fn right_size_norev(&self) -> usize {
        unsafe { self.r.map_or(0, |r| (*r.as_ptr()).subt) }
    }
    /// Updates the value of `subt`, but not resolving `rev`.
    fn update_subt_norev(&mut self) {
        self.subt = 1 + self.left_size_norev() + self.right_size_norev()
    }

    fn prop_rev(&mut self) {
        if self.rev {
            self.rev = false;
            mem::swap(&mut self.l, &mut self.r);
            unsafe {
                if let Some(l) = self.l {
                    (*l.as_ptr()).rev ^= true;
                }
                if let Some(r) = self.r {
                    (*r.as_ptr()).rev ^= true;
                }
            }
        }
    }

    /// Returns `Some(is_left, parent)`. If `x` doesn't have a parent node, returns `None`.
    /// Also resolves `rev` of the parent of `x`. Note that it doesn't resolve `rev` of `x`.
    fn is_left_child_withrev(x: NonNull<Self>) -> Option<(bool, NonNull<Self>)> {
        unsafe {
            (*x.as_ptr()).prop_rev();
            if let Some(p) = (*x.as_ptr()).p {
                if (*p.as_ptr())
                    .l
                    .map_or(false, |pl| ptr::eq(x.as_ptr(), pl.as_ptr()))
                {
                    Some((true, p))
                } else {
                    Some((false, p))
                }
            } else {
                None
            }
        }
    }
}

impl<T> Rope<T> {
    /// Adds `value` as a new root of a rope, and putting the original root as a left child of
    /// the root.
    unsafe fn push_ontop_root(&mut self, value: T) {
        let new_node = NonNull::new_unchecked(Box::into_raw(Box::new(Node::new(value))));
        if let Some(root) = self.root {
            (*root.as_ptr()).p = Some(new_node);
            (*new_node.as_ptr()).l = Some(root);
        }
        self.root = Some(new_node);
        (*new_node.as_ptr()).update_subt_norev();
        self.size += 1;
    }

    /// Returns `false` if `x` has no parent, and does nothing.
    /// Returns `true` if `x` has a parent, and perform rotation.
    unsafe fn rotate(&mut self, x: NonNull<Node<T>>) -> bool {
        (*x.as_ptr()).prop_rev();
        if let Some((is_x_left, p)) = Node::is_left_child_withrev(x) {
            // Check if p is root
            if let Some(root) = self.root {
                if ptr::eq(root.as_ptr(), p.as_ptr()) {
                    self.root = Some(x);
                }
            }

            // Connect x to xpp. If pp is None, do nothing.
            (*x.as_ptr()).p = (*p.as_ptr()).p;
            if let Some((is_p_left, pp)) = Node::is_left_child_withrev(p) {
                if is_p_left {
                    (*pp.as_ptr()).l = Some(x);
                } else {
                    (*pp.as_ptr()).r = Some(x);
                }
            }

            if is_x_left {
                let b = (*x.as_ptr()).r;
                (*x.as_ptr()).r = Some(p);
                (*p.as_ptr()).p = Some(x);
                (*p.as_ptr()).l = b;
                if let Some(b) = b {
                    (*b.as_ptr()).p = Some(p);
                }
            } else {
                let b = (*x.as_ptr()).l;
                (*x.as_ptr()).l = Some(p);
                (*p.as_ptr()).p = Some(x);
                (*p.as_ptr()).r = b;
                if let Some(b) = b {
                    (*b.as_ptr()).p = Some(p);
                }
            }

            (*p.as_ptr()).update_subt_norev();
            (*x.as_ptr()).update_subt_norev();
            true
        } else {
            // `x` has no parent
            false
        }
    }

    /// Splays `x` up to `self`'s root.
    fn splay(&mut self, x: NonNull<Node<T>>) {
        unsafe {
            (*x.as_ptr()).prop_rev();
            while let Some(root) = self.root {
                if ptr::eq(x.as_ptr(), root.as_ptr()) {
                    break;
                }

                if let Some((is_x_left, p)) = Node::is_left_child_withrev(x) {
                    if ptr::eq(root.as_ptr(), p.as_ptr()) {
                        // If p is root, rotate x once
                        self.rotate(x);
                    } else {
                        // Panics if pp doesn't exist, which happens only when p is root
                        let (is_p_left, _pp) = Node::is_left_child_withrev(p).unwrap();
                        if is_x_left == is_p_left {
                            self.rotate(p);
                            self.rotate(x);
                        } else {
                            self.rotate(x);
                            self.rotate(x);
                        }
                    }
                } else {
                    // x has no parent, which should logically never happen
                    unreachable!()
                }
            }
        }
    }

    /// Returns a link to the element at `index`. Returns `None` if `index` is out of bounds.
    /// The returned node may have its `rev` field as `true`.
    unsafe fn kth_ptr(&self, index: usize) -> Link<T> {
        if self.size <= index {
            return None;
        }
        if let Some(r) = self.root {
            let mut rem = index;
            let mut ptr = r;
            loop {
                (*ptr.as_ptr()).prop_rev();
                let lsize = (*ptr.as_ptr()).left_size_norev();
                match rem.cmp(&lsize) {
                    Less => {
                        ptr = (*ptr.as_ptr()).l?;
                    }
                    Equal => {
                        break;
                    }
                    Greater => {
                        rem -= lsize + 1;
                        ptr = (*ptr.as_ptr()).r?;
                    }
                }
            }
            Some(ptr)
        } else {
            None
        }
    }

    /// Insert `new` right before of `x`.
    unsafe fn naive_insert_at_left(&mut self, x: NonNull<Node<T>>, new: NonNull<Node<T>>) {
        (*x.as_ptr()).prop_rev();
        if let Some(l) = (*x.as_ptr()).l {
            // If `x` has its left child, then we need to find another place for `new`. Set `ptr`
            // as the node right before `x`.
            let mut ptr = l;
            (*ptr.as_ptr()).prop_rev();
            while let Some(r) = (*ptr.as_ptr()).r {
                ptr = r;
                (*ptr.as_ptr()).prop_rev();
            }
            // Now `ptr.r` is `None`. Attach `new` to `ptr.r`
            (*new.as_ptr()).p = Some(ptr);
            (*ptr.as_ptr()).r = Some(new);
        } else {
            // If `x` doesn't have its left child, then `new` can be attached right away at `x.l`
            (*new.as_ptr()).p = Some(x);
            (*x.as_ptr()).l = Some(new);
        }
    }

    /// Remove `x` from `self`, while keeping `self`'s BST characteristic, and returns the
    /// removed node.
    unsafe fn remove_helper(&mut self, x: NonNull<Node<T>>) -> NonNull<Node<T>> {
        (*x.as_ptr()).prop_rev();

        // Set `remove_target` to the actual node to delete
        match ((*x.as_ptr()).l, ((*x.as_ptr()).r)) {
            (None, None) => {
                // Reset root if the node itself is root
                if let Some(root) = self.root {
                    if ptr::eq(root.as_ptr(), x.as_ptr()) {
                        self.root = None;
                    }
                }

                // Detach itself from parent
                if let Some((is_x_left, p)) = Node::is_left_child_withrev(x) {
                    if is_x_left {
                        (*p.as_ptr()).l = None;
                    } else {
                        (*p.as_ptr()).r = None;
                    }
                    // Update subtree size
                    let mut p = p;
                    (*p.as_ptr()).update_subt_norev();
                    while let Some(pp) = (*p.as_ptr()).p {
                        p = pp;
                        (*p.as_ptr()).update_subt_norev();
                    }
                }
                x
            }

            (Some(l), None) => {
                // `x` only has its left child `l`
                // Reset root if `x` is root
                if let Some(root) = self.root {
                    if ptr::eq(root.as_ptr(), x.as_ptr()) {
                        // `l` will be the new root
                        self.root = Some(l);
                    }
                }

                (*l.as_ptr()).p = (*x.as_ptr()).p; // Change `l.p` from `x` to `x.p`
                if let Some((is_rt_left, p)) = Node::is_left_child_withrev(x) {
                    // Change `x.p`'s child from `x` to `l`
                    if is_rt_left {
                        (*p.as_ptr()).l = Some(l);
                    } else {
                        (*p.as_ptr()).r = Some(l);
                    }
                }

                let mut p = l;
                while let Some(pp) = (*p.as_ptr()).p {
                    p = pp;
                    (*p.as_ptr()).update_subt_norev();
                }
                x
            }

            (None, Some(r)) => {
                // `x` only has its right child `r`
                // Reset root if `x` is root
                if let Some(root) = self.root {
                    if ptr::eq(root.as_ptr(), x.as_ptr()) {
                        // `r` will be the new root
                        self.root = Some(r);
                    }

                    (*r.as_ptr()).p = (*x.as_ptr()).p; // Set `r.p` from `x` to `x.p`
                    if let Some((is_rt_left, p)) = Node::is_left_child_withrev(x) {
                        // Change `x.p`'s child from `x` to `r`
                        if is_rt_left {
                            (*p.as_ptr()).l = Some(r);
                        } else {
                            (*p.as_ptr()).r = Some(r);
                        }
                    }

                    let mut p = r;
                    while let Some(pp) = (*p.as_ptr()).p {
                        p = pp;
                        (*p.as_ptr()).update_subt_norev();
                    }
                }
                x
            }

            (Some(l), Some(_)) => {
                // Set `sw` as the rightmost node at the left side of `x`
                let mut sw = l;
                (*sw.as_ptr()).prop_rev();
                while let Some(sr) = (*sw.as_ptr()).r {
                    sw = sr;
                    (*sw.as_ptr()).prop_rev();
                }
                mem::swap(&mut (*x.as_ptr()).data, &mut (*sw.as_ptr()).data);
                sw = self.remove_helper(sw); // Naively remove the moved node `sw`
                sw
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
