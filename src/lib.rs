use std::{cmp::Ordering, fmt::Debug, marker::PhantomData, ops::RangeBounds};

pub struct Rope<T> {
	_marker: PhantomData<T>,
}

impl<T> Rope<T> {
	/// Constructs a new, empty `Rope<T>`.
	pub fn new() -> Self { todo!() }

	/// Returns the number of elements in the rope, also referred to as its 'length'.
	pub fn len(&self) -> usize { todo!() }

	/// Returns `true` if the rope contains no elements.
	pub fn is_empty(&self) -> bool { self.len() == 0 }

	/// Clears the rope, dropping all values.
	pub fn clear(&mut self) { todo!() }

	/// Returns a reference to the `i`-th element of the rope, or `None` if `i` is out of bounds.
	pub fn get(&mut self, i: usize) -> Option<&T> { todo!() }

	/// Returns a mutable reference to the `i`-th element of the rope, or `None` if `i` is out of bounds.
	pub fn get_mut(&mut self, i: usize) -> Option<&mut T> { todo!() }

	/// Returns a reference to the first element of the rope, or `None` if it's empty.
	pub fn first(&mut self) -> Option<&T> { self.get(0) }

	/// Returns a mutable reference to the first element of the rope, or `None` if it's empty.
	pub fn first_mut(&mut self) -> Option<&mut T> { self.get_mut(0) }

	/// Returns a reference to the last element of the rope, or `None` if it's empty.
	pub fn last(&mut self) -> Option<&T> { self.len().checked_sub(1).and_then(|i| self.get(i)) }

	/// Returns a mutable reference to the last element of the rope, or `None` if it's empty.
	pub fn last_mut(&mut self) -> Option<&mut T> { self.len().checked_sub(1).and_then(|i| self.get_mut(i)) }

	/// Inserts an element at `index` within the rope.
	///
	/// # Panics
	/// Panics if `index > len`.
	pub fn insert(&mut self, index: usize, value: T) { todo!() }

	/// Removes and returns the element at `index` from the rope, or `None` if `index` is out of bounds.
	pub fn remove(&mut self, index: usize) -> Option<T> { todo!() }

	/// Removes the first element from a rope and returns it, or `None` if it's empty.
	pub fn pop_front(&mut self) -> Option<T> { todo!() }

	/// Removes the last element from a rope and returns it, or `None` if it's empty.
	pub fn pop_back(&mut self) -> Option<T> { todo!() }

	/// Prepends an element to the rope.
	pub fn push_front(&mut self, value: T) { todo!() }

	/// Appends an element to the rope.
	pub fn push_back(&mut self, value: T) { todo!() }

	/// Takes out a chunk of `range` from the rope.
	///
	/// The `range` must be within the bounds of `self`.
	///
	/// # Panics
	/// Panics if the range is out of bounds.
	pub fn take_chunk(&mut self, range: impl RangeBounds<usize>) -> Self { todo!() }

	/// Concatenates to ropes into one.
	pub fn concat(self, other: Self) -> Self { todo!() }

	/// Divides one rope into two at an index.
	///
	/// The first will contain all indices from `[0, mid)` (*excluding* the index `mid` itself) and the second will contain
	/// all indices from `[mid, len)` (*including* the index `mid` itself).
	///
	/// # Panics
	/// Panics if `mid > len`.
	///
	/// # Examples
	/// ```no_run
	/// todo!()
	/// ```
	pub fn split_at(self) -> (Self, Self) { todo!() }

	/// Splits the rope into two at the given index.
	///
	/// Returns a newly allocated rope containing the elements in the range `[at, len)`.
	/// After the call, the original rope will be left containing the elements `[0, at)`.
	///
	/// # Panics
	/// Panics if `at > len`.
	pub fn split_off(&mut self, at: usize) -> Self { self.take_chunk(at..) }

	/// Moves all element of `other` into `self`, consuming `other`.
	pub fn append(&mut self, other: Self) { todo!() }

	/// Shortens the rope, keeping the first `len` elements and dropping the rest.
	///
	/// If `len` is greater than the vector's current length, this has no effect.
	pub fn truncate(&mut self, len: usize) {
		if len > self.len() {
			return;
		}
		let trash = self.split_off(len);
		drop(trash);
	}

	/// Swaps two elements in the rope. If `a == b`, it's guaranteed that elements won't change value.
	///
	/// # Arguments
	/// - `a` - The index of the first element
	/// - `b` - The index of the second element
	///
	/// # Panics
	/// Panics if `a` or `b` are out of bounds.
	///
	/// # Examples
	/// ```no_run
	/// todo!()
	/// ```
	pub fn swap(&mut self, a: usize, b: usize) { todo!() }

	/// Reverses the order of elements in the rope.
	pub fn reverse(&mut self) { todo!() }

	/// Reverses the specified range from the rope.
	pub fn reverse_range(&mut self, range: impl RangeBounds<usize>) { todo!() }

	/// Resizes the rope in-place so that `len` is equal to `new_len`.
	///
	/// If `new_len` is greater than `len`, the rope is extended by the difference, with each additional slot filled with `value`.
	/// If `new_len` is less than `len`, the rope is simply truncated.
	///
	/// This method requires `T` to implement `Clone`, in order to be able to clone the passed value.
	/// If you need more flexibility (or want to rely on `Default` instead of `Clone`), use `resize_with`.
	/// If you only need to resize to a smaller size, use `truncate`.
	pub fn resize(&mut self, new_len: usize, value: T)
	where T: Clone {
		todo!()
	}

	/// Resizes the rope in-place so that `len` is equal to `new_len`.
	///
	/// If `new_len` is greater than `len`, the rope is extended by the difference, with each additional slot filled with the result of calling the closure `f`.
	/// The return values from `f` will end up in the rope in the order they have been generated.
	/// If `new_len` is less than `len`, the rope is simply truncated.
	///
	/// This method uses a closure to create new values on every push. If you'd rather clone a given value, use `resize`.
	/// If you want to use the `Default` trait to generate values, you can pass `Default::default` as the second argument.
	pub fn resize_with(&mut self, new_len: usize, f: impl FnMut() -> T) { todo!() }

	/// Fills `self` with elements by cloning `value`.
	pub fn fill(&mut self, value: T)
	where T: Clone {
		todo!()
	}

	/// Fills `self` with elements returned by calling a closure repeatedly.
	///
	/// This method uses a closure to create new values. If you'd rather `Clone` a given value, use `fill`.
	/// If you want to use the `Default` trait to generate values, you can pass `Default::default` as the argument.
	pub fn fill_with(&mut self, f: impl FnMut() -> T) { todo!() }

	/// Copies `self` into a new `Vec`.
	pub fn to_vec(&self) -> Vec<T>
	where T: Clone {
		todo!()
	}

	/// Clones and appends all elements in a slice to the rope.
	///
	/// Iterates over the slice `other`, clones each element, and then appends it to `self`. The `other` slice is traversed in-order.
	pub fn extend_from_slice(&mut self, other: &[T])
	where T: Clone {
		todo!()
	}

	/// Returns the index of the partition point according to the given predicate (the index of the first element of the second partition).
	///
	/// The rope is assumed to be partitioned according to the given predicate.
	/// This means that all elements for which the predicate returns true are at the start of the rope and all elements for which the predicate returns false are at the end.
	/// For example, `[7, 15, 3, 5, 4, 12, 6]` is partitioned under the predicate `x % 2 != 0` (all odd numbers are at the start, all even at the end).
	///
	/// If this rope is not partitioned, the returned result is unspecified and meaningless, as this method performs a kind of binary search.
	///
	/// See also binary_search.
	pub fn partition_point(&mut self, pred: impl FnMut(&T) -> bool) -> usize { todo!() }

	/// Binary searches this rope for a given element. If the rope is not sorted, the returned result is unspecified and meaningless.
	///
	/// If the value is found then `Result::Ok` is returned, containing the index of the matching element. If there are multiple matches, then the leftmost one is returned. If the value is not found the `Result::Err` is returned, containing the index where a matching element could be inserted while maintaining sorted order.
	///
	/// See also `partition_point`.
	///
	/// # Examples
	/// ```no_run
	/// todo!()
	/// ```
	pub fn binary_search(&self, x: &T) -> Result<usize, usize>
	where T: Ord {
		todo!()
	}

	/// Sorts the rope.
	///
	/// This sort is stable (i.e., does not reorder equal elements) and <insert time complexity> worst-case.
	///
	/// # Current implementation
	/// <insert implementation details>
	///
	/// # Examples
	/// ```no_run
	/// todo!()
	/// ```
	pub fn sort(&mut self)
	where T: Ord {
		self.sort_by(|x, y| x.cmp(y));
	}

	/// Sorts the rope with a comparator function.
	///
	/// This sort is stable (i.e., does not reorder equal elements) and <insert time complexity> worst-case.
	///
	/// The comparator function must define a total ordering for the elements in the rope. If the ordering is not total, the order of the elements is unspecified. An order is a total order if it is (for all `a`, `b` and `c`):
	/// - total and antisymmetric: exactly one of `a < b`, `a == b` or `a > b` is true, and
	/// - transitive, `a < b` and `b < c` implies `a < c`. The same must hold for both `==` and `>`.
	///
	/// For example, while `f64` doesn't implement `Ord` because `NaN != NaN`, we can use `partial_cmp` as our sort function when we know the rope doesn't contain a `NaN`.
	/// ```no_run
	/// todo!()
	/// ```
	///
	/// # Current implementation
	/// <insert implementation details>
	///
	/// # Examples
	/// ```no_run
	/// todo!()
	/// ```
	pub fn sort_by(&mut self, compare: impl FnMut(&T, &T) -> Ordering) { todo!() }

	/// Sorts the rope with a key extraction function.
	///
	/// This sort is stable (i.e., does not reorder equal elements) and <insert time complexity> worst-case.
	///
	/// For expensive key functions (e.g. functions that are not simple property accesses or baic operations), `sort_by_cached_key` is likely to be significantly faster, as it does not recompute element keys.
	///
	/// # Current implementation
	/// <insert implementation details>
	///
	/// # Examples
	/// ```no_run
	/// todo!()
	/// ```
	pub fn sort_by_key<K>(&mut self, f: impl FnMut(&T) -> K)
	where K: Ord {
	}

	/// Rotates the rope in-place such that the first `mid` elements of the rope move to the end while the last `self.len() - mid` elements move to the front.
	/// After calling `rotate_left`, the element previously at index `mid` will become the first element in the rope.
	///
	/// # Panics
	/// This function will panic if `mid > len`. Note that `mid == len` does *not* panic and is a no-op rotation.
	///
	/// # Examples
	/// ```no_run
	/// todo!()
	/// ```
	pub fn rotate_left(&mut self, mid: usize) {}

	/// Rotates the rope in-place such that the first `len - k` elements of the rope move to the end while the last `k` elements move to the front.
	/// After calling `rotate_right`, the element previously at index `len - k` will become the first element in the rope.
	///
	/// # Panics
	/// This function will panic if `mid > len`. Note that `mid == len` does *not* panic and is a no-op rotation.
	///
	/// # Examples
	/// ```no_run
	/// todo!()
	/// ```
	pub fn rotate_right(&mut self, k: usize) {}

	/// Converts `self` into a vector without clones.
	pub fn into_vec(self) -> Vec<T> { todo!() }

	/// Removes consecutive repeated elements in the rope according to the `PartialEq` trait implementation.
	///
	/// If the rope is sorted, this removes all duplicates.
	pub fn dedup(&mut self) { todo!() }

	/// Creates a vector by copying a rope in `n` times.
	pub fn repeat(&self, n: usize) -> Vec<T>
	where T: Copy {
		let v = self.to_vec();
		v.repeat(n)
	}

	/// Returns an iterator over the rope. The iterator yields all items from start to end.
	pub fn iter(&self) -> Iter<T> { todo!() }

	/// Returns an iterator that allows modifying each value. The iterator yields all items from start to end.
	pub fn iter_mut(&mut self) -> IterMut<T> { todo!() }

	/// Returns `true` if the rope contains an element with the given value. This operation is *O*(*n*).
	///
	/// Note that if you have a sorted rope, `binary_search` may be faster.
	pub fn contains(&self, x: &T) -> bool
	where T: PartialEq<T> {
		todo!()
	}
}

impl<T: Clone> Clone for Rope<T> {
	fn clone(&self) -> Self { todo!() }
}

impl<T: Debug> Debug for Rope<T> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { todo!() }
}

impl<T> Default for Rope<T> {
	fn default() -> Self { todo!() }
}

impl<T> Drop for Rope<T> {
	fn drop(&mut self) { todo!() }
}

impl<T> Extend<T> for Rope<T> {
	fn extend<S: IntoIterator<Item = T>>(&mut self, iter: S) { todo!() }
}

pub struct IntoIter<T> {
	hold: Rope<T>,
}

impl<T> Iterator for IntoIter<T> {
	type Item = T;
	fn next(&mut self) -> Option<Self::Item> { todo!() }
}

impl<T> IntoIterator for Rope<T> {
	type Item = T;
	type IntoIter = IntoIter<T>;
	fn into_iter(self) -> Self::IntoIter { todo!() }
}

pub struct Iter<'a, T> {
	hold: &'a Rope<T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
	type Item = &'a T;
	fn next(&mut self) -> Option<Self::Item> { todo!() }
}

impl<'a, T> IntoIterator for &'a Rope<T> {
	type Item = &'a T;
	type IntoIter = Iter<'a, T>;
	fn into_iter(self) -> Self::IntoIter { todo!() }
}

pub struct IterMut<'a, T> {
	hold: &'a Rope<T>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
	type Item = &'a mut T;
	fn next(&mut self) -> Option<Self::Item> { todo!() }
}

impl<'a, T> IntoIterator for &'a mut Rope<T> {
	type Item = &'a mut T;
	type IntoIter = IterMut<'a, T>;
	fn into_iter(self) -> Self::IntoIter { todo!() }
}
