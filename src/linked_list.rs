//! This module provides a doubly linked-list with owned nodes.
//!
//! The `LinkedList` allows for popping and pushing from either end of the list with constant O(1)
//! time.
//!
//! This is implemented while reading both the [`std::collections::LinkedList`] library and [*Learning
//! Rust With Entirely Too Many Linked Lists*](https://rust-unofficial.github.io/too-many-lists/)
//! by rust-unofficial. This is a personal project to further learn Rust and its unsafe features.

use std::cmp::Ordering;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem;
use std::ptr::NonNull;

/// A doubly linked-list with owned nodes.
///
/// The `LinkedList` allows for popping and pushing from either end of the list with constant *O(1)*
/// time.
///
/// A linked-list with a known list of items could be initialised through an array:
/// ```
/// use crate::data_structure::linked_list::LinkedList;
///
/// let list = LinkedList::from([1, 2, 3, 4, 5]);
/// ```
pub struct LinkedList<T> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<T>,
}

struct Node<T> {
    val: T,
    next: Option<NonNull<Node<T>>>,
    prev: Option<NonNull<Node<T>>>,
}

/// An iterator over the elements of a `LinkedList`.
///
/// This `struct` is created by [`LinkedList::iter()`], see its documentation for more.
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[derive(Clone)]
pub struct Iter<'a, T> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<&'a T>,
}

/// A mutable iterator over the elements of a `LinkedList`.
///
/// This `struct` is created by [`LinkedList::iter_mut()`], see its documentation for more.
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[derive(Clone)]
pub struct IterMut<'a, T> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<&'a mut T>,
}

/// An owning iterator over the elements of a `LinkedList`.
///
/// This `struct` is created by [`LinkedList::into_iter()`], see its documentation for more.
pub struct IntoIter<T> {
    list: LinkedList<T>,
}

impl<T> Node<T> {
    pub fn new(val: T) -> Node<T> {
        Node {
            val,
            next: None,
            prev: None,
        }
    }
}

impl<T> LinkedList<T> {
    /// Creates a new, empty `LinkedList<T>`.
    ///
    /// # Example
    ///
    /// ```
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let list: LinkedList<i32> = LinkedList::new();
    /// ```
    pub fn new() -> LinkedList<T> {
        LinkedList {
            head: None,
            tail: None,
            len: 0,
            marker: PhantomData,
        }
    }

    /// Connects `other` to the tail of the list.
    ///
    /// This function takes all nodes of `other`. After calling the function, `other` would become empty.
    ///
    /// This function should compute in *O(1)* time and memory.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let mut list1 = LinkedList::new();
    /// list1.push_back(1);
    ///
    /// let mut list2 = LinkedList::new();
    /// list2.push_back(2);
    /// list2.push_back(3);
    ///
    /// list1.append(&mut list2);
    ///
    /// let mut iter = list1.iter();
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&3));
    /// # }
    /// ```
    pub fn append(&mut self, other: &mut Self) {
        match self.tail {
            None => mem::swap(self, other),
            Some(mut tail) => {
                if let Some(mut other_head) = other.head {
                    unsafe {
                        tail.as_mut().next = Some(other_head);
                        other_head.as_mut().prev = Some(tail);
                    }
                }
                self.tail = other.tail.take();
                self.len += mem::replace(&mut other.len, 0);
            }
        }
    }

    /// Returns the length of the `LinkedList`.
    ///
    /// This operation should compute in *O(1)* time.
    ///
    /// # Example
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    /// assert_eq!(list.len(), 0);
    ///
    /// list.push_back(1);
    /// assert_eq!(list.len(), 1);
    /// list.push_back(2);
    /// assert_eq!(list.len(), 2);
    /// list.push_back(3);
    /// assert_eq!(list.len(), 3);
    /// # }
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns a reference to the first element of the list, `None` if the list is empty.
    ///
    /// This operation should compute in *O(1)* time.
    ///
    /// # Example
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    /// assert_eq!(list.head(), None);
    ///
    /// list.push_front(1);
    /// assert_eq!(list.head(), Some(&1));
    /// list.push_front(2);
    /// assert_eq!(list.head(), Some(&2));
    /// list.push_front(3);
    /// assert_eq!(list.head(), Some(&3));
    /// # }
    /// ```
    pub fn head(&self) -> Option<&T> {
        unsafe { Some(&(*self.head?.as_ptr()).val) }
    }

    /// Returns a mutable reference to the first element of the list, `None` if the list is empty.
    ///
    /// This operation should compute in *O(1)* time.
    ///
    /// # Example
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    /// assert_eq!(list.head_mut(), None);
    ///
    /// list.push_front(1);
    /// assert_eq!(list.head_mut(), Some(&mut 1));
    /// list.push_front(2);
    /// assert_eq!(list.head_mut(), Some(&mut 2));
    /// list.push_front(3);
    /// assert_eq!(list.head_mut(), Some(&mut 3));
    /// # }
    /// ```
    pub fn head_mut(&mut self) -> Option<&mut T> {
        unsafe { Some(&mut (*self.head?.as_mut()).val) }
    }

    /// Returns a reference to the last element of the list, `None` if the list is empty.
    ///
    /// This operation should compute in *O(1)* time.
    ///
    /// # Example
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    /// assert_eq!(list.tail(), None);
    ///
    /// list.push_back(1);
    /// assert_eq!(list.tail(), Some(&1));
    /// list.push_back(2);
    /// assert_eq!(list.tail(), Some(&2));
    /// list.push_back(3);
    /// assert_eq!(list.tail(), Some(&3));
    /// # }
    /// ```
    pub fn tail(&self) -> Option<&T> {
        unsafe { Some(&(*self.tail?.as_ptr()).val) }
    }

    /// Returns a mutable reference to the last element of the list, `None` if the list is empty.
    ///
    /// This operation should compute in *O(1)* time.
    ///
    /// # Example
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    /// assert_eq!(list.tail_mut(), None);
    ///
    /// list.push_back(1);
    /// assert_eq!(list.tail_mut(), Some(&mut 1));
    /// list.push_back(2);
    /// assert_eq!(list.tail_mut(), Some(&mut 2));
    /// list.push_back(3);
    /// assert_eq!(list.tail_mut(), Some(&mut 3));
    /// # }
    /// ```
    pub fn tail_mut(&mut self) -> Option<&mut T> {
        unsafe { Some(&mut (*self.tail?.as_mut()).val) }
    }

    /// Pushes an element to the front of the list.
    ///
    /// This operation should compute in *O(1)* time.
    ///
    /// # Example
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    ///
    /// list.push_front(1);
    /// assert_eq!(list.head().unwrap(), &1);
    /// list.push_front(2);
    /// assert_eq!(list.head().unwrap(), &2);
    /// list.push_front(3);
    /// assert_eq!(list.head().unwrap(), &3);
    /// # }
    /// ```
    pub fn push_front(&mut self, val: T) {
        unsafe {
            let new_node = NonNull::from(Box::leak(Box::new(Node::new(val))));
            if let Some(old_head) = self.head {
                (*old_head.as_ptr()).prev = Some(new_node);
                (*new_node.as_ptr()).next = Some(old_head);
            } else {
                self.tail = Some(new_node);
            }
            self.head = Some(new_node);
            self.len += 1;
        }
    }

    /// Pushes an element to the back of the list.
    ///
    /// This operation should compute in *O(1)* time.
    ///
    /// # Example
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    ///
    /// list.push_back(1);
    /// assert_eq!(list.tail().unwrap(), &1);
    /// list.push_back(2);
    /// assert_eq!(list.tail().unwrap(), &2);
    /// list.push_back(3);
    /// assert_eq!(list.tail().unwrap(), &3);
    /// # }
    /// ```
    pub fn push_back(&mut self, val: T) {
        unsafe {
            let new_node = NonNull::from(Box::leak(Box::new(Node::new(val))));
            if let Some(old_tail) = self.tail {
                (*old_tail.as_ptr()).next = Some(new_node);
                (*new_node.as_ptr()).prev = Some(old_tail);
            } else {
                self.head = Some(new_node);
            }
            self.tail = Some(new_node);
            self.len += 1;
        }
    }

    /// Returns an owned value to the first element of the list, or `None` if the list is empty.
    /// After the operation, the element would be removed.
    ///
    /// This operation should compute in *O(1)* time.
    ///
    /// # Example
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    /// assert_eq!(list.pop_front(), None);
    ///
    /// list.push_back(1);
    /// list.push_back(2);
    /// list.push_back(3);
    /// assert_eq!(list.pop_front(), Some(1));
    /// assert_eq!(list.pop_front(), Some(2));
    /// assert_eq!(list.pop_front(), Some(3));
    /// assert_eq!(list.len(), 0);
    /// # }
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        unsafe {
            self.head.map(|node| {
                let box_node = Box::from_raw(node.as_ptr());
                let result = box_node.val;

                self.head = box_node.next;
                if let Some(new) = self.head {
                    (*new.as_ptr()).prev = None;
                } else {
                    self.tail = None;
                }

                self.len -= 1;
                result
            })
        }
    }

    /// Returns an owned value to the last element of the list, or `None` if the list is empty.
    /// After the operation, the element would be removed.
    ///
    /// This operation should compute in *O(1)* time.
    ///
    /// # Example
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    /// assert_eq!(list.pop_back(), None);
    ///
    /// list.push_front(1);
    /// list.push_front(2);
    /// list.push_front(3);
    /// assert_eq!(list.pop_back(), Some(1));
    /// assert_eq!(list.pop_back(), Some(2));
    /// assert_eq!(list.pop_back(), Some(3));
    /// assert_eq!(list.len(), 0);
    /// # }
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        unsafe {
            self.tail.map(|node| {
                let box_node = Box::from_raw(node.as_ptr());
                let result = box_node.val;

                self.head = box_node.prev;
                if let Some(new) = self.tail {
                    (*new.as_ptr()).next = None;
                } else {
                    self.head = None;
                }

                self.len -= 1;
                result
            })
        }
    }

    /// Provides a forward iterator returning references to the element.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    ///
    /// list.push_back(1);
    /// list.push_back(2);
    /// list.push_back(3);
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&3));
    /// # }
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            head: self.head,
            tail: self.tail,
            len: self.len,
            marker: PhantomData,
        }
    }

    /// Provides a forward iterator returning mutable references to the element.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    ///
    /// list.push_back(1);
    /// list.push_back(2);
    /// list.push_back(3);
    ///
    /// let mut iter = list.iter_mut();
    /// assert_eq!(iter.next(), Some(&mut 1));
    /// assert_eq!(iter.next(), Some(&mut 2));
    /// assert_eq!(iter.next(), Some(&mut 3));
    /// # }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            head: self.head,
            tail: self.tail,
            len: self.len,
            marker: PhantomData,
        }
    }

    fn into_iter(self) -> IntoIter<T> {
        IntoIter { list: self }
    }

    /// Returns whether the list is empty or not.
    ///
    /// This operation should compute in *O(1)* time.
    ///
    /// # Example
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let list: LinkedList<i32> = LinkedList::new();
    ///
    /// assert!(list.is_empty())
    /// # }
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Clears all nodes in the list. this acts the exact same as `drop()`.
    ///
    /// This operation should compute in *O(n)* time.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    /// list.push_back(1);
    /// list.push_back(2);
    /// list.push_back(3);
    ///
    /// list.clear();
    /// assert!(list.is_empty())
    /// # }
    /// ```
    pub fn clear(&mut self) {
        while let Some(_) = self.pop_front() {}
    }

    /// Checks whether the list contains a certain value.
    ///
    /// This operation should compute in *O(n)* time.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    ///
    /// list.push_back(1);
    /// list.push_back(2);
    /// list.push_back(3);
    ///
    /// assert!(list.contains(&1));
    /// assert!(!list.contains(&4));
    /// # }
    /// ```
    pub fn contains(&self, val: &T) -> bool
    where
        T: PartialEq<T>,
    {
        self.iter().any(|e| e == val)
    }

    /// Splits the list into two separate lists at the given index. Returning everything after and
    /// including the given index.
    ///
    /// This operation should compute in *O(n)* time.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Example
    ///
    /// ```
    /// # fn foo() {
    /// use crate::data_structure::linked_list::LinkedList;
    ///
    /// let mut list = LinkedList::new();
    ///
    /// list.push_front(1);
    /// list.push_front(2);
    /// list.push_front(3);
    ///
    /// let mut split = list.split_off(2);
    ///
    /// assert_eq!(split.pop_front(), Some(1));
    /// assert_eq!(split.pop_front(), None);
    /// # }
    /// ```
    pub fn split_off(&mut self, at: usize) -> LinkedList<T> {
        let len = self.len();
        assert!(
            at <= len,
            "LinkedList::split_off(): cannot split off, out of bounds"
        );

        if at == 0 {
            return mem::replace(self, Self::new());
        } else if at == len {
            return Self::new();
        }

        let split_node = if at - 1 <= len - at {
            let mut iter = self.iter_mut();
            for _ in 0..(at - 1) {
                iter.next();
            }
            iter.head
        } else {
            let mut iter = self.iter_mut();
            for _ in 0..(len - at) {
                iter.next_back();
            }
            iter.tail
        };

        let split_node = split_node.expect("LinkedList::split_off(): split_node is in None");

        unsafe {
            let new_head = (*split_node.as_ptr())
                .next
                .take()
                .expect("LinkedList::split_off(): split_node.next is None");
            (*new_head.as_ptr()).prev = None;
            let ret = LinkedList {
                head: Some(new_head),
                tail: self.tail,
                len: len - at,
                marker: PhantomData,
            };
            (*split_node.as_ptr()).next = None;
            self.tail = Some(split_node);
            self.len = at;
            ret
        }
    }
}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        while let Some(_) = self.pop_front() {}
    }
}

impl<'a, T> IntoIterator for &'a LinkedList<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T> IntoIterator for LinkedList<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a mut LinkedList<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.head.map(|node| unsafe {
                self.len -= 1;
                self.head = (*node.as_ptr()).next;
                &(*node.as_ptr()).val
            })
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.tail.map(|node| unsafe {
                self.len -= 1;
                self.tail = (*node.as_ptr()).prev;
                &(*node.as_ptr()).val
            })
        } else {
            None
        }
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.head.map(|node| unsafe {
                self.len -= 1;
                self.head = (*node.as_ptr()).next;
                &mut (*node.as_ptr()).val
            })
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.tail.map(|node| unsafe {
                self.len -= 1;
                self.tail = (*node.as_ptr()).prev;
                &mut (*node.as_ptr()).val
            })
        } else {
            None
        }
    }
}

impl<'a, T> ExactSizeIterator for IterMut<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.list.pop_front()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.len, Some(self.list.len))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.list.pop_back()
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.list.len
    }
}

impl<'a, T: 'a + Copy> Extend<&'a T> for LinkedList<T> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned())
    }

    fn extend_one(&mut self, &item: &'a T) {
        self.push_back(item);
    }
}

impl<T> Extend<T> for LinkedList<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            self.push_back(item);
        }
    }

    fn extend_one(&mut self, item: T) {
        self.push_back(item);
    }
}

impl<T> FromIterator<T> for LinkedList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut list = Self::new();
        list.extend(iter);
        list
    }
}

impl<T, const N: usize> From<[T; N]> for LinkedList<T> {
    fn from(value: [T; N]) -> Self {
        Self::from_iter(value)
    }
}

impl<T: Debug> Debug for LinkedList<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<T: PartialEq> PartialEq for LinkedList<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().eq(other)
    }

    fn ne(&self, other: &Self) -> bool {
        self.len() != other.len() || self.iter().ne(other)
    }
}

impl<T: Eq> Eq for LinkedList<T> {}

impl<T: PartialOrd> PartialOrd for LinkedList<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord> Ord for LinkedList<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<T: Hash> Hash for LinkedList<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for i in self {
            i.hash(state);
        }
    }
}

impl<T: Clone> Clone for LinkedList<T> {
    fn clone(&self) -> Self {
        let mut new_list = Self::new();
        for item in self {
            new_list.push_back(item.clone());
        }
        new_list
    }
}

unsafe impl<T: Send + Send> Send for LinkedList<T> {}
unsafe impl<T: Sync + Sync> Sync for LinkedList<T> {}
unsafe impl<'a, T: Send> Send for Iter<'a, T> {}
unsafe impl<'a, T: Sync> Sync for Iter<'a, T> {}
unsafe impl<'a, T: Send> Send for IterMut<'a, T> {}
unsafe impl<'a, T: Sync> Sync for IterMut<'a, T> {}
