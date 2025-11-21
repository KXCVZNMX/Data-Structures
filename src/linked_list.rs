use std::alloc::{Allocator, Global};
use std::cmp::Ordering;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem;
use std::ptr::NonNull;

pub struct LinkedList<T, A: Allocator = Global> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    alloc: A,
    marker: PhantomData<Box<Node<T>, A>>,
}

struct Node<T> {
    val: T,
    next: Option<NonNull<Node<T>>>,
    prev: Option<NonNull<Node<T>>>,
}

#[must_use = "iterators are lazy and do nothing unless consumed"]
#[derive(Clone)]
pub struct Iter<'a, T> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<&'a T>,
}

pub struct IterMut<'a, T> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<&'a mut T>,
}

pub struct IntoIter<T, A: Allocator = Global> {
    list: LinkedList<T, A>,
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
    pub fn new() -> LinkedList<T> {
        LinkedList {
            head: None,
            tail: None,
            len: 0,
            alloc: Global,
            marker: PhantomData,
        }
    }

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
}

impl<T, A: Allocator> LinkedList<T, A> {
    pub fn new_in(alloc: A) -> LinkedList<T, A> {
        LinkedList {
            head: None,
            tail: None,
            len: 0,
            alloc,
            marker: PhantomData,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn head(&self) -> Option<&T> {
        unsafe { Some(&(*self.head?.as_ptr()).val) }
    }

    pub fn head_mut(&mut self) -> Option<&mut T> {
        unsafe { Some(&mut (*self.head?.as_mut()).val) }
    }

    pub fn tail(&self) -> Option<&T> {
        unsafe { Some(&(*self.tail?.as_ptr()).val) }
    }

    pub fn tail_mut(&mut self) -> Option<&mut T> {
        unsafe { Some(&mut (*self.tail?.as_mut()).val) }
    }

    pub fn push_front(&mut self, val: T) {
        unsafe {
            let new_node = NonNull::from(Box::leak(Box::new_in(Node::new(val), &self.alloc)));
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

    pub fn push_back(&mut self, val: T) {
        unsafe {
            let new_node = NonNull::from(Box::leak(Box::new_in(Node::new(val), &self.alloc)));
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

    pub fn pop_front(&mut self) -> Option<T> {
        unsafe {
            self.head.map(|node| {
                let box_node = Box::from_raw_in(node.as_ptr(), &self.alloc);
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

    pub fn pop_back(&mut self) -> Option<T> {
        unsafe {
            self.tail.map(|node| {
                let box_node = Box::from_raw_in(node.as_ptr(), &self.alloc);
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

    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            head: self.head,
            tail: self.tail,
            len: self.len,
            marker: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            head: self.head,
            tail: self.tail,
            len: self.len,
            marker: PhantomData,
        }
    }

    pub fn into_iter(self) -> IntoIter<T, A> {
        IntoIter { list: self }
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn clear(&mut self) {
        while let Some(_) = self.pop_front() {}
    }

    pub fn contains(&self, val: &T) -> bool
    where
        T: PartialEq<T>,
    {
        self.iter().any(|e| e == val)
    }

    pub fn split_off(&mut self, at: usize) -> LinkedList<T, A>
    where
        A: Clone,
    {
        let len = self.len();
        assert!(
            at <= len,
            "LinkedList::split_off(): cannot split off, out of bounds"
        );

        if at == 0 {
            return mem::replace(self, Self::new_in(self.alloc.clone()));
        } else if at == len {
            return Self::new_in(self.alloc.clone());
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
                alloc: self.alloc.clone(),
                marker: PhantomData,
            };
            (*split_node.as_ptr()).next = None;
            self.tail = Some(split_node);
            self.len = at;
            ret
        }
    }
}

impl<T, A: Allocator> Drop for LinkedList<T, A> {
    fn drop(&mut self) {
        while let Some(_) = self.pop_front() {}
    }
}

impl<'a, T, A: Allocator> IntoIterator for &'a LinkedList<T, A> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T, A: Allocator> IntoIterator for LinkedList<T, A> {
    type Item = T;
    type IntoIter = IntoIter<T, A>;

    fn into_iter(self) -> Self::IntoIter {
        self.into_iter()
    }
}

impl<'a, T, A: Allocator> IntoIterator for &'a mut LinkedList<T, A> {
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

impl<T, A: Allocator> Iterator for IntoIter<T, A> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.list.pop_front()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.len, Some(self.list.len))
    }
}

impl<T, A: Allocator> DoubleEndedIterator for IntoIter<T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.list.pop_back()
    }
}

impl<T, A: Allocator> ExactSizeIterator for IntoIter<T, A> {
    fn len(&self) -> usize {
        self.list.len
    }
}

impl<'a, T: 'a + Copy, A: Allocator> Extend<&'a T> for LinkedList<T, A> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned())
    }

    fn extend_one(&mut self, &item: &'a T) {
        self.push_back(item);
    }
}

impl<T, A: Allocator> Extend<T> for LinkedList<T, A> {
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
    fn from_iter<I: IntoIterator<Item=T>>(iter: I) -> Self {
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

impl<T: Debug, A: Allocator> Debug for LinkedList<T, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<T: PartialEq, A: Allocator> PartialEq for LinkedList<T, A> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() || self.iter().eq(other)
    }

    fn ne(&self, other: &Self) -> bool {
        self.len() != other.len() || self.iter().ne(other)
    }
}

impl<T: Eq, A: Allocator> Eq for LinkedList<T, A> { }

impl<T: PartialOrd, A: Allocator> PartialOrd for LinkedList<T, A> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord, A: Allocator> Ord for LinkedList<T, A> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<T: Hash, A: Allocator> Hash for LinkedList<T, A>{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for i in self {
            i.hash(state);
        }
    }
}