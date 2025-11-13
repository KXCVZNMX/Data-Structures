use std::fmt::Display;
use std::ops::{Index, IndexMut};
use std::thread;

/// This module provides a Singly Linked List struct
/// named `ListNode`
///
/// Functions implemented:
/// * [new](struct.ListNode.html#method.new) -> `Box<Self>`
/// * [from_vec](struct.ListNode.html#method.from_vec) -> `Box<Self>`
/// * [print](struct.ListNode.html#method.print) -> `()`
/// * [push](struct.ListNode.html#method.push) -> `()`
/// * [push_back](struct.ListNode.html#method.push_back) -> `()`
/// * [delete](struct.ListNode.html#method.delete) -> `Result<(), &'static str>`
/// * [find](struct.ListNode.html#method.find) -> `Result<&Box<Self>, &'static str>`
/// * [len](struct.ListNode.html#method.len) -> `i32`
/// * [reverse](struct.ListNode.html#method.reverse) -> `()`
/// * [copy](struct.ListNode.html#method.copy) -> `Box<ListNode<T>>`
/// * [insert](struct.ListNode.html#method.insert) -> `()`
/// * [pop](struct.ListNode.html#method.pop) -> `Option<T>`
/// * [contains](struct.ListNode.html#method.contains) -> `bool`
/// * [merge](struct.ListNode.html#method.merge) -> `Option<Box<ListNode<i32>>>`
/// * [sort](struct.ListNode.html#method.sort) -> `Option<Box<ListNode<i32>>>`
#[derive(Clone, Debug)]
pub struct ListNode<T> {
    pub val: T,
    pub next: Option<Box<ListNode<T>>>,
}

impl<T> ListNode<T> {
    /// Constructs a new instance of `ListNode<T>` with the 
    /// default value of whatever `T` is, whereby, `T` has to implement
    /// `Default`
    /// 
    /// # Example
    /// ```
    /// # use crate::data_structure::linked_list::ListNode;
    /// let linked_list: Box<ListNode<i32>> = ListNode::with();
    /// assert_eq!(linked_list, Box::new( ListNode{val: i32::default(), next: None}))
    /// ```
    pub fn new() -> Box<Self> where T: Default {
        Box::new(ListNode::default())
    }
    
    /// Constructs a new instance of `ListNode<T>` with
    /// the provided `val: T`, returning `Box<ListNode<T>>`
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::linked_list::ListNode;
    /// let linked_list = ListNode::with(0);
    /// assert_eq!(linked_list, Box::new( ListNode{ val: 0, next: None } ));
    /// ```
    pub fn with(val: T) -> Box<Self> {
        Box::new(ListNode { val, next: None })
    }

    /// Constructs a new instance of `ListNode<T>` with
    /// a `Vec<T>`, returning `Box<ListNode<T>>`
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::linked_list::ListNode;
    /// assert_eq!(
    ///     ListNode::from_vec(vec![1, 2, 3]),
    ///     Box::new(ListNode {
    ///         val: 1,
    ///         next: Some(Box::new(ListNode {
    ///             val: 2,
    ///             next: Some(Box::new(ListNode {
    ///                 val: 3,
    ///                 next: None,
    ///             }))
    ///         }))
    ///     })
    /// );
    /// ```
    pub fn from_vec(l: Vec<T>) -> Box<Self>
    where
        T: Clone,
    {
        if l.is_empty() {
            panic!("Vector can't be empty");
        }

        let mut list = ListNode::with(l[0].clone());
        let mut head = &mut list;
        for i in 1..l.len() {
            let new_node = ListNode::with(l[i].clone());
            head.next = Some(new_node);
            head = head.next.as_mut().unwrap();
        }
        list
    }

    /// Prints the provided `ListNode<T>`
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::linked_list::ListNode;
    /// let list = ListNode::from_vec(vec![1, 2, 3]);
    /// list.print(); //Output = 1 -> 2 -> 3 -> None
    pub fn print(&self) -> ()
    where
        T: Display,
    {
        let mut head = Some(self);
        while let Some(node) = head {
            print!("{} ({:p}) -> ", node.val, node);
            head = node.next.as_deref();
        }
        print!("None");
        println!();
    }

    /// Pushes an instance of `ListNode<T>` to the front of the list
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::linked_list::ListNode;
    /// let mut list = ListNode::from_vec(vec![2, 3]);
    /// list.push(1);
    /// assert_eq!(list, ListNode::from_vec(vec![1, 2, 3]));
    /// ```
    pub fn push(&mut self, val: T) -> ()
    where
        T: Clone,
    {
        let new_node = ListNode::with(val);
        let mut new_head = new_node;
        new_head.next = Some(Box::new(ListNode {
            val: self.val.clone(),
            next: self.next.take(),
        }));
        *self = *new_head;
    }

    /// Pushes an instance of `ListNode<T>` to the back of the list
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::linked_list::ListNode;
    /// let mut list = ListNode::from_vec(vec![1, 2]);
    /// list.push_back(3);
    /// assert_eq!(list, ListNode::from_vec(vec![1, 2, 3]));
    /// ```
    pub fn push_back(&mut self, val: T) -> ()
    where
        T: Copy,
    {
        let mut head = self;
        loop {
            if head.next.is_none() {
                head.next = Some(ListNode::with(val));
                break;
            }
            head = head.next.as_deref_mut().unwrap();
        }
    }

    /// Deletes the node that equals to the given `val: T`
    ///
    /// The function will delete the first node in the sequence
    /// iterating from `head`, not by index.
    ///
    /// If the element is not found, the program would panic,
    /// yielding `Node not found`.
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::linked_list::ListNode;
    /// # fn foo() -> Result<(), &'static str> {
    /// let mut list = ListNode::from_vec(vec![1, 2, 2, 3]);
    /// list.delete(2)?;
    /// assert_eq!(list, ListNode::from_vec(vec![1, 2, 3]));
    /// # Ok(())
    /// # }
    pub fn delete(&mut self, val: T) -> Result<(), &'static str>
    where
        T: PartialEq,
    {
        let mut head = self;
        loop {
            if head
                .next
                .as_ref()
                .unwrap_or_else(|| {
                    panic!("Node not found");
                })
                .val
                == val
            {
                let next_node = head.next.as_mut().unwrap();
                if next_node.val == val {
                    head.next = next_node.next.take();
                    return Ok(());
                }
                return Err("Node not found");
            }
            head = head.next.as_deref_mut().unwrap();
        }
    }

    /// Finds the node with the give `val: T` and
    /// returns a reference of element.
    ///
    /// This function does not return a new copy of the linked-list, it
    /// returns a reference to a node already on the list.
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::linked_list::ListNode;
    /// # fn foo<T: Default>() -> Result<(), &'static str> {
    /// let mut l1 = ListNode::from_vec(vec![1, 2, 3, 4, 5]);
    /// let node = l1.find(2)?;
    /// assert_eq!(node.val, 2);
    /// # Ok(())
    /// # }
    /// ```
    pub fn find(&mut self, val: T) -> Result<&Self, &'static str>
    where
        T: PartialEq,
    {
        let mut head = self;

        loop {
            let next = match head.next.as_deref_mut() {
                Some(n) => n,
                None => return Err("Node not found"),
            };

            if next.val == val {
                return Ok(next);
            }

            head = next;
        }
    }

    /// Return the length of the given `ListNode<T>` as an i32
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::linked_list::ListNode;
    /// let mut list = ListNode::from_vec(vec![1, 2, 3]);
    /// assert_eq!(list.len(), 3);
    /// ```
    pub fn len(&mut self) -> i32 {
        let mut head = self;
        let mut count: i32 = 0;
        loop {
            if head.next.is_none() {
                count += 1;
                break;
            }
            count += 1;
            head = head.next.as_deref_mut().unwrap();
        }
        count
    }

    /// Reverses the given `ListNode<T>`
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::linked_list::ListNode;
    /// let mut list = ListNode::from_vec(vec![1, 2, 3]);
    /// let mut rev_list = ListNode::from_vec(vec![3, 2, 1]);
    /// rev_list.reverse();
    /// assert_eq!(list, rev_list);
    /// ```
    pub fn reverse(&mut self)
    where
        T: Copy,
    {
        let mut prev = None;
        let mut current = Some(Box::new(ListNode {
            val: std::mem::replace(&mut self.val, unsafe { std::mem::zeroed() }),
            next: self.next.take(),
        }));

        while let Some(mut boxed_node) = current {
            let next = boxed_node.next.take();
            boxed_node.next = prev;
            prev = Some(boxed_node);
            current = next;
        }

        if let Some(mut new_head) = prev {
            self.val = new_head.val;
            self.next = new_head.next.take();
        }
    }

    /// Deep copies the given `ListNode<T>`
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::linked_list::ListNode;
    /// let list = ListNode::from_vec(vec![1, 2, 3]);
    /// let copied = list.copy();
    /// assert_eq!(list, copied);
    /// // compares the pointers
    /// assert_ne!(
    ///     (format!(
    ///         "{:p}{:p}{:p}",
    ///         list,
    ///         list.next.as_ref().unwrap(),
    ///         list.next.as_ref().unwrap().next.as_ref().unwrap())),
    ///     (format!(
    ///         "{:p}{:p}{:p}",
    ///         copied,
    ///         copied.next.as_ref().unwrap(),
    ///         copied.next.as_ref().unwrap().next.as_ref().unwrap())),
    /// );
    /// ```
    pub fn copy(&self) -> Box<ListNode<T>>
    where
        T: Clone,
    {
        Box::new(ListNode {
            val: self.val.clone(),
            next: self.next.as_ref().map(|node| node.clone()),
        })
    }

    /// Inserts a new node of `ListNode<T>` with the `val: T` and in position `index: usize`
    ///
    /// if the index is out of range, the function would return Err
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::linked_list::ListNode;
    /// # fn foo() -> Result<(), &'static str> {
    ///  let mut list = ListNode::from_vec(vec![1, 3]);
    ///  list.insert(1, 2)?;
    ///  assert_eq!(list, ListNode::from_vec(vec![1, 2, 3]));
    /// # Ok(())
    /// # }
    /// ```
    pub fn insert(&mut self, index: usize, val: T) -> Result<(), &'static str> {
        if index == 0 {
            let temp_node = Box::new(ListNode {
                val,
                next: self.next.take(),
            });
            self.next = Some(temp_node);
            std::mem::swap(&mut self.val, &mut self.next.as_mut().unwrap().val);
            return Ok(());
        }

        let mut head = self;
        for _ in 0..index - 1 {
            head = match head.next.as_mut() {
                Some(node) => node,
                None => return Err("Index out of range"),
            };
        }

        let temp_node = Box::new(ListNode {
            val,
            next: head.next.take(),
        });
        head.next = Some(temp_node);
        Ok(())
    }

    /// Pops the element on the front of the list
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::linked_list::ListNode;
    /// # fn foo<T>() -> Option<T> {
    /// let mut list = ListNode::from_vec(vec![1, 1, 2, 3]);
    /// list.pop()?;
    /// assert_eq!(list, ListNode::from_vec(vec![1, 2, 3]));
    /// # None
    /// # }
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if self.next.is_none() {
            return Some(std::mem::replace(&mut self.val, unsafe {
                std::mem::zeroed()
            }));
        }

        let mut oldhead = self.next.take().unwrap();
        std::mem::swap(&mut self.val, &mut oldhead.val);
        self.next = oldhead.next.take();

        Some(oldhead.val)
    }

    /// Checks if whether the `ListNode<T>` contains the given `val: T` element
    ///
    /// # Example
    /// ```
    /// # use data_structure::linked_list::ListNode;
    /// let list = ListNode::from_vec(vec![1, 2, 3]);
    /// assert_eq!(list.contains(2), true);
    /// ```
    pub fn contains(&self, val: T) -> bool
    where
        T: PartialEq,
    {
        let mut head = self;
        while !head.next.is_none() {
            if head.val == val {
                return true;
            } else {
                head = head.next.as_deref().unwrap();
            }
        }
        false
    }

    /// Merges two sorted `ListNode<T>` while keeping the order
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::linked_list::ListNode;
    /// # fn foo() -> Option<Box<ListNode<i32>>> {
    /// let temp1 = ListNode::from_vec(vec![1, 3]);
    /// let temp2 = ListNode::from_vec(vec![2, 4, 5]);
    /// let list = ListNode::<i32>::merge(Some(temp1), Some(temp2))?;
    /// assert_eq!(list, ListNode::from_vec(vec![1, 2, 3, 4, 5]));
    /// # Some(ListNode::with(0))
    /// # }
    /// ```
    pub fn merge(
        mut l1: Option<Box<ListNode<i32>>>,
        mut l2: Option<Box<ListNode<i32>>>,
    ) -> Option<Box<ListNode<i32>>>
    where
        T: PartialOrd,
    {
        let mut r = &mut l1;
        while l2.is_some() {
            if r.is_none() || l2.as_ref()?.val < r.as_ref()?.val {
                std::mem::swap(r, &mut l2);
            }
            r = &mut r.as_mut()?.next;
        }
        l1
    }

    fn split_list(head: Option<Box<ListNode<i32>>>, k: i32) -> Vec<Option<Box<ListNode<i32>>>> {
        let mut length = 0;
        let mut current = head.as_ref();
        let mut parts = Vec::new();

        while let Some(node) = current {
            length += 1;
            current = node.next.as_ref();
        }

        let (base_size, mut extra) = (length / k, length % k);
        let mut current = head;

        for _ in 0..k {
            let mut part_size = base_size + if extra > 0 { 1 } else { 0 };
            let mut dummy = Box::new(ListNode { val: 0, next: None });
            let mut tail = &mut dummy;

            while part_size > 0 {
                tail.next = current.take();
                tail = tail.next.as_mut().unwrap();
                current = tail.next.take();
                part_size -= 1;
            }

            parts.push(dummy.next.take());
            if extra > 0 {
                extra -= 1;
            }
        }

        parts
    }

    /// Sorts the `ListNode<T>` through merge sort
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::linked_list::ListNode;
    /// # fn foo() -> Option<Box<ListNode<i32>>> {
    /// let list = ListNode::<i32>::sort(Some(ListNode::from_vec(vec![5, 2, 3, 1, 4])))?;
    /// assert_eq!(list, ListNode::from_vec(vec![1, 2, 3, 4, 5]));
    /// # Some(ListNode::with(0))
    /// # }
    /// ```
    pub fn sort(head: Option<Box<ListNode<i32>>>) -> Option<Box<ListNode<i32>>> {
        if head.is_none() || head.as_ref().unwrap().next.is_none() {
            return head;
        }

        let (left, right) = {
            let v = ListNode::<i32>::split_list(head, 2);
            (
                v[0].as_ref().unwrap().as_ref().clone(),
                v[1].as_ref().unwrap().as_ref().clone(),
            )
        };

        let left_handle = thread::spawn(move || ListNode::<i32>::sort(Some(Box::new(left))));
        let right_handle = thread::spawn(move || ListNode::<i32>::sort(Some(Box::new(right))));

        let left_sorted = left_handle.join().unwrap();
        let right_sorted = right_handle.join().unwrap();

        ListNode::<i32>::merge(left_sorted, right_sorted)
    }
}

impl<T> Index<usize> for ListNode<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        let mut head = self;

        for _ in 0..index {
            head = head.next.as_deref().expect("Index out of range");
        }
        &head.val
    }
}

impl<T> IndexMut<usize> for ListNode<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let mut head = self;

        for _ in 0..index {
            head = head.next.as_deref_mut().expect("Index out of range");
        }
        &mut head.val
    }
}

impl<T: PartialEq> PartialEq for ListNode<T> {
    fn eq(&self, other: &Self) -> bool {
        let mut head = Some(self);
        let mut other_head = Some(other);
        while let (Some(current), Some(other_current)) = (head, other_head) {
            if current.val != other_current.val {
                return false;
            }
            head = current.next.as_deref();
            other_head = other_current.next.as_deref();
        }
        head.is_none() && other_head.is_none()
    }
}

impl<T: Default> Default for ListNode<T> {
    fn default() -> Self {
        Self {val: T::default(), next: None}
    }
}
