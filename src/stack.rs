use crate::linked_list::ListNode;
use std::fmt::Display;

/// This module provides a Stack struct named `Stack`
///
/// Functions Implemented:
/// * [new](struct.Stack.html#method.new) -> `Self`
/// * [from_vec](struct.Stack.html#method.from_vec) -> `Self`
/// * [print](struct.Stack.html#method.print) -> `()`
/// * [pop](struct.Stack.html#method.pop) -> `T`
/// * [push](struct.Stack.html#method.push) -> `()`
/// * [peak](struct.Stack.html#method.peak) -> `T`
/// * [clear](struct.Stack.html#method.clear) -> `()`
#[derive(Debug, Clone)]
pub struct Stack<T> {
    pub list: Box<ListNode<T>>,
    pub len: usize,
}

impl<T> Stack<T>
where
    T: Display,
{
    /// Constructs a new instance of `Stack<T>` with the provided
    /// `val: T`, returning `Self`
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::stack::Stack;
    /// # use crate::data_structure::linked_list::ListNode;
    /// let stack = Stack::new(1);
    /// assert_eq!(stack, Stack{list: ListNode::new(1), len: 1});
    /// ```
    ///
    /// There cannot be an empty stack if you are initialising it.
    pub fn new(val: T) -> Self {
        Stack {
            list: ListNode::new(val),
            len: 1,
        }
    }

    /// Constructs a new instance of `Stack<T>` with the provided
    /// `Vec<T>`, returning `Self`
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::{stack::Stack, linked_list::ListNode};
    /// let stack = Stack::from_vec(vec![1, 2, 3]);
    /// assert_eq!(
    ///     stack,
    ///     Stack{
    ///         len: 3,
    ///         list: ListNode::from_vec(vec![1, 2, 3]),
    ///     }
    /// )
    /// ```
    pub fn from_vec(vec: Vec<T>) -> Self
    where
        T: Clone,
    {
        let temp = vec.clone();
        Stack {
            list: ListNode::from_vec(temp),
            len: vec.len(),
        }
    }

    /// Prints the given Stack.
    ///
    /// # Example Output
    ///
    /// ```text
    /// +---+---+---+---+---+
    /// | 1 | 2 | 3 | 4 | 5 |
    /// +---+---+---+---+---+
    ///   ↑
    ///  HEAD
    /// ```
    ///
    /// The stack is displayed with the top (HEAD) indicated.
    pub fn print(&self) {
        let separator = "+---".repeat(self.len) + "+";

        println!("{}", separator);

        for i in 0..self.len {
            print!("| {:^2}", self.list[i]);
        }

        println!("|");
        println!("{}", separator);
        println!("  ↑");
        println!(" HEAD");
    }

    /// Pops the first element of the stack off, returning it
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::stack::Stack;
    /// let mut stack = Stack::from_vec(vec![1, 1, 2, 3, 4, 5]);
    /// let poped_val = stack.pop();
    /// assert_eq!(poped_val, 1);
    /// ```
    pub fn pop(&mut self) -> T {
        let val = self.list.pop().unwrap();
        self.len -= 1;
        val
    }

    /// Pushes an element on to the top of the stack
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::stack::Stack;
    /// let mut stack = Stack::from_vec(vec![2, 3, 4, 5]);
    /// stack.push(1);
    /// assert_eq!(stack, Stack::from_vec(vec![1, 2, 3, 4, 5]));
    /// ```
    pub fn push(&mut self, val: T)
    where
        T: Clone,
    {
        self.list.push(val);
        self.len += 1;
    }

    /// Clears the entire stack, making it with one element with value of `T::default`
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::{linked_list::ListNode, stack::Stack};
    ///
    /// let mut stack = Stack::from_vec(vec![1, 2, 3, 4, 5]);
    /// stack.clear();
    /// assert_eq!(stack, Stack{len: 1, list: ListNode::new(i32::default())});
    /// ```
    pub fn clear(&mut self)
    where
        T: Default,
    {
        self.list = ListNode::new(T::default());
        self.len = 1;
    }

    /// Peaks at the top of the stack, returning the value `T`, but not removing it
    ///
    /// # Example
    /// ```
    /// # use crate::data_structure::stack::Stack;
    /// let stack = Stack::from_vec(vec![1, 2, 3, 4, 5]);
    /// let peak_val = stack.peak();
    /// assert_eq!(peak_val, 1);
    /// assert_eq!(stack, Stack::from_vec(vec![1, 2, 3, 4, 5]));
    /// ```
    pub fn peak(&self) -> T
    where
        T: Clone,
    {
        self.list.val.clone()
    }
}

impl<T: PartialEq + Clone + Copy> PartialEq for Stack<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.len != other.len {
            return false;
        }
        let head = *self.list.copy();
        let other_head = *self.list.copy();
        for i in 0..self.len {
            if head[i] != other_head[i] {
                return false;
            }
        }
        true
    }
}
