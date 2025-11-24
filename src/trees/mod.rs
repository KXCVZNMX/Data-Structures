pub mod bst;

pub struct Node<T> {
    val: T,
    left: Option<Box<Node<T>>>,
    right: Option<Box<Node<T>>>,
}

impl<T> Node<T> {
    pub fn new(val: T) -> Self {
        Self { val, left: None, right: None }
    }
    
    pub fn left(&self) -> Option<&T> {
        self.left.as_ref().map(|node| &node.val)
    }

    pub fn left_mut(&mut self) -> Option<&mut T> {
        self.left.as_mut().map(|node| &mut node.val)
    }

    pub fn right(&self) -> Option<&T> {
        self.right.as_ref().map(|node| &node.val)
    }

    pub fn right_mut(&mut self) -> Option<&mut T> {
        self.right.as_mut().map(|node| &mut node.val)
    }
}