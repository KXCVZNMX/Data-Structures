use std::fmt::{Debug, Display};

pub trait Visualise<T> {
    fn inorder(&self, level: usize, v: &mut Vec<(usize, T)>);
    fn print(&self);
}

#[derive(Debug)]
pub struct BST<T>
where
    T: PartialOrd + PartialEq + Clone + Display + Debug
{
    pub val: T,
    pub left: Option<Box<BST<T>>>,
    pub right: Option<Box<BST<T>>>,
}

impl<T> BST<T>
where
    T: PartialOrd + PartialEq + Clone + Display + Debug
{
    pub fn new(val: T) -> Box<Self> {
        Box::new(Self {
            val,
            left: None,
            right: None,
        })
    }

    pub fn insert(&mut self, val: T) {
        if val < self.val {
            if self.left.is_some() {
                self.left.as_mut().unwrap().insert(val);
            } else {
                self.left = Some(BST::new(val))
            }
        } else if val >= self.val {
            if self.right.is_some() {
                self.right.as_mut().unwrap().insert(val);
            } else {
                self.right = Some(BST::new(val))
            }
        }
    }
}

impl<T> Visualise<T> for BST<T>
where
    T: PartialOrd + PartialEq + Clone + Display + Debug
{
    fn inorder(&self, level: usize, v: &mut Vec<(usize, T)>) {
        if let Some(ref left) = self.left { left.inorder(level + 1, v); }
        v.push((level, self.val.clone()));
        if let Some(ref right) = self.right { right.inorder(level + 1, v); }
    }

    fn print(&self) {
        let mut v = vec![];
        self.inorder(0, &mut v);
        for (depth, val) in v {
            let indent = "    ".repeat(depth);
            println!("{} ── {}", indent, val);
        }
    }
}