use std::fmt::{Debug, Display};

pub trait BSTValue: PartialOrd + PartialEq + Clone + Copy + Display + Debug {}
impl<T> BSTValue for T where T: PartialOrd + PartialEq + Clone + Copy + Display + Debug {}

pub trait Visualise<T> {
    fn inorder(&self, level: usize, v: &mut Vec<(usize, T)>);
    fn print(&self);
}

pub trait BSTrees<T>
where
    T: BSTValue
{
    fn new(val: T) -> Box<Self>;
    fn val(&self) -> T;
    fn left(&self) -> Option<&Box<Self>>;
    fn left_mut(&mut self) -> &mut Option<Box<Self>>;
    fn right(&self) -> Option<&Box<Self>>;
    fn right_mut(&mut self) -> &mut Option<Box<Self>>;

    fn insert(&mut self, val: T);
    fn build(arr: &[T]) -> Option<Box<Self>>;
    fn from_vec(v: &mut Vec<T>) -> Box<Self>;
    fn from_vec_unsorted(v: &mut Vec<T>) -> Box<Self>;
    fn from_vec_unbalanced(v: &mut Vec<T>) -> Box<Self>;
    fn min(&self) -> T {
        match self.left() {
            Some(left) => left.min(),
            None => self.val(),
        }
    }
    fn max(&self) -> T {
        match self.right() {
            Some(right) => right.max(),
            None => self.val(),
        }
    }
    fn height(&self) -> usize {
        1 + std::cmp::max(
            self.left().map_or(0, |n| n.height()),
            self.right().map_or(0, |n| n.height()),
        )
    }
    fn find(&self, val: &T) -> Option<&Self> {
        if *val == self.val() {
            Some(self)
        } else if *val < self.val() {
            self.left()?.find(val)
        } else {
            self.right()?.find(val)
        }
    }
    fn contains(&self, val: &T) -> bool {
        self.find(val).is_some()
    }
    fn delete_root(root: Box<Self>) -> Option<Box<Self>>;
    fn delete(self: Box<Self>, target: T) -> Option<Box<Self>>;
}

#[derive(Debug)]
pub struct BST<T>
where
    T: BSTValue
{
    val: T,
    left: Option<Box<BST<T>>>,
    right: Option<Box<BST<T>>>,
}



impl<T> BSTrees<T> for BST<T>
where
    T: BSTValue
{
    fn new(val: T) -> Box<Self> {
        Box::new(Self {
            val,
            left: None,
            right: None,
        })
    }

    fn val(&self) -> T {
        self.val
    }

    fn left(&self) -> Option<&Box<Self>> {
        self.left.as_ref()
    }

    fn left_mut(&mut self) -> &mut Option<Box<Self>> {
        &mut self.left
    }

    fn right(&self) -> Option<&Box<Self>> {
        self.right.as_ref()
    }

    fn right_mut(&mut self) -> &mut Option<Box<Self>> {
        &mut self.right
    }

    fn insert(&mut self, val: T) {
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

    fn build(arr: &[T]) -> Option<Box<BST<T>>> {
        if arr.is_empty() {
            return None;
        }
        let mid = arr.len() / 2;
        let mut node = BST::new(arr[mid]);

        if let Some(left) = Self::build(&arr[..mid]) {
            node.left = Some(left);
        }

        if let Some(right) = Self::build(&arr[mid + 1..]) {
            node.right = Some(right);
        }

        Some(node)
    }

    fn from_vec(v: &mut Vec<T>) -> Box<Self> {
        Self::build(v).unwrap()
    }

    fn from_vec_unsorted(v: &mut Vec<T>) -> Box<Self> {
        v.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
        Self::build(v).unwrap()
    }

    fn from_vec_unbalanced(v: &mut Vec<T>) -> Box<Self> {
        let mut b = BST::new(v[0]);
        for i in 1..v.len() {
            b.insert(v[i]);
        }

        b
    }

    fn delete_root(mut root: Box<Self>) -> Option<Box<Self>> {
        if root.left.is_none() {
            return root.right;
        }
        if root.right.is_none() {
            return root.left;
        }

        let succ = {
            let mut curr = root.right.as_ref().unwrap();
            while let Some(ref l) = curr.left {
                curr = l;
            }
            curr.val
        };

        root.val = succ;
        let right = root.right.take().unwrap();
        root.right = right.delete(succ);

        Some(root)
    }

    fn delete(self: Box<Self>, target: T) -> Option<Box<Self>> {
        match target
            .partial_cmp(&self.val)
            .unwrap_or(std::cmp::Ordering::Equal)
        {
            std::cmp::Ordering::Less => {
                let mut node = self;
                if let Some(left) = node.left.take() {
                    node.left = left.delete(target);
                }
                Some(node)
            }

            std::cmp::Ordering::Greater => {
                let mut node = self;
                if let Some(right) = node.right.take() {
                    node.right = right.delete(target);
                }
                Some(node)
            }

            std::cmp::Ordering::Equal => Self::delete_root(self),
        }
    }
}

impl<T> Visualise<T> for BST<T>
where
    T: BSTValue
{
    fn inorder(&self, level: usize, v: &mut Vec<(usize, T)>) {
        if let Some(ref left) = self.left {
            left.inorder(level + 1, v);
        }
        v.push((level, self.val.clone()));
        if let Some(ref right) = self.right {
            right.inorder(level + 1, v);
        }
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
