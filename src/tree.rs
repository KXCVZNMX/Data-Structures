use std::fmt::{Debug, Display};

pub trait Visualise<T> {
    fn inorder(&self, level: usize, v: &mut Vec<(usize, T)>);
    fn print(&self);
}

#[derive(Debug)]
pub struct BST<T>
where
    T: PartialOrd + PartialEq + Clone + Copy + Display + Debug
{
    pub val: T,
    pub left: Option<Box<BST<T>>>,
    pub right: Option<Box<BST<T>>>,
}

impl<T> BST<T>
where
    T: PartialOrd + PartialEq + Clone + Copy + Display + Debug
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

    pub fn from_vec(v: &mut Vec<T>) -> Box<Self> {
        v.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());

        fn build<K>(arr: &[K]) -> Option<Box<BST<K>>>
        where
            K: PartialOrd + PartialEq + Clone + Copy + Display + Debug,
        {
            if arr.is_empty() { return None; }
            let mid = arr.len() / 2;
            let mut node = BST::new(arr[mid]);

            if let Some(left) = build(&arr[..mid]) {
                node.left = Some(left);
            }

            if let Some(right) = build(&arr[mid + 1..]) {
                node.right = Some(right);
            }

            Some(node)
        }

        build(v).unwrap()
    }

    pub fn from_vec_unbalanced(v: Vec<T>) -> Box<Self> {
        let mut b = BST::new(v[0]);
        for i in 1..v.len() {
            b.insert(v[i]);
        }

        b
    }

    pub fn min(&self) -> &T {
        match &self.left {
            Some(left) => left.min(),
            None => &self.val,
        }
    }

    pub fn max(&self) -> &T {
        match &self.right {
            Some(right) => right.max(),
            None => &self.val,
        }
    }

    pub fn height(&self) -> usize {
        1 + usize::max(
            self.left.as_ref().map_or(0, |n| n.height()),
            self.right.as_ref().map_or(0, |n| n.height())
        )
    }

    pub fn delete(&self, val: &T) -> Result<(), &'static str> {
        todo!()
    }

    pub fn find(&self, val: &T) -> Option<&Self>{
        if self.val == *val {
            Some(&self)
        } else if *val >= self.val {
            self.right.as_ref()?.find(val)
        } else {
            self.left.as_ref()?.find(val)
        }
    }

    pub fn contains(&self, val: &T) -> bool {
        self.find(&val).is_some()
    }
}

impl<T> Visualise<T> for BST<T>
where
    T: PartialOrd + PartialEq + Clone + Copy + Display + Debug
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