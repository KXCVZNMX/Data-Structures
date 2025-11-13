pub trait Visualise {
    fn walk(&self);
}

#[derive(Debug)]
pub struct BST<T> {
    pub val: T,
    pub left: Option<Box<BST<T>>>,
    pub right: Option<Box<BST<T>>>,
}

impl<T> BST<T> {
    pub fn new(val: T) -> Box<Self> {
        Box::new(Self {val, left: None, right: None})
    }
}