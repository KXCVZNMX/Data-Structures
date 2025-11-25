use crate::trees::Node;

pub struct BST<T: Ord> {
    root: Option<Box<Node<T>>>,
}

impl<T: Ord> BST<T> {
    fn insert_into_root(node: &mut Box<Node<T>>, val: T) {
        if val < node.val {
            if node.left.is_some() {
                // It's safe to use unwrap() after the is_some() check.
                Self::insert_into_root(node.left.as_mut().unwrap(), val);
            } else {
                node.left = Some(Box::new(Node::new(val)));
            }
        } else if val >= node.val {
            if node.right.is_some() {
                // It's safe to use unwrap() after the is_some() check.
                Self::insert_into_root(node.right.as_mut().unwrap(), val);
            } else {
                node.right = Some(Box::new(Node::new(val)));
            }
        }
    }

    fn contains_elem_in_root(node: &Box<Node<T>>, val: &T) -> bool {
        if val == &node.val {
            true
        } else if val < &node.val && node.left.is_some() {
            Self::contains_elem_in_root(node.left.as_ref().unwrap(), val)
        } else if val > &node.val && node.right.is_some() {
            Self::contains_elem_in_root(node.right.as_ref().unwrap(), val)
        } else {
            false
        }
    }

    fn minimum_node(node: &Box<Node<T>>) -> &T {
        match node.left.as_ref() {
            None => &node.val,
            Some(n) => Self::minimum_node(n),
        }
    }

    fn maximum_node(node: &Box<Node<T>>) -> &T {
        match node.right.as_ref() {
            None => &node.val,
            Some(n) => Self::maximum_node(n),
        }
    }

    fn remove_node(node: &mut Option<Box<Node<T>>>, val: &T) {
        let Some(n) = node.as_mut() else {
            return;
        };

        match val.cmp(&n.val) {
            std::cmp::Ordering::Greater => Self::remove_node(&mut n.right, val),
            std::cmp::Ordering::Less => Self::remove_node(&mut n.left, val),
            std::cmp::Ordering::Equal => match (n.left.take(), n.right.take()) {
                (None, None) => *node = None,
                (Some(left), None) => *node = Some(left),
                (None, Some(right)) => *node = Some(right),
                (Some(left), Some(mut right)) => {
                    {
                        let mut cur = &mut right;
                        while let Some(ref mut l) = cur.left {
                            cur = l;
                        }
                        cur.left = Some(left);
                    }
                    *node = Some(right)
                }
            },
        }
    }

    fn inorder_traversal<'a>(node: &'a Box<Node<T>>, level: usize, v: &mut Vec<(usize, &'a T)>) {
        if let Some(ref left) = node.left {
            Self::inorder_traversal(left, level + 1, v);
        }
        v.push((level, &node.val));
        if let Some(ref right) = node.right {
            Self::inorder_traversal(right, level + 1, v);
        }
    }
}

impl<T: Ord> BST<T> {
    pub fn new() -> Self {
        BST { root: None }
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    pub fn insert(&mut self, val: T) {
        if let Some(root) = self.root.as_mut() {
            Self::insert_into_root(root, val);
        } else {
            self.root = Some(Box::new(Node::new(val)));
        }
    }

    pub fn contains(&self, val: &T) -> bool {
        match self.root.as_ref() {
            None => false,
            Some(root) => Self::contains_elem_in_root(root, val),
        }
    }

    pub fn min(&self) -> Option<&T> {
        self.root.as_ref().map(|node| Self::minimum_node(&node))
    }

    pub fn max(&self) -> Option<&T> {
        self.root.as_ref().map(|node| Self::maximum_node(&node))
    }

    pub fn remove(&mut self, val: &T) {
        Self::remove_node(&mut self.root, val);
    }

    pub fn inorder<'a>(&'a self) -> Vec<(usize, &'a T)> {
        let mut v: Vec<(usize, &'a T)> = Vec::new();
        self.root
            .as_ref()
            .map(|root| Self::inorder_traversal(root, 0, &mut v));
        v
    }
}

#[cfg(test)]
mod tests {
    use super::BST;

    #[test]
    fn new_tree_is_empty() {
        let bst = BST::<i32>::new();
        assert!(bst.is_empty());
        assert_eq!(bst.min(), None);
        assert_eq!(bst.max(), None);
        assert!(bst.inorder().is_empty());
        assert!(!bst.contains(&10));
    }

    #[test]
    fn insert_single_element() {
        let mut bst = BST::new();
        bst.insert(5);

        assert!(!bst.is_empty());
        assert!(bst.contains(&5));
        assert_eq!(bst.min(), Some(&5));
        assert_eq!(bst.max(), Some(&5));

        let inorder: Vec<(usize, i32)> = bst
            .inorder()
            .into_iter()
            .map(|(lvl, v)| (lvl, *v))
            .collect();
        assert_eq!(inorder, vec![(0, 5)]);
    }

    #[test]
    fn insert_multiple_elements_and_check_contains() {
        let mut bst = BST::new();
        for v in [5, 3, 7, 2, 4, 6, 8] {
            bst.insert(v);
        }

        for v in [5, 3, 7, 2, 4, 6, 8] {
            assert!(bst.contains(&v), "tree should contain {v}");
        }
        for v in [0, 1, 9, 10] {
            assert!(!bst.contains(&v), "tree should not contain {v}");
        }

        assert_eq!(bst.min(), Some(&2));
        assert_eq!(bst.max(), Some(&8));
    }

    #[test]
    fn inorder_traversal_balanced_tree() {
        //           5 (0)
        //         /     \
        //      3 (1)   7 (1)
        //     /   \   /   \
        //  2(2) 4(2) 6(2) 8(2)
        let mut bst = BST::new();
        for v in [5, 3, 7, 2, 4, 6, 8] {
            bst.insert(v);
        }

        let got: Vec<(usize, i32)> = bst
            .inorder()
            .into_iter()
            .map(|(lvl, v)| (lvl, *v))
            .collect();

        let expected = vec![(2, 2), (1, 3), (2, 4), (0, 5), (2, 6), (1, 7), (2, 8)];

        assert_eq!(got, expected);
    }

    #[test]
    fn inorder_traversal_right_skewed_tree() {
        // 1(0) - 2(1) - 3(2) - 4(3)
        let mut bst = BST::new();
        for v in [1, 2, 3, 4] {
            bst.insert(v);
        }

        let got: Vec<(usize, i32)> = bst
            .inorder()
            .into_iter()
            .map(|(lvl, v)| (lvl, *v))
            .collect();

        let expected = vec![(0, 1), (1, 2), (2, 3), (3, 4)];

        assert_eq!(got, expected);
    }

    #[test]
    fn remove_from_empty_tree_does_not_panic() {
        let mut bst = BST::<i32>::new();
        bst.remove(&10); // should not panic
        assert!(bst.is_empty());
        assert_eq!(bst.min(), None);
        assert_eq!(bst.max(), None);
        assert!(bst.inorder().is_empty());
    }

    #[test]
    fn remove_leaf_node() {
        //      5
        //     /
        //    3
        //   /
        //  2  <- leaf
        let mut bst = BST::new();
        for v in [5, 3, 2] {
            bst.insert(v);
        }

        assert!(bst.contains(&2));
        bst.remove(&2);
        assert!(!bst.contains(&2));

        assert!(bst.contains(&3));
        assert!(bst.contains(&5));

        let vals: Vec<i32> = bst.inorder().into_iter().map(|(_, v)| *v).collect();
        assert_eq!(vals, vec![3, 5]);
        assert_eq!(bst.min(), Some(&3));
        assert_eq!(bst.max(), Some(&5));
    }

    #[test]
    fn remove_node_with_one_right_child() {
        //   5
        //    \
        //     7
        //      \
        //       8
        let mut bst = BST::new();
        for v in [5, 7, 8] {
            bst.insert(v);
        }

        bst.remove(&7);

        assert!(!bst.contains(&7));
        assert!(bst.contains(&5));
        assert!(bst.contains(&8));

        let vals: Vec<i32> = bst.inorder().into_iter().map(|(_, v)| *v).collect();
        assert_eq!(vals, vec![5, 8]);
        assert_eq!(bst.min(), Some(&5));
        assert_eq!(bst.max(), Some(&8));
    }

    #[test]
    fn remove_node_with_one_left_child() {
        //     5
        //    /
        //   3
        //  /
        // 2
        let mut bst = BST::new();
        for v in [5, 3, 2] {
            bst.insert(v);
        }

        bst.remove(&3);

        assert!(!bst.contains(&3));
        assert!(bst.contains(&2));
        assert!(bst.contains(&5));

        let vals: Vec<i32> = bst.inorder().into_iter().map(|(_, v)| *v).collect();
        assert_eq!(vals, vec![2, 5]);
        assert_eq!(bst.min(), Some(&2));
        assert_eq!(bst.max(), Some(&5));
    }

    #[test]
    fn remove_node_with_two_children_non_root() {
        //        10
        //       /  \
        //      5    15
        //     / \
        //    3   7   <- 5 has two children
        let mut bst = BST::new();
        for v in [10, 5, 15, 3, 7] {
            bst.insert(v);
        }

        bst.remove(&5);

        assert!(!bst.contains(&5));
        for v in [3, 7, 10, 15] {
            assert!(bst.contains(&v));
        }

        let vals: Vec<i32> = bst.inorder().into_iter().map(|(_, v)| *v).collect();
        assert_eq!(vals, vec![3, 7, 10, 15]);
        assert_eq!(bst.min(), Some(&3));
        assert_eq!(bst.max(), Some(&15));
    }

    #[test]
    fn remove_root_with_two_children() {
        //          5
        //        /   \
        //       3     7
        //      / \   / \
        //     2  4  6  8
        let mut bst = BST::new();
        for v in [5, 3, 7, 2, 4, 6, 8] {
            bst.insert(v);
        }

        bst.remove(&5);

        assert!(!bst.contains(&5));
        for v in [2, 3, 4, 6, 7, 8] {
            assert!(bst.contains(&v));
        }

        let vals: Vec<i32> = bst.inorder().into_iter().map(|(_, v)| *v).collect();
        assert_eq!(vals, vec![2, 3, 4, 6, 7, 8]);
        assert_eq!(bst.min(), Some(&2));
        assert_eq!(bst.max(), Some(&8));
    }

    #[test]
    fn remove_all_nodes_until_empty() {
        let mut bst = BST::new();
        let values = [5, 3, 7, 2, 4, 6, 8];

        for v in values {
            bst.insert(v);
        }

        for v in values {
            assert!(bst.contains(&v));
            bst.remove(&v);
            assert!(!bst.contains(&v));
        }

        assert!(bst.is_empty());
        assert_eq!(bst.min(), None);
        assert_eq!(bst.max(), None);
        assert!(bst.inorder().is_empty());
    }

    #[test]
    fn inserting_duplicates_and_removing_them() {
        let mut bst = BST::new();

        bst.insert(5);
        bst.insert(5);
        bst.insert(5);

        assert!(bst.contains(&5));

        // Remove 5 three times; depending on structure, each remove
        // should delete one occurrence until the tree is empty.
        bst.remove(&5);
        assert!(bst.contains(&5));

        bst.remove(&5);
        assert!(bst.contains(&5));

        bst.remove(&5);
        assert!(!bst.contains(&5));
        assert!(bst.is_empty());
    }
}
