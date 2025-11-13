//! This crate provides some data structures
//! implemented by [KXCVZNMX](https://github.com/KXCVZNMX) ([source](https://github.com/KXCVZNMX/Data-Structures))
//!
//! Data structures currently implemented:
//! * Linked List
//! * Stack (with linked list)

pub mod linked_list;
pub mod stack;
mod tree;

#[cfg(test)]
mod test {
    use crate::linked_list::ListNode;
    use crate::stack::Stack;

    #[test]
    fn test_linked_list() {
        let mut l1 = ListNode::with(1);
        let temp = ListNode::from_vec(vec![2, 3, 4, 5]);
        l1.next = Some(temp);
        assert_eq!(l1, ListNode::from_vec(vec![1, 2, 3, 4, 5]));

        let mut l2 = ListNode::from_vec(vec![2, 3, 4, 5]);
        l2.push(1);
        assert_eq!(l2, ListNode::from_vec(vec![1, 2, 3, 4, 5]));

        let mut l4 = ListNode::from_vec(vec![1, 2, 3, 4]);
        l4.push_back(5);
        assert_eq!(l4, ListNode::from_vec(vec![1, 2, 3, 4, 5]));

        let mut l5 = ListNode::from_vec(vec![1, 2, 2, 3, 4, 5]);
        match l5.delete(2) {
            Ok(_) => (),
            Err(e) => panic!("{}", e),
        }
        assert_eq!(l5, ListNode::from_vec(vec![1, 2, 3, 4, 5]));

        let mut l6 = ListNode::from_vec(vec![3, 3, 3, 1, 2, 3, 4, 5]);
        let l6 = match l6.find(1) {
            Ok(res) => res,
            Err(e) => panic!("{e}"),
        }.to_owned();
        assert_eq!(l6, *ListNode::from_vec(vec![1, 2, 3, 4, 5]));

        let mut l7 = ListNode::from_vec(vec![1, 2, 3, 4, 5]);
        assert_eq!(l7.len(), 5);

        let mut l8 = ListNode::from_vec(vec![5, 4, 3, 2, 1]);
        l8.reverse();
        assert_eq!(l8, ListNode::from_vec(vec![1, 2, 3, 4, 5]));

        let temp = ListNode::from_vec(vec![1, 2, 3, 4, 5]);
        let l9 = temp.copy();
        assert_eq!(temp, l9);

        let l10 = ListNode::from_vec(vec![1, 2, 3, 4, 5]);
        let element = l10[1];
        let element2 = l10[2];
        assert_eq!(element, 2);
        assert_eq!(element2, 3);

        let mut l11 = ListNode::from_vec(vec![1, 3, 4, 5]);
        let _ = match l11.insert(1, 2) {
            Ok(_) => (),
            Err(e) => panic!("{e}"),
        };
        assert_eq!(l11, ListNode::from_vec(vec![1, 2, 3, 4, 5]));

        let mut l12 = ListNode::from_vec(vec![1, 1, 2, 3, 4, 5]);
        let _popped = l12.pop().unwrap();
        assert_eq!(l12, ListNode::from_vec(vec![1, 2, 3, 4, 5]));

        let l13 = ListNode::from_vec(vec![1, 2, 3, 4, 5]);
        let found = l13.contains(3);
        assert_eq!(found, true);
        let notfound = l13.contains(0);
        assert_eq!(notfound, false);

        let t1 = ListNode::from_vec(vec![1, 3, 5]);
        let t2 = ListNode::from_vec(vec![2, 4]);
        let l16 = ListNode::<i32>::merge(Some(t1), Some(t2)).unwrap();
        assert_eq!(l16, ListNode::from_vec(vec![1, 2, 3, 4, 5]));

        let l18 = ListNode::from_vec(vec![1, 5, 3, 2, 4]);
        let l18 = ListNode::<i32>::sort(Some(l18)).unwrap();
        assert_eq!(l18, ListNode::from_vec(vec![1, 2, 3, 4, 5]));
    }

    #[test]
    fn test_stack() {
        let mut s1 = Stack::from_vec(vec![1, 1, 2, 3, 4, 5]);
        s1.pop();
        assert_eq!(s1.list, Stack::from_vec(vec![1, 2, 3, 4, 5]).list);

        let mut s2 = Stack::from_vec(vec![2, 3, 4, 5]);
        s2.push(1);
        assert_eq!(s2.list, Stack::from_vec(vec![1, 2, 3, 4, 5]).list);

        let s3 = Stack::from_vec(vec![1, 2, 3, 4, 5]);
        let comp = s3.peak();
        assert_eq!(comp, 1);
    }
}