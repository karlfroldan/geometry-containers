use std::borrow::Borrow;
use std::fmt::Debug;
use std::{ptr, boxed};
use std::boxed::Box;

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
enum Color {Black, Red}

#[derive(PartialEq, Eq, Clone)]
pub struct Node<K, V> {
    pub key:   K,
    pub value: V,

    // Pointers to other nodes.
    parent: NodePtr<K, V>,
    left:   NodePtr<K, V>,
    right:  NodePtr<K, V>,

    color: Color,
}

#[derive(PartialEq, Eq, Debug, Copy)]
pub struct NodePtr<K, V> (*mut Node<K, V>);

impl<K, V> Clone for NodePtr<K, V> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<K, V> NodePtr<K, V> {

    /// Create a new node allocated on the heap from the key and the value.
    pub fn new(key: K, value: V) -> Self {
        let n = Node::new(key, value);
        Self::from_node(n)
    }

    /// Create a new empty node pointer.
    pub fn null() -> Self {
        NodePtr(ptr::null_mut())
    }

    /// Create a new node pointer from a node and allocate to the heap.
    pub fn from_node(n: Node<K, V>) -> Self {
        // First, create a boxed version of the node.
        let boxed_node = Box::new(n);
        
        NodePtr(Box::into_raw(boxed_node))
    }

    /// Get the associated key from the node that the pointer is pointing to.
    pub fn key(&self) -> K {
        unsafe { self.0.read() }.key
    }

    /// Get the associated value from the node that the pointer is pointing to.
    pub fn value(&self) -> V {
        unsafe { self.0.read() }.value
    }

    fn color(&self) -> Color {
        if self.0.is_null() {
            Color::Black
        } else {
            unsafe { self.0.read() }.color
        }
    }

    pub fn is_null(&self) -> bool {
        self.0.is_null()
    }

    /// Return a new pointer to the left child of the node.
    pub fn left(&self) -> Self {
        if self.is_null() {
            Self::null()
        } else {
            unsafe { (*self.0).left.clone() }
        }
    }

    /// Return a new pointer to the parent pointer of the node.
    pub fn parent(&self) -> Self {
        if self.is_null() {
            Self::null()
        } else {
            unsafe { (*self.0).parent.clone() }
        }
    }

    /// Return a new pointer to the right child of the node.
    pub fn right(&self) -> Self {
        if self.is_null() {
            Self::null()
        } else {
            unsafe { (*self.0).right.clone() }
        }
    }

    /// Set the right child of the current node pointer.
    pub fn set_right(&mut self, other: &Self) {
        if !self.is_null() {
            unsafe { (*self.0).right = other.clone() }
        }
    }

    /// Set the parent of the current node pointer.
    pub fn set_parent(&mut self, other: &Self) {
        if !self.is_null() {
            unsafe { (*self.0).parent = other.clone() }
        }
    }

    /// Set the left child of the current node pointer.
    pub fn set_left(&mut self, other: &Self) {
        if !self.is_null() {
            unsafe { (*self.0).left = other.clone() }
        }
    }

    /// Get the minimum node reachable from this node.
    pub fn minimum(&self) -> Self {
        let mut y = self;
        let mut left = self.clone();

        while !y.left().clone().is_null() {
            left = y.left().clone();

            y = left.borrow();
        }

        left.clone()
    }

    /// Get the maximum node reachable from this node.
    pub fn maximum(&self) -> Self {
        let mut y = self;
        let mut right = self.clone();

        while !y.right().clone().is_null() {
            right = y.right().clone();

            y = right.borrow();
        }

        right.clone()
    }

    pub fn successor(&self) -> Self {
        // if there is a right subtree
        if !self.right().is_null() {
            self.right().minimum()
        } else {
            let mut parent = self.parent();
            let mut x = self;
            let mut x_parent;

            while parent.right().0 == x.0 && !parent.is_null()  {
                parent = parent.parent().clone();
                x_parent = x.parent();
                x = x_parent.borrow();
            }

            parent
        }
    }

    pub fn predecessor(&self) -> Self {
        // if there is a right subtree
        if !self.left().is_null() {
            self.left().minimum()
        } else {
            let mut parent = self.parent();
            let mut x = self;
            let mut x_parent;

            while parent.left().0 == x.0 && !parent.is_null()  {
                parent = parent.parent().clone();
                x_parent = x.parent();
                x = x_parent.borrow();
            }

            parent
        }
    }

}

impl<K, V> Node<K, V> {

    pub fn new(k: K, v: V) -> Self {
        Self { key: k, value: v, 
            parent: NodePtr::null(), 
            left: NodePtr::null(), 
            right: NodePtr::null(), 
            color: Color::Red,
        }
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn null_nodeptr_is_black() {
        let n_ptr: NodePtr<i32, i32> = NodePtr::null();
        assert_eq!(n_ptr.color(), Color::Black);
    }

    #[test]
    fn new_node_is_red() {
        let n_node = Node::new(6, 7);

        assert_eq!(n_node.color, Color::Red);
    }

    #[test]
    fn heap_allocated_node_has_correct_values() {
        let n_node = Node::new(6, 7);
        let n_ptr = NodePtr::from_node(n_node);

        assert_eq!(n_ptr.key(), 6);
        assert_eq!(n_ptr.value(), 7);
        assert_eq!(n_ptr.color(), Color::Red);
    }

    #[test]
    fn setting_the_right_child() {
        let mut n = NodePtr::new(10, 0);
        let mut m = NodePtr::new(51, 32);

        n.set_right(&m);
        m.set_parent(&n);

        println!("{:?}", m.is_null());

        let right = n.right();
        let parent = m.parent();

        assert_eq!(right.key(), m.key());
        assert_eq!(right.value(), m.value());
        assert_eq!(parent.key(), n.key());
        assert_eq!(parent.value(), n.value());
    }

    #[test]
    fn setting_the_left_child() {
        let mut n = NodePtr::new(10, 0);
        let mut m = NodePtr::new(51, 32);

        n.set_left(&m);
        m.set_parent(&n);

        println!("{:?}", m.is_null());

        let left = n.left();
        let parent = m.parent();

        assert_eq!(left.key(), m.key());
        assert_eq!(left.value(), m.value());
        assert_eq!(parent.key(), n.key());
        assert_eq!(parent.value(), n.value());
    }

    #[test]
    fn minimum_node() {
        let mut n0 = NodePtr::new(1, 0);
        let mut n1 = NodePtr::new(0, 0);
        let mut n2 = NodePtr::new(5, 4);
        let mut n3 = NodePtr::new(-1, 10);

        n0.set_left(&n1);
        n1.set_parent(&n0);

        n1.set_left(&n3);
        n3.set_parent(&n1);

        n0.set_right(&n2);
        n2.set_parent(&n0);

        let m = n0.minimum();

        assert_eq!(m.key(), -1);
        assert_eq!(m.value(), 10);

        assert_eq!(m.0, n3.0);
    }

    #[test]
    fn maximum_node() {
        let mut n0 = NodePtr::new(1, 0);
        let mut n1 = NodePtr::new(0, 0);
        let mut n2 = NodePtr::new(5, 4);
        let mut n3 = NodePtr::new(-1, 10);

        n0.set_left(&n1);
        n1.set_parent(&n0);

        n1.set_left(&n3);
        n3.set_parent(&n1);

        n0.set_right(&n2);
        n2.set_parent(&n0);

        let m = n0.maximum();

        assert_eq!(m.key(), 5);
        assert_eq!(m.value(), 4);

        assert_eq!(m.0, n2.0);
    }

    #[test]
    fn minimum_singleton_node() {
        let n0 = NodePtr::new(10, 4);

        let m1 = n0.maximum();
        let m2 = n0.minimum();

        assert_eq!(m1.0, n0.0);
        assert_eq!(m2.key(), n0.key());
    }

    #[test]
    fn successor_right_subtree_singleton() {
        let mut n0 = NodePtr::new(10, 100);
        let mut n1 = NodePtr::new(11, 40);

        n0.set_right(&n1);
        n1.set_parent(&n0);

        let succ = n0.successor();

        assert_eq!(succ.key(), n1.key());
    }

    #[test]
    fn successor_right_subtree() {
        let mut n0 = NodePtr::new(10, 100);
        let mut n1 = NodePtr::new(11, 40);
        let mut n2 = NodePtr::new(4, 2);
        let mut n3 = NodePtr::new(100, 4);

        n0.set_right(&n1);
        n1.set_parent(&n0);

        n1.set_left(&n2);
        n2.set_parent(&n1);

        n2.set_left(&n3);
        n3.set_parent(&n2);

        let succ = n0.successor();

        assert_eq!(succ.key(), n3.key());
    }

    #[test]
    fn successor_is_ancestor() {
        let mut n0 = NodePtr::new(10, 100);
        let mut n1 = NodePtr::new(11, 40);
        let mut n2 = NodePtr::new(4, 2);
        let mut n3 = NodePtr::new(100, 4);

        n0.set_left(&n1);
        n1.set_parent(&n0);

        n1.set_right(&n2);
        n2.set_parent(&n1);

        n2.set_right(&n3);
        n3.set_parent(&n2);

        let succ = n3.successor();

        assert_eq!(succ.key(), n0.key());
    }

    #[test]
    fn no_successor() {
        let mut n0 = NodePtr::new(10, 100);
        let mut n1 = NodePtr::new(11, 40);
        let mut n2 = NodePtr::new(4, 2);
        let mut n3 = NodePtr::new(100, 4);

        n0.set_left(&n1);
        n1.set_parent(&n0);

        n1.set_right(&n2);
        n2.set_parent(&n1);

        n2.set_right(&n3);
        n3.set_parent(&n2);

        let succ = n0.successor();

        assert!(succ.is_null());
    }
}