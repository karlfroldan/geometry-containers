use std::borrow::Borrow;
use std::boxed::Box;
use std::fmt::Debug;
use std::ptr;

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Color {
    Black,
    Red,
}

#[derive(PartialEq, Eq, Clone)]
pub struct Node<K, V> {
    pub key: K,
    pub value: V,

    // Pointers to other nodes.
    parent: NodePtr<K, V>,
    left: NodePtr<K, V>,
    right: NodePtr<K, V>,

    color: Color,
}

#[derive(Debug, Copy)]
pub struct NodePtr<K, V>(*mut Node<K, V>);

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

    pub fn color(&self) -> Color {
        if self.0.is_null() {
            Color::Black
        } else {
            unsafe { self.0.read() }.color
        }
    }

    pub fn drop_in_place(&self) {
        unsafe { self.0.drop_in_place() };
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

    pub fn set_color(&mut self, color: Color) {
        // We can only change the color of non-leaf nodes.
        if !self.is_null() {
            unsafe { (*self.0).color = color };
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

    /// Swap the keys and values of two nodes.
    pub fn swap(&mut self, other: &mut Self) {
        let k1 = self.key();
        let v1 = self.value();

        let k2 = other.key();
        let v2 = other.value();

        unsafe { (*self.0).key = k2 };
        unsafe { (*self.0).value = v2 };

        unsafe { (*other.0).key = k1 };
        unsafe { (*other.0).value = v1 };
    }

    pub fn successor(&self) -> Self {
        // if there is a right subtree
        if !self.right().is_null() {
            self.right().minimum()
        } else {
            let mut parent = self.parent();
            let mut x = self;
            let mut x_parent;

            while parent.right().0 == x.0 && !parent.is_null() {
                parent = parent.parent().clone();
                x_parent = x.parent();
                x = x_parent.borrow();
            }

            parent
        }
    }

    pub fn has_left(&self) -> bool {
        !self.left().is_null()
    }

    pub fn has_right(&self) -> bool {
        !self.right().is_null()
    }

    pub fn has_parent(&self) -> bool {
        !self.parent().is_null()
    }

    pub fn predecessor(&self) -> Self {
        // if there is a right subtree
        if !self.left().is_null() {
            self.left().minimum()
        } else {
            let mut parent = self.parent();
            let mut x = self;
            let mut x_parent;

            while parent.left().0 == x.0 && !parent.is_null() {
                parent = parent.parent().clone();
                x_parent = x.parent();
                x = x_parent.borrow();
            }

            parent
        }
    }

    pub fn set_parent_null(&mut self) {
        unsafe { (*self.0).parent = NodePtr::null() };
    }

    pub fn set_left_null(&mut self) {
        unsafe { (*self.0).left = NodePtr::null() };
    }

    pub fn set_right_null(&mut self) {
        unsafe { (*self.0).right = NodePtr::null() };
    }

    pub fn set_value(&mut self, v: V) {
        unsafe { (*self.0).value = v };
    }

    /// Check if two node pointers are pointing to the same node.
    pub fn is_node_same(&self, other: &Self) -> bool {
        ptr::eq(self.0, other.0)
    }

    // /// Right rotate assumes the existence of a left child.
    // /// This function rotates the node and turns the left child
    // /// into its parent node.
    // pub fn right_rotate(&mut self) {
    //     /*
    //      *   self        b
    //      *    / \       / \
    //      *   b   3  => 1  self
    //      *  / \           / \
    //      * 1   2         2   3
    //      */

    //     let mut b = self.left();
    //     let mut node_2 = b.right();

    //     let mut parent = self.parent();

    //     // set b to be the parent of self.
    //     self.set_parent(&b);
    //     b.set_right(&self);

    //     // set node_2 to self.
    //     self.set_left(&node_2);
    //     if !node_2.is_null() {
    //         node_2.set_parent(&self);
    //     }

    //     // and set self's parent to b
    //     b.set_parent(&parent);

    //     if !parent.is_null() {
    //         if parent.left().is_node_same(&self) {
    //             parent.set_left(&b);
    //         } else {
    //             parent.set_right(&b);
    //         }
    //     }
    // }

    pub fn red_node_has_black_children(&self) -> bool {
        if self.is_null() {
            true // since NULL is black.
        } else {
            let left = self.left();
            let right = self.right();

            let predicate_value = match self.color() {
                Color::Black => true,
                Color::Red   => left.color() == Color::Black && right.color() == Color::Black,
            };

            left.red_node_has_black_children() && right.red_node_has_black_children() && predicate_value
        }
    }

    fn count_path(&self) -> (usize, bool) {
        if self.is_null() {
            (1, true)
        } else {
            let c = if self.color() == Color::Black {
                1usize
            } else {
                0usize
            };

            let (left, left_b) = self.left().count_path();
            let (right, right_b) = self.right().count_path();

            if !(left_b && right_b) && (left != right) {
                return (0, false);
            }

            (c + left, true)
        }
    }
}

impl<K: PartialEq, V> PartialEq for NodePtr<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}

impl<K: Eq, V> Eq for NodePtr<K, V> {}

impl<K: PartialOrd, V> PartialOrd for NodePtr<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.key().partial_cmp(&other.key())
    }
}

impl<K: Ord, V> Ord for NodePtr<K, V> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key().cmp(&other.key())
    }
}

impl<K, V> Node<K, V> {
    pub fn new(k: K, v: V) -> Self {
        Self {
            key: k,
            value: v,
            parent: NodePtr::null(),
            left: NodePtr::null(),
            right: NodePtr::null(),
            color: Color::Red,
        }
    }
}

impl<K: Debug, V: Debug> NodePtr<K, V> {
    #[allow(dead_code)]
    pub fn show_tree(&self) {
        self.show_tree_aux(0);
    }

    #[allow(dead_code)]
    fn show_tree_aux(&self, depth: usize) {
        let spaces = String::from_utf8(vec![b' '; depth * 2]).unwrap();
        if !self.is_null() {
            let k = self.key();
            let v = self.value();

            let c = self.color();

            println!("{spaces}- {:?} => {:?} | {:?}", k, v, c);

            self.left().show_tree_aux(depth + 1);
            self.right().show_tree_aux(depth + 1);

        } else {
            println!("{spaces}- NULL | BLACK");
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
