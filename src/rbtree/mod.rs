mod node;

use std::ops::{Index, IndexMut};

use node::*;

fn identity_ref<T: Clone>(x: &T) -> T {
    x.clone()
}

pub struct RBTree<K, V> {
    root: NodePtr<K, V>,
    size: usize,
}


#[derive(Clone, Copy)]
pub struct TreeElement<K, V> {
    nodeptr: NodePtr<K, V>,
}



impl<K, V> RBTree<K, V> {
    pub fn new() -> Self {
        Self { root: NodePtr::null(), size: 0 }
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// The function `insert_with` inserts into a binary search tree with a priority
    /// function `f: K -> U` which is applied on the key. This is useful in the case of
    /// sweep-line algorithms.
    /// 
    /// Suppose that we have segments `s1` and `s2` where `f` maps segments
    /// to their position on the `x`-intercept (in the case of a horinzontal sweep-line).
    /// Then insertion into the binary search tree will be ordered according to the values
    /// with `f` applied, but the `s1` and `s2` are stored instead.
    pub fn insert_with<U, F>(&mut self, f: F, k: K, v: V) 
        where U: Ord, F: Fn(&K) -> U
    {
    }
}

impl<K: Ord, V> RBTree<K, V> {
    fn insert_aux(&mut self, mut n: NodePtr<K, V>) {

        // we can assume that there is a root.
        let mut y = self.root.clone();
        let mut parent: NodePtr<K, V> = NodePtr::null();
        let mut child: NodePtr<K, V>; // placeholder.

        while !y.is_null() {
            parent = y.clone();

            if n == y {
                // change the value of y.
                y.set_value(n.value());
                self.size += 1;
                return; // do nothing else.
            } else if n > y {

                // insert n to y's right.
                child = y.right().clone();
                y = child;
                
            } else {

                // insert n to y's left.
                child = y.left().clone();
                y = child;

            }

        }

        if n > parent {
            parent.set_right(&n);
        } else {
            parent.set_left(&n);
        }

        n.set_parent(&parent);
        self.size += 1;

    }
    
    /// Insert a new element into the tree.
    pub fn insert(&mut self, k: K, v: V) {
        let n = NodePtr::new(k, v);

        if self.is_empty() {
            self.root = n;
            self.size += 1;
        } else {
            self.insert_aux(n);
        }
    }

    /// Give some key, find the node with that key in the tree.
    pub fn find(&self, k: K) -> Option<TreeElement<K, V>> {
        if self.is_empty() {
            return None;
        } 

        let mut parent = self.root.clone();

        while !parent.is_null() {

            if parent.key() == k {
                let elem = TreeElement::new(&parent);
                return Some(elem);
            } else if parent.key() > k {
                parent = parent.left();
            } else {
                parent = parent.right();
            }
        }

        return None;
    }
}

impl<K, V> TreeElement<K, V> {
    fn new(n: &NodePtr<K, V>) -> TreeElement<K, V>{
        Self {
            nodeptr: n.clone()
        }
    }

    pub fn key(&self) -> K {
        self.nodeptr.key()
    }

    pub fn value(&self) -> V {
        self.nodeptr.value()
    }

    pub fn successor(&self) -> Option<TreeElement<K, V>> {
        let succ = self.nodeptr.successor();

        if succ.is_null() {
            None
        } else {
            Some(TreeElement::new(&succ))
        }
    }

    pub fn predecessor(&self) -> Option<TreeElement<K, V>> {
        let succ = self.nodeptr.predecessor();

        if succ.is_null() {
            None
        } else {
            Some(TreeElement::new(&succ))
        }
    }
}

// impl<K: Ord, V> Index<K> for RBTree<K, V>{
//     type Output = TreeElement<K, V>;

//     fn index(&self, index: K) -> &Self::Output {
//         Output
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inserting_to_empty_tree() {

        let mut tree = RBTree::new();

        tree.insert(4, 1);

        assert_eq!(tree.size, 1);
        assert_eq!(tree.root.key(), 4);

    }

    #[test]
    fn inserting_to_singleton_tree() {
        let mut tree = RBTree::new();

        tree.insert(10, 10);

        tree.insert(11, 40);

        let root = tree.root;

        assert_eq!(root.right().key(), 11);
        assert_eq!(root.right().value(), 40);
    }

    #[test]
    fn inserting_multiple_keys() {
        let mut tree = RBTree::new();
        tree.insert(14, 10);
        tree.insert(10, 14);
        tree.insert(12, 4);

        let root = tree.root;
        let leaf = root.left().right();

        assert_eq!(leaf.key(), 12);
        assert_eq!(leaf.value(), 4);
    }

    #[test]
    fn tree_find_something() {
        let mut tree = RBTree::new();
        tree.insert(14, 10);
        tree.insert(10, 14);
        tree.insert(12, 4);

        let x = tree.find(12).unwrap();

        assert_eq!(x.key(), 12);
        assert_eq!(x.value(), 4);
    }

    #[test]
    fn tree_find_nothing() {
        let mut tree = RBTree::new();
        tree.insert(14, 10);
        tree.insert(10, 14);
        tree.insert(12, 4);

        let x = tree.find(15);

        assert!(x.is_none());
    }
}