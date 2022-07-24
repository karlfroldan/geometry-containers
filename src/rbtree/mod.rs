mod node;

use node::*;

fn identity_ref<T: Clone>(x: &T) -> T {
    x.clone()
}

pub struct RBTree<K, V> {
    root: NodePtr<K, V>,
    size: usize,
}

impl<K, V> RBTree<K, V> {
    pub fn new() -> Self {
        Self { root: NodePtr::null(), size: 0 }
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

impl<K: Ord + Clone, V> RBTree<K, V> {
    pub fn insert(&mut self, k: K, v: V) {
        self.insert_with(identity_ref, k, v);
    }
}