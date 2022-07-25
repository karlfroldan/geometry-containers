mod node;

use node::*;



pub struct RBTree<K, V> {
    root: NodePtr<K, V>,
    size: usize,
}

impl<K, V> RBTree<K, V> {
    pub fn new() -> Self {
        Self { root: NodePtr::null(), size: 0 }
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    pub fn find_with<U, D, F>(&self, f: F, x: &D, k: K) -> Option<TreeElement<K, V>> 
        where U: Ord, F: Fn(&K, &D) -> U
    {
        if self.is_empty() {
            return None;
        } 

        let mut parent = self.root.clone();

        while !parent.is_null() {

            let p_k = parent.key();

            if f(&p_k, x) == f(&k, x) {
                let elem = TreeElement::new(&parent);
                return Some(elem);
            } else if f(&p_k, x) > f(&k, x) {
                parent = parent.left();
            } else {
                parent = parent.right();
            }
        }

        return None;
    }

    /// The function `insert_with` inserts into a binary search tree with a priority
    /// function `f: (K, D) -> U` where `K` is the type of the key, `D` is another type 
    /// which makes `f` the dynamic insertion function, and `U` is their output. In this way,
    /// `U`'s behavior on `K` depends on whatever value is passed to `D`.
    pub fn insert_with<U, D, F>(&mut self, f: F, x: &D, k: K, v: V) 
        where U: Ord, F: Fn(&K, &D) -> U
    {
        let n = NodePtr::new(k, v);

        if self.is_empty() {
            self.root = n;
            self.size += 1;
        } else {
            self.insert_with_aux(f, x, n);
        }
    }

    pub fn insert_with_aux<U, D, F>(&mut self, f: F, x: &D,  mut n: NodePtr<K, V>) 
        where U: Ord, F: Fn(&K, &D) -> U
    {
        // we can assume that there is a root.
        let mut y = self.root.clone();
        let mut parent: NodePtr<K, V> = NodePtr::null();
        let mut child: NodePtr<K, V>; // placeholder.

        let n_k = n.key();

        while !y.is_null() {
            parent = y.clone();

            let y_k = y.key();

            if f(&n_k, x) == f(&y_k, x) {
                // change the value of y.
                y.set_value(n.value());
                self.size += 1;
                return; // do nothing else.
                
            } else if f(&n_k, x) > f(&y_k, x) {

                // insert n to y's right.
                child = y.right();
                y = child;
                
            } else {

                // insert n to y's left.
                child = y.left();
                y = child;

            }

        }

        let p_k = parent.key();

        if f(&n_k, x) > f(&p_k, x) {
            parent.set_right(&n);
        } else {
            parent.set_left(&n);
        }

        n.set_parent(&parent);
        self.size += 1;

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
                child = y.right();
                y = child;
                
            } else {

                // insert n to y's left.
                child = y.left();
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

        // The root must always be black.
        self.root.set_color(Color::Black);
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

    pub fn remove(&mut self, n: TreeElement<K, V>) {

        let mut ptr = n.nodeptr;

        // we have three cases:
        // 1. is leaf. This is easy.
        // 2. has one child.
        // 3. has two children.

        let mut parent = ptr.parent();

        // CASE 1. Ptr is leaf.
        if !ptr.has_left() && !ptr.has_right() {

            if !parent.is_null() {
                if parent.left().is_node_same(&ptr) {
                    parent.set_left_null();
                } else {
                    parent.set_right_null();
                }
            } else {
                self.root = NodePtr::null();
            }

            ptr.drop_in_place();
        // Has two children.
        } else if ptr.has_left() && ptr.has_right() {
            
            let mut succ = ptr.successor();

            // swap the key and value of succ and ptr.
            ptr.swap(&mut succ);

            // then delete `succ`.
            let mut parent_2 = succ.parent();

            if parent_2.is_node_same(&ptr) {
                parent_2.set_right_null();
            } else {
                parent_2.set_left_null();
            }

            ptr.drop_in_place();

        // When there is only one child.
        } else {
            if ptr.has_left() {
                let mut pred = ptr.predecessor();

                ptr.swap(&mut pred);

                // then delete `pred`.
                let mut parent_2 = pred.parent();

                if parent_2.is_node_same(&ptr) {
                    parent_2.set_left_null();
                } else {
                    parent_2.set_right_null();
                }
            } else {
                let mut succ = ptr.successor();

                // swap the key and value of succ and ptr.
                ptr.swap(&mut succ);

                // then delete `succ`.
                let mut parent_2 = succ.parent();

                if parent_2.is_node_same(&ptr) {
                    parent_2.set_right_null();
                } else {
                    parent_2.set_left_null();
                }
            }

            ptr.drop_in_place();
        }

        self.size -= 1;
    }
}

/// A `TreeElement` returns a pointer to a node of the tree
#[derive(Clone, Copy)]
pub struct TreeElement<K, V> {
    nodeptr: NodePtr<K, V>,
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

    #[test]
    fn delete_singleton() {
        let mut tree = RBTree::new();

        tree.insert(14, 10);

        let n = tree.find(14).unwrap();

        println!("size: {}", tree.size);

        tree.remove(n);

        println!("size: {}", tree.size);

        assert!(tree.is_empty());
        assert!(tree.root.is_null());
    }

    #[test]
    fn delete_leaf() {
        let mut tree = RBTree::new();

        tree.insert(14, 10);
        tree.insert(15, 12);

        let n = tree.find(15).unwrap();
        tree.remove(n);


        assert_eq!(tree.root.key(), 14);
        assert_eq!(tree.size, 1);
        assert!(!tree.root.has_right());
    }

    #[test]
    fn delete_singlechild() {
        let mut tree = RBTree::new();

        tree.insert(0, 4);
        tree.insert(13, 4);
        tree.insert(10, 4);
        tree.insert(3, 4);

        let r = tree.root;

        let n_10 = tree.find(10).unwrap();

        tree.remove(n_10);

        let n_13 = tree.find(13).unwrap();

        let n_13_ptr = n_13.nodeptr.clone();

        assert_eq!(n_13_ptr.left().key(), 3);
        
        tree.remove(n_13);
        

        assert_eq!(r.right().key(), 3);
        assert_eq!(tree.size, 2);
    }

    #[test]
    fn delete_two_children() {
        let mut tree = RBTree::new();

        tree.insert(0, 4);
        tree.insert(-1, 2);
        tree.insert(1, 4);
    }

    
    type Point = (f64, f64);
    type Segment = (Point, Point);

    fn slope(s: &Segment) -> f64 {
        let (p1, p2) = s;
        let (x1, y1) = p1;
        let (x2, y2) = p2;

        (y2 - y1) / (x2 - x1)
    }

    fn bias(s: &Segment) -> f64 {
        let ((x, y), _) = s;

        // y = mx + b => y-mx = b
        let m = slope(s);

        y - (m * x)
    }

    fn x_int(s: &Segment, y: f64) -> f64 {
        let m = slope(s);
        let b = bias(s);

        // y = mx + b => (y - b) / m = x
        (y - b) / m
    }

    // Some tests for a dynamic red black tree.
    #[test]
    fn insert_dynamic_empty_tree() {
        let mut tree: RBTree<Segment, i32> = RBTree::new();
        
        
    }
}