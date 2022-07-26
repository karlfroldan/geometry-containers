//BSD 3-Clause License

// Copyright (c) 2022, Karl Roldan
// All rights reserved.

// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:

// 1. Redistributions of source code must retain the above copyright notice, this
//    list of conditions and the following disclaimer.

// 2. Redistributions in binary form must reproduce the above copyright notice,
//    this list of conditions and the following disclaimer in the documentation
//    and/or other materials provided with the distribution.

// 3. Neither the name of the copyright holder nor the names of its
//    contributors may be used to endorse or promote products derived from
//    this software without specific prior written permission.

// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
// FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
// DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
// SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
// CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
// OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

// RED-BLACK TREE DELETE AND DELETE-FIXUP CODE IS LICENSED BY
// Copyright 2017-2018 By tickdream125@hotmail.com.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// A Red-Black Tree structure that allows dynamic keys. That is, the key stored in the 
/// tree is not the one being used for comparisons. Instead, there is another comparison 
/// function `f: (Key, Key, D) -> Ordering` where `D` is the type of the comparison modifier.
/// An example of this is a comparison function of line segments where the *priority* is the
/// `x`-intercept. In this way `D` is the set of `y`-intercepts.
/// 
/// This red-black tree implementation is driven by the needs of sweep-line algorithms but can be used
/// for other things if needed.

mod node;
use std::cmp::Ordering;
use std::fmt::Debug;
use node::*;

pub struct RBTree<K, V> {
    root: NodePtr<K, V>,
    size: usize,
}

impl<K, V> Default for RBTree<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Drop for RBTree<K, V> {
    fn drop(&mut self) {
        let mut root = self.root.clone();
        self.drop_recursive(&mut root);
    }
}

impl<K, V> RBTree<K, V> {
    pub fn new() -> Self {
        Self {
            root: NodePtr::null(),
            size: 0,
        }
    }

    fn drop_recursive(&mut self, n: &mut NodePtr<K, V>) {
        if !n.is_null() {
            self.drop_recursive(&mut n.left());
            self.drop_recursive(&mut n.right());
            n.dealloc();
        }
    }

    // Check if the given node is the root of the tree.
    fn is_root(&self, n: &NodePtr<K, V>) -> bool {
        self.root.ptr_eq(n)
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Left rotate assumes the existence of a right child.
    /// This function rotates the node and turns the right child
    /// into its parent node.
    fn left_rotate(&mut self, x: &mut NodePtr<K, V>) {
        /*
         *   self          b
         *   / \          / \
         *  1   b    => self 3
         *     / \      / \
         *    2   3    1   2
         */
        let mut y = x.right();

        // set y's left subtree into x's right subtree
        x.set_right(&y.left());

        if !y.left().is_null() {
            y.left().set_parent(x);
        }

        // Link x's parent to y.
        y.set_parent(&x.parent());

        if x.parent().is_null() {
            self.root = y.clone();
        } else if x.ptr_eq(&x.parent().left()) {
            x.parent().set_left(&y);
        } else {
            x.parent().set_right(&y);
        }

        y.set_left(x);
        x.set_parent(&y);
    }

    /// Right rotate assumes the existence of a left child.
    /// This function rotates the node and turns the left child
    /// into its parent node.
    fn right_rotate(&mut self, x: &mut NodePtr<K, V>) {
        /*
         *   self        b
         *    / \       / \
         *   b   3  => 1  self
         *  / \           / \
         * 1   2         2   3
         */
        let mut y = x.left();

        // set y's right subtree into x's left subtree
        x.set_left(&y.right());

        if !y.right().is_null() {
            y.right().set_parent(x);
        }

        // Link x's parent to y.
        y.set_parent(&x.parent());

        if x.parent().is_null() {
            self.root = y.clone();
        } else if x.ptr_eq(&x.parent().left()) {
            x.parent().set_left(&y);
        } else {
            x.parent().set_right(&y);
        }

        y.set_right(x);
        x.set_parent(&y);
    }

    /// Find the element of a tree given a comparison function, a modifier, and the key.
    pub fn find_with<D, F>(&self, cmp_op: F, x: &D, k: K) -> Option<TreeElement<K, V>>
    where
        F: Fn(&K, &K, &D) -> Ordering,
    {
        if self.is_empty() {
            return None;
        }

        let mut parent = self.root.clone();

        while !parent.is_null() {
            let p_k = parent.key();

            match cmp_op(&p_k, &k, x) {
                Ordering::Less => parent = parent.left(),
                Ordering::Equal => {
                    let elem = TreeElement::new(&parent);
                    return Some(elem);
                }
                Ordering::Greater => parent = parent.right(),
            }
        }

        None
    }

    /// The function `insert_with` inserts into a binary search tree with a priority
    /// function `f: (K, D) -> U` where `K` is the type of the key, `D` is another type
    /// which makes `f` the dynamic insertion function, and `U` is their output. In this way,
    /// `U`'s behavior on `K` depends on whatever value is passed to `D`.
    pub fn insert_with<D, F>(&mut self, cmp_op: F, x: &D, k: K, v: V)
    where
        F: Fn(&K, &K, &D) -> Ordering,
    {
        let n = NodePtr::new(k, v);

        if self.is_empty() {
            self.root = n;
            self.size += 1;
        } else {
            self.insert_with_aux(cmp_op, x, n);
        }

        self.root.set_color(Color::Black);
    }

    fn insert_with_aux<D, F>(&mut self, cmp_op: F, x: &D, mut n: NodePtr<K, V>)
    where
        F: Fn(&K, &K, &D) -> Ordering,
    {
        // we can assume that there is a root.
        let mut y = self.root.clone();
        let mut parent: NodePtr<K, V> = NodePtr::null();

        let n_k = n.key();

        while !y.is_null() {
            parent = y.clone();

            let y_k = y.key();

            match cmp_op(&n_k, &y_k, x) {
                // insert to y's left.
                Ordering::Less => y = y.left(),
                Ordering::Equal => {
                    // actually do nothing but changes the y value.
                    y.set_value(n.value());
                    self.size += 1;
                    return; // do nothing else.
                }
                Ordering::Greater => y = y.right(),
            }
        }

        let p_k = parent.key();

        match cmp_op(&n_k, &p_k, x) {
            Ordering::Greater => parent.set_right(&n),
            _ => parent.set_left(&n),
        }

        n.set_parent(&parent);
        self.size += 1;

        self.insert_fixup(&mut n);
    }

    fn insert_fixup(&mut self, n: &mut NodePtr<K, V>) {
        let mut z = n.clone();
        let mut grandparent;

        while z.parent().color() == Color::Red {
            grandparent = z.parent().parent();

            // If z's parent is the left child.
            if z.parent().ptr_eq(&grandparent.left()) {
                let mut y = grandparent.right(); // the uncle.

                if y.color() == Color::Red {
                    // CASE 1
                    z.parent().set_color(Color::Black);
                    y.set_color(Color::Black);
                    grandparent.set_color(Color::Red);
                    z = grandparent;
                } else {
                    if z.ptr_eq(&z.parent().right()) {
                        // CASE 2
                        z = z.parent();
                        self.left_rotate(&mut z);
                    }

                    // CASE 3
                    z.parent().set_color(Color::Black);
                    grandparent.set_color(Color::Red);
                    self.right_rotate(&mut grandparent);
                }
            } else {
                // if z's parent is the right child.
                let mut y = grandparent.left(); // the uncle.

                if y.color() == Color::Red {
                    // CASE 1
                    z.parent().set_color(Color::Black);
                    y.set_color(Color::Black);
                    grandparent.set_color(Color::Red);
                    z = grandparent;
                } else {
                    if z.ptr_eq(&z.parent().left()) {
                        // CASE 2
                        z = z.parent();
                        self.right_rotate(&mut z);
                    }

                    // CASE 3
                    z.parent().set_color(Color::Black);
                    grandparent.set_color(Color::Red);
                    self.left_rotate(&mut grandparent);
                }
            }
        }

        self.root.set_color(Color::Black)
    }

    // Some functions to test red-black tree properties.

    #[allow(dead_code)]
    fn black_root_property(&self) -> bool {
        self.root.color() == Color::Black
    }

    // Every red node should have black children.
    #[allow(dead_code)]
    fn red_node_property(&self) -> bool {
        self.root.red_node_has_black_children()
    }

    /// Delete the node given a node pointer and return the key and value.
    pub fn delete(&mut self, n: TreeElement<K, V>) -> (K, V) {
        // Modified implementation from `tickbh/rbtree-rs`
        // This piece of code is licensed under MIT as stated in 
        // the file header.
        let node = n.nodeptr;
        let mut child: NodePtr<K, V>;
        let mut parent: NodePtr<K, V>;
        let color: Color;

        // If the node has two children.
        if node.has_left() && node.has_right() {
            // replace the current node with its successor.
            let mut succ = node.successor();

            if self.is_root(&node) {
                self.root = succ;
            } else {
                // If the node is the left child.
                if node.parent().left().ptr_eq(&node) {
                    node.parent().set_left(&succ);
                } else {
                    node.parent().set_right(&succ);
                }
            }

            // In this case, the `child` is the `right` of `succ`
            child = succ.right();
            parent = succ.parent();
            color = succ.color();

            if parent.ptr_eq(&node) {
                parent = succ;
            } else {
                if !child.is_null() {
                    child.set_parent(&parent);
                }

                parent.set_left(&child);
                succ.set_right(&node.right());
                node.right().set_parent(&succ);
            }

            succ.set_parent(&node.parent());
            succ.set_color(node.color());
            succ.set_left(&node.left());
            node.left().set_parent(&succ);

            if color == Color::Black {
                self.delete_fixup(child,  parent);
            }

            self.size -= 1;
            let closure = move || NodePtr::move_out(node);
            return closure();
        } 
        
        if node.has_left() {
            child = node.left();
        } else {
            child = node.right();
        }

        parent = node.parent();
        color = node.color();

        if !child.is_null() {
            child.set_parent(&parent);
        }

        if self.root.ptr_eq(&node) {
            self.root = child;
        } else {
            if parent.left().ptr_eq(&node) {
                parent.set_left(&child);
            } else {
                parent.set_right(&child);
            }
        }

        if color == Color::Black {
            self.delete_fixup(child, parent);
        }


        self.size -= 1;
        
        let closure = move || NodePtr::move_out(node);
        closure()
    }

    /// Deletes a node from the tree and returns the key-value pair.
    pub fn remove_with<F, D>(&mut self, cmp_op: F, x: &D, k: K) -> Option<(K, V)>
    where 
        F: Fn(&K, &K, &D) -> Ordering,
    {
        let elem = self.find_with(cmp_op, x, k);

        match elem {
            None    => None,
            Some(n) => Some(self.delete(n)),
        }
    }

    fn delete_fixup(&mut self, mut z: NodePtr<K, V>, mut p: NodePtr<K, V>) {
        let mut x: NodePtr<K, V>;


        while !self.is_root(&z) && z.color() == Color::Black {
            if p.left().ptr_eq(&z) {
                x = p.right();
                // CASE 1: z's sibling x is red.
                if x.color() == Color::Red {
                    x.set_color(Color::Black);
                    p.set_color(Color::Red);
                    self.left_rotate(&mut p);
                    x = p.right();
                }

                // z's sibling x is black and both of x's children are black.
                if x.left().color() == Color::Black && x.right().color() == Color::Black {
                    x.set_color(Color::Red);
                    z = p;
                    p = z.parent();
                } else {
                    // If z's sibling x is black and the left child of 
                    // z is red and the right child is black.
                    if x.right().color() == Color::Black {
                        x.left().set_color(Color::Black);
                        x.set_color(Color::Red);
                        self.right_rotate(&mut x);
                        x = p.right();
                    }

                    // z's brother x is black, z's right child is red and its left child is any color.
                    x.set_color(p.color());
                    p.set_color(Color::Black);
                    x.right().set_color(Color::Black);
                    self.left_rotate(&mut p);
                    z = self.root;
                    break;
                }
            } else {

                x = p.left();
                // CASE 1: z's sibling x is red.
                if x.color() == Color::Red {
                    x.set_color(Color::Black);
                    p.set_color(Color::Red);
                    self.right_rotate(&mut p);
                    x = p.left();
                }

                // z's sibling x is black and both of x's children are black.
                if x.left().color() == Color::Black && x.right().color() == Color::Black {
                    x.set_color(Color::Red);
                    z = p;
                    p = z.parent();
                } else {
                    // If z's sibling x is black and the left child of 
                    // z is red and the right child is black.
                    if x.left().color() == Color::Black {
                        x.right().set_color(Color::Black);
                        x.set_color(Color::Red);
                        self.left_rotate(&mut x);
                        x = p.left();
                    }

                    // z's brother x is black, z's right child is red and its left child is any color.
                    x.set_color(p.color());
                    p.set_color(Color::Black);
                    x.left().set_color(Color::Black);
                    self.right_rotate(&mut p);
                    z = self.root;
                    break;
                }

            }
        }

        z.set_color(Color::Black);
    }

}

impl<K: Ord, V> RBTree<K, V> {
    fn insert_aux(&mut self, mut n: NodePtr<K, V>) {
        // we can assume that there is a root.
        let mut y = self.root.clone();
        let mut parent: NodePtr<K, V> = NodePtr::null();

        while !y.is_null() {
            parent = y;

            match Ord::cmp(&n, &y) {
                Ordering::Less => y = y.left(),
                Ordering::Greater => y = y.right(),
                Ordering::Equal => {
                    y.set_value(n.value());
                    self.size += 1;
                    return; // do nothing else.
                }
            }
        }

        if n > parent {
            parent.set_right(&n);
        } else {
            parent.set_left(&n);
        }

        n.set_parent(&parent);
        self.size += 1;

        self.insert_fixup(&mut n);
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

    /// Find the element of the tree with the given key.
    pub fn find(&self, k: K) -> Option<TreeElement<K, V>> {
        if self.is_empty() {
            return None;
        }

        let mut parent = self.root.clone();

        while !parent.is_null() {
            match Ord::cmp(&k, &parent.key()) {
                Ordering::Less => parent = parent.left(),
                Ordering::Equal => return Some(TreeElement::new(&parent)),
                Ordering::Greater => parent = parent.right(),
            }
        }

        None
    }

    /// Delete an element from the tree.
    pub fn remove(&mut self, k: K) -> Option<(K, V)> {
        let elem = self.find(k);

        if let Some(e) = elem {
            Some(self.delete(e))
        } else {
            None
        }
    }
}

impl<K: Debug, V: Debug> RBTree<K, V> {
    #[allow(dead_code)]
    fn show_tree(&self) {
        self.root.show_tree();
    }
}

/// A `TreeElement` returns a pointer to a node of the tree
#[derive(Clone, Copy)]
pub struct TreeElement<K, V> {
    nodeptr: NodePtr<K, V>,
}

impl<K, V> TreeElement<K, V> {
    fn new(n: &NodePtr<K, V>) -> Self {
        Self { nodeptr: n.clone() }
    }

    pub fn successor(&self) -> Option<Self> {
        let succ = self.nodeptr.successor();

        if succ.is_null() {
            None
        } else {
            Some(TreeElement::new(&succ))
        }
    }

    pub fn predecessor(&self) -> Option<Self> {
        let succ = self.nodeptr.predecessor();

        if succ.is_null() {
            None
        } else {
            Some(TreeElement::new(&succ))
        }
    }

    /// Swaps the elements of the red-black tree.
    pub fn swap(&mut self, other: &mut Self) {
        let mut p0 = self.nodeptr.clone();
        let mut p1 = other.nodeptr.clone();

        p0.swap(&mut p1);
    }
}

impl<K: Clone, V: Clone> TreeElement<K, V> {
    pub fn key(&self) -> K {
        self.nodeptr.key().clone()
    }

    pub fn value(&self) -> V {
        self.nodeptr.value().clone()
    }
}

// impl <K: Clone, V: Clone>

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inserting_to_empty_tree() {
        let mut tree = RBTree::new();

        tree.insert(4, 1);

        assert_eq!(tree.size, 1);
        assert_eq!(tree.root.key(), 4);

        assert_eq!(tree.root.color(), Color::Black);
    }

    #[test]
    fn inserting_to_singleton_tree() {
        let mut tree = RBTree::new();

        tree.insert(10, 10);

        tree.insert(11, 40);

        let root = tree.root;

        assert_eq!(root.right().key(), 11);
        assert_eq!(root.right().value(), 40);

        assert_eq!(tree.root.color(), Color::Black);
        assert_eq!(tree.root.right().color(), Color::Red);
    }

    #[test]
    fn inserting_multiple_keys() {
        let mut tree = RBTree::new();
        tree.insert(14, 10);
        tree.insert(10, 14);
        tree.insert(12, 4);
        tree.insert(19, 4);
        tree.insert(21, 4);
        tree.insert(20, 14);
        tree.insert(22, 14);
        tree.insert(31, 14);
        tree.insert(35, 100);
        tree.insert(-100, 5);

        tree.root.show_tree();

        // This node is red.
        let node_35 = tree.find(35).unwrap();

        assert_eq!(tree.root.color(), Color::Black);
        assert_eq!(tree.root.left().color(), Color::Red);
        assert_eq!(tree.root.right().color(), Color::Red);
        assert_eq!(tree.root.key(), 19);
        assert_eq!(node_35.nodeptr.color(), Color::Red);
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
    fn remove_singleton() {
        let mut tree = RBTree::new();

        tree.insert(14, 10);
        tree.remove(14);
        assert!(tree.is_empty());
        assert!(tree.root.is_null());
    }

    #[test]
    fn delete_singleton() {
        let mut tree = RBTree::new();

        tree.insert(14, 10);

        let n = tree.find(14).unwrap();
        tree.delete(n);
        assert!(tree.is_empty());
        assert!(tree.root.is_null());
    }

    #[test]
    fn delete_leaf() {
        let mut tree = RBTree::new();

        tree.insert(14, 10);
        tree.insert(15, 12);

        let n = tree.find(15).unwrap();
        tree.delete(n);

        tree.show_tree();

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

        /*
            Tree:
                10
               /  \
              0    13
               \ 
                3
        */

        let _ = tree.remove(0);

        let r = tree.root;

        assert_eq!(r.key(), 10);
        assert_eq!(r.left().key(), 3);
        assert_eq!(r.right().key(), 13);
    }

    #[test]
    fn delete_two_children() {
        let mut tree = RBTree::new();

        tree.insert(0, 4);
        tree.insert(-1, 2);
        tree.insert(1, 4);

        let _ = tree.remove(0);

        assert_eq!(tree.root.key(), 1);
        assert_eq!(tree.root.left().color(), Color::Red);
    }

    #[test]
    fn swap_tree_elements() {
        let mut tree = RBTree::new();

        tree.insert(0, 4);
        tree.insert(1, 0);

        let mut root = tree.find(0).unwrap();
        let mut succ = root.successor().unwrap();

        root.swap(&mut succ);

        assert_eq!(tree.root.key(), 1);
        assert_eq!(tree.root.value(), 0);
        assert_eq!(tree.root.right().key(), 0);
        assert_eq!(tree.root.right().value(), 4);
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

    fn x_int(s: &Segment, y: &f64) -> f64 {
        let m = slope(s);
        let b = bias(s);

        // y = mx + b => (y - b) / m = x
        (y - b) / m
    }

    fn cmp_by_x_int(s0: &Segment, s1: &Segment, y: &f64) -> Ordering {
        let x0 = x_int(s0, y);
        let x1 = x_int(s1, y);

        x0.partial_cmp(&x1).unwrap()
    }

    // Some tests for a dynamic red black tree.
    #[test]
    fn insert_dynamic_empty_tree() {
        let mut tree1 = RBTree::new();

        let s0: Segment = ((0.0, 0.0), (1.0, 2.0));
        let s1: Segment = ((0.0, 1.0), (2.0, -1.0));

        tree1.insert_with(cmp_by_x_int, &0.9, s0.clone(), 4);
        tree1.insert_with(cmp_by_x_int, &0.9, s1.clone(), 3);

        // Right now, s1 should be on s0's left.
        assert_eq!(tree1.root.value(), 4);
        assert_eq!(tree1.root.left().value(), 3);

        let mut tree2 = RBTree::new();

        tree2.insert_with(cmp_by_x_int, &0.1, s0.clone(), 4);
        tree2.insert_with(cmp_by_x_int, &0.1, s1.clone(), 3);

        // Right now, s1 should be on s0's right.
        assert_eq!(tree2.root.value(), 4);
        assert_eq!(tree2.root.right().value(), 3);
    }
}
