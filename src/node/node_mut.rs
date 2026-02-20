use std::cmp::Ordering;
use std::num::Saturating;

use crate::behaviors::RemoveBehavior;
use crate::node::{Node, NodeId, NodeRef, Relatives};
use crate::tree::Tree;

///
/// A mutable reference to a given `Node`'s data and its relatives.
///
#[derive(Debug)]
pub struct NodeMut<'a, T> {
    node_id: NodeId,
    tree: &'a mut Tree<T>,
}

impl<'a, T> NodeMut<'a, T> {
    pub(crate) fn new(node_id: NodeId, tree: &mut Tree<T>) -> NodeMut<'_, T> {
        NodeMut { node_id, tree }
    }

    ///
    /// Returns the `NodeId` that identifies this `Node` in the tree.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let root_id = tree.root_id().expect("root doesn't exist?");
    /// let root = tree.root_mut().expect("root doesn't exist?");
    ///
    /// let root_id_again = root.node_id();
    ///
    /// assert_eq!(root_id_again, root_id);
    /// ```
    ///
    pub fn node_id(&self) -> NodeId {
        self.node_id
    }

    ///
    /// Returns a mutable reference to the data contained by the given `Node`.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let mut root = tree.root_mut().expect("root doesn't exist?");
    ///
    /// let data = root.data();
    ///
    /// assert_eq!(data, &mut 1);
    ///
    /// *data = 3;
    ///
    /// assert_eq!(data, &mut 3);
    /// ```
    ///
    pub fn data(&mut self) -> &mut T {
        if let Some(node) = self.tree.get_node_mut(self.node_id) {
            &mut node.data
        } else {
            unreachable!()
        }
    }

    ///
    /// Returns a `NodeMut` pointing to this `Node`'s parent.  Returns a `Some`-value containing
    /// the `NodeMut` if this `Node` has a parent; otherwise returns a `None`.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let mut root = tree.root_mut().expect("root doesn't exist?");
    ///
    /// assert!(root.parent().is_none());
    /// ```
    ///
    pub fn parent(&mut self) -> Option<NodeMut<'_, T>> {
        self.get_self_as_node()
            .relatives
            .parent
            .map(move |id| NodeMut::new(id, self.tree))
    }

    ///
    /// Returns a `NodeMut` pointing to this `Node`'s previous sibling.  Returns a `Some`-value
    /// containing the `NodeMut` if this `Node` has a previous sibling; otherwise returns a `None`.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let mut root = tree.root_mut().expect("root doesn't exist?");
    ///
    /// assert!(root.prev_sibling().is_none());
    /// ```
    ///
    pub fn prev_sibling(&mut self) -> Option<NodeMut<'_, T>> {
        self.get_self_as_node()
            .relatives
            .prev_sibling
            .map(move |id| NodeMut::new(id, self.tree))
    }

    ///
    /// Returns a `NodeMut` pointing to this `Node`'s next sibling.  Returns a `Some`-value
    /// containing the `NodeMut` if this `Node` has a next sibling; otherwise returns a `None`.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let mut root = tree.root_mut().expect("root doesn't exist?");
    ///
    /// assert!(root.next_sibling().is_none());
    /// ```
    ///
    pub fn next_sibling(&mut self) -> Option<NodeMut<'_, T>> {
        self.get_self_as_node()
            .relatives
            .next_sibling
            .map(move |id| NodeMut::new(id, self.tree))
    }

    ///
    /// Returns a `NodeMut` pointing to this `Node`'s first child.  Returns a `Some`-value
    /// containing the `NodeMut` if this `Node` has a first child; otherwise returns a `None`.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let mut root = tree.root_mut().expect("root doesn't exist?");
    ///
    /// assert!(root.first_child().is_none());
    /// ```
    ///
    pub fn first_child(&mut self) -> Option<NodeMut<'_, T>> {
        self.get_self_as_node()
            .relatives
            .first_child
            .map(move |id| NodeMut::new(id, self.tree))
    }

    ///
    /// Returns a `NodeMut` pointing to this `Node`'s last child.  Returns a `Some`-value
    /// containing the `NodeMut` if this `Node` has a last child; otherwise returns a `None`.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let mut root = tree.root_mut().expect("root doesn't exist?");
    ///
    /// assert!(root.last_child().is_none());
    /// ```
    ///
    pub fn last_child(&mut self) -> Option<NodeMut<'_, T>> {
        self.get_self_as_node()
            .relatives
            .last_child
            .map(move |id| NodeMut::new(id, self.tree))
    }

    ///
    /// Returns `true` if this `Node` is an orphan (i.e., has no parent and is not the root).
    /// Returns `false` if this `Node` has a parent or is the root.
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    /// use nary_tree::behaviors::RemoveBehavior::*;
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let mut root = tree.root_mut().expect("root doesn't exist?");
    /// assert!(!root.is_orphan());
    /// let mut child = root.append(2);
    /// assert!(!child.is_orphan());
    /// let grandchild_id = child.append(3).node_id();
    /// let mut child = root.remove_first(OrphanChildren).unwrap();
    /// let grandchild = tree.get_mut(grandchild_id).unwrap();
    /// assert!(grandchild.is_orphan());
    /// ```
    pub fn is_orphan(&self) -> bool {
        self.get_self_as_node().relatives.parent.is_none()
            && self.tree.root_id() != Some(self.node_id)
    }

    ///
    /// Appends a new `Node` as this `Node`'s last child (and first child if it has none).
    /// Returns a `NodeMut` pointing to the newly added `Node`.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let mut root = tree.root_mut().expect("root doesn't exist?");
    ///
    /// root.append(2);
    ///
    /// assert!(root.first_child().is_some());
    /// assert_eq!(root.first_child().unwrap().data(), &mut 2);
    ///
    /// assert!(root.last_child().is_some());
    /// assert_eq!(root.last_child().unwrap().data(), &mut 2);
    ///
    /// let mut child = root.first_child().unwrap();
    ///
    /// assert!(child.parent().is_some());
    /// assert_eq!(child.parent().unwrap().data(), &mut 1);
    ///
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// tree.set_root(0);
    /// tree
    ///     .root_mut()
    ///     .unwrap()
    ///     .append(2);
    /// assert_eq!(tree.root().unwrap().last_child().unwrap().data(), &2);
    /// let mut s = String::new();
    /// tree.write_formatted(&mut s).unwrap();
    /// assert_eq!(&s, "\
    /// 0
    /// ├── 1
    /// └── 2
    /// ");
    /// ```
    ///
    pub fn append(&mut self, data: T) -> NodeMut<'_, T> {
        let new_id = self.tree.core_tree.insert(data);
        self.append_node_id(new_id)
    }

    ///
    /// Appends an orphaned `Node` as this `Node`'s first child (and last child if it has none).
    /// Returns `Some(NodeMut)` pointing to the newly adopted `Node` if it exists and was orphaned.
    /// Returns `None` if the `Node` was not orphaned or doesn't exist.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// tree.root_mut().expect("root doesn't exist?");
    ///
    /// let two_id = tree.insert_orphaned(2);
    /// let mut root = tree.root_mut().expect("root doesn't exist?");
    /// let two = root.append_orphaned(two_id);
    ///
    /// assert!(two.is_some());
    /// assert!(root.first_child().is_some());
    /// assert_eq!(root.first_child().unwrap().data(), &mut 2);
    ///
    /// assert!(root.last_child().is_some());
    /// assert_eq!(root.last_child().unwrap().data(), &mut 2);
    ///
    /// let mut child = root.first_child().unwrap();
    ///
    /// assert!(child.parent().is_some());
    /// assert_eq!(child.parent().unwrap().data(), &mut 1);
    ///
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// tree.set_root(0);
    /// tree
    ///     .root_mut()
    ///     .unwrap()
    ///     .append(2);
    /// assert_eq!(tree.root().unwrap().last_child().unwrap().data(), &2);
    /// let mut s = String::new();
    /// tree.write_formatted(&mut s).unwrap();
    /// assert_eq!(&s, "\
    /// 0
    /// ├── 1
    /// └── 2
    /// ");
    /// ```
    ///
    pub fn append_orphaned(&mut self, orphan_id: NodeId) -> Option<NodeMut<'_, T>> {
        let orphan = self.tree.get(orphan_id)?;
        if !orphan.is_orphan() {
            return None; // Orphan must not have a parent or be the root
        }
        Some(self.append_node_id(orphan_id))
    }

    fn append_node_id(&mut self, node_id: NodeId) -> NodeMut<'_, T> {
        let relatives = self.tree.get_node_relatives(self.node_id);

        let prev_sibling = relatives.last_child;
        self.tree.set_parent(node_id, Some(self.node_id));
        self.tree.set_prev_sibling(node_id, prev_sibling);

        let first_child = relatives.first_child.or(Some(node_id));
        self.tree.set_first_child(self.node_id, first_child);
        self.tree.set_last_child(self.node_id, Some(node_id));

        if let Some(sibling) = prev_sibling {
            self.tree.set_next_sibling(sibling, Some(node_id));
        }

        NodeMut::new(node_id, self.tree)
    }

    ///
    /// Prepends a new `Node` as this `Node`'s first child (and last child if it has none).
    /// Returns a `NodeMut` pointing to the newly added `Node`.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let mut root = tree.root_mut().expect("root doesn't exist?");
    ///
    /// root.prepend(2);
    ///
    /// assert!(root.first_child().is_some());
    /// assert_eq!(root.first_child().unwrap().data(), &mut 2);
    ///
    /// assert!(root.last_child().is_some());
    /// assert_eq!(root.last_child().unwrap().data(), &mut 2);
    ///
    /// let mut child = root.first_child().unwrap();
    ///
    /// assert!(child.parent().is_some());
    /// assert_eq!(child.parent().unwrap().data(), &mut 1);
    /// ```
    ///
    pub fn prepend(&mut self, data: T) -> NodeMut<'_, T> {
        let new_id = self.tree.core_tree.insert(data);
        self.prepend_node_id(new_id)
    }

    ///
    /// Prepends an orphaned `Node` as this `Node`'s first child (and last child if it has none).
    /// Returns `Some(NodeMut)` pointing to the newly adopted `Node` if it exists and was orphaned.
    /// Returns `None` if the `Node` was not orphaned or doesn't exist.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// tree.root_mut().expect("root doesn't exist?");
    ///
    /// let two_id = tree.insert_orphaned(2);
    /// let mut root = tree.root_mut().expect("root doesn't exist?");
    /// let two = root.prepend_orphaned(two_id);
    ///
    /// assert!(two.is_some());
    /// assert!(root.first_child().is_some());
    /// assert_eq!(root.first_child().unwrap().data(), &mut 2);
    ///
    /// assert!(root.last_child().is_some());
    /// assert_eq!(root.last_child().unwrap().data(), &mut 2);
    ///
    /// let mut child = root.first_child().unwrap();
    ///
    /// assert!(child.parent().is_some());
    /// assert_eq!(child.parent().unwrap().data(), &mut 1);
    /// ```
    ///
    pub fn prepend_orphaned(&mut self, orphan_id: NodeId) -> Option<NodeMut<'_, T>> {
        let orphan = self.tree.get(orphan_id)?;
        if !orphan.is_orphan() {
            return None; // Orphan must not have a parent or be the root
        }
        Some(self.prepend_node_id(orphan_id))
    }

    fn prepend_node_id(&mut self, node_id: NodeId) -> NodeMut<'_, T> {
        let relatives = self.tree.get_node_relatives(self.node_id);

        let next_sibling = relatives.first_child;
        self.tree.set_parent(node_id, Some(self.node_id));
        self.tree.set_next_sibling(node_id, next_sibling);

        let last_child = relatives.last_child.or(Some(node_id));
        self.tree.set_first_child(self.node_id, Some(node_id));
        self.tree.set_last_child(self.node_id, last_child);

        if let Some(sibling) = next_sibling {
            self.tree.set_prev_sibling(sibling, Some(node_id));
        }

        NodeMut::new(node_id, self.tree)
    }

    ///
    /// Remove the first child of this `Node` and return the data that child contained.
    /// Returns a `Some`-value if this `Node` has a child to remove; returns a `None`-value
    /// otherwise.
    ///
    /// Children of the removed `Node` can either be dropped with `DropChildren` or orphaned with
    /// `OrphanChildren`.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    /// use nary_tree::behaviors::RemoveBehavior::*;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let mut root = tree.root_mut().expect("root doesn't exist?");
    /// root.append(2);
    /// root.append(3);
    ///
    /// let two = root.remove_first(DropChildren);
    ///
    /// assert!(two.is_some());
    /// assert_eq!(two.unwrap(), 2);
    ///
    /// assert!(root.first_child().is_some());
    /// assert_eq!(root.first_child().unwrap().data(), &mut 3);
    ///
    /// assert!(root.last_child().is_some());
    /// assert_eq!(root.last_child().unwrap().data(), &mut 3);
    /// ```
    ///
    pub fn remove_first(&mut self, behavior: RemoveBehavior) -> Option<T> {
        // todo: can probably simplify this
        let relatives = self.tree.get_node_relatives(self.node_id);
        let first = relatives.first_child;
        let first_id = first?;
        self.tree.remove(first_id, behavior)
    }

    ///
    /// Remove the last child of this `Node` and return the data that child contained.
    /// Returns a `Some`-value if this `Node` has a child to remove; returns a `None`-value
    /// otherwise.
    ///
    /// Children of the removed `Node` can either be dropped with `DropChildren` or orphaned with
    /// `OrphanChildren`.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    /// use nary_tree::behaviors::RemoveBehavior::*;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let mut root = tree.root_mut().expect("root doesn't exist?");
    /// root.append(2);
    /// root.append(3);
    ///
    /// let three = root.remove_last(DropChildren);
    ///
    /// assert!(three.is_some());
    /// assert_eq!(three.unwrap(), 3);
    ///
    /// assert!(root.first_child().is_some());
    /// assert_eq!(root.first_child().unwrap().data(), &mut 2);
    ///
    /// assert!(root.last_child().is_some());
    /// assert_eq!(root.last_child().unwrap().data(), &mut 2);
    /// ```
    ///
    pub fn remove_last(&mut self, behavior: RemoveBehavior) -> Option<T> {
        // todo: can probably simplify this
        let relatives = self.tree.get_node_relatives(self.node_id);
        let last = relatives.last_child;
        let last_id = last?;
        self.tree.remove(last_id, behavior)
    }

    ///
    /// Returns a `NodeRef` pointing to this `NodeMut`.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let mut root = tree.root_mut().expect("root doesn't exist?");
    /// root.append(2);
    ///
    /// let root = root.as_ref();
    ///
    /// assert_eq!(root.data(), &1);
    /// ```
    ///
    pub fn as_ref(&self) -> NodeRef<'_, T> {
        NodeRef::new(self.node_id, self.tree)
    }

    /// Exchange positions with the next sibling.
    ///
    /// Returns true if swapped with a next sibling, returns false if this was
    /// already the last sibling.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let two_id = {
    ///     let mut root = tree.root_mut().expect("root doesn't exist?");
    ///     let two_id = root.append(2).node_id();
    ///     root.append(3);
    ///     root.append(4);
    ///     two_id
    /// };
    /// assert_eq!(
    ///     tree.root().unwrap().children().map(|child_ref| *child_ref.data())
    ///         .collect::<Vec<i32>>(),
    ///     vec![2, 3, 4]);
    /// assert!(tree.get_mut(two_id).unwrap().swap_next_sibling());
    /// assert_eq!(
    ///     tree.root().unwrap().children().map(|child_ref| *child_ref.data())
    ///         .collect::<Vec<i32>>(),
    ///     vec![3, 2, 4]);
    /// assert_eq!(
    ///     *tree.get(two_id).unwrap().parent().unwrap().first_child().unwrap()
    ///         .data(),
    ///     3);
    /// assert_eq!(
    ///     *tree.get(two_id).unwrap().parent().unwrap().last_child().unwrap()
    ///         .data(),
    ///     4);
    /// assert!(tree.get_mut(two_id).unwrap().swap_next_sibling());
    /// assert_eq!(
    ///   tree.root().unwrap().children().map(|child_ref| *child_ref.data())
    ///         .collect::<Vec<i32>>(),
    ///     vec![3, 4, 2]);
    /// assert_eq!(
    ///     *tree.get(two_id).unwrap().parent().unwrap().first_child().unwrap()
    ///         .data(),
    ///     3);
    /// assert_eq!(
    ///     *tree.get(two_id).unwrap().parent().unwrap().last_child().unwrap()
    ///         .data(),
    ///     2);
    /// assert!(!tree.get_mut(two_id).unwrap().swap_next_sibling());
    /// assert_eq!(
    ///     tree.root().unwrap().children().map(|child_ref| *child_ref.data())
    ///         .collect::<Vec<i32>>(),
    ///     vec![3, 4, 2]);
    /// assert_eq!(
    ///     *tree.get(two_id).unwrap().parent().unwrap().first_child().unwrap()
    ///         .data(),
    ///     3);
    /// assert_eq!(
    ///     *tree.get(two_id).unwrap().parent().unwrap().last_child().unwrap()
    ///         .data(),
    ///     2);
    /// ```
    pub fn swap_next_sibling(&mut self) -> bool {
        let node_id = self.node_id();
        let prev_id = self.tree.get_node_prev_sibling_id(node_id);
        let next_id = self.tree.get_node_next_sibling_id(node_id);
        if let Some(next_id) = next_id {
            if let Some(parent_id) = self.parent().map(|parent| parent.node_id()) {
                let (set_first, set_last) = {
                    let parent = self.tree.get(parent_id).unwrap();
                    (
                        node_id == parent.first_child().unwrap().node_id(),
                        next_id == parent.last_child().unwrap().node_id(),
                    )
                };
                if set_first {
                    self.tree.set_first_child(parent_id, Some(next_id));
                }
                if set_last {
                    self.tree.set_last_child(parent_id, Some(node_id));
                }
            }
            let new_next_id = self.tree.get_node_next_sibling_id(next_id);
            self.tree
                .set_prev_siblings_next_sibling(node_id, Some(next_id));
            self.tree.set_next_siblings_prev_sibling(node_id, prev_id);
            self.tree.set_prev_sibling(node_id, Some(next_id));
            self.tree.set_next_sibling(node_id, new_next_id);
            self.tree
                .set_prev_siblings_next_sibling(node_id, Some(node_id));
            self.tree
                .set_next_siblings_prev_sibling(node_id, Some(node_id));
            true
        } else {
            false
        }
    }

    /// Exchange positions with the previous sibling.
    ///
    /// Returns true if swapped with a previous sibling, returns false if this
    /// was already the first sibling.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let four_id = {
    ///     let mut root = tree.root_mut().expect("root doesn't exist?");
    ///     root.append(2);
    ///     root.append(3);
    ///     let four_id = root.append(4).node_id();
    ///     four_id
    /// };
    /// assert_eq!(
    ///     tree.root().unwrap().children().map(|child_ref| *child_ref.data())
    ///         .collect::<Vec<i32>>(),
    ///     vec![2, 3, 4]);
    /// assert!(tree.get_mut(four_id).unwrap().swap_prev_sibling());
    /// assert_eq!(
    ///     tree.root().unwrap().children().map(|child_ref| *child_ref.data())
    ///         .collect::<Vec<i32>>(),
    ///     vec![2, 4, 3]);
    /// assert_eq!(
    ///     *tree.get(four_id).unwrap().parent().unwrap().first_child().unwrap()
    ///         .data(),
    ///     2);
    /// assert_eq!(
    ///     *tree.get(four_id).unwrap().parent().unwrap().last_child().unwrap()
    ///         .data(),
    ///     3);
    /// assert!(tree.get_mut(four_id).unwrap().swap_prev_sibling());
    /// assert_eq!(
    ///     tree.root().unwrap().children().map(|child_ref| *child_ref.data())
    ///         .collect::<Vec<i32>>(),
    ///     vec![4, 2, 3]);
    /// assert_eq!(
    ///     *tree.get(four_id).unwrap().parent().unwrap().first_child().unwrap()
    ///         .data(),
    ///     4);
    /// assert_eq!(
    ///     *tree.get(four_id).unwrap().parent().unwrap().last_child().unwrap()
    ///         .data(),
    ///     3);
    /// assert!(!tree.get_mut(four_id).unwrap().swap_prev_sibling());
    /// assert_eq!(
    ///     tree.root().unwrap().children().map(|child_ref| *child_ref.data())
    ///         .collect::<Vec<i32>>(),
    ///     vec![4, 2, 3]);
    /// assert_eq!(
    ///     *tree.get(four_id).unwrap().parent().unwrap().first_child().unwrap()
    ///         .data(),
    ///     4);
    /// assert_eq!(
    ///     *tree.get(four_id).unwrap().parent().unwrap().last_child().unwrap()
    ///         .data(),
    ///     3);
    /// ```
    pub fn swap_prev_sibling(&mut self) -> bool {
        let node_id = self.node_id();
        let prev_id = self.tree.get_node_prev_sibling_id(node_id);
        let next_id = self.tree.get_node_next_sibling_id(node_id);
        if let Some(prev_id) = prev_id {
            if let Some(parent_id) = self.parent().map(|parent| parent.node_id()) {
                let (set_first, set_last) = {
                    let parent = self.tree.get(parent_id).unwrap();
                    (
                        prev_id == parent.first_child().unwrap().node_id(),
                        node_id == parent.last_child().unwrap().node_id(),
                    )
                };
                if set_first {
                    self.tree.set_first_child(parent_id, Some(node_id));
                }
                if set_last {
                    self.tree.set_last_child(parent_id, Some(prev_id));
                }
            }
            let new_prev_id = self.tree.get_node_prev_sibling_id(prev_id);
            self.tree.set_prev_siblings_next_sibling(node_id, next_id);
            self.tree
                .set_next_siblings_prev_sibling(node_id, Some(prev_id));
            self.tree.set_prev_sibling(node_id, new_prev_id);
            self.tree.set_next_sibling(node_id, Some(prev_id));
            self.tree
                .set_prev_siblings_next_sibling(node_id, Some(node_id));
            self.tree
                .set_next_siblings_prev_sibling(node_id, Some(node_id));
            true
        } else {
            false
        }
    }

    /// Moves this node to the last sibling position.
    ///
    /// Returns false if the node was already the last sibling.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let two_id = {
    ///     let mut root = tree.root_mut().expect("root doesn't exist?");
    ///     let two_id = root.append(2).node_id();
    ///     root.append(3);
    ///     root.append(4);
    ///     two_id
    /// };
    /// assert_eq!(
    ///     tree.root().unwrap().children().map(|child_ref| *child_ref.data())
    ///         .collect::<Vec<i32>>(),
    ///     vec![2, 3, 4]);
    /// assert!(tree.get_mut(two_id).unwrap().make_last_sibling());
    /// assert_eq!(
    ///     tree.root().unwrap().children().map(|child_ref| *child_ref.data())
    ///         .collect::<Vec<i32>>(),
    ///     vec![3, 4, 2]);
    /// assert_eq!(
    ///     *tree.get(two_id).unwrap().parent().unwrap().first_child().unwrap()
    ///         .data(),
    ///     3);
    /// assert_eq!(
    ///     *tree.get(two_id).unwrap().parent().unwrap().last_child().unwrap()
    ///         .data(),
    ///     2);
    /// assert!(!tree.get_mut(two_id).unwrap().make_last_sibling());
    /// assert_eq!(
    ///     tree.root().unwrap().children().map(|child_ref| *child_ref.data())
    ///         .collect::<Vec<i32>>(),
    ///     vec![3, 4, 2]);
    /// assert_eq!(
    ///     *tree.get(two_id).unwrap().parent().unwrap().first_child().unwrap()
    ///         .data(),
    ///     3);
    /// assert_eq!(
    ///     *tree.get(two_id).unwrap().parent().unwrap().last_child().unwrap()
    ///         .data(),
    ///     2);
    /// ```
    pub fn make_last_sibling(&mut self) -> bool {
        if let Some(parent_id) = self.parent().map(|parent| parent.node_id()) {
            let node_id = self.node_id();
            let prev_id = self.tree.get_node_prev_sibling_id(node_id);
            let next_id = self.tree.get_node_next_sibling_id(node_id);
            let last_id = self
                .tree
                .get(parent_id)
                .unwrap()
                .last_child()
                .unwrap()
                .node_id();
            let first_id = self
                .tree
                .get(parent_id)
                .unwrap()
                .first_child()
                .unwrap()
                .node_id();
            if node_id != last_id {
                self.tree.set_last_child(parent_id, Some(node_id));
                if node_id == first_id {
                    self.tree.set_first_child(parent_id, next_id);
                }
                self.tree.set_next_sibling(last_id, Some(node_id));
                self.tree.set_prev_siblings_next_sibling(node_id, next_id);
                self.tree.set_next_siblings_prev_sibling(node_id, prev_id);
                self.tree.set_prev_sibling(node_id, Some(last_id));
                self.tree.set_next_sibling(node_id, None);
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    /// Moves this node to the first sibling position.
    ///
    /// Returns false if the node was already the first sibling.
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(1).build();
    /// let four_id = {
    ///     let mut root = tree.root_mut().expect("root doesn't exist?");
    ///     root.append(2);
    ///     root.append(3);
    ///     root.append(4).node_id()
    /// };
    /// assert_eq!(
    ///     tree.root().unwrap().children().map(|child_ref| *child_ref.data())
    ///         .collect::<Vec<i32>>(),
    ///     vec![2, 3, 4]);
    /// assert!(tree.get_mut(four_id).unwrap().make_first_sibling());
    /// assert_eq!(
    ///     tree.root().unwrap().children().map(|child_ref| *child_ref.data())
    ///         .collect::<Vec<i32>>(),
    ///     vec![4, 2, 3]);
    /// assert_eq!(
    ///     *tree.get(four_id).unwrap().parent().unwrap().first_child().unwrap()
    ///         .data(),
    ///     4);
    /// assert_eq!(
    ///     *tree.get(four_id).unwrap().parent().unwrap().last_child().unwrap()
    ///         .data(),
    ///     3);
    /// assert!(!tree.get_mut(four_id).unwrap().make_first_sibling());
    /// assert_eq!(
    ///     tree.root().unwrap().children().map(|child_ref| *child_ref.data())
    ///         .collect::<Vec<i32>>(),
    ///     vec![4, 2, 3]);
    /// assert_eq!(
    ///     *tree.get(four_id).unwrap().parent().unwrap().first_child().unwrap()
    ///         .data(),
    ///     4);
    /// assert_eq!(
    ///     *tree.get(four_id).unwrap().parent().unwrap().last_child().unwrap()
    ///         .data(),
    ///     3);
    /// ```
    pub fn make_first_sibling(&mut self) -> bool {
        if let Some(parent_id) = self.parent().map(|parent| parent.node_id()) {
            let node_id = self.node_id();
            let prev_id = self.tree.get_node_prev_sibling_id(node_id);
            let next_id = self.tree.get_node_next_sibling_id(node_id);
            let first_id = self
                .tree
                .get(parent_id)
                .unwrap()
                .first_child()
                .unwrap()
                .node_id();
            let last_id = self
                .tree
                .get(parent_id)
                .unwrap()
                .last_child()
                .unwrap()
                .node_id();
            if node_id != first_id {
                self.tree.set_first_child(parent_id, Some(node_id));
                if node_id == last_id {
                    self.tree.set_last_child(parent_id, prev_id);
                }
                self.tree.set_prev_sibling(first_id, Some(node_id));
                self.tree.set_prev_siblings_next_sibling(node_id, next_id);
                self.tree.set_next_siblings_prev_sibling(node_id, prev_id);
                self.tree.set_next_sibling(node_id, Some(first_id));
                self.tree.set_prev_sibling(node_id, None);
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    /// Sorts the direct children of this node.
    ///
    /// # Current implementation
    ///
    /// The current implementation uses an adaptation of merge sort for linked lists
    /// by Simon Tatham, described [here](https://www.chiark.greenend.org.uk/~sgtatham/algorithms/listsort.html).
    ///
    /// This sort is stable, and it runs in *n* log(*n*) time.
    ///
    /// # Example
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(0).build();
    /// let mut root = tree.root_mut().expect("has root node");
    /// for n in [2, 0, 4, 5, 1, 2] {
    ///     root.append(n);
    /// }
    ///
    /// root.sort_children();
    ///
    /// assert_eq!(
    ///     root.as_ref().children().map(|c| *c.data()).collect::<Vec<_>>(),
    ///     [0, 1, 2, 2, 4, 5],
    /// );
    /// ```
    pub fn sort_children(&mut self)
    where
        T: Ord,
    {
        self.sort_children_by(&T::cmp);
    }

    /// Sorts the direct children of this node using the specified comparison function.
    ///
    /// See [`sort_children`](Self::sort_children) for more details.
    pub fn sort_children_by<F>(&mut self, mut compare: F)
    where
        F: FnMut(&T, &T) -> Ordering,
    {
        let first_child = {
            let node = self.get_self_as_node();
            let Relatives {
                first_child: Some(first_child),
                last_child: Some(last_child),
                ..
            } = node.relatives
            else {
                // no children, already sorted
                return;
            };
            if first_child == last_child {
                // one child, already sorted
                return;
            }
            first_child
        };

        // References:
        // https://www.chiark.greenend.org.uk/~sgtatham/algorithms/listsort.html
        // https://www.chiark.greenend.org.uk/~sgtatham/algorithms/listsort.c

        // The size of the blocks to merge.
        // In the first iteration, it is set to 1, so "blocks" of size 1 are merged into blocks of size 2.
        // In the second iteration, it is set to 2, so blocks of size 2 are merged into blocks of size 4, and so on.
        let mut k = 1;

        // The head and tail of the linked list containing this node's children.
        // It is rebuilt on each iteration of the outer loop.
        let mut head = first_child;
        let mut tail;
        loop {
            let mut merges = Saturating(0u8);
            let mut p = SiblingList::new(head);
            tail = None;

            while !p.reached_end() {
                merges += 1;

                // Select the next two blocks of nodes to merge.
                let mut q = p.pair_from_current_position(self.tree, k);

                loop {
                    // Take the next node to merge into the list from either p or q.
                    let e = match (p.head(), q.head()) {
                        (None, None) => break,
                        (Some(p_head), None) => {
                            // q is empty, take from p.
                            p.advance(self.tree);
                            p_head
                        }
                        (None, Some(q_head)) => {
                            // p is empty, take from q.
                            q.advance(self.tree);
                            q_head
                        }
                        (Some(p_head), Some(q_head)) => {
                            let p_data = &self.tree.get_node(p_head).expect("node exists").data;
                            let q_data = &self.tree.get_node(q_head).expect("node exists").data;

                            // Pick the smallest element to remove.
                            // If both are equal, remove from p, to ensure the sort is stable.
                            if compare(p_data, q_data) == Ordering::Greater {
                                q.advance(self.tree);
                                q_head
                            } else {
                                p.advance(self.tree);
                                p_head
                            }
                        }
                    };

                    // Append it to the tail of the list.
                    if let Some(tail) = tail {
                        self.tree.set_next_sibling(tail, Some(e));
                    } else {
                        // This is the first node, so make it the head of the list as well.
                        head = e;
                    }
                    self.tree.set_prev_sibling(e, tail);
                    tail = Some(e);
                }

                // Advance p to where q ended, so that the next loop sorts the next set of nodes.
                p.advance_to(&q);
            }
            if let Some(tail) = tail {
                self.tree.set_next_sibling(tail, None);
            }

            if merges.0 <= 1 {
                // Stop once all items have been merged into a single sorted block.
                break;
            }

            k *= 2;
        }
        assert!(tail.is_some());

        if let Some(node) = self.tree.get_node_mut(self.node_id) {
            node.relatives.first_child = Some(head);
            node.relatives.last_child = tail;
        } else {
            unreachable!()
        }
    }

    /// Sorts the children of this node recursively.
    ///
    /// This function calls [`sort_children`](Self::sort_children), see its documentation for details.
    ///
    /// # Example
    ///
    /// ```
    /// use nary_tree::tree::TreeBuilder;
    ///
    /// let mut tree = TreeBuilder::new().with_root(0).build();
    /// let (node2, node3, node1) = {
    ///     let mut root = tree.root_mut().unwrap();
    ///     (
    ///         root.append(2).node_id(),
    ///         root.append(3).node_id(),
    ///         root.append(1).node_id(),
    ///     )
    /// };
    ///
    /// let (node5, node4) = {
    ///     let mut node1 = tree.get_mut(node1).unwrap();
    ///     (node1.append(5).node_id(), node1.append(4).node_id())
    /// };
    ///
    /// tree.get_mut(node4).unwrap().append(6);
    /// tree.get_mut(node5).unwrap().append(8);
    /// tree.get_mut(node5).unwrap().append(7);
    ///
    /// let node9 = {
    ///     let mut node2 = tree.get_mut(node2).unwrap();
    ///     let mut node9 = node2.append(9);
    ///     node9.append(12);
    ///     node9.append(10);
    ///     node9.append(11);
    ///     node9.node_id()
    /// };
    /// tree.get_mut(node3).unwrap().append(13);
    ///
    /// tree.root_mut().unwrap().sort_recursive();
    ///
    /// let children = |id| tree.get(id).unwrap().children().map(|c| *c.data()).collect::<Vec<_>>();
    /// assert_eq!(children(tree.root_id().unwrap()), [1, 2, 3]);
    /// assert_eq!(children(node1), [4, 5]);
    /// assert_eq!(children(node4), [6]);
    /// assert_eq!(children(node5), [7, 8]);
    /// assert_eq!(children(node2), [9]);
    /// assert_eq!(children(node9), [10, 11, 12]);
    /// assert_eq!(children(node3), [13]);
    /// ```
    pub fn sort_recursive(&mut self)
    where
        T: Ord,
    {
        self.sort_recursive_by(&T::cmp);
    }

    /// Sorts the children of this node recursively using the specified comparison function.
    ///
    /// This function calls [`sort_children_by`](Self::sort_children_by), see its documentation for details.
    pub fn sort_recursive_by<F>(&mut self, mut compare: F)
    where
        F: FnMut(&T, &T) -> Ordering,
    {
        self.sort_children_by(&mut compare);

        let Some(first_child) = self.get_self_as_node().relatives.first_child else {
            return;
        };
        let mut children = vec![first_child];

        while let Some(current) = children.pop() {
            if let Some(mut current_ref) = self.tree.get_mut(current) {
                current_ref.sort_children_by(&mut compare);
            } else {
                unreachable!()
            }

            if let Some(current_node) = self.tree.get_node(current) {
                if let Some(next_sibling) = current_node.relatives.next_sibling {
                    children.push(next_sibling);
                }
                if let Some(first_child) = current_node.relatives.first_child {
                    children.push(first_child);
                }
            } else {
                unreachable!()
            }
        }
    }

    fn get_self_as_node(&self) -> &Node<T> {
        if let Some(node) = self.tree.get_node(self.node_id) {
            node
        } else {
            unreachable!()
        }
    }
}

/// List of sibling nodes for use as a merge sort block, see [`NodeMut::sort_children_by`].
#[derive(Copy, Clone, Default)]
struct SiblingList {
    head: Option<NodeId>,
    size: usize,
}

impl SiblingList {
    /// Creates a new `SiblingList` at the specified position.
    ///
    /// `pair_from_current_position` should be called at least once before the list is used.
    fn new(head: NodeId) -> Self {
        Self {
            head: Some(head),
            size: 0,
        }
    }

    /// Creates two blocks starting from the current position.
    ///
    /// This list's size will be set to `k` unless we reach the end of the entire sibling list,
    /// in which case it will be less than `k`.
    ///
    /// The second list, the value returned by this method, will always have its size set to `k`,
    /// but may contain fewer than `k` items (or none at all).
    /// (There is no advantage in looking up the number of items ahead of time.)
    fn pair_from_current_position<T>(&mut self, tree: &Tree<T>, k: usize) -> Self {
        self.size = 0;
        let mut second_head = self.head.expect("hasn't reached end");
        for _ in 0..k {
            self.size += 1;
            match tree.get_node_next_sibling_id(second_head) {
                Some(next) => second_head = next,
                None => return Self::default(),
            }
        }

        Self {
            head: Some(second_head),
            size: k,
        }
    }

    /// Advances the list to the specified position.
    ///
    /// `pair_from_current_position` should be called after calling this.
    fn advance_to(&mut self, other: &SiblingList) {
        self.head = other.head;
    }

    /// Returns the node at the head of the list, if any.
    fn head(&self) -> Option<NodeId> {
        if self.size == 0 { None } else { self.head }
    }

    /// Checks if the list has reached the end of the entire sibling list.
    fn reached_end(&self) -> bool {
        self.head.is_none()
    }

    /// Advances the list to point to the next sibling.
    fn advance<T>(&mut self, tree: &Tree<T>) {
        if let Some(head) = self.head {
            self.head = tree.get_node_next_sibling_id(head);
            self.size -= 1;
        }
    }
}

#[cfg_attr(tarpaulin, skip)]
#[cfg(test)]
mod node_mut_tests {
    use crate::behaviors::RemoveBehavior::{DropChildren, OrphanChildren};
    use crate::tree::Tree;

    #[test]
    fn node_id() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let root_mut = tree.get_mut(root_id).unwrap();
        assert_eq!(root_id, root_mut.node_id());
    }

    #[test]
    fn data() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        assert_eq!(root_mut.data(), &mut 1);

        *root_mut.data() = 2;
        assert_eq!(root_mut.data(), &mut 2);
    }

    #[test]
    fn parent() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");
        let mut root_mut = tree.get_mut(root_id).unwrap();
        assert!(root_mut.parent().is_none());
    }

    #[test]
    fn prev_sibling() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");
        let mut root_mut = tree.get_mut(root_id).unwrap();
        assert!(root_mut.prev_sibling().is_none());
    }

    #[test]
    fn next_sibling() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");
        let mut root_mut = tree.get_mut(root_id).unwrap();
        assert!(root_mut.next_sibling().is_none());
    }

    #[test]
    fn first_child() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");
        let mut root_mut = tree.get_mut(root_id).unwrap();
        assert!(root_mut.first_child().is_none());
    }

    #[test]
    fn last_child() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");
        let mut root_mut = tree.get_mut(root_id).unwrap();
        assert!(root_mut.last_child().is_none());
    }

    #[test]
    fn append_no_children_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let new_id = root_mut.append(2).node_id();

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, Some(new_id));
        assert_eq!(root_node.relatives.last_child, Some(new_id));

        let new_node = tree.get_node(new_id);
        assert!(new_node.is_some());

        let new_node = new_node.unwrap();
        assert_eq!(new_node.relatives.parent, Some(root_id));
        assert_eq!(new_node.relatives.prev_sibling, None);
        assert_eq!(new_node.relatives.next_sibling, None);
        assert_eq!(new_node.relatives.first_child, None);
        assert_eq!(new_node.relatives.last_child, None);

        let root = tree.get(root_id).unwrap();
        assert_eq!(root.data(), &1);

        let new_node = root.first_child().unwrap();
        assert_eq!(new_node.data(), &2);
    }

    #[test]
    fn append_single_child_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let new_id = root_mut.append(2).node_id();
        let new_id_2 = root_mut.append(3).node_id();

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, Some(new_id));
        assert_eq!(root_node.relatives.last_child, Some(new_id_2));

        let new_node = tree.get_node(new_id);
        assert!(new_node.is_some());

        let new_node = new_node.unwrap();
        assert_eq!(new_node.relatives.parent, Some(root_id));
        assert_eq!(new_node.relatives.prev_sibling, None);
        assert_eq!(new_node.relatives.next_sibling, Some(new_id_2));
        assert_eq!(new_node.relatives.first_child, None);
        assert_eq!(new_node.relatives.last_child, None);

        let new_node_2 = tree.get_node(new_id_2);
        assert!(new_node_2.is_some());

        let new_node_2 = new_node_2.unwrap();
        assert_eq!(new_node_2.relatives.parent, Some(root_id));
        assert_eq!(new_node_2.relatives.prev_sibling, Some(new_id));
        assert_eq!(new_node_2.relatives.next_sibling, None);
        assert_eq!(new_node_2.relatives.first_child, None);
        assert_eq!(new_node_2.relatives.last_child, None);

        let root = tree.get(root_id).unwrap();
        assert_eq!(root.data(), &1);

        let new_node = root.first_child().unwrap();
        assert_eq!(new_node.data(), &2);

        let new_node_2 = root.last_child().unwrap();
        assert_eq!(new_node_2.data(), &3);
    }

    #[test]
    fn append_two_children_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let new_id = root_mut.append(2).node_id();
        let new_id_2 = root_mut.append(3).node_id();
        let new_id_3 = root_mut.append(4).node_id();

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, Some(new_id));
        assert_eq!(root_node.relatives.last_child, Some(new_id_3));

        let new_node = tree.get_node(new_id);
        assert!(new_node.is_some());

        let new_node = new_node.unwrap();
        assert_eq!(new_node.relatives.parent, Some(root_id));
        assert_eq!(new_node.relatives.prev_sibling, None);
        assert_eq!(new_node.relatives.next_sibling, Some(new_id_2));
        assert_eq!(new_node.relatives.first_child, None);
        assert_eq!(new_node.relatives.last_child, None);

        let new_node_2 = tree.get_node(new_id_2);
        assert!(new_node_2.is_some());

        let new_node_2 = new_node_2.unwrap();
        assert_eq!(new_node_2.relatives.parent, Some(root_id));
        assert_eq!(new_node_2.relatives.prev_sibling, Some(new_id));
        assert_eq!(new_node_2.relatives.next_sibling, Some(new_id_3));
        assert_eq!(new_node_2.relatives.first_child, None);
        assert_eq!(new_node_2.relatives.last_child, None);

        let new_node_3 = tree.get_node(new_id_3);
        assert!(new_node_3.is_some());

        let new_node_3 = new_node_3.unwrap();
        assert_eq!(new_node_3.relatives.parent, Some(root_id));
        assert_eq!(new_node_3.relatives.prev_sibling, Some(new_id_2));
        assert_eq!(new_node_3.relatives.next_sibling, None);
        assert_eq!(new_node_3.relatives.first_child, None);
        assert_eq!(new_node_3.relatives.last_child, None);

        let root = tree.get(root_id).unwrap();
        assert_eq!(root.data(), &1);

        // left to right
        let new_node = root.first_child().unwrap();
        let new_node_2 = new_node.next_sibling().unwrap();
        let new_node_3 = new_node_2.next_sibling().unwrap();
        assert_eq!(new_node.data(), &2);
        assert_eq!(new_node_2.data(), &3);
        assert_eq!(new_node_3.data(), &4);

        // right to left
        let new_node_3 = root.last_child().unwrap();
        let new_node_2 = new_node_3.prev_sibling().unwrap();
        let new_node = new_node_2.prev_sibling().unwrap();
        assert_eq!(new_node_3.data(), &4);
        assert_eq!(new_node_2.data(), &3);
        assert_eq!(new_node.data(), &2);
    }

    #[test]
    fn prepend_no_children_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let new_id = root_mut.prepend(2).node_id();

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, Some(new_id));
        assert_eq!(root_node.relatives.last_child, Some(new_id));

        let new_node = tree.get_node(new_id);
        assert!(new_node.is_some());

        let new_node = new_node.unwrap();
        assert_eq!(new_node.relatives.parent, Some(root_id));
        assert_eq!(new_node.relatives.prev_sibling, None);
        assert_eq!(new_node.relatives.next_sibling, None);
        assert_eq!(new_node.relatives.first_child, None);
        assert_eq!(new_node.relatives.last_child, None);

        let root = tree.get(root_id).unwrap();
        assert_eq!(root.data(), &1);

        let new_node = root.first_child().unwrap();
        assert_eq!(new_node.data(), &2);
    }

    #[test]
    fn prepend_single_child_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let new_id = root_mut.prepend(2).node_id();
        let new_id_2 = root_mut.prepend(3).node_id();

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, Some(new_id_2));
        assert_eq!(root_node.relatives.last_child, Some(new_id));

        let new_node = tree.get_node(new_id);
        assert!(new_node.is_some());

        let new_node = new_node.unwrap();
        assert_eq!(new_node.relatives.parent, Some(root_id));
        assert_eq!(new_node.relatives.prev_sibling, Some(new_id_2));
        assert_eq!(new_node.relatives.next_sibling, None);
        assert_eq!(new_node.relatives.first_child, None);
        assert_eq!(new_node.relatives.last_child, None);

        let new_node_2 = tree.get_node(new_id_2);
        assert!(new_node_2.is_some());

        let new_node_2 = new_node_2.unwrap();
        assert_eq!(new_node_2.relatives.parent, Some(root_id));
        assert_eq!(new_node_2.relatives.prev_sibling, None);
        assert_eq!(new_node_2.relatives.next_sibling, Some(new_id));
        assert_eq!(new_node_2.relatives.first_child, None);
        assert_eq!(new_node_2.relatives.last_child, None);

        let root = tree.get(root_id).unwrap();
        assert_eq!(root.data(), &1);

        let new_node = root.first_child().unwrap();
        assert_eq!(new_node.data(), &3);

        let new_node_2 = root.last_child().unwrap();
        assert_eq!(new_node_2.data(), &2);
    }

    #[test]
    fn prepend_two_children_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let new_id = root_mut.prepend(2).node_id();
        let new_id_2 = root_mut.prepend(3).node_id();
        let new_id_3 = root_mut.prepend(4).node_id();

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, Some(new_id_3));
        assert_eq!(root_node.relatives.last_child, Some(new_id));

        let new_node = tree.get_node(new_id);
        assert!(new_node.is_some());

        let new_node = new_node.unwrap();
        assert_eq!(new_node.relatives.parent, Some(root_id));
        assert_eq!(new_node.relatives.prev_sibling, Some(new_id_2));
        assert_eq!(new_node.relatives.next_sibling, None);
        assert_eq!(new_node.relatives.first_child, None);
        assert_eq!(new_node.relatives.last_child, None);

        let new_node_2 = tree.get_node(new_id_2);
        assert!(new_node_2.is_some());

        let new_node_2 = new_node_2.unwrap();
        assert_eq!(new_node_2.relatives.parent, Some(root_id));
        assert_eq!(new_node_2.relatives.prev_sibling, Some(new_id_3));
        assert_eq!(new_node_2.relatives.next_sibling, Some(new_id));
        assert_eq!(new_node_2.relatives.first_child, None);
        assert_eq!(new_node_2.relatives.last_child, None);

        let new_node_3 = tree.get_node(new_id_3);
        assert!(new_node_3.is_some());

        let new_node_3 = new_node_3.unwrap();
        assert_eq!(new_node_3.relatives.parent, Some(root_id));
        assert_eq!(new_node_3.relatives.prev_sibling, None);
        assert_eq!(new_node_3.relatives.next_sibling, Some(new_id_2));
        assert_eq!(new_node_3.relatives.first_child, None);
        assert_eq!(new_node_3.relatives.last_child, None);

        let root = tree.get(root_id).unwrap();
        assert_eq!(root.data(), &1);

        // left to right
        let new_node_3 = root.first_child().unwrap();
        let new_node_2 = new_node_3.next_sibling().unwrap();
        let new_node = new_node_2.next_sibling().unwrap();
        assert_eq!(new_node_3.data(), &4);
        assert_eq!(new_node_2.data(), &3);
        assert_eq!(new_node.data(), &2);

        // right to left
        let new_node = root.last_child().unwrap();
        let new_node_2 = new_node.prev_sibling().unwrap();
        let new_node_3 = new_node_2.prev_sibling().unwrap();
        assert_eq!(new_node.data(), &2);
        assert_eq!(new_node_2.data(), &3);
        assert_eq!(new_node_3.data(), &4);
    }

    #[test]
    fn remove_first_no_children_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let first_child_data = root_mut.remove_first(DropChildren);
        assert_eq!(first_child_data, None);

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, None);
        assert_eq!(root_node.relatives.last_child, None);
    }

    #[test]
    fn remove_first_drop_single_child_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let two_id = root_mut.append(2).node_id();

        let removed = root_mut.remove_first(DropChildren);
        assert_eq!(removed, Some(2));

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, None);
        assert_eq!(root_node.relatives.last_child, None);

        let two = tree.get_node(two_id);
        assert!(two.is_none());
    }

    #[test]
    fn remove_first_drop_two_children_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        root_mut.append(2);
        let three_id = root_mut.append(3).node_id();

        let removed = root_mut.remove_first(DropChildren);
        assert_eq!(removed, Some(2));

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, Some(three_id));
        assert_eq!(root_node.relatives.last_child, Some(three_id));

        let three = tree.get_node(three_id);
        assert!(three.is_some());

        let three = three.unwrap();
        assert_eq!(three.relatives.parent, Some(root_id));
        assert_eq!(three.relatives.prev_sibling, None);
        assert_eq!(three.relatives.next_sibling, None);
        assert_eq!(three.relatives.first_child, None);
        assert_eq!(three.relatives.last_child, None);
    }

    #[test]
    fn remove_first_drop_three_children_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        root_mut.append(2);
        let three_id = root_mut.append(3).node_id();
        let four_id = root_mut.append(4).node_id();

        let removed = root_mut.remove_first(DropChildren);
        assert_eq!(removed, Some(2));

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, Some(three_id));
        assert_eq!(root_node.relatives.last_child, Some(four_id));

        let three = tree.get_node(three_id);
        assert!(three.is_some());

        let three = three.unwrap();
        assert_eq!(three.relatives.parent, Some(root_id));
        assert_eq!(three.relatives.prev_sibling, None);
        assert_eq!(three.relatives.next_sibling, Some(four_id));
        assert_eq!(three.relatives.first_child, None);
        assert_eq!(three.relatives.last_child, None);

        let four = tree.get_node(four_id);
        assert!(four.is_some());

        let four = four.unwrap();
        assert_eq!(four.relatives.parent, Some(root_id));
        assert_eq!(four.relatives.prev_sibling, Some(three_id));
        assert_eq!(four.relatives.next_sibling, None);
        assert_eq!(four.relatives.first_child, None);
        assert_eq!(four.relatives.last_child, None);
    }

    #[test]
    fn remove_first_drop_grandchild_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let three_id = root_mut.append(2).append(3).node_id();

        let removed = root_mut.remove_first(DropChildren);
        assert_eq!(removed, Some(2));

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, None);
        assert_eq!(root_node.relatives.last_child, None);

        let three = tree.get_node(three_id);
        assert!(three.is_none());
    }

    #[test]
    fn remove_first_orphan_grandchild_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let three_id = root_mut.append(2).append(3).node_id();

        let removed = root_mut.remove_first(OrphanChildren);
        assert_eq!(removed, Some(2));

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, None);
        assert_eq!(root_node.relatives.last_child, None);

        let three = tree.get_node(three_id);
        assert!(three.is_some());

        let three = three.unwrap();
        assert_eq!(three.relatives.parent, None);
    }

    #[test]
    fn remove_last_no_children_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let removed = root_mut.remove_last(DropChildren);
        assert_eq!(removed, None);

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, None);
        assert_eq!(root_node.relatives.last_child, None);
    }

    #[test]
    fn remove_last_single_child_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        root_mut.append(2);
        let removed = root_mut.remove_last(DropChildren);
        assert_eq!(removed, Some(2));

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, None);
        assert_eq!(root_node.relatives.last_child, None);
    }

    #[test]
    fn remove_last_two_children_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let two_id = root_mut.append(2).node_id();
        root_mut.append(3);

        let removed = root_mut.remove_last(DropChildren);
        assert_eq!(removed, Some(3));

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, Some(two_id));
        assert_eq!(root_node.relatives.last_child, Some(two_id));

        let two = tree.get_node(two_id);
        assert!(two.is_some());

        let two = two.unwrap();
        assert_eq!(two.relatives.parent, Some(root_id));
        assert_eq!(two.relatives.prev_sibling, None);
        assert_eq!(two.relatives.next_sibling, None);
        assert_eq!(two.relatives.first_child, None);
        assert_eq!(two.relatives.last_child, None);
    }

    #[test]
    fn remove_last_three_children_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let two_id = root_mut.append(2).node_id();
        let three_id = root_mut.append(3).node_id();
        root_mut.append(4);

        let removed = root_mut.remove_last(DropChildren);
        assert_eq!(removed, Some(4));

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, Some(two_id));
        assert_eq!(root_node.relatives.last_child, Some(three_id));

        let two = tree.get_node(two_id);
        assert!(two.is_some());

        let two = two.unwrap();
        assert_eq!(two.relatives.parent, Some(root_id));
        assert_eq!(two.relatives.prev_sibling, None);
        assert_eq!(two.relatives.next_sibling, Some(three_id));
        assert_eq!(two.relatives.first_child, None);
        assert_eq!(two.relatives.last_child, None);

        let three = tree.get_node(three_id);
        assert!(three.is_some());

        let three = three.unwrap();
        assert_eq!(three.relatives.parent, Some(root_id));
        assert_eq!(three.relatives.prev_sibling, Some(two_id));
        assert_eq!(three.relatives.next_sibling, None);
        assert_eq!(three.relatives.first_child, None);
        assert_eq!(three.relatives.last_child, None);
    }

    #[test]
    fn remove_last_orphan_grandchild_present() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let three_id = root_mut.append(2).append(3).node_id();

        let removed = root_mut.remove_last(OrphanChildren);
        assert_eq!(removed, Some(2));

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, None);
        assert_eq!(root_node.relatives.last_child, None);

        let three = tree.get_node(three_id);
        assert!(three.is_some());

        let three = three.unwrap();
        assert_eq!(three.relatives.parent, None);
    }

    #[test]
    fn append_orphaned_success() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().unwrap();
        let orphan_id = tree.insert_orphaned(10);

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let new_child = root_mut.append_orphaned(orphan_id);

        assert!(new_child.is_some());
        assert_eq!(new_child.unwrap().data(), &mut 10);

        let root_ref = tree.get(root_id).unwrap();
        assert_eq!(root_ref.children().count(), 1);
        assert_eq!(root_ref.first_child().unwrap().data(), &10);
        assert_eq!(root_ref.last_child().unwrap().data(), &10);

        let orphan_ref = tree.get(orphan_id).unwrap();
        assert!(!orphan_ref.is_orphan());
        assert_eq!(orphan_ref.parent().unwrap().node_id(), root_id);
    }

    #[test]
    fn append_orphaned_to_node_with_children() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().unwrap();
        let orphan_id = tree.insert_orphaned(10);

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let first_child_id = root_mut.append(2).node_id();
        let new_child = root_mut.append_orphaned(orphan_id);

        assert!(new_child.is_some());

        let root_ref = tree.get(root_id).unwrap();
        assert_eq!(root_ref.children().count(), 2);
        assert_eq!(root_ref.first_child().unwrap().node_id(), first_child_id);
        assert_eq!(root_ref.last_child().unwrap().node_id(), orphan_id);

        let orphan_ref = tree.get(orphan_id).unwrap();
        assert_eq!(orphan_ref.prev_sibling().unwrap().node_id(), first_child_id);
    }

    #[test]
    fn append_orphaned_non_orphan_node() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().unwrap();

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let child_id = root_mut.append(2).node_id();
        let result = root_mut.append_orphaned(child_id);

        assert!(result.is_none());
    }

    #[test]
    fn prepend_orphaned_success() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().unwrap();
        let orphan_id = tree.insert_orphaned(10);

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let new_child = root_mut.prepend_orphaned(orphan_id);

        assert!(new_child.is_some());
        assert_eq!(new_child.unwrap().data(), &mut 10);

        let root_ref = tree.get(root_id).unwrap();
        assert_eq!(root_ref.children().count(), 1);
        assert_eq!(root_ref.first_child().unwrap().data(), &10);
        assert_eq!(root_ref.last_child().unwrap().data(), &10);

        let orphan_ref = tree.get(orphan_id).unwrap();
        assert!(!orphan_ref.is_orphan());
        assert_eq!(orphan_ref.parent().unwrap().node_id(), root_id);
    }

    #[test]
    fn prepend_orphaned_to_node_with_children() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().unwrap();
        let orphan_id = tree.insert_orphaned(10);

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let last_child_id = root_mut.append(2).node_id();
        let new_child = root_mut.prepend_orphaned(orphan_id);

        assert!(new_child.is_some());

        let root_ref = tree.get(root_id).unwrap();
        assert_eq!(root_ref.children().count(), 2);
        assert_eq!(root_ref.first_child().unwrap().node_id(), orphan_id);
        assert_eq!(root_ref.last_child().unwrap().node_id(), last_child_id);

        let orphan_ref = tree.get(orphan_id).unwrap();
        assert_eq!(orphan_ref.next_sibling().unwrap().node_id(), last_child_id);
    }

    #[test]
    fn prepend_orphaned_non_orphan_node() {
        let mut tree = Tree::new();
        tree.set_root(1);
        let root_id = tree.root_id().unwrap();

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let child_id = root_mut.append(2).node_id();
        let result = root_mut.prepend_orphaned(child_id);

        assert!(result.is_none());
    }

    #[test]
    fn sort() {
        let mut tree = Tree::new();
        tree.set_root(0);
        let root_id = tree.root_id().expect("root doesn't exist?");

        let mut root_mut = tree.get_mut(root_id).unwrap();
        let new_id = root_mut.append(7).node_id();
        let new_id_2 = root_mut.append(3).node_id();
        let new_id_3 = root_mut.append(4).node_id();
        let new_id_4 = root_mut.append(1).node_id();
        let new_id_5 = root_mut.append(4).node_id();

        root_mut.sort_children();

        let root_node = tree.get_node(root_id);
        assert!(root_node.is_some());

        let root_node = root_node.unwrap();
        assert_eq!(root_node.relatives.first_child, Some(new_id_4));
        assert_eq!(root_node.relatives.last_child, Some(new_id));

        let new_node = tree.get_node(new_id);
        assert!(new_node.is_some());

        let new_node = new_node.unwrap();
        assert_eq!(new_node.data, 7);
        assert_eq!(new_node.relatives.parent, Some(root_id));
        assert_eq!(new_node.relatives.prev_sibling, Some(new_id_5));
        assert_eq!(new_node.relatives.next_sibling, None);
        assert_eq!(new_node.relatives.first_child, None);
        assert_eq!(new_node.relatives.last_child, None);

        let new_node_2 = tree.get_node(new_id_2);
        assert!(new_node_2.is_some());

        let new_node_2 = new_node_2.unwrap();
        assert_eq!(new_node_2.data, 3);
        assert_eq!(new_node_2.relatives.parent, Some(root_id));
        assert_eq!(new_node_2.relatives.prev_sibling, Some(new_id_4));
        assert_eq!(new_node_2.relatives.next_sibling, Some(new_id_3));
        assert_eq!(new_node_2.relatives.first_child, None);
        assert_eq!(new_node_2.relatives.last_child, None);

        let new_node_3 = tree.get_node(new_id_3);
        assert!(new_node_3.is_some());

        let new_node_3 = new_node_3.unwrap();
        assert_eq!(new_node_3.data, 4);
        assert_eq!(new_node_3.relatives.parent, Some(root_id));
        assert_eq!(new_node_3.relatives.prev_sibling, Some(new_id_2));
        assert_eq!(new_node_3.relatives.next_sibling, Some(new_id_5));
        assert_eq!(new_node_3.relatives.first_child, None);
        assert_eq!(new_node_3.relatives.last_child, None);

        let new_node_4 = tree.get_node(new_id_4);
        assert!(new_node_4.is_some());

        let new_node_4 = new_node_4.unwrap();
        assert_eq!(new_node_4.data, 1);
        assert_eq!(new_node_4.relatives.parent, Some(root_id));
        assert_eq!(new_node_4.relatives.prev_sibling, None);
        assert_eq!(new_node_4.relatives.next_sibling, Some(new_id_2));
        assert_eq!(new_node_4.relatives.first_child, None);
        assert_eq!(new_node_4.relatives.last_child, None);

        let new_node_5 = tree.get_node(new_id_5);
        assert!(new_node_5.is_some());

        let new_node_5 = new_node_5.unwrap();
        assert_eq!(new_node_5.data, 4);
        assert_eq!(new_node_5.relatives.parent, Some(root_id));
        assert_eq!(new_node_5.relatives.prev_sibling, Some(new_id_3));
        assert_eq!(new_node_5.relatives.next_sibling, Some(new_id));
        assert_eq!(new_node_5.relatives.first_child, None);
        assert_eq!(new_node_5.relatives.last_child, None);

        let root = tree.get(root_id).unwrap();
        assert_eq!(root.data(), &0);

        // left to right
        let new_node = root.first_child().unwrap();
        let new_node_2 = new_node.next_sibling().unwrap();
        let new_node_3 = new_node_2.next_sibling().unwrap();
        let new_node_4 = new_node_3.next_sibling().unwrap();
        let new_node_5 = new_node_4.next_sibling().unwrap();
        assert_eq!(new_node.data(), &1);
        assert_eq!(new_node_2.data(), &3);
        assert_eq!(new_node_3.data(), &4);
        assert_eq!(new_node_4.data(), &4);
        assert_eq!(new_node_5.data(), &7);

        // right to left
        let new_node_5 = root.last_child().unwrap();
        let new_node_4 = new_node_5.prev_sibling().unwrap();
        let new_node_3 = new_node_4.prev_sibling().unwrap();
        let new_node_2 = new_node_3.prev_sibling().unwrap();
        let new_node = new_node_2.prev_sibling().unwrap();
        assert_eq!(new_node_5.data(), &7);
        assert_eq!(new_node_4.data(), &4);
        assert_eq!(new_node_3.data(), &4);
        assert_eq!(new_node_2.data(), &3);
        assert_eq!(new_node.data(), &1);
    }

    #[test]
    fn sort_none() {
        let mut tree = Tree::new();
        let root = tree.set_root(0);

        tree.root_mut().unwrap().sort_children();

        let root_node = tree.get_node(root).unwrap();
        assert_eq!(root_node.data, 0);
        assert_eq!(root_node.relatives.first_child, None);
        assert_eq!(root_node.relatives.last_child, None);
        assert_eq!(root_node.relatives.next_sibling, None);
        assert_eq!(root_node.relatives.prev_sibling, None);
        assert_eq!(root_node.relatives.parent, None);
    }

    #[test]
    fn sort_one() {
        let mut tree = Tree::new();
        let root = tree.set_root(0);
        let child = {
            let mut root_mut = tree.root_mut().unwrap();
            let child = root_mut.append(1).node_id();
            root_mut.sort_children();
            child
        };

        let root_node = tree.get_node(root).unwrap();
        assert_eq!(root_node.data, 0);
        assert_eq!(root_node.relatives.first_child, Some(child));
        assert_eq!(root_node.relatives.last_child, Some(child));
        assert_eq!(root_node.relatives.next_sibling, None);
        assert_eq!(root_node.relatives.prev_sibling, None);
        assert_eq!(root_node.relatives.parent, None);

        let child_node = tree.get_node(child).unwrap();
        assert_eq!(child_node.data, 1);
        assert_eq!(child_node.relatives.first_child, None);
        assert_eq!(child_node.relatives.last_child, None);
        assert_eq!(child_node.relatives.next_sibling, None);
        assert_eq!(child_node.relatives.prev_sibling, None);
        assert_eq!(child_node.relatives.parent, Some(root));
    }
}
