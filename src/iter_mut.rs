pub use lender::Lender;
use lender::{Lending, check_covariance};

use crate::node::Relatives;
use crate::{NodeId, NodeMut, Tree};

pub struct NextSiblingsMut<'a, T> {
    node_id: Option<NodeId>,
    tree: &'a mut Tree<T>,
}

impl<'a, T> NextSiblingsMut<'a, T> {
    pub(crate) fn new(node_id: Option<NodeId>, tree: &'a mut Tree<T>) -> NextSiblingsMut<'a, T> {
        NextSiblingsMut { node_id, tree }
    }
}

impl<'this, 'lend, T> Lending<'lend> for NextSiblingsMut<'this, T> {
    type Lend = NodeMut<'lend, T>;
}

impl<'this, T> Lender for NextSiblingsMut<'this, T> {
    check_covariance!();

    fn next(&mut self) -> Option<NodeMut<'_, T>> {
        self.node_id.take().map(|node_id| {
            self.node_id = self.tree.get_node_relatives(node_id).next_sibling;
            NodeMut::new(node_id, self.tree)
        })
    }
}

/// Depth-first pre-order iterator
pub struct PreOrderMut<'a, T> {
    queue: Vec<NodeId>,
    tree: &'a mut Tree<T>,
}

impl<'a, T> PreOrderMut<'a, T> {
    pub(crate) fn new(node_id: NodeId, tree: &'a mut Tree<T>) -> PreOrderMut<'a, T> {
        PreOrderMut {
            queue: vec![node_id],
            tree,
        }
    }
}

impl<'this, 'lend, T> Lending<'lend> for PreOrderMut<'this, T> {
    type Lend = NodeMut<'lend, T>;
}

impl<'this, T> Lender for PreOrderMut<'this, T> {
    check_covariance!();

    fn next(&mut self) -> Option<NodeMut<'_, T>> {
        let node_id = self.queue.pop()?;
        let Relatives {
            first_child,
            next_sibling,
            ..
        } = self.tree.get_node_relatives(node_id);

        if let Some(next_sibling) = next_sibling {
            self.queue.push(next_sibling);
        }

        if let Some(first_child) = first_child {
            self.queue.push(first_child);
        }

        Some(NodeMut::new(node_id, self.tree))
    }
}

/// Depth-first post-order iterator
pub struct PostOrderMut<'a, T> {
    queue: Vec<NodeId>,
    tree: &'a mut Tree<T>,
}

impl<'a, T> PostOrderMut<'a, T> {
    pub(crate) fn new(node_id: NodeId, tree: &'a mut Tree<T>) -> PostOrderMut<'a, T> {
        let mut iter = PostOrderMut {
            queue: Vec::new(),
            tree,
        };
        iter.add_node_and_descendants_to_queue(node_id);
        iter
    }

    fn add_node_and_descendants_to_queue(&mut self, mut node_id: NodeId) {
        loop {
            self.queue.push(node_id);
            let Some(node) = self.tree.get_node(node_id) else {
                unreachable!();
            };

            match node.relatives.first_child {
                Some(next) => node_id = next,
                None => break,
            }
        }
    }
}

impl<'this, 'lend, T> Lending<'lend> for PostOrderMut<'this, T> {
    type Lend = NodeMut<'lend, T>;
}

impl<'this, T> Lender for PostOrderMut<'this, T> {
    check_covariance!();

    fn next(&mut self) -> Option<NodeMut<'_, T>> {
        let node_id = self.queue.pop()?;

        if !self.queue.is_empty() // don't iterate through the siblings of the first node
            && let Some(next_sibling) = self.tree.get_node_relatives(node_id).next_sibling
        {
            self.add_node_and_descendants_to_queue(next_sibling);
        }

        Some(NodeMut::new(node_id, self.tree))
    }
}
