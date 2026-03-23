pub use lender::Lender;
use lender::{Lending, check_covariance};

use crate::iter::{PostOrderQueue, PreOrderQueue};
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
        self.node_id.take().and_then(|node_id| {
            self.node_id = self
                .tree
                .get_node(node_id)
                .and_then(|node| node.relatives.next_sibling);
            self.tree.get_mut(node_id)
        })
    }
}

/// Depth-first pre-order iterator
pub struct PreOrderMut<'a, T> {
    queue: PreOrderQueue,
    tree: &'a mut Tree<T>,
}

impl<'a, T> PreOrderMut<'a, T> {
    pub(crate) fn new(node_id: NodeId, tree: &'a mut Tree<T>) -> PreOrderMut<'a, T> {
        PreOrderMut {
            queue: PreOrderQueue::new(node_id),
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
        let node_id = self.queue.next(self.tree)?;
        Some(NodeMut::new(node_id, self.tree))
    }
}

/// Depth-first post-order iterator
pub struct PostOrderMut<'a, T> {
    queue: PostOrderQueue,
    tree: &'a mut Tree<T>,
}

impl<'a, T> PostOrderMut<'a, T> {
    pub(crate) fn new(node_id: NodeId, tree: &'a mut Tree<T>) -> PostOrderMut<'a, T> {
        Self {
            queue: PostOrderQueue::new(node_id, tree),
            tree,
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
            self.queue
                .add_node_and_descendants_to_queue(next_sibling, self.tree);
        }

        Some(NodeMut::new(node_id, self.tree))
    }
}
