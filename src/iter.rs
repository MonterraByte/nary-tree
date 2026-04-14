use crate::NodeId;
use crate::node::*;
use crate::tree::Tree;

// todo: document this

pub struct Ancestors<'a, T> {
    node_id: Option<NodeId>,
    tree: &'a Tree<T>,
}

impl<'a, T> Ancestors<'a, T> {
    pub(crate) fn new(node_id: Option<NodeId>, tree: &'a Tree<T>) -> Ancestors<'a, T> {
        Ancestors { node_id, tree }
    }
}

impl<'a, T> Iterator for Ancestors<'a, T> {
    type Item = NodeRef<'a, T>;

    fn next(&mut self) -> Option<NodeRef<'a, T>> {
        self.node_id
            .take()
            .and_then(|node_id| self.tree.get_node_relatives(node_id).parent)
            .map(|id| {
                self.node_id = Some(id);
                NodeRef::new(id, self.tree)
            })
    }
}

// possibly re-name this, not sure how I feel about it
pub struct NextSiblings<'a, T> {
    node_id: Option<NodeId>,
    tree: &'a Tree<T>,
}

impl<'a, T> NextSiblings<'a, T> {
    pub(crate) fn new(node_id: Option<NodeId>, tree: &'a Tree<T>) -> NextSiblings<'a, T> {
        NextSiblings { node_id, tree }
    }
}

impl<'a, T> Iterator for NextSiblings<'a, T> {
    type Item = NodeRef<'a, T>;

    fn next(&mut self) -> Option<NodeRef<'a, T>> {
        self.node_id.take().map(|node_id| {
            self.node_id = self.tree.get_node_relatives(node_id).next_sibling;
            NodeRef::new(node_id, self.tree)
        })
    }
}

/// Depth-first pre-order iterator
pub struct PreOrder<'a, T> {
    queue: PreOrderQueue,
    tree: &'a Tree<T>,
}

impl<'a, T> PreOrder<'a, T> {
    pub(crate) fn new(node_id: NodeId, tree: &'a Tree<T>) -> PreOrder<'a, T> {
        PreOrder {
            queue: PreOrderQueue::new(node_id),
            tree,
        }
    }
}

pub(crate) struct PreOrderQueue(Vec<NodeId>);

impl PreOrderQueue {
    pub fn new(node_id: NodeId) -> Self {
        Self(vec![node_id])
    }

    pub fn next<T>(&mut self, tree: &Tree<T>) -> Option<NodeId> {
        let node_id = self.0.pop()?;
        let Relatives {
            first_child,
            next_sibling,
            ..
        } = tree.get_node_relatives(node_id);

        if let Some(next_sibling) = next_sibling {
            self.0.push(next_sibling);
        }

        if let Some(first_child) = first_child {
            self.0.push(first_child);
        }

        Some(node_id)
    }
}

impl<'a, T> Iterator for PreOrder<'a, T> {
    type Item = NodeRef<'a, T>;

    fn next(&mut self) -> Option<NodeRef<'a, T>> {
        let node_id = self.queue.next(self.tree)?;
        Some(NodeRef::new(node_id, self.tree))
    }
}

/// Depth-first post-order iterator
pub struct PostOrder<'a, T> {
    queue: PostOrderQueue,
    tree: &'a Tree<T>,
}

impl<'a, T> PostOrder<'a, T> {
    pub(crate) fn new(node_id: NodeId, tree: &'a Tree<T>) -> PostOrder<'a, T> {
        Self {
            queue: PostOrderQueue::new(node_id, tree),
            tree,
        }
    }
}

pub(crate) struct PostOrderQueue(Vec<NodeId>);

impl PostOrderQueue {
    pub fn new<T>(node_id: NodeId, tree: &Tree<T>) -> Self {
        let mut queue = Self(Vec::new());
        queue.add_node_and_descendants_to_queue(node_id, tree);
        queue
    }

    pub fn add_node_and_descendants_to_queue<T>(&mut self, mut node_id: NodeId, tree: &Tree<T>) {
        loop {
            self.0.push(node_id);
            let Some(node) = tree.get_node(node_id) else {
                unreachable!();
            };

            match node.relatives.first_child {
                Some(next) => node_id = next,
                None => break,
            }
        }
    }

    pub fn pop(&mut self) -> Option<NodeId> {
        self.0.pop()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<'a, T> Iterator for PostOrder<'a, T> {
    type Item = NodeRef<'a, T>;

    fn next(&mut self) -> Option<NodeRef<'a, T>> {
        let node_id = self.queue.pop()?;

        if !self.queue.is_empty() // don't iterate through the siblings of the first node
            && let Some(next_sibling) = self.tree.get_node_relatives(node_id).next_sibling
        {
            self.queue
                .add_node_and_descendants_to_queue(next_sibling, self.tree);
        }

        Some(NodeRef::new(node_id, self.tree))
    }
}

/// Depth-first level-order iterator
pub struct LevelOrder<'a, T> {
    start: NodeRef<'a, T>,
    levels: Vec<(NodeId, NextSiblings<'a, T>)>,
    tree: &'a Tree<T>,
}

impl<'a, T> LevelOrder<'a, T> {
    pub(crate) fn new(node: &NodeRef<'a, T>, tree: &'a Tree<T>) -> LevelOrder<'a, T> {
        let start = tree
            .get(node.node_id())
            .expect("getting node of node ref id");
        let levels = Vec::new();
        LevelOrder {
            start,
            levels,
            tree,
        }
    }
}

impl<'a, T> Iterator for LevelOrder<'a, T> {
    type Item = NodeRef<'a, T>;

    fn next(&mut self) -> Option<NodeRef<'a, T>> {
        if self.levels.is_empty() {
            self.levels.push((
                self.start.node_id(),
                NextSiblings::new(self.start.first_child_id(), self.tree),
            ));
            let node = self
                .tree
                .get(self.start.node_id())
                .expect("getting node of existing node ref id");
            Some(node)
        } else {
            let mut on_level = self.levels.len();
            let next_level = on_level + 1;
            let mut level = on_level;
            while level > 0 {
                if let Some(node) = self.levels.last_mut().expect("non-empty levels").1.next() {
                    if level >= on_level {
                        return Some(node);
                    } else {
                        self.levels.push((
                            node.node_id(),
                            NextSiblings::new(node.first_child_id(), self.tree),
                        ));
                        level += 1;
                    }
                } else {
                    let (node_id, _) = self.levels.pop().expect("on level > 0");
                    if let Some(next) = self.levels.last_mut().and_then(|level| level.1.next()) {
                        self.levels.push((
                            next.node_id(),
                            NextSiblings::new(next.first_child_id(), self.tree),
                        ));
                    } else if level == 1 {
                        if on_level < next_level {
                            on_level += 1;
                            let node = self
                                .tree
                                .get(node_id)
                                .expect("getting node of existing node ref id");
                            self.levels.push((
                                node.node_id(),
                                NextSiblings::new(node.first_child_id(), self.tree),
                            ));
                        } else {
                            break;
                        }
                    } else {
                        level -= 1;
                    }
                }
            }
            None
        }
    }
}
