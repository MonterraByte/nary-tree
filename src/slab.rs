#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Index {
    pub(crate) index: usize,
    generation: usize,
}

impl Index {
    fn new(index: usize, generation: usize) -> Self {
        Self { index, generation }
    }
}

#[derive(Debug)]
struct SlabNode<T> {
    data: T,
    generation: usize,
}

impl<T> SlabNode<T> {
    fn new(data: T, generation: usize) -> Self {
        Self { data, generation }
    }
}

#[derive(Debug)]
pub(crate) struct Slab<T> {
    slab: slab_tokio::Slab<SlabNode<T>>,
    generation: usize,
}

impl<T> Slab<T> {
    pub(crate) fn new(capacity: usize) -> Self {
        Self {
            slab: slab_tokio::Slab::with_capacity(capacity),
            generation: 0,
        }
    }

    pub(crate) fn capacity(&self) -> usize {
        self.slab.capacity()
    }

    pub(crate) fn insert(&mut self, data: T) -> Index {
        Index::new(
            self.slab.insert(SlabNode::new(data, self.generation)),
            self.generation,
        )
    }

    pub(crate) fn try_remove(&mut self, index: Index) -> Option<T> {
        if let Some(to_remove) = self.slab.get(index.index)
            && to_remove.generation != index.generation
        {
            return None;
        }
        self.slab.try_remove(index.index).map(|entry| {
            self.next_generation();
            entry.data
        })
    }

    pub(crate) fn get(&self, index: Index) -> Option<&T> {
        if let Some(node) = self.slab.get(index.index) {
            if index.generation != node.generation {
                return None;
            }
            Some(&node.data)
        } else {
            None
        }
    }

    pub(crate) fn get_mut(&mut self, index: Index) -> Option<&mut T> {
        if let Some(node) = self.slab.get_mut(index.index) {
            if index.generation != node.generation {
                return None;
            }
            Some(&mut node.data)
        } else {
            None
        }
    }

    pub(crate) fn shrink_to_fit(&mut self) {
        self.slab.shrink_to_fit();
    }

    #[cfg(feature = "experimental")]
    pub(crate) fn compact<F>(&mut self, mut rekey: F)
    where
        F: FnMut(usize, Index),
    {
        let generation = self.next_generation();
        self.slab.compact(|node, from, to| {
            node.generation = generation;
            rekey(from, Index::new(to, generation));
            true
        });
    }

    fn next_generation(&mut self) -> usize {
        self.generation += 1;
        self.generation
    }
}

#[cfg_attr(tarpaulin, skip)]
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn capacity() {
        let capacity = 5;
        let slab = Slab::<i32>::new(capacity);

        assert_eq!(slab.capacity(), capacity);
        assert_eq!(slab.generation, 0);
    }

    #[test]
    fn insert() {
        let capacity = 2;
        let mut slab = Slab::new(capacity);

        let six = slab.insert(6);

        assert_eq!(slab.generation, 0);
        assert_eq!(slab.slab.len(), 1);
        assert_eq!(slab.capacity(), capacity);

        assert_eq!(six.generation, 0);
        assert_eq!(six.index, 0);

        let seven = slab.insert(7);

        assert_eq!(slab.generation, 0);
        assert_eq!(slab.slab.len(), 2);
        assert_eq!(slab.capacity(), capacity);

        assert_eq!(seven.generation, 0);
        assert_eq!(seven.index, 1);

        let eight = slab.insert(8);

        assert_eq!(slab.generation, 0);
        assert_eq!(slab.slab.len(), 3);
        assert!(slab.capacity() >= capacity);

        assert_eq!(eight.generation, 0);
        assert_eq!(eight.index, 2);
    }

    #[test]
    fn remove_basic() {
        let mut slab = Slab::new(5);
        let six = slab.insert(6);
        let seven = slab.insert(7);
        let eight = slab.insert(8);
        // |6|7|8|

        let seven_rem = slab.try_remove(seven);
        // |6|.|8|
        assert!(seven_rem.is_some());
        assert_eq!(seven_rem.unwrap(), 7);

        assert_eq!(slab.generation, 1);

        let six_slot = slab.slab.get(six.index);
        assert!(six_slot.is_some());
        assert_eq!(six_slot.as_ref().unwrap().data, 6);

        let seven_slot = slab.slab.get(seven.index);
        assert!(seven_slot.is_none());

        let eight_slot = slab.slab.get(eight.index);
        assert!(eight_slot.is_some());
        assert_eq!(eight_slot.as_ref().unwrap().data, 8);
    }

    #[test]
    fn double_remove() {
        let mut slab = Slab::new(5);
        let _six = slab.insert(6);
        let seven = slab.insert(7);
        let _eight = slab.insert(8);
        // |6|7|8|

        let seven_rem = slab.try_remove(seven);
        // |6|.|8|
        assert!(seven_rem.is_some());
        assert_eq!(seven_rem.unwrap(), 7);

        let seven_again = slab.try_remove(seven);
        assert!(seven_again.is_none());
    }

    #[test]
    fn remove_multiple() {
        let mut slab = Slab::new(5);
        let six = slab.insert(6);
        let seven = slab.insert(7);
        let eight = slab.insert(8);
        // |6|7|8|

        let seven_rem = slab.try_remove(seven);
        // |6|.|8|
        assert!(seven_rem.is_some());
        assert_eq!(seven_rem.unwrap(), 7);

        assert_eq!(slab.generation, 1);

        let six_slot = slab.slab.get(six.index);
        assert!(six_slot.is_some());
        assert_eq!(six_slot.as_ref().unwrap().data, 6);

        let seven_slot = slab.slab.get(seven.index);
        assert!(seven_slot.is_none());

        let eight_slot = slab.slab.get(eight.index);
        assert!(eight_slot.is_some());
        assert_eq!(eight_slot.as_ref().unwrap().data, 8);

        let eight_rem = slab.try_remove(eight);
        // |6|.|.|
        assert!(eight_rem.is_some());
        assert_eq!(eight_rem.unwrap(), 8);

        assert_eq!(slab.generation, 2);

        let six_slot = slab.slab.get(six.index);
        assert!(six_slot.is_some());
        assert_eq!(six_slot.as_ref().unwrap().data, 6);

        let seven_slot = slab.slab.get(seven.index);
        assert!(seven_slot.is_none());

        let eight_slot = slab.slab.get(eight.index);
        assert!(eight_slot.is_none());
    }

    #[test]
    fn remove_and_reinsert() {
        let mut slab = Slab::new(5);
        let six = slab.insert(6);
        let seven = slab.insert(7);
        let eight = slab.insert(8);
        // |6|7|8|

        let seven_rem = slab.try_remove(seven);
        // |6|.|8|
        assert!(seven_rem.is_some());
        assert_eq!(seven_rem.unwrap(), 7);

        assert_eq!(slab.generation, 1);

        let eight_rem = slab.try_remove(eight);
        // |6|.|.|
        assert!(eight_rem.is_some());
        assert_eq!(eight_rem.unwrap(), 8);

        assert_eq!(slab.generation, 2);

        let nine = slab.insert(9);
        // |6|.|9|
        assert_eq!(nine.index, 2);
        assert_eq!(nine.generation, 2);

        let eight_again = slab.try_remove(eight);
        assert!(eight_again.is_none());

        let six_slot = slab.slab.get(six.index);
        assert!(six_slot.is_some());
        assert_eq!(six_slot.as_ref().unwrap().data, 6);

        let seven_slot = slab.slab.get(seven.index);
        assert!(seven_slot.is_none());

        let nine_slot = slab.slab.get(nine.index);
        assert!(nine_slot.is_some());
        assert_eq!(nine_slot.as_ref().unwrap().data, 9);
    }

    #[test]
    fn remove_with_bad_index() {
        let mut slab = Slab::new(5);
        let six = slab.insert(6);
        let seven = slab.insert(7);
        let mut eight = slab.insert(8);
        // |6|7|8| value

        assert_ne!(six.index, usize::MAX);
        assert_ne!(seven.index, usize::MAX);
        assert_ne!(eight.index, usize::MAX);

        eight.index = usize::MAX;

        let eight_rem = slab.try_remove(eight);
        assert!(eight_rem.is_none());
    }

    #[test]
    fn get() {
        let mut slab = Slab::new(5);

        let six = slab.insert(6);
        assert_eq!(six.generation, 0);

        let seven = slab.insert(7);
        assert_eq!(seven.generation, 0);

        let six_ref = slab.get(six);
        assert!(six_ref.is_some());
        assert_eq!(six_ref.unwrap(), &6);

        slab.try_remove(six);

        let six_ref = slab.get(six);
        assert!(six_ref.is_none());

        let eight = slab.insert(8);
        assert_eq!(eight.generation, 1);

        let eight_ref = slab.get(eight);
        assert!(eight_ref.is_some());
        assert_eq!(eight_ref.unwrap(), &8);

        let six_ref = slab.get(six);
        assert!(six_ref.is_none());
    }

    #[test]
    fn get_mut() {
        let mut slab = Slab::new(5);

        let six = slab.insert(6);
        assert_eq!(six.generation, 0);

        let seven = slab.insert(7);
        assert_eq!(seven.generation, 0);

        let six_mut = slab.get_mut(six);
        assert!(six_mut.is_some());

        let six_mut = six_mut.unwrap();
        assert_eq!(six_mut, &mut 6);

        *six_mut = 60;
        assert_eq!(six_mut, &mut 60);

        slab.try_remove(six);

        let six_ref = slab.get_mut(six);
        assert!(six_ref.is_none());

        let eight = slab.insert(8);
        assert_eq!(eight.generation, 1);

        let eight_ref = slab.get_mut(eight);
        assert!(eight_ref.is_some());
        assert_eq!(eight_ref.unwrap(), &mut 8);

        let six_ref = slab.get_mut(six);
        assert!(six_ref.is_none());
    }
}
