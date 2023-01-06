use std::{
    cmp::Ordering,
    collections::{BinaryHeap, HashMap},
    hash::Hash,
    marker::PhantomData,
    mem,
    ops::Add,
};

pub trait GraphCursor<'a>
where
    Self: 'a,
{
    type Distance;

    type Neighbors<'b>: Iterator<Item = (Self::Distance, Self)>
    where
        Self: 'b;

    fn neighbors<'b>(&'b self) -> Self::Neighbors<'b>;

    /// Find the shortest path (under comparator `cmp`) to an arbitrary node which satisfies
    /// `is_target`. Returns the total length of the path and the path itself. Note that the
    /// returned path will iterate in reverse order (from the target node to the source). If all
    /// nodes in the graph are exhausted and the target has not been found, returns `None`.
    fn shortest_path_with<IsTarget, Cmp>(
        self,
        is_target: IsTarget,
        cmp: Cmp,
    ) -> Option<(Self::Distance, Path<'a, Self>)>
    where
        IsTarget: Fn(&Self) -> bool,
        Cmp: Fn(&Self::Distance, &Self::Distance) -> Ordering + Copy,
        // TODO: remove this Clone bound (use a slab)
        Self: Sized + Hash + Eq + Clone,
        Self::Distance: Add<Output = Self::Distance> + Clone,
    {
        let mut distances: HashMap<Self, Self::Distance> = HashMap::new();

        let mut predecessors: HashMap<Self, Self> = HashMap::new();

        let mut frontier: BinaryHeap<RevCmpByKey<Self::Distance, Self, Cmp>> = BinaryHeap::new();

        for (distance, neighbor) in self.clone().neighbors() {
            distances.insert(neighbor.clone(), distance.clone());
            predecessors.insert(neighbor.clone(), self.clone());
            frontier.push(RevCmpByKey {
                key: distance,
                val: neighbor,
                cmp,
            })
        }

        while let Some(RevCmpByKey {
            key: distance,
            val: center,
            ..
        }) = frontier.pop()
        {
            if is_target(&center) {
                return Some((distance, Path::new(predecessors, center)));
            }

            if distances
                .get(&center)
                .map(|current_distance| cmp(&distance, current_distance).is_gt())
                .unwrap_or(false)
            {
                continue;
            }

            let center_distance = distances
                .get(&center)
                .expect(
                    "all values in the frontier should have had their distances processed already",
                )
                .clone();
            for (edge_weight, neighbor) in center.neighbors() {
                let alternate_distance = center_distance.clone() + edge_weight;
                if distances
                    .get(&neighbor)
                    .map(|d| cmp(&alternate_distance, d).is_lt())
                    .unwrap_or(true)
                {
                    distances.insert(neighbor.clone(), alternate_distance.clone());
                    predecessors.insert(neighbor.clone(), center.clone());
                    frontier.push(RevCmpByKey {
                        key: alternate_distance,
                        val: neighbor,
                        cmp,
                    });
                }
            }
        }

        None
    }
}

/// A container for which all comparison operations go through a custom comparator, whose output
/// is reversed. This is mainly just a helper type for making Dijkstra's algorithm neater.
struct RevCmpByKey<K, V, F> {
    key: K,
    val: V,
    cmp: F,
}

impl<K, V, F> PartialEq for RevCmpByKey<K, V, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    fn eq(&self, other: &Self) -> bool {
        (self.cmp)(&self.key, &other.key) == Ordering::Equal
    }
}

impl<K, V, F> Eq for RevCmpByKey<K, V, F> where F: Fn(&K, &K) -> Ordering {}

impl<K, V, F> Ord for RevCmpByKey<K, V, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    fn cmp(&self, other: &Self) -> Ordering {
        (self.cmp)(&self.key, &other.key).reverse()
    }
}

impl<K, V, F> PartialOrd for RevCmpByKey<K, V, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

pub struct Path<'a, C: GraphCursor<'a>> {
    path: HashMap<C, C>,
    cursor: C,
    _marker: PhantomData<&'a ()>,
}

impl<'a, C: GraphCursor<'a>> Path<'a, C> {
    pub fn new(path: HashMap<C, C>, start: C) -> Self {
        Self {
            path,
            cursor: start,
            _marker: PhantomData,
        }
    }
}

impl<'a, C: GraphCursor<'a>> Iterator for Path<'a, C>
where
    C: Eq + Hash,
{
    type Item = C;

    fn next(&mut self) -> Option<Self::Item> {
        let mut next = self.path.remove(&self.cursor)?;
        mem::swap(&mut next, &mut self.cursor);
        Some(next)
    }
}
