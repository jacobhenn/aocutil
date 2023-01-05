use std::{
    cmp::Ordering,
    collections::{BinaryHeap, HashMap},
    fmt::Debug,
    hash::Hash,
    marker::PhantomData,
    mem,
    ops::Add,
};

use tracing::{debug, trace, trace_span};

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
        // TODO: remove this Clone bound
        // TODO: remove this Debug bound (for logging)
        Self: Sized + Hash + Eq + Clone + Debug,
        Self::Distance: Add<Output = Self::Distance> + Clone,
    {
        let mut distances: HashMap<Self, Self::Distance> = HashMap::new();

        let mut predecessors: HashMap<Self, Self> = HashMap::new();

        let mut frontier: BinaryHeap<CmpByKey<Self::Distance, Self, Cmp>> = BinaryHeap::new();

        for (distance, neighbor) in self.clone().neighbors() {
            distances.insert(neighbor.clone(), distance.clone());
            predecessors.insert(neighbor.clone(), self.clone());
            frontier.push(CmpByKey {
                key: distance,
                val: neighbor,
                cmp,
            })
        }

        let mut visited_ = HashMap::new();
        let mut iterations_ = 0;

        // TODO: figure out setup

        while let Some(CmpByKey {
            key: distance,
            val: center,
            ..
        }) = frontier.pop()
        {
            let s = trace_span!("center", ?center);
            let _g = s.enter();
            trace!(frontier.len = ?frontier.len());

            iterations_ += 1;
            *visited_.entry(center.clone()).or_insert(0) += 1;

            if is_target(&center) {
                debug!(?iterations_, ?visited_);
                return Some((distance, Path::new(predecessors, center)));
            }

            if distances
                .get(&center)
                .map(|prev_distance| cmp(&distance, prev_distance).is_gt())
                .unwrap_or(false)
            {
                trace!("skipping");
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
                let neighbor_distance = distances.get(&neighbor);
                if neighbor_distance
                    .map(|d| cmp(&alternate_distance, d).is_lt())
                    .unwrap_or(true)
                {
                    distances.insert(neighbor.clone(), alternate_distance.clone());
                    predecessors.insert(neighbor.clone(), center.clone());
                    frontier.push(CmpByKey {
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

/// A container for which all comparison operations go through a custom comparator.
struct CmpByKey<K, V, F> {
    key: K,
    val: V,
    cmp: F,
}

impl<K, V, F> PartialEq for CmpByKey<K, V, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    fn eq(&self, other: &Self) -> bool {
        (self.cmp)(&self.key, &other.key) == Ordering::Equal
    }
}

impl<K, V, F> Eq for CmpByKey<K, V, F> where F: Fn(&K, &K) -> Ordering {}

impl<K, V, F> PartialOrd for CmpByKey<K, V, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some((self.cmp)(&self.key, &other.key))
    }
}

impl<K, V, F> Ord for CmpByKey<K, V, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    fn cmp(&self, other: &Self) -> Ordering {
        (self.cmp)(&self.key, &other.key)
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
