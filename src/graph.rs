use std::{
    cmp::Ordering,
    collections::{BinaryHeap, HashMap},
    fmt::Debug,
    hash::Hash,
    marker::PhantomData,
    mem,
    ops::Add,
    rc::Rc,
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
        Self: Sized + Hash + Eq,
        Self::Distance: Add<Output = Self::Distance> + Clone,
    {
        let mut distances: HashMap<Rc<Self>, Self::Distance> = HashMap::new();

        let mut predecessors: HashMap<Rc<Self>, Rc<Self>> = HashMap::new();

        let mut frontier: BinaryHeap<RevCmpByKey<Self::Distance, Rc<Self>, Cmp>> =
            BinaryHeap::new();

        let this = Rc::new(self);

        for (distance, neighbor) in this.neighbors() {
            let neighbor = Rc::new(neighbor);
            distances.insert(Rc::clone(&neighbor), distance.clone());
            predecessors.insert(Rc::clone(&neighbor), Rc::clone(&neighbor));
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
                let neighbor = Rc::new(neighbor);
                let alternate_distance = center_distance.clone() + edge_weight;
                if distances
                    .get(&neighbor)
                    .map(|d| cmp(&alternate_distance, d).is_lt())
                    .unwrap_or(true)
                {
                    distances.insert(Rc::clone(&neighbor), alternate_distance.clone());
                    predecessors.insert(Rc::clone(&neighbor), Rc::clone(&center));
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
/// is reversed. This is mainly just a helper type for making Dijkstra's algorithm cleaner.
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
    path: HashMap<Rc<C>, Rc<C>>,
    cursor: Rc<C>,
    _marker: PhantomData<&'a ()>,
}

impl<'a, C: GraphCursor<'a>> Path<'a, C> {
    pub fn new(path: HashMap<Rc<C>, Rc<C>>, start: Rc<C>) -> Self {
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
    type Item = Rc<C>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut next = self.path.remove(&self.cursor)?;
        mem::swap(&mut next, &mut self.cursor);
        Some(next)
    }
}
