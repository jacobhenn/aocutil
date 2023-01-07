use std::{
    cmp::Ordering,
    collections::{BinaryHeap, HashMap},
    hash::Hash,
    mem::ManuallyDrop,
    ops::Add,
    ptr,
};

use indexmap::IndexSet;

pub trait Graph {
    type Distance;

    type Node;

    type Neighbors<'a>: Iterator<Item = (Self::Distance, Self::Node)>
    where
        Self: 'a;

    fn neighbors<'a>(&'a self, center: &'a Self::Node) -> Self::Neighbors<'a>;

    /// Find the shortest path (under comparator `cmp`) to an arbitrary node which satisfies
    /// `is_target`. Returns the total length of the path and the path itself. Note that the
    /// returned path will iterate in reverse order (from the target node to the source). If all
    /// nodes in the graph are exhausted and the target has not been found, returns `None`.
    fn shortest_path<'a>(
        &'a self,
        start: &'a Self::Node,
        is_target: impl Fn(&Self::Node) -> bool,
        cmp: impl Fn(&Self::Distance, &Self::Distance) -> Ordering + Copy,
    ) -> Option<Path<'a, Self>>
    where
        Self::Node: Eq + Hash,
        Self::Distance: Add<Output = Self::Distance> + Clone,
    {
        let mut nodes: IndexSet<Self::Node> = IndexSet::new();

        let mut distances: HashMap<usize, Self::Distance> = HashMap::new();

        let mut predecessors: HashMap<usize, Option<usize>> = HashMap::new();

        let mut frontier = BinaryHeap::new();

        for (distance, neighbor) in self.neighbors(start) {
            let (neighbor_key, _) = nodes.insert_full(neighbor);

            distances.insert(neighbor_key, distance.clone());
            predecessors.insert(neighbor_key, None);
            frontier.push(RevCmpByKey {
                key: distance,
                val: neighbor_key,
                cmp,
            })
        }

        while let Some(RevCmpByKey {
            key: distance,
            val: center_idx,
            ..
        }) = frontier.pop()
        {
            let center = nodes
                .get_index(center_idx)
                .expect("frontier nodes should have been added to the set");

            if is_target(&center) {
                return Some(Path::new(nodes, predecessors, start, distances, center_idx));
            }

            let center_distance = distances
                .get(&center_idx)
                .expect(
                    "all values in the frontier should have had their distances processed already",
                )
                .clone();

            if cmp(&distance, &center_distance).is_gt() {
                continue;
            }

            // SAFETY: this read leaves us with the obligations to prevent a double-free of
            // `center`, and to act as though it has been moved out of `nodes`. wrapping it in a
            // `ManuallyDrop` takes care of the frist condition, and so we just have to be careful
            // about uses of `nodes` from now until `center` is forgotten.
            let center = ManuallyDrop::new(unsafe { ptr::read(center) });

            for (edge_weight, neighbor) in self.neighbors(&center) {
                let (neighbor_idx, _) = nodes.insert_full(neighbor);

                let alternate_distance = center_distance.clone() + edge_weight;
                if distances
                    .get(&neighbor_idx)
                    .map(|d| cmp(&alternate_distance, d).is_lt())
                    .unwrap_or(true)
                {
                    distances.insert(neighbor_idx, alternate_distance.clone());
                    predecessors.insert(neighbor_idx, Some(center_idx));
                    frontier.push(RevCmpByKey {
                        key: alternate_distance,
                        val: neighbor_idx,
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

/// # Properties
///
/// - there are no cycles in `predecessors`
/// - all indices which appear as keys in `predecessors`, `cursor` or `distances` begin as valid
/// indices into `nodes`. when `next` is called, `cursor` ceases to be a valid index (at least in
/// pretend land).
#[derive(Debug, Clone)]
pub struct Path<'a, G: Graph + ?Sized> {
    nodes: IndexSet<G::Node>,
    swapped_nodes: Vec<usize>,
    original_len: usize,
    predecessors: HashMap<usize, Option<usize>>,
    start: &'a G::Node,
    distances: HashMap<usize, G::Distance>,
    cursor: Option<usize>,
    done: bool,
}

// TODO: figure out where i should `expect` versus `try` down below

impl<'a, G: Graph + ?Sized> Path<'a, G> {
    pub fn new(
        nodes: IndexSet<G::Node>,
        predecessors: HashMap<usize, Option<usize>>,
        start: &'a G::Node,
        distances: HashMap<usize, G::Distance>,
        cursor: usize,
    ) -> Self {
        let original_len = nodes.len();
        Self {
            nodes,
            swapped_nodes: Vec::new(),
            original_len,
            predecessors,
            start,
            distances,
            cursor: Some(cursor),
            done: false,
        }
    }

    /// Returns the **remaining** length in the path. This should decrease (according to the
    /// comparator function provided to [`Graph::shortest_path_with`]) every time `next` is called.
    /// Returns `None` if the path has been walked to completion.
    pub fn len(&self) -> Option<&G::Distance>
    where
        G::Node: Eq + Hash,
    {
        self.distances.get(&self.cursor?)
    }
}

// unfortunately, i can't use `Cow` for this, because then i'd have to require that `Node` be
// `ToOwned`.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum MaybeOwned<'a, T> {
    Borrowed(&'a T),
    Owned(T),
}

impl<'a, G: Graph> Iterator for Path<'a, G>
where
    G::Node: Eq + Hash,
{
    type Item = MaybeOwned<'a, G::Node>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        
        let Some(mut idx) = self.cursor
        else { 
            self.done = true;
            return Some(MaybeOwned::Borrowed(&self.start));
        };

        self.cursor = self
            .predecessors
            .remove(&idx)
            .expect("all nodes should have a predecessor");

        self.swapped_nodes.push(idx);
        while idx >= self.nodes.len() {
            idx = self.swapped_nodes[self.original_len - idx];
        }

        Some(MaybeOwned::Owned(
            self.nodes
                .swap_remove_index(idx)
                .expect("node set should be populated"),
        ))
    }
}
