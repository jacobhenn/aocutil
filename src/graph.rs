use std::{
    cmp::Ordering,
    collections::{BinaryHeap, HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    ops::Add,
};

use tracing::trace;

pub trait Graph {
    type Distance;

    type Node;

    fn neighbors<'a>(
        &'a self,
        center: &'a Self::Node,
    ) -> impl Iterator<Item = (Self::Distance, Self::Node)> + 'a;

    // TODO: add documentation
    fn shortest_paths_dijkstra(
        &self,
        start: Self::Node,
        is_target: impl Fn(&Self::Node) -> bool,
        cmp: impl Fn(&Self::Distance, &Self::Distance) -> Ordering + Clone,
    ) -> (
        Option<Self::Node>,
        HashMap<Self::Node, (Self::Distance, Self::Node)>,
    )
    where
        // TODO: remove debug bounds
        Self::Node: Eq + Hash + Clone + Debug,
        Self::Distance: Ord + Add<Output = Self::Distance> + Clone + Debug,
    {
        let mut spanning_tree: HashMap<Self::Node, (Self::Distance, Self::Node)> = HashMap::new();

        // TODO: does this need to be here?
        let mut visited: HashSet<Self::Node> = HashSet::new();

        let mut frontier = BinaryHeap::new();

        for (distance, neighbor) in self.neighbors(&start) {
            frontier.push(RevCmpBy {
                key: distance.clone(),
                val: neighbor.clone(),
                cmp: cmp.clone(),
            });

            spanning_tree.insert(neighbor, (distance, start.clone()));
        }

        while let Some(RevCmpBy {
            key: current_node_dist,
            val: current_node,
            ..
        }) = frontier.pop()
        {
            trace!("looking at frontier entry: {current_node:?} at dist {current_node_dist:?}");

            if is_target(&current_node) {
                return (Some(current_node), spanning_tree);
            }

            // Check if this is an old frontier entry that should be ignored

            if current_node == start {
                continue;
            }

            let (current_node_best_dist, _) = spanning_tree.get(&current_node).expect(
                "all values in the frontier should have had their distances processed already",
            );

            // TODO: is this check necessary given `visited`?
            if &current_node_dist > current_node_best_dist {
                continue;
            }

            if !visited.insert(current_node.clone()) {
                continue;
            }

            // trace!("  (valid)");

            // Update neighbors

            for (neighbor_dist, neighbor) in self.neighbors(&current_node) {
                let neighbor_new_dist = current_node_dist.clone() + neighbor_dist;

                if let Some((neighbor_best_dist, _)) = spanning_tree.get(&neighbor) {
                    if neighbor_best_dist < &neighbor_new_dist {
                        continue;
                    }
                }

                trace!("  found better distance to {neighbor:?}: {neighbor_new_dist:?}");

                spanning_tree.insert(
                    neighbor.clone(),
                    (neighbor_new_dist.clone(), current_node.clone()),
                );

                frontier.push(RevCmpBy {
                    key: neighbor_new_dist,
                    val: neighbor,
                    cmp: cmp.clone(),
                });
            }
        }

        (None, spanning_tree)
    }
}

/// A container for which all comparison operations use a key, and comparison
/// is reversed. This is mainly just a helper type for making Dijkstra's algorithm cleaner.
struct RevCmpBy<K, V, F> {
    key: K,
    val: V,
    cmp: F,
}

impl<K, V, F> PartialEq for RevCmpBy<K, V, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    fn eq(&self, other: &Self) -> bool {
        (self.cmp)(&self.key, &other.key).is_eq()
    }
}

impl<K, V, F> Eq for RevCmpBy<K, V, F> where F: Fn(&K, &K) -> Ordering {}

impl<K, V, F> Ord for RevCmpBy<K, V, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    fn cmp(&self, other: &Self) -> Ordering {
        (self.cmp)(&self.key, &other.key).reverse()
    }
}

impl<K, V, F> PartialOrd for RevCmpBy<K, V, F>
where
    F: Fn(&K, &K) -> Ordering,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some((self.cmp)(&self.key, &other.key).reverse())
    }
}
