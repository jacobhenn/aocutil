use aocutil::prelude::*;

struct GridGraph(Grid<u32>);

impl Graph for GridGraph {
    type Distance = u32;

    type Node = GridPos;

    fn neighbors<'a>(
        &'a self,
        center: &'a GridPos,
    ) -> impl Iterator<Item = (Self::Distance, Self::Node)> + 'a {
        RookDirection::iter()
            .map(|d| *center + d)
            .filter_map(|n| self.0.get(n).map(|w| (*w, n)))
    }
}

#[test]
fn test_shortest_path() {
    let _ = aocutil::log::test_subscriber().init();

    let grid: Grid<u32> = vec![vec![1, 0, 3], vec![0, 9, 0], vec![4, 0, 7]]
        .into_iter()
        .collect();
    let graph = GridGraph(grid);
    let (_, spanning_tree) = graph.shortest_paths_dijkstra(v!(0, 0), |&v| v == v!(2, 2));

    assert_eq!(spanning_tree.get(&v!(2, 2)).unwrap().0, 10);
}
