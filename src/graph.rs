use std::collections::HashMap;

pub trait Graph {
    type Location;

    type Node;

    type Weight;

    type Neighbors<'a>: Iterator<Item = (Self::Weight, Self::Location)>
    where
        Self: 'a;

    fn get(&self, loc: Self::Location) -> Option<&Self::Node>;

    fn get_mut(&mut self, loc: Self::Location) -> Option<&mut Self::Node>;

    fn neighbors(&self, loc: Self::Location) -> Self::Neighbors<'_>;

    // fn shortest_path(
    //     &self,
    //     source: Self::Location,
    //     target: impl Fn(&Self::Node) -> bool,
    // ) -> impl Iterator<Item = (Self::Weight, Self::Location)>
    // where
    //     Self: Sized,
    //     Self::Weight: PartialOrd,
    // {
    //     let mut previous: HashMap<Self::Location, (Self::Weight, Self::Location)> = HashMap::new();
    //     todo!()
    // }
}

pub struct DijkstraPath<G: Graph> {
    path: HashMap<G::Location, (G::Weight, G::Location)>,
    cursor: G::Location,
}
