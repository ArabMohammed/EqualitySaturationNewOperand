use std::fmt::Debug;
use std::iter::ExactSizeIterator;

use crate::{Id, Language};

/// An equivalence class of enodes.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub struct EClass<L, D> {
    /// This eclass's id.
    pub id: Id,
    /// The equivalent vectorization_equality_saturation_combinationsenodes in this equivalence class.
    pub nodes: Vec<L>,
    /// The analysis data associated with this eclass.
    pub data: D,
    pub(crate) parents: Vec<(L, Id)>,
}

impl<L, D> EClass<L, D> {
    /// Returns `true` if the `eclass` is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Returns the number of enodes in this eclass.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Iterates over the enodes in this eclass.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &L> {
        self.nodes.iter()
    }
    // delete all eclass nodes 
    pub fn clear_nodes(&mut self,length : usize) {
            //self.nodes.clear();
            self.nodes.drain(0..length) ;
       /*  if let Some(last_element) = self.nodes.pop() { // or `clone` method
            self.nodes.clear();
            self.nodes.push(last_element);
        } */
       /*  if self.nodes.len() > 0 {
            let last_element = self.nodes.swap_remove(self.nodes.len() - 1);
            self.nodes.clear();
            self.nodes.push(last_element);
        } */
    }
}

impl<L: Language, D> EClass<L, D> {
    /// Iterates over the childless enodes in this eclass.
    pub fn leaves(&self) -> impl Iterator<Item = &L> {
        self.nodes.iter().filter(|&n| n.is_leaf())
    }

    /// Asserts that the childless enodes in this eclass are unique.
    pub fn assert_unique_leaves(&self)
    where
        L: Language,
    {
        let mut leaves = self.leaves();
        if let Some(first) = leaves.next() {
            assert!(
                leaves.all(|l| l == first),
                "Different leaves in eclass {}: {:?}",
                self.id,
                self.leaves().collect::<indexmap::IndexSet<_>>()
            );
        }
    }
}
