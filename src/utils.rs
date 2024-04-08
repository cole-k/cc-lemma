use std::collections::{HashMap, HashSet, VecDeque};
use colored::Colorize;

use egg::*;
use itertools::Itertools;
use log::warn;
use crate::analysis::{CvecAnalysis, CycleggAnalysis, print_cvec};

fn cartesian_product_helper<T: Clone>(
  vector: &[Vec<T>],
  index: usize,
  current_combination: Vec<T>,
  result: &mut Vec<Vec<T>>,
) {
  if index == vector.len() {
    result.push(current_combination);
  } else {
    for elem in &vector[index] {
      let mut new_combination = current_combination.clone();
      new_combination.push(elem.clone());
      cartesian_product_helper(vector, index + 1, new_combination, result);
    }
  }
}

/// Given a vector of vectors, generates the "cartesian product" of all the vectors.
/// TODO: figure out how to use multi_cartesian_product from itertools instead of writing our own
pub fn cartesian_product<T: Clone>(vector: &[Vec<T>]) -> Vec<Vec<T>> {
  let mut result = Vec::new();
  cartesian_product_helper(vector, 0, Vec::new(), &mut result);
  result
}

/// prints all the expressions in the eclass with the given id
pub fn print_expressions_in_eclass<L: egg::Language + std::fmt::Display, N: egg::Analysis<L>>(
  egraph: &EGraph<L, N>,
  id: Id,
) {
  let extractor = egg::Extractor::new(&egraph, AstSize);

  for node in egraph[id].nodes.iter() {
    let child_rec_exprs: String = node
      .children()
      .iter()
      .map(|child_id| {
        let (_, best_rec_expr) = extractor.find_best(*child_id);
        best_rec_expr.to_string()
      })
      .collect::<Vec<String>>()
      .join(" ");
    if child_rec_exprs.is_empty() {
      println!("({})", node);
    } else {
      println!("({} {})", node, child_rec_exprs);
    }
  }
}
#[derive(Clone)]
struct ExpressionStorage {
  pub exp_storage: Vec<HashSet<String>>
}

impl ExpressionStorage {
  fn new(size_limit: usize) -> Self{
    ExpressionStorage {exp_storage: vec![HashSet::new(); size_limit + 1]}
  }
  fn merge(&mut self, other: &Self) -> bool {
    assert_eq!(self.exp_storage.len(), other.exp_storage.len());
    let mut is_changed = false;
    for (self_set, other_set) in self.exp_storage.iter_mut().zip(other.exp_storage.iter()) {
      for exp in other_set {
        is_changed |= self_set.insert(exp.clone());
      }
    }
    is_changed
  }
  fn print(&self) {
    for exp_set in self.exp_storage.iter() {
      for expression in exp_set.iter() {
        println!("  {}", expression);
      }
    }
  }
  fn construct(size_limit: usize, op: String, sub_storages: &Vec<ExpressionStorage>) -> Self{
    let mut res = ExpressionStorage::new(size_limit);
    if sub_storages.is_empty() {
      if size_limit >= 1 {res.exp_storage.get_mut(1).unwrap().insert(op);}
      return res;
    }
    let size_pool = vec![(0..size_limit).collect::<Vec<usize>>(); sub_storages.len()];
    for size_list in cartesian_product(&size_pool) {
      let total_size: usize = 1 + size_list.iter().sum::<usize>();
      if total_size > size_limit {continue;}
      let res_set: &mut HashSet<String> = res.exp_storage.get_mut(total_size).unwrap();
      let expression_pool: Vec<Vec<String>> = size_list.iter().zip(sub_storages.iter()).map(
        |(size, sub_storage)| {sub_storage.exp_storage[*size].clone().into_iter().collect()}
      ).collect();
      for sub_list in cartesian_product(&expression_pool) {
        let new_exp = format!("({} {})", op, sub_list.join(" "));
        res_set.insert(new_exp);
      }
    }
    res
  }
}

pub fn print_all_expressions_in_egraph (egraph: &EGraph<SymbolLang, CycleggAnalysis>, size_limit: usize) {
  let mut node_info: HashMap<Id, ExpressionStorage> = egraph.classes().map(
    |class| {(class.id, ExpressionStorage::new(size_limit))}
  ).collect();
  let mut is_changed = true;
  while is_changed {
    is_changed = false;
    for class in egraph.classes() {
      for node in class.nodes.iter() {
        //println!("\n\nupdate according to node {}", node);
        //println!("previous info");
        //node_info[&class.id].print();
        let sub_storage = node.children.iter().map(|id| {node_info.get(&egraph.find(*id)).unwrap().clone()}).collect_vec();
        //for (child, child_storage) in sub_storage.iter().enumerate() {
        //  println!("child {}:", child);
        //  child_storage.print();
        //}
        let new_storage = ExpressionStorage::construct(size_limit, node.op.to_string(), &sub_storage);
        //println!("extend with info");
        //new_storage.print();
        is_changed |= node_info.get_mut(&class.id).unwrap().merge(&new_storage);
        //println!("result info");
        // node_info[&class.id].print();
      }
    }
  }
  println!("#nodes: {}, #classes: {}", egraph.total_number_of_nodes(), egraph.number_of_classes());
  for class in egraph.classes() {
    println!("{} {}", "EClass ".cyan(), class.id.to_string().cyan());
    // print_cvec(&egraph.analysis.cvec_analysis, &class.data.cvec_data);
    for enode in class.nodes.iter() {
      println!("  node: {:?}", enode);
    }
    node_info[&class.id].print();
  }
}

/// This is the set of mutually incomparable elements that are the smallest seen
/// so far. We can't just keep one element because partial orders may have
/// multiple (local) minima.
#[derive(Debug, Clone)]
pub struct MinElements<T>
where T: PartialOrd + PartialEq {
  pub elems: Vec<T>,
}

impl<T> Default for MinElements<T>
where T: PartialOrd + PartialEq {
    fn default() -> Self {
        Self { elems: Default::default() }
    }
}

impl<T> MinElements<T>
where T: PartialOrd + PartialEq
{

  pub fn insert(&mut self, elem: T) -> bool {
    // Is it less than any element?
    let mut less_than_some = false;
    // Is it incomparable with all elements?
    let mut incomparable = true;
    self.elems.retain(|e| {
      match elem.partial_cmp(e) {
        Some(std::cmp::Ordering::Less) => {
          // If the new element is less than e, remove it.
          // We will later add the new element.
          less_than_some = true;
          incomparable = false;
          false
        }
        Some(_) => {
          // The new element is not incomparable
          incomparable = false;
          true
        }
        _ => true,
      }
    });
    if less_than_some || incomparable {
      self.elems.push(elem);
    }
    less_than_some || incomparable
  }

  pub fn contains_leq(&self, elem: &T) -> bool {
    self.elems.iter().any(|e| e <= elem)
  }

}

impl<T> Extend<T> for MinElements<T>
where T: PartialOrd + PartialEq {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
      for i in iter {
        self.insert(i);
      }
    }
}

/// This is the set of mutually incomparable elements that are the largest seen
/// so far. We can't just keep one element because partial orders may have
/// multiple (local) maxima.
#[derive(Debug, Clone)]
pub struct MaxElements<T>
where T: PartialOrd + PartialEq {
  pub elems: Vec<T>,
}

impl<T> Default for MaxElements<T>
where T: PartialOrd + PartialEq {
    fn default() -> Self {
        Self { elems: Default::default() }
    }
}

impl<T> MaxElements<T>
where T: PartialOrd + PartialEq
{

  pub fn insert(&mut self, elem: T) -> bool {
    // Is it greater than any element?
    let mut greater_than_some = false;
    // Is it incomparable with all elements?
    let mut incomparable = true;
    self.elems.retain(|e| {
      match elem.partial_cmp(e) {
        Some(std::cmp::Ordering::Greater) => {
          // If the new element is greater than e, remove it. We will later add
          // the new element.
          greater_than_some = true;
          incomparable = false;
          false
        }
        Some(_) => {
          // The new element is not incomparable
          incomparable = false;
          true
        }
        _ => true,
      }
    });
    if greater_than_some || incomparable {
      self.elems.push(elem);
    }
    greater_than_some || incomparable
  }

  pub fn contains_geq(&self, elem: &T) -> bool {
    self.elems.iter().any(|e| e >= elem)
  }

}

impl<T> Extend<T> for MaxElements<T>
where T: PartialOrd + PartialEq {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
      for i in iter {
        self.insert(i);
      }
    }
}

/// Chainsets contain (usually) disjoint chains (total orders) in the partial
/// order.
///
/// Ideally we would have a proper partial order data structure, but for now we
/// fake this by duplicating an element in the rare case that it is comparable
/// with multiple chains.
#[derive(Clone, Debug)]
pub struct ChainSet<T>
where T: PartialOrd + PartialEq + Clone {
  pub chains: Vec<Chain<T>>,
}

impl<T> Default for ChainSet<T>
where T: PartialOrd + PartialEq + Clone {
    fn default() -> Self {
        Self { chains: Default::default() }
    }
}

impl<T> ChainSet<T>
where T: PartialOrd + PartialEq + Clone {
  pub fn new() -> Self {
    ChainSet {
      chains: vec!(),
    }
  }

  pub fn insert(&mut self, elem: T) {
    let mut num_inserts = 0;
    for chain in self.chains.iter_mut() {
      if chain.first().partial_cmp(&elem).is_some() {
        chain.insert(elem.clone());
        num_inserts += 1;
      }
    }
    if num_inserts == 0 {
      self.chains.push(Chain::new(elem))
    } else if num_inserts > 1 {
      warn!("Inserted an element {} times in the chain set.", num_inserts);
    }
  }

  pub fn contains(&self, elem: &T) -> bool {
    self.chains.iter().any(|chain| chain.contains(elem))
  }

  pub fn contains_leq(&self, elem: &T) -> bool {
    self.chains.iter().any(|chain| chain.contains_leq(elem))
  }

  pub fn take_up_to(&mut self, chain_index: usize, chain_elem_index: usize) {
    self.chains[chain_index].chain.truncate(chain_elem_index);
    if self.chains[chain_index].chain.is_empty() {
      self.chains.remove(chain_index);
    }
  }

  pub fn drop_from(&mut self, chain_index: usize, chain_elem_index: usize) {
    let mut new_chain = self.chains[chain_index].chain.split_off(chain_elem_index);
    new_chain.pop_front();

    if new_chain.is_empty() {
      self.chains.remove(chain_index);
    } else {
      self.chains[chain_index] = Chain { chain: new_chain }
    }
  }
}

impl<T> Extend<T> for ChainSet<T>
where T: PartialOrd + PartialEq + Clone {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
      for i in iter {
        self.insert(i);
      }
    }
}

/// Chains are nonempty sets in sorted order
#[derive(Clone, Debug)]
pub struct Chain<T>
where T: PartialOrd + PartialEq {
  pub chain: VecDeque<T>
}

impl<T> Default for Chain<T>
where T: PartialOrd + PartialEq {
    fn default() -> Self {
        Self { chain: Default::default() }
    }
}

impl<T> Chain<T>
where T: PartialOrd + PartialEq {
  pub fn new(elem: T) -> Self {
    Self {
      chain: vec!(elem).into(),
    }
  }
  pub fn insert(&mut self, elem: T) -> bool {
    for (i, self_elem) in self.chain.iter().enumerate() {
      match elem.partial_cmp(self_elem) {
        // Incomparable or already present
        None | Some(std::cmp::Ordering::Equal) => {
          return false;
        }
        Some(std::cmp::Ordering::Less) => {
          self.chain.insert(i, elem);
          return true;
        }
        Some(std::cmp::Ordering::Greater) => {}
      }
    }
    // It must be the greatest element
    self.chain.push_back(elem);
    true
  }

  pub fn contains(&self, elem: &T) -> bool {
    for e in self.chain.iter() {
      match e.partial_cmp(elem) {
        None => {
          return false;
        }
        Some(std::cmp::Ordering::Equal) => {
          return true;
        }
        _ => {}
      }
    }
    false
  }

  pub fn contains_leq(&self, elem: &T) -> bool {
    self.first() <= elem
  }

  pub fn first(&self) -> &T {
    &self.chain.front().unwrap()
  }

}
