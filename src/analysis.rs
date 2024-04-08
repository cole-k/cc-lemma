use crate::ast::{Context, Env, Type, SSubst, resolve_sexp, Expr, is_constructor, is_var, mangle_name};
use crate::config::CONFIG;
use egg::*;
use itertools::{repeat_n, Itertools};
use rand::{thread_rng, Rng};
use rand::distributions::uniform::SampleUniform;
use rand::distributions::weighted::WeightedIndex;
use rand::distributions::Distribution;
use rand::seq::SliceRandom;
use std::cell::RefCell;
use std::{collections::{BTreeMap, BTreeSet}, iter::zip, str::FromStr};
use symbolic_expressions::Sexp;

// We use an analysis inspired by cvecs from Ruler (https://github.com/uwplse/ruler)
// to help us guess equalities between separate e-classes as lemmas. Because our
// rewrites are simply rules in an e-graph, we don't bother implementing the same
// evaluation code and use an e-graph to evaluate the terms. This allows us to
// store them compactly, too.

pub fn random_term_from_type(
  ty: &Type,
  env: &Env,
  ctx: &Context,
  max_depth: usize,
) -> Sexp {
  random_term_from_type_with_weight::<usize>(ty, env, ctx, max_depth, &BTreeMap::default())
}

/// Generates random terms that are up to `max_depth` deep. Constructors are depth 0.
///
/// The `constructor_weights` should map a type's name to a WeightedIndex whose
/// size is equal to the number of constructors and whose weights are assumed
/// to be in the same order as the constructors. If not present for a type,
/// constructors are sampled uniformly.
///
/// If a type doesn't have a base case, then we will continue to recurse on a
/// random constructor until we find one. In principle this means that we can generate
/// terms with depth bigger than `max_depth`, but I suspect that this will not be
/// much of an issue. If it is, then we will need to precompute the `has_base_case`
/// check for all types and figure out the minimum depth for each type.
pub fn random_term_from_type_with_weight<W>(
  ty: &Type,
  env: &Env,
  ctx: &Context,
  max_depth: usize,
  constructor_weights: &BTreeMap<String, WeightedIndex<W>>,
) -> Sexp
where
  W: SampleUniform + PartialOrd,
{
  let (dt_name, arg_types) = ty.datatype().unwrap();
  let (vars, cons) = env.get(&Symbol::from_str(dt_name).unwrap()).or_else(|| {
    // this should be a type variable we can't look up
    assert!(dt_name.starts_with(char::is_lowercase));
    env.get(&Symbol::from_str(&mangle_name("Bool")).unwrap())
  }).unwrap();
  let type_var_map: SSubst = zip(vars.iter().cloned(), arg_types.iter().map(|arg_type| arg_type.repr.clone())).collect();

  // Has any base cases (depth 0 terms)? This could be precomputed to speed
  // things up.
  let is_base_case = |dt_name: &String, args: &Vec<Type>| -> bool {
    args.iter().all(|name| {!name.to_string().contains(dt_name)})
  } ;
  let has_base_case = cons.iter().any(|con| {
    let con_ty = ctx.get(con).unwrap();
    let (args, _ret) = con_ty.args_ret();
    is_base_case(dt_name, &args)
  });

  let mut rng = thread_rng();

  let weights_opt = constructor_weights.get(dt_name);

  loop {
    let ind = random_constructor_index(weights_opt, cons.len(), &mut rng);
    let con = cons[ind];
    let con_ty = ctx.get(&con).unwrap();
    let (args, _ret) = con_ty.args_ret();
    // If the depth is 0, there is a base case to reach, and we haven't reached
    // one, keep going.
    //
    // NOTE: I think there is the possibility for infinite loops here if the
    // weights are wrong (e.g. base cases all have 0 weights).
    if max_depth == 0 && has_base_case && !is_base_case(dt_name, &args) {
      continue;
    }

    let mut children: Vec<Sexp> = args.iter().map(|arg| {
      // Substitute over the type. This could be more efficient if we skipped
      // when the type_var_map is empty.
      let resolved_arg = Type::new(resolve_sexp(&arg.repr, &type_var_map));
      // We do a saturating subtraction here because max_depth could be 0 if
      // there are no base cases. This is why the max depth might end up
      // greater in a pathological case.
      random_term_from_type_with_weight(&resolved_arg, env, ctx, max_depth.saturating_sub(1), constructor_weights)
    }).collect();

    children.insert(0, Sexp::String(con.to_string()));
    return Sexp::List(children);
  }
}

fn random_constructor_index<W, R>(weights_opt: Option<&WeightedIndex<W>>, num_cons: usize, rng: &mut R) -> usize
where
  W: SampleUniform + PartialOrd,
  R: Rng
{
  weights_opt.map(|weights| {
    weights.sample(rng)
  // else pick at random
  }).unwrap_or_else(|| {
    rng.gen_range(0..num_cons)
  })
}

#[derive(Debug, Clone)]
pub struct CvecAnalysis {
  pub cvec_egraph: RefCell<EGraph<SymbolLang, ()>>,
  // NOTE: It would help if we could somehow cache the random terms we
  // generate for each type and reuse them when making other types.
  //
  // For example, if we generate for Nat: [0, 5, 1, 3, 7]
  //
  // For (List Nat) it would make sense to only use the previous Nats to
  // generate the elements.
  //
  // I didn't do this because it would probably loop infinitely for mutually
  // recursive types - or at least would require some sophisticated analysis.
  /// We will choose randomly from the terms associated with each type to
  /// instantiate a Cvec for a given variable. Each of these vectors
  /// will be of length `num_random_terms_per_type` and as such may
  /// not have distinct Ids.
  type_to_random_terms: Vec<(Type, Vec<Id>)>,
  /// Number of terms in the Cvec. This must be less than or equal to
  /// num_random_terms_per_type.
  cvec_size: usize,
  /// Maximum depth of the term
  term_max_depth: usize,
  /// We try to generate distinct random terms, so if we don't
  /// generate a distinct one, this is how many times we will
  /// try again until we find one.
  num_rolls: usize,
  /// How many random terms will we generate per type?
  num_random_terms_per_type: usize,
  pub reductions: Vec<Rewrite<SymbolLang, ()>>,
  /// This is necessary to avoid infinitely looping when we rebuild the e-graph
  /// analysis for cycles. We will update analyses that have older timestamps, but
  /// break the loop when we try to merge analyses with the same timestamp.
  pub current_timestamp: usize,
  // TODO: Add hashmap from Cvec to Id that we can use to efficiently find
  // candidate equalities.

  // FIXME: it's an implementation detail that we don't thread the global environment
  // and contex through to the CvecAnalysis. It's worth doing that so we can make
  // cvecs variables when they are merged in instead of making their value Stuck until
  // we can set them manually.
  //
  // This will probably allow us to remove the timestamp (almost) entirely
}

impl Default for CvecAnalysis {
  fn default() -> Self {
    Self {
      cvec_egraph: RefCell::new(EGraph::new(())),
      type_to_random_terms: Vec::new(),
      cvec_size: CONFIG.cvec_size,
      term_max_depth: CONFIG.cvec_term_max_depth,
      num_rolls: CONFIG.cvec_num_rolls,
      num_random_terms_per_type: CONFIG.cvec_num_random_terms_per_type,
      reductions: vec!(),
      current_timestamp: 0,
    }
  }
}

impl CvecAnalysis {
  pub fn new(cvec_size: usize, term_max_depth: usize, max_tries_to_make_distinct_term: usize, num_random_terms_per_type: usize, reductions: Vec<Rewrite<SymbolLang, ()>>) -> Self {
    assert!(cvec_size < num_random_terms_per_type, "num_random_terms_per_type must be greater than cvec_size");
    Self {
      cvec_egraph: RefCell::new(EGraph::new(())),
      type_to_random_terms: Vec::new(),
      cvec_size,
      term_max_depth,
      num_rolls: max_tries_to_make_distinct_term,
      num_random_terms_per_type,
      reductions,
      current_timestamp: 0,
    }
  }

  // We have to do this because Sexps aren't orderable or hashable...
  fn lookup_ty(&self, ty: &Type) -> Option<Vec<Id>> {
    for (other_ty, terms) in self.type_to_random_terms.iter() {
      if ty == other_ty {
        return Some(terms.clone());
      }
    }
    None
  }


  /// Returns a vector of length `num_random_terms`. We try to ensure they're
  /// distinct but there's a chance that they aren't.
  fn initialize_ty(&mut self, ty: &Type, env: &Env, ctx: &Context) -> Vec<Id> {
    let mut random_term_ids = Vec::new();
    for _ in 0..self.num_random_terms_per_type {
      let mut try_number = 0;
      loop {
        try_number += 1;
        // For now, we don't pass weights in
        let new_sexp = random_term_from_type(ty, env, ctx, self.term_max_depth);
        let new_term = new_sexp.to_string().parse().unwrap();
        let new_id = self.cvec_egraph.borrow_mut().add_expr(&new_term);
        // If we haven't generated this already or we're out of tries,
        // add the term and break.
        if !random_term_ids.contains(&new_id) || try_number == self.num_rolls {
          random_term_ids.push(new_id);
          break;
        }
      }
    }
    // Save these random terms for reuse.
    self.type_to_random_terms.push((ty.clone(), random_term_ids.clone()));
    random_term_ids
  }

  /// Makes a cvec by picking randomly without repetition from the vector of
  /// random term ids generated for its type.
  pub fn make_cvec_for_type(&mut self, ty: &Type, env: &Env, ctx: &Context) -> Cvec {
    let random_terms = self.lookup_ty(ty).unwrap_or_else(|| self.initialize_ty(ty, env, ctx));
    let mut rng = thread_rng();
    let cvec = random_terms.choose_multiple(&mut rng, self.cvec_size).map(|id| *id).collect();
    Cvec::Cvec(cvec)

  }

  pub fn saturate(&mut self) {
    /*println!("reductions");
    for rewrite in self.reductions.iter() {
      println!("  {:?}", rewrite);
    }*/
    self.cvec_egraph.replace_with(|egraph|{
      let runner = Runner::default()
        .with_egraph(egraph.to_owned())
          .with_iter_limit(10000000)
        .run(&self.reductions);
      runner.egraph
    });
  }

}

/// Returns None for incomparable types (contradictions)
pub fn cvecs_equal(cvec_analysis: &CvecAnalysis, cvec_1: &Cvec, cvec_2: &Cvec) -> Option<bool> {
  match (cvec_1, cvec_2) {
    (Cvec::Cvec(cv1), Cvec::Cvec(cv2)) => {
      Some(zip(cv1.iter(), cv2.iter()).all(|(id1, id2)| {
        let resolved_id1 = cvec_analysis.cvec_egraph.borrow_mut().find(*id1);
        let resolved_id2 = cvec_analysis.cvec_egraph.borrow_mut().find(*id2);
        resolved_id1 == resolved_id2
      }))
    }
    _ => None,
  }

}

pub fn print_cvec(cvec_analysis: &CvecAnalysis, cvec: &Cvec) {
  match cvec {
    Cvec::Cvec(cv1) => {
      let eg = cvec_analysis.cvec_egraph.borrow();
      let extractor = Extractor::new(&eg, AstSize);
      let terms = cv1.iter().map(|cv_id| {
        extractor.find_best(*cv_id).1.to_string()
      }).join(",");
      println!("cvec: {}", terms);
    }
    Cvec::Stuck => {
      println!("Stuck");
    }
  }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Cvec {
  /// Vector of CvecAnalysis.cvec_size Ids corresponding to random terms.
  ///
  /// In the base case (when they're assigned to variables), these should
  /// all be distinct Ids if the type permits it (e.g. Booleans only have
  /// two distinct values), but once we construct Cvecs recursively there
  /// is no guarantee of distinct valuations.
  Cvec(Vec<Id>),
  /// We don't know how to evaluate this cvec yet (possibly because we haven't
  /// given information about it)
  Stuck,
  // /// Cvecs that we will not check for contradictions. These most often come
  // /// from case splits. Variables previously can take on a range of values,
  // /// but after a case split, they are narrowed.
  // ///
  // /// These may not be of size CvecAnalysis.cvec_size, and if for some reason we
  // /// need to compare with a Cvec, we will repeat its length to match the length
  // /// of it.
  // // TrustedCvec(Vec<Id>),
  // /// Arises when we union two things that disagree on their CVecs,
  // /// we store the Ids of the terms in the CvecAnalysis that disagree.
  // ///
  // /// This overrides other analyses, although we should catch it and fail
  // /// quickly.
  // Contradiction(Id, Id),
}

impl Cvec {
  // FIXME: Should be an iterator, also fix code reuse below
  // pub fn zip(&self, other: &Cvec) -> Vec<(Id, Id)> {
  //   match (self, other) {
  //     // (Cvec::Stuck(s), Cvec::Stuck(o)) => {
  //     //   vec!((*s, *o))
  //     // }
  //     // // Dunno how to make the types work here or how to dereference the ids.
  //     // // Someone can fix this later.
  //     // (Cvec::Cvec(s), Cvec::Stuck(o)) => {
  //     //   zip(s, repeat(o)).map(|(e1, e2)| (*e1, *e2)).collect()
  //     // }
  //     // (Cvec::Stuck(s), Cvec::Cvec(o)) => {
  //     //   zip(repeat(s), o).map(|(e1, e2)| (*e1, *e2)).collect()
  //     // }
  //     (Cvec::Cvec(s), Cvec::Cvec(o)) => {
  //       zip(s, o).map(|(e1, e2)| (*e1, *e2)).collect()
  //     }
  //     _ => Vec::default(),
  //   }
  // }

  // pub fn is_contradiction(&self) -> bool {
  //   match self {
  //     Cvec::Contradiction(..) => true,
  //     _ => false,
  //   }
  // }

  /// Calls get on Cvecs.
  /// Always fails for stuck or contradictory cvecs.
  pub fn get_at_index(&self, index: usize) -> Option<&Id> {
    match self {
      Cvec::Cvec(cv) => cv.get(index),
      _ => None,
    }
  }

  fn make(egraph: &EGraph<SymbolLang, CycleggAnalysis>, enode: &SymbolLang) -> (Self, usize) {
    // println!("making cvec for enode: {}", enode);
    let mut max_child_timestamp = egraph.analysis.cvec_analysis.current_timestamp;
    if enode.is_leaf() {
      // if egraph.analysis.global_ctx.contains_key(&enode.op) {
      //   println!("making dummy cvec for {}", &enode.op);
      // }
      // We can't evaluate vars (we need outside input, i.e. type information to create them)
      // This could be resolved by having a type information analysis.
      //
      // The second check is to verify that this isn't a function.
      if is_var(&enode.op.to_string()) && !egraph.analysis.global_ctx.contains_key(&enode.op) {
        return (Cvec::Stuck, max_child_timestamp);
      } else {
        // This cvec is for a value like Z or Leaf, so make a concrete cvec out of it.
        let id = egraph.analysis.cvec_analysis.cvec_egraph.borrow_mut().add(enode.clone());
        let cvec = repeat_n(id, egraph.analysis.cvec_analysis.cvec_size).collect();
        return (Cvec::Cvec(cvec), max_child_timestamp);
      }
    }

    let op = enode.op;

    let mut new_cvec = Vec::new();
    // The max size of a Cvec should be this
    for i in 0..egraph.analysis.cvec_analysis.cvec_size {
      // Get the ith element of each cvec.
      let opt_children = enode.children().iter().map(|child| {
        max_child_timestamp = std::cmp::max(max_child_timestamp, egraph[*child].data.timestamp);
        egraph[*child].data.cvec_data.get_at_index(i).map(|id| *id)
      }).collect();
      match opt_children {
        // If it's stuck, then propagate that it's stuck
        // NOTE: we don't update the timestamp because we don't use its children from which it would've
        // gotten a fresher timestamp
        None => return (Cvec::Stuck, egraph.analysis.cvec_analysis.current_timestamp),
        Some(cvec_children) => {
          let new_enode = SymbolLang::new(op, cvec_children);
          let id = egraph.analysis.cvec_analysis.cvec_egraph.borrow_mut().add(new_enode);
          new_cvec.push(id);
        }
      }
    }
    (Cvec::Cvec(new_cvec), max_child_timestamp)
  }

  fn merge(&mut self, a_timestamp: usize, b: Self, b_timestamp: usize, egraph: &RefCell<EGraph<SymbolLang, ()>>) -> DidMerge {
    // println!("merging cvecs: {:?} and {:?} ({} is newer) {} < {}", self, b, if a_timestamp < b_timestamp {"second"} else {"first"}, a_timestamp, b_timestamp);
    // Always replace a stuck cvec
    // *self = b;
    // return DidMerge(false, false);
    match (&self, &b) {
      (Cvec::Stuck, Cvec::Cvec(_)) => {
        // println!("taking {:?}", b);
        *self = b;
        DidMerge(true, false)
      }
      (Cvec::Cvec(cv1), Cvec::Cvec(cv2)) => {
        let different = zip(cv1.iter(), cv2.iter()).any(|(id1, id2)|{
          let resolved_id1 = egraph.borrow_mut().find(*id1);
          let resolved_id2 = egraph.borrow_mut().find(*id2);
          if resolved_id1 != resolved_id2 {
            // let borrowed_egraph = &egraph.borrow();
            // let extractor = Extractor::new(borrowed_egraph, AstSize);
            // let expr1 = extractor.find_best(resolved_id1).1;
            // let expr2 = extractor.find_best(resolved_id2).1;
            // println!("differing cvecs: {} {}", expr1, expr2);
          }
          resolved_id1 != resolved_id2
        });
        if different && a_timestamp < b_timestamp {
          // println!("taking {:?}", b);
          *self = b;
          DidMerge(true, false)
        } else {
          // println!("keeping {:?}", self);
          DidMerge(false, true)
        }
      }
      (Cvec::Cvec(_), Cvec::Stuck) => {
        // println!("keeping {:?}", self);
        DidMerge(false, true)
      }
      (Cvec::Stuck, Cvec::Stuck) => {
        // println!("keeping {:?}", self);
        DidMerge(false, false)
      }
    }

    // // FIXME: why do we infinitely loop if we don't return
    // // DidMerge(false, false) here?
    // DidMerge(false, false)

    // TODO: Check for contradictions later
    // for (id1, id2) in self.zip(&b) {
    //   let resolved_id1 = egraph.borrow_mut().find(id1);
    //   let resolved_id2 = egraph.borrow_mut().find(id2);
    //   if resolved_id1 != resolved_id2 {
    //     *self = Cvec::Contradiction(resolved_id1, resolved_id2);
    //     return DidMerge(true, true)
    //   }
    // }
    // match (&self, &b) {
    //   // Don't bother looking if it's a contradiction
    //   (Cvec::Contradiction(..), _) => DidMerge(false, false),
    //   // Otherwise, overwrite if we find one
    //   (_, Cvec::Contradiction(..)) => {
    //     *self = b;
    //     DidMerge(true, false)
    //   }
    //   // If we got this far, we didn't find any contradictions,
    //   // so we can use either Cvec.
    //   _ => DidMerge(false, false),
    // }
  }
}

/// The set of constructors in an e-class.
/// The order of variants is important: since we use the derived order during the merge.
#[derive(Debug, PartialEq, PartialOrd, Eq, Ord, Clone)]
pub enum CanonicalForm {
  /// This class has neither constructors nor variables, so it is a function we
  /// can't evaluate
  Stuck(SymbolLang),
  /// This class has a variable but no constructors
  Var(SymbolLang),
  /// This class has a single constructor;
  /// because the analysis merges the children of the same constructor,
  /// there cannot be two different constructor e-nodes with the same head constructor in an e-class.
  Const(SymbolLang),
  /// This class has at least two different constructors
  /// or it contains an infinite term (this class is reachable from an argument of its constructor);
  /// in any case, this is an inconsistency.
  Inconsistent(SymbolLang, SymbolLang),
}

impl CanonicalForm {

  pub fn get_enode(&self) -> &SymbolLang {
    match self {
      // For an inconsistent anlysis, we can take any enode
      CanonicalForm::Stuck(enode) | CanonicalForm::Var(enode) | CanonicalForm::Const(enode) | CanonicalForm::Inconsistent(enode, _) => {
        enode
      }
    }
  }

  pub fn merge(&mut self, from: Self) -> DidMerge {
    // If we are merging classes with two different constructors,
    // record that this class is now inconsistent
    // (and remember both constructors, we'll need them to build an explanation)
    if let CanonicalForm::Const(n1) = self {
      if let CanonicalForm::Const(ref n2) = from {
        if n1.op != n2.op {
          *self = CanonicalForm::Inconsistent(n1.clone(), n2.clone());
          return DidMerge(true, true);
        }
      }
    }
    // Otherwise, just take the max constructor set
    merge_max(self, from)
  }

  pub fn make(enode: &SymbolLang) -> Self {
    if is_constructor(enode.op.into()) {
      CanonicalForm::Const(enode.clone())
    } else if enode.children.is_empty() {
      CanonicalForm::Var(enode.clone())
    } else {
      CanonicalForm::Stuck(enode.clone())
    }
  }

  pub fn modify(egraph: &mut EGraph<SymbolLang, CycleggAnalysis>, id: Id) {
    if let CanonicalForm::Const(ref n1) = egraph[id].data.canonical_form_data {
      let n1 = n1.clone();
      // We have just merged something into a constructor.
      // 1) Check if there are any other constructors in this class with the same head and union their children
      let other_constructors: Vec<SymbolLang> = egraph[id]
        .nodes
        .iter()
        .filter(|n2| n1 != **n2 && n1.op == n2.op)
        .cloned()
        .collect();

      for n2 in other_constructors {
        // We can't always extract because of destructive rewrites
        // // The extraction is only here for logging purposes
        // let extractor = Extractor::new(egraph, AstSize);
        // let expr1 = extract_with_node(&n1, &extractor);
        // let expr2 = extract_with_node(&n2, &extractor);
        /*if CONFIG.verbose && n1 != n2 {
          println!("INJECTIVITY {} = {}", n1, n2);
        }*/
        // Unify the parameters of the two constructors
        for (c1, c2) in n1.children.iter().zip(n2.children.iter()) {
          let c1 = egraph.find(*c1);
          let c2 = egraph.find(*c2);
          if c1 != c2 {
            egraph.union_trusted(
              c1,
              c2,
              format!("constructor-injective {} = {}", n1, n2),
            );
          }
        }
      }
      // NOTE CK: This isn't actually helping us prove props and is
      // causing issues when combined with destructive rewrites, so it's getting
      // commented out for now.
      //
      // // 2) Check if we created a cycle made up of only constructors,
      // // and if so, report inconsistency (infinite term)
      // if CanonicalFormAnalysis::is_canonical_cycle(egraph, &n1, id) {
      //   // The extraction is only here for logging purposes
      //   let extractor = Extractor::new(egraph, AstSize);
      //   let n2 = extractor.find_best_node(id);
      //   let expr1 = extract_with_node(&n1, &extractor);
      //   let expr2 = extract_with_node(n2, &extractor);
      //   if CONFIG.verbose {
      //     println!("INFINITE TERM {} = {}", expr1, expr2);
      //   }
      //   egraph[id].data.canonical_form_data = CanonicalForm::Inconsistent(n1, n2.clone());
      // }
    }
  }

}

#[derive(Default, Clone)]
pub struct CanonicalFormAnalysis {}

impl CanonicalFormAnalysis {
  /// Extract the canonical form of an e-class if it exists.
  /// Note: this function does not check for cycles, so it should only be called
  /// after the analysis has finished.
  pub fn extract_canonical(egraph: &EGraph<SymbolLang, CycleggAnalysis>, id: Id) -> Option<Expr> {
    match &egraph[id].data.canonical_form_data {
      CanonicalForm::Const(n) => {
        // Extract canonical forms of the children:
        let children: BTreeMap<Id, Expr> =
          n.children
            .iter()
            .try_fold(BTreeMap::new(), |mut acc, child| {
              let child_expr = Self::extract_canonical(egraph, *child)?;
              acc.insert(*child, child_expr);
              Some(acc)
            })?;
        // Join those forms into a single expression:
        let expr = n.join_recexprs(|child_id| children.get(&child_id).unwrap());
        Some(expr)
      }
      CanonicalForm::Var(n) => Some(vec![n.clone()].into()),
      _ => None,
    }
  }

  /// Check if the canonical form of eclass id (whose constructor node is n)
  /// has a cycle back to itself made up of only constructors.
  /// This means that the eclass represents an infinite term.
  // FIXME: when we find a contradiction this way, we store the conflicting
  // e-nodes, but these nodes might be removed due to a destructive rewrite
  // later. So we need to generate an explanation for their equality immediately
  // - or just not use this part of the analysis.
  fn _is_canonical_cycle(egraph: &EGraph<SymbolLang, CycleggAnalysis>, n: &SymbolLang, id: Id) -> bool {
    // We have to keep track of visited nodes because there might also be a lasso
    // (i.e. a cycle not starting at id)
    let mut visited: BTreeSet<Id> = BTreeSet::new();
    visited.insert(id);
    Self::_is_reachable(egraph, n, id, &mut visited)
  }

  fn _is_reachable(egraph: &EGraph<SymbolLang, CycleggAnalysis>, n: &SymbolLang, id: Id, visited: &mut BTreeSet<Id>) -> bool {
    n.children.iter().any(|c| {
      let c = egraph.find(*c);
      if c == id {
        true
      } else if visited.contains(&c) {
        // We return false here because a) this might just be a DAG and
        // b) if there is a cycle at c, it will be detected in c's modify call
        false
      } else {
        visited.insert(c);
        if let CanonicalForm::Const(n2) = &egraph[c].data.canonical_form_data {
          Self::_is_reachable(egraph, n2, id, visited)
        } else {
          false
        }
      }
    })
  }
}

#[derive(Debug, Clone, Default)]
pub struct CycleggAnalysis {
  pub cvec_analysis: CvecAnalysis,
  pub blocking_vars: BTreeSet<Symbol>,
  pub case_split_vars: BTreeSet<Symbol>,
  pub local_ctx: Context,
  pub global_ctx: Context,
}

#[derive(Debug, Clone)]
pub struct CycleggData {
  pub cvec_data: Cvec,
  pub timestamp: usize,
  // /// Should we force update the Cvec?
  // ///
  // /// This skips checking for contradictions, which is necessary when we case
  // /// split.
  // pub force_update_cvec: bool,
  // /// Older data will take priority over younger data if we are trying to merge
  // /// two CycleggData's Cvecs and both have force_update_cvec set.
  // ///
  // /// By default this is 0, but we will set it when we case split and force
  // /// updates.
  // pub age: usize,
  pub canonical_form_data: CanonicalForm,
}

impl Analysis<SymbolLang> for CycleggAnalysis {
  type Data = CycleggData;

  fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
    // let cvec_result =
    //   match (a.force_update_cvec, b.force_update_cvec) {
    //     // Without any force updates, do the contradiction check
    //     (false, false) => {
    //       a.cvec_data.merge(b.cvec_data, &self.cvec_analysis.cvec_egraph)
    //     }
    //     // Otherwise, we need to figure out which we take, breaking ties
    //     // by using age.
    //     (true, false) => {
    //       DidMerge(false, true)
    //     }
    //     (false, true) => {
    //       a.cvec_data = b.cvec_data;
    //       DidMerge(true, false)
    //     }
    //     (true, true) => {
    //       if a.age > b.age {
    //         DidMerge(false, true)
    //       } else {
    //         a.cvec_data = b.cvec_data;
    //         DidMerge(true, false)
    //       }
    //     }
    //   };
    // self.cvec_analysis.saturate();
    a.cvec_data.merge(a.timestamp, b.cvec_data, b.timestamp, &self.cvec_analysis.cvec_egraph)
      | merge_max(&mut a.timestamp, b.timestamp)
      | a.canonical_form_data.merge(b.canonical_form_data)
  }

  fn make(egraph: &EGraph<SymbolLang, Self>, enode: &SymbolLang) -> Self::Data {
    let (cvec_data, timestamp) = Cvec::make(egraph, enode);
    let canonical_form_data = CanonicalForm::make(enode);
    CycleggData {
      cvec_data,
      // force_update_cvec: false,
      // age: 0,
      canonical_form_data,
      timestamp,
    }
  }

  fn modify(egraph: &mut EGraph<SymbolLang, Self>, id: Id) {
    CanonicalForm::modify(egraph, id);
    // egraph.analysis.cvec_analysis.saturate();
  }
}
