use crate::ast::{Context, Env, Type, SSubst, resolve_sexp, Expr, is_constructor, is_var, mangle_name, Prop, substitute_sexp_map};
use crate::config::CONFIG;
use crate::goal::GlobalSearchState;
use crate::lemma_tree::{PatternWithHoles, sexp_to_pattern, FnDefs};
use egg::*;
use itertools::{repeat_n, Itertools};
use rand::{thread_rng, Rng};
use rand::distributions::uniform::SampleUniform;
use rand::distributions::weighted::WeightedIndex;
use rand::distributions::Distribution;
use rand::seq::SliceRandom;
use std::cell::RefCell;
use std::iter::repeat;
use std::{collections::{BTreeMap, BTreeSet}, iter::zip, str::FromStr};
use symbolic_expressions::Sexp;

// We use an analysis inspired by cvecs from Ruler (https://github.com/uwplse/ruler)
// to help us guess equalities between separate e-classes as lemmas. Because our
// rewrites are simply rules in an e-graph, we don't bother implementing the same
// evaluation code and use an e-graph to evaluate the terms. This allows us to
// store them compactly, too.

pub fn random_term_from_type_max_depth(
  ty: &Type,
  env: &Env,
  ctx: &Context,
  max_depth: usize,
) -> Sexp {
  random_term_from_type_with_weight_max_depth::<usize>(ty, env, ctx, max_depth, &BTreeMap::default())
}

pub fn random_term_from_type_max_size(
  ty: &Type,
  env: &Env,
  ctx: &Context,
  max_size: usize,
) -> Sexp {
  random_term_from_type_with_weight_max_size::<usize>(ty, env, ctx, max_size, &BTreeMap::default())
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
pub fn random_term_from_type_with_weight_max_depth<W>(
  ty: &Type,
  env: &Env,
  ctx: &Context,
  max_depth: usize,
  constructor_weights: &BTreeMap<String, WeightedIndex<W>>,
) -> Sexp
where
  W: SampleUniform + PartialOrd,
{
  let mut rng = thread_rng();
  // Techncially we will generate the same kind of random value for any arrow we
  // don't know how to make random terms for.
  //
  // It seems vanishingly unlikely that this will cause problems.
  let mut gen_rand_const = |prefix| {
    let rand_k = format!("{}{}",prefix,rng.gen_range(0..CONFIG.cvec_num_random_terms_per_type));
    Sexp::String(rand_k)
  };
  let dt_res = ty.datatype();
  if dt_res.is_err() {
    // Generate a random constant for arrows since we don't know how to generate
    // things of type arrow.
    return gen_rand_const("arr");
  }
  let (dt_name, arg_types) = dt_res.unwrap();
  let dt_symb = Symbol::new(dt_name);
  if !env.contains_key(&dt_symb) {
    // This must be a type variable
    assert!(dt_name.starts_with(char::is_lowercase));
    return gen_rand_const(dt_name);
  }
  let (vars, cons) = env.get(&dt_symb).unwrap();
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
      random_term_from_type_with_weight_max_depth(&resolved_arg, env, ctx, max_depth.saturating_sub(1), constructor_weights)
    }).collect();

    children.insert(0, Sexp::String(con.to_string()));
    return Sexp::List(children);
  }
}

/// Generates random terms that have an AST size of at most `max_size`.
///
/// Terms are not guaranteed to be smaller than `max_size`, but we make a best
/// effort to ensure it.
///
/// Takes the same arguments as random_term_from_type_with_weight_max_depth.
pub fn random_term_from_type_with_weight_max_size<W>(
  ty: &Type,
  env: &Env,
  ctx: &Context,
  max_size: usize,
  constructor_weights: &BTreeMap<String, WeightedIndex<W>>,
) -> Sexp
where
  W: SampleUniform + PartialOrd,
{
  todo!("incorporate random gen from max_depth version");
  let (dt_name, arg_types) = ty.datatype().unwrap();
  let (vars, cons) = env.get(&Symbol::from_str(dt_name).unwrap()).or_else(|| {
    // this should be a type variable we can't look up
    assert!(dt_name.starts_with(char::is_lowercase));
    env.get(&Symbol::from_str(&mangle_name("Bool")).unwrap())
  }).unwrap();
  let type_var_map: SSubst = zip(vars.iter().cloned(), arg_types.iter().map(|arg_type| arg_type.repr.clone())).collect();

  // Has any base cases (terms that are not obviously recursive)? This could be
  // precomputed to speed things up.
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
    // If all of the other cases are too big and there is a base case to reach
    // and we haven't reached one, keep going.
    //
    // NOTE: I think there is the possibility for infinite loops here if the
    // weights are wrong (e.g. base cases all have 0 weights).
    if args.len() > (max_size - 1) && has_base_case && !is_base_case(dt_name, &args) {
      continue;
    }

    if args.len() == 0 {
      return Sexp::String(con.to_string());
    }
    // Divide up the remaining size randomly. We subtract 1 to account for the
    // size of the constructor.
    let child_sizes = split_randomly(max_size - 1, args.len(), &mut rng);
    let mut children: Vec<Sexp> = args.iter().zip(child_sizes.into_iter()).map(|(arg, child_size)| {
      // Substitute over the type. This could be more efficient if we skipped
      // when the type_var_map is empty.
      let resolved_arg = Type::new(resolve_sexp(&arg.repr, &type_var_map));
      // We do a saturating subtraction here because max_depth could be 0 if
      // there are no base cases. This is why the max depth might end up
      // greater in a pathological case.
      random_term_from_type_with_weight_max_size(&resolved_arg, env, ctx, child_size, constructor_weights)
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

fn split_randomly<R>(n: usize, num_parts: usize, rng: &mut R) -> Vec<usize>
where
  R: Rng
{
  if num_parts == 0 || num_parts > n {
    panic!("impossible to split {} into {} parts", n, num_parts);
  }

  let mut parts = vec![0; num_parts];

  // Generate random cut points
  let mut cut_points: Vec<usize> = (1..n).collect();
  cut_points.shuffle(rng);
  cut_points.truncate(num_parts - 1);
  cut_points.sort_unstable();

  let mut prev_cut = 0;
  for (i, cut) in cut_points.into_iter().enumerate() {
    parts[i] = cut - prev_cut;
    prev_cut = cut;
  }
  parts[num_parts - 1] = n - prev_cut;

  parts
}

/// Our normal cvec analysis uses a single egraph to do its checks, as well as
/// caches random values. This is a function that naively generates a new egraph
/// and random terms each time it checks.
///
/// In principle, an evaluator would be better than both approaches, but that
/// takes time to write.
pub fn has_counterexample_check(prop: &Prop, env: &Env, ctx: &Context, reductions: &Vec<Rewrite<SymbolLang, ()>>) -> bool {
  for _ in 0..CONFIG.cvec_size {
    let substs: Vec<(Sexp, Sexp)> = prop.params.iter().map(|(param, ty)| {
      let rand_sexp = random_term_from_type_max_depth(ty, env, ctx, CONFIG.cvec_term_max_depth);
      (Sexp::String(param.to_string()), rand_sexp)
    }).collect();
    let rand_inst_lhs_sexp = substitute_sexp_map(&prop.eq.lhs, &substs);
    let rand_inst_rhs_sexp = substitute_sexp_map(&prop.eq.rhs, &substs);
    // println!("instantiated {} = {} to {} = {}", prop.eq.lhs, prop.eq.rhs, rand_inst_lhs_sexp, rand_inst_rhs_sexp);
    let rand_inst_lhs_term = rand_inst_lhs_sexp.to_string().parse().unwrap();
    let rand_inst_rhs_term = rand_inst_rhs_sexp.to_string().parse().unwrap();
    let mut eg: EGraph<SymbolLang, ()> = EGraph::new(());
    let lhs_id = eg.add_expr(&rand_inst_lhs_term);
    let rhs_id = eg.add_expr(&rand_inst_rhs_term);
    let runner = Runner::default()
      .with_egraph(eg)
        .with_iter_limit(10000000)
      .run(reductions);
    if runner.egraph.find(lhs_id) != runner.egraph.find(rhs_id) {
      return true;
    }
  }
  // panic!("counterexample check failed");
  false
}

#[derive(Debug, Clone)]
pub struct CvecAnalysis {
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
  type_to_random_terms: Vec<(Type, Vec<PatternWithHoles>)>,
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
  /// Used so that we can force updates to the contents of this egraph.
  pub current_timestamp: usize,
}

impl Default for CvecAnalysis {
  fn default() -> Self {
    Self {
      type_to_random_terms: Vec::new(),
      cvec_size: CONFIG.cvec_size,
      term_max_depth: CONFIG.cvec_term_max_depth,
      num_rolls: CONFIG.cvec_num_rolls,
      num_random_terms_per_type: CONFIG.cvec_num_random_terms_per_type,
      current_timestamp: 0,
    }
  }
}

impl CvecAnalysis {
  pub fn new(cvec_size: usize, term_max_depth: usize, max_tries_to_make_distinct_term: usize, num_random_terms_per_type: usize, reductions: Vec<Rewrite<SymbolLang, ()>>) -> Self {
    assert!(cvec_size < num_random_terms_per_type, "num_random_terms_per_type must be greater than cvec_size");
    Self {
      type_to_random_terms: Vec::new(),
      cvec_size,
      term_max_depth,
      num_rolls: max_tries_to_make_distinct_term,
      num_random_terms_per_type,
      current_timestamp: 0,
    }
  }

  // We have to do this because Sexps aren't orderable or hashable...
  fn lookup_ty(&self, ty: &Type) -> Option<Vec<PatternWithHoles>> {
    for (other_ty, terms) in self.type_to_random_terms.iter() {
      if ty == other_ty {
        return Some(terms.clone());
      }
    }
    None
  }


  /// Returns a vector of length `num_random_terms`. We try to ensure they're
  /// distinct but there's a chance that they aren't.
  fn initialize_ty(&mut self, ty: &Type, global_context: &Context, env: &Env) -> Vec<PatternWithHoles> {
    let mut random_terms = Vec::new();
    for _ in 0..self.num_random_terms_per_type {
      let mut try_number = 0;
      loop {
        try_number += 1;
        // For now, we don't pass weights in
        let new_sexp = random_term_from_type_max_depth(ty, env, global_context, self.term_max_depth);
        let new_term = sexp_to_pattern(&new_sexp);
        if !random_terms.contains(&new_term) || try_number == self.num_rolls {
          random_terms.push(new_term);
          break;
        }
      }
    }
    // Save these random terms for reuse.
    self.type_to_random_terms.push((ty.clone(), random_terms.clone()));
    random_terms
  }

  /// Makes a cvec by picking randomly without repetition from the vector of
  /// random term ids generated for its type.
  pub fn make_cvec_for_type(&mut self, ty: &Type, global_context: &Context, env: &Env) -> Cvec {
    // println!("making cvec for {}", ty);
    let random_terms = self.lookup_ty(ty).unwrap_or_else(|| self.initialize_ty(ty, global_context, env));
    let mut rng = thread_rng();
    let mut terms = Vec::with_capacity(self.cvec_size);
    random_terms.choose_multiple(&mut rng, self.cvec_size).for_each(|term|{
      // println!("term: {}", term);
      terms.push(term.clone());
    });
    Cvec {
      terms,
    }
  }

}

#[derive(Debug, Clone, PartialEq)]
pub struct Cvec {
  /// Vector of CvecAnalysis.cvec_size random terms.
  pub terms: Vec<PatternWithHoles>,
  // /// We don't know how to evaluate this cvec yet (possibly because we haven't
  // /// given information about it)
  // Stuck,
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

  fn make(egraph: &EGraph<SymbolLang, CycleggAnalysis>, enode: &SymbolLang) -> (Self, usize) {
    // println!("making cvec for enode: {}", enode);
    let mut max_child_timestamp = egraph.analysis.cvec_analysis.borrow().current_timestamp;
    if enode.is_leaf() {
      // println!("op: {}", enode.op);
      if is_constructor(enode.op.as_str()) {
        return (Cvec {terms: repeat_n(PatternWithHoles::Node(enode.op, vec!()), egraph.analysis.cvec_analysis.borrow().cvec_size).collect()}, max_child_timestamp);
      }
      let ty = egraph.analysis.local_ctx.get(&enode.op).unwrap_or_else(|| egraph.analysis.global_ctx.get(&enode.op).unwrap());
      return (egraph.analysis.cvec_analysis.borrow_mut().make_cvec_for_type(ty, &egraph.analysis.global_ctx, &egraph.analysis.env), max_child_timestamp);
    }

    let op = enode.op;

    let mut new_cvec = Vec::with_capacity(egraph.analysis.cvec_analysis.borrow().cvec_size);
    // The max size of a Cvec should be this
    for i in 0..egraph.analysis.cvec_analysis.borrow().cvec_size {
      // Get the ith element of each cvec.
      let child_args = enode.children().iter().map(|child| {
        max_child_timestamp = std::cmp::max(max_child_timestamp, egraph[*child].data.timestamp);
        Box::new(egraph[*child].data.cvec_data.terms[i].clone())
      }).collect();
      let mut new_term = PatternWithHoles::Node(op, child_args);
      new_term.eval(&egraph.analysis.defs_for_eval);
      new_cvec.push(new_term);
    }
    (Cvec {terms: new_cvec}, max_child_timestamp)
  }

  fn merge(&mut self, a_timestamp: usize, b: Self, b_timestamp: usize) -> DidMerge {
    // println!("merging cvecs: {:?} and {:?} ({} is newer) {} < {}", self, b, if a_timestamp < b_timestamp {"second"} else {"first"}, a_timestamp, b_timestamp);
    let different = zip(self.terms.iter(), b.terms.iter()).any(|(term1, term2)|{
      term1 != term2
    });
    if different && a_timestamp < b_timestamp {
      // println!("taking {:?}", b);
      *self = b;
      DidMerge(true, false)
    } else {
      // println!("keeping {:?}", self);
      DidMerge(false, true)
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

  pub fn print(&self) {
    println!("{}", self.terms.iter().map(|term| format!("{}", term)).join(", "));
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

#[derive(Clone, Default)]
pub struct CycleggAnalysis {
  pub cvec_analysis: RefCell<CvecAnalysis>,
  pub blocking_vars: BTreeSet<Symbol>,
  pub case_split_vars: BTreeSet<Symbol>,
  pub local_ctx: Context,
  pub global_ctx: Context,
  pub defs_for_eval: FnDefs,
  pub env: Env,
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
    a.cvec_data.merge(a.timestamp, b.cvec_data, b.timestamp)
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
