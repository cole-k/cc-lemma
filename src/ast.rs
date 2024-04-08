use egg::*;
use lazy_static::lazy_static;

use indexmap::IndexMap;
use std::{collections::{BTreeMap, BTreeSet}, fmt::Display, str::FromStr, hash::Hash};
use symbolic_expressions::{Sexp, SexpError};

use crate::config::CONFIG;

pub type SSubst = BTreeMap<String, Sexp>;
// This is almost like egg's Subst but iterable
pub type IdSubst = IndexMap<Symbol, Id>;

#[derive(Debug, Clone, PartialEq)]
pub struct Type {
  pub repr: Sexp,
}

impl Type {
  pub fn new(repr: Sexp) -> Self {
    Self { repr }
  }

  /// If this type is a datatype, returns its name and arguments in order (if it
  /// has any) and otherwise return error.
  pub fn datatype(&self) -> Result<(&String, Vec<Type>), SexpError> {
    match &self.repr {
      Sexp::String(s) => Ok((s, Vec::default())), // This type is a D
      Sexp::List(lst) => {
        let mut lst_iter = lst.iter();
        let dt = lst_iter.next().unwrap().string()?;
        if dt == ARROW {
          return Err(SexpError::Other("datatype: unexpected arrow".to_string()));
        }
        let arg_types = lst_iter.map(|arg| Type::new(arg.clone())).collect();
        Ok((dt, arg_types))
      }
      _ => panic!("arity: type is empty"),
    }
  }

  /// Split a type into arguments and return value
  /// (arguments are empty if the type is not an arrow)
  pub fn args_ret(&self) -> (Vec<Type>, Type) {
    match &self.repr {
      Sexp::String(_) => (vec![], self.clone()), // This type is a D
      Sexp::List(xs) => {
        // This is a type constructor application
        match xs[0].string().unwrap().as_str() {
          ARROW => {
            let args = xs[1]
              .list()
              .unwrap()
              .iter()
              .map(|x| Type::new(x.clone()))
              .collect();
            (args, Type::new(xs[2].clone()))
          }
          _ => (vec![], self.clone()),
        }
      }
      _ => panic!("arity: type is empty"),
    }
  }

  pub fn is_arrow(&self) -> bool {
    match &self.repr {
      Sexp::List(xs) => {
        xs[0].string().unwrap().as_str() == ARROW
      }
      _ => false
    }
  }

}

impl FromStr for Type {
  type Err = SexpError;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    Ok(Type::new(symbolic_expressions::parser::parse_str(s)?))
  }
}

impl Display for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "{}", self.repr)
  }
}

// Expressions
pub type Expr = RecExpr<SymbolLang>;
pub type Pat = Pattern<SymbolLang>;

pub fn mangle_name(name: &str) -> String {
  // We never mangle symbols. The cases we have are:
  //   $  (function application)
  //   -> (type arrows)
  //   ?x (variable names)
  if name
    .chars()
    .next()
    .map(|c| !c.is_alphabetic())
    .unwrap_or(true)
  {
    return name.to_string();
  }
  if CONFIG.mangle_names {
    if name.chars().next().unwrap().is_ascii_uppercase() {
      format!("Cyclegg_{}", name)
    } else {
      format!("cyclegg_{}", name)
    }
  } else {
    name.to_string()
  }
}

pub fn mangle_sexp(sexp: &Sexp) -> Sexp {
  map_sexp(|elem| Sexp::String(mangle_name(elem)), sexp)
}

// Constants
lazy_static! {
  pub static ref BOOL_TYPE: String = mangle_name("Bool");
  pub static ref ITE: String = mangle_name("ite");
  pub static ref TRUE: String = mangle_name("True");
  pub static ref FALSE: String = mangle_name("False");
}
pub const ARROW: &str = "->";
pub const APPLY: &str = "$";
// FIXME: we look for this prefix among variables but when we generate lemmas we
// don't make their parameters fresh. This means that we can mistakenly treat
// them as guards. I don't actually know if this causes problems with proof
// search since guards will always be booleans anyway, but this is a source of
// potential brittleness.
pub const GUARD_PREFIX: &str = "g_";

pub fn var_depth(var_name: &str) -> usize {
  var_name.matches('_').count()
}

pub fn is_descendant(var_name: &str, ancestor_name: &str) -> bool {
  var_name.starts_with(ancestor_name)
    && var_name.len() > ancestor_name.len()
    && var_name.chars().nth(ancestor_name.len()).unwrap() == '_'
}

#[derive(PartialEq, PartialOrd, Ord, Eq, Debug)]
pub enum StructuralComparison {
  /// Strictly less than
  LT,
  /// Not greater than
  LE,
  /// Don't know - we reject these
  Incomparable,
}

/// Check if sub is a subterm of sup
pub fn is_subterm(sub: &Expr, sup: &Expr) -> StructuralComparison {
  // Convert both expressions to strings and check if one is a substring of the other
  let sub_str = sub.to_string();
  let sup_str = sup.to_string();
  if sup_str.contains(&sub_str) {
    if sub_str.len() < sup_str.len() {
      StructuralComparison::LT
    } else {
      StructuralComparison::LE
    }
  } else {
    StructuralComparison::Incomparable
  }
}

/// Replace one variable with another in a RecExpr;
/// also returns whether the variable was found
pub fn replace_var(expr: &Expr, var: Symbol, replacement: Symbol) -> (Expr, bool) {
  let mut new_expr = vec![];
  let mut found = false;
  for node in expr.as_ref() {
    if node.op == var {
      new_expr.push(SymbolLang::leaf(replacement));
      found = true;
    } else {
      new_expr.push(node.clone());
    }
  }
  (new_expr.into(), found)
}

pub fn map_sexp<F>(f: F, sexp: &Sexp) -> Sexp
where
  F: Copy + Fn(&str) -> Sexp,
{
  match sexp {
    Sexp::Empty => Sexp::Empty,
    Sexp::String(str) => f(str),
    Sexp::List(list) => Sexp::List(list.iter().map(|s| map_sexp(f, s)).collect()),
  }
}


/// Unlike map_sexp, this substitutes Sexp -> Sexp, so the base case is when f
/// returns Some(new_sexp), which replaces the Sexp entirely.
pub fn map_sexp_sexp<F>(f: F, sexp: &Sexp) -> Sexp
where
  F: Copy + Fn(&Sexp) -> Option<Sexp>,
{
  f(sexp).unwrap_or_else(|| {
    match sexp {
      // Recursive case, try mapping over each child
      Sexp::List(list) => Sexp::List(list.iter().map(|s| map_sexp_sexp(f, s)).collect()),
      // Base case, f doesn't apply so just return the sexp unchanged
      _ => sexp.clone(),
    }
  })
}

/// Iterates over every sub-sexp in the sexp, substituting it entirely if it
/// matches the substitution.
pub fn substitute_sexp(sexp: &Sexp, from: &Sexp, to: &Sexp) -> Sexp {
  map_sexp_sexp(|interior_sexp| {
    if interior_sexp == from {
      Some(to.clone())
    } else {
      None
    }
  }, sexp)
}

/// Returns every subexpression in the sexp that contains a var, ignoring base
/// cases. This is basically every subexpression we would consider to
/// generalize.
///
/// Since Sexps can't be hashed we hack the set using their string
/// representation...
pub fn nontrivial_sexp_subexpressions_containing_vars(sexp: &Sexp) -> BTreeMap<String, Sexp> {
  let mut subexprs = BTreeMap::default();
  add_sexp_subexpressions(sexp, &mut subexprs);
  subexprs
}

fn add_sexp_subexpressions(sexp: &Sexp, subexprs: &mut BTreeMap<String, Sexp>) -> bool {
  let mut any_child_has_var = false;
  match sexp {
    Sexp::List(children) => {
      let mut child_iter = children.iter();
      // The root is a function so we shouldn't add it
      child_iter.next();
      child_iter.for_each(|child| {any_child_has_var |= add_sexp_subexpressions(child, subexprs);});
    }
    Sexp::String(s) if is_var(s) => {
      // We won't add the variable, but we will add every subexpression
      // containing it.
      return true;
    }
    _ => {},
  }
  // If there's a variable in this sexp, we can generalize it.
  if any_child_has_var {
    subexprs.insert(sexp.to_string(), sexp.clone());
  }
  any_child_has_var
}

pub fn contains_function(sexp: &Sexp) -> bool {
  match sexp {
    Sexp::List(list) => {
      if !list.is_empty() {
        if let Sexp::String(str) = &list[0] {
          if !is_constructor(str) {
            return true;
          }
        }
      }
      list.iter().any(contains_function)
    }
    _ => false,
  }
}

fn find_instantiations_helper<F>(proto: &Sexp, actual: &Sexp, is_var: F, instantiations_map: &mut SSubst) -> bool
where F: FnOnce(&str) -> bool + Copy {
  match (proto, actual) {
    (Sexp::Empty, _) | (_, Sexp::Empty) => unreachable!(),
    (Sexp::String(proto_str), actual_sexp) => {
      if is_var(proto_str) {
        // It's a type variable so we can instantiate it
        let instantiation = actual_sexp.clone();
        if let Some(existing_instantiation) = instantiations_map.get(proto_str) {
          // Past instantiations must agree
          &instantiation == existing_instantiation
        } else {
          instantiations_map.insert(proto_str.clone(), instantiation);
          true
        }
      } else {
        // Otherwise, it must match the actual
        proto == actual
      }
    }
    (Sexp::List(proto_list), actual_sexp) => {
      // The actual must match the proto
      if !actual_sexp.is_list() {
        return false;
      }
      let actual_list = actual_sexp.list().unwrap();
      // Including lengths.
      if proto_list.len() != actual_list.len() {
        return false;
      }
      proto_list
        .iter()
        .zip(actual_list.iter())
        .all(|(sub_proto, sub_actual)| {
          find_instantiations_helper(sub_proto, sub_actual, is_var, instantiations_map)
        })
    }
  }
}

/// Find the instantiations of proto needed to obtain actual
///
/// ex: proto  = (Pair a (Pair b b))
///     actual = (Pair (List x) (Pair Nat Nat))
///
///     instantiations = {a: (List x), b: Nat}
///
/// actual is assumed to be a valid instantiation of proto.
pub fn find_instantiations<F>(proto: &Sexp, actual: &Sexp, is_var: F) -> Option<SSubst>
where F: FnOnce(&str) -> bool + Copy {
  let mut instantiations = BTreeMap::new();
  let successful_instantiation = find_instantiations_helper(&proto, &actual, is_var, &mut instantiations);
  if successful_instantiation {
    Some(instantiations)
  } else{
    // The instantiations are bogus/partial if it is not successful
    None
  }
}

/// Resolves a Sexp using instantiations, but does not recursively resolve it.
///
/// Ex: sexp:           (List a)
///     instantiations: {a: (List b), b: Nat}
///
///     returns:        (List b)
pub fn resolve_sexp(sexp: &Sexp, instantiations: &SSubst) -> Sexp {
  map_sexp(
    |v| {
      instantiations
        .get(v)
        .cloned()
        .unwrap_or_else(|| Sexp::String(v.to_string()))
    },
    sexp,
  )
}

/// Recursively resolves a Sexp using instantiations.
///
/// Ex: sexp:           (List a)
///     instantiations: {a: (List b), b: Nat}
///
///     returns:        (List Nat)
pub fn recursively_resolve_sexp(sexp: &Sexp, instantiations: &SSubst) -> Sexp {
  map_sexp(|v| recursively_resolve_variable(v, instantiations), sexp)
}

/// Requires that there are no cycles in instantiations.
pub fn recursively_resolve_variable(var: &str, instantiations: &SSubst) -> Sexp {
  instantiations
    .get(var)
    .map(|sexp| map_sexp(|v| recursively_resolve_variable(v, instantiations), sexp))
    .unwrap_or_else(|| Sexp::String(var.to_string()))
}

pub fn is_constructor(var_name: &str) -> bool {
  var_name.chars().next().unwrap().is_uppercase()
}

pub fn sexp_is_constructor(sexp: &Sexp) -> bool {
  match sexp {
    Sexp::String(s) => is_constructor(s),
    Sexp::List(v) => is_constructor(&v[0].string().unwrap()),
    _ => false,
  }
}

/// WARNING: this should probably only be used for type variables, because we might
/// want to declare terms in our language such as one = (S Z) and this function
/// will incorrectly identify this as a variable. For us, variables really means
/// parameters (e.g. xs in the equation sorted xs === True).
pub fn is_var(var_name: &str) -> bool {
  var_name.chars().next().unwrap().is_lowercase()
}

pub fn get_vars<F>(e: &Expr, f: F) -> BTreeSet<Symbol>
where F: FnOnce(&str) -> bool + Copy
{
  let mut vars = BTreeSet::new();
  for n in e.as_ref() {
    if n.is_leaf() && is_var(&n.op.to_string()) {
      vars.insert(n.op);
    }
  }
  vars
}

pub fn sexp_leaves(sexp: &Sexp) -> BTreeSet<String> {
  let mut leaves = BTreeSet::default();
  sexp_leaves_helper(sexp, &mut leaves);
  leaves
}

fn sexp_leaves_helper(sexp: &Sexp, leaves: &mut BTreeSet<String>) {
  match sexp {
    Sexp::String(s) => {
      leaves.insert(s.clone());
    },
    Sexp::List(list) => {
      let mut list_iter = list.iter();
      // Skip the head, it's a function
      list_iter.next();
      list_iter.for_each(|sexp| sexp_leaves_helper(sexp, leaves));
    }
    Sexp::Empty => {}
  }
}

// Convert a symbol into a wildcard by prepending a '?' to it
pub fn to_wildcard(s: &Symbol) -> Var {
  format!("?{}", s).parse().unwrap()
}

// Does this pattern contain a wildcard derived from a guard variable?
// If so, we don't want to use it in a lemma because it cannot possibly be applied in a useful way.
pub fn has_guard_wildcards(p: &Pat) -> bool {
  p.vars().iter().any(|v| {
    v.to_string()
      .starts_with(format!("?{}", GUARD_PREFIX).as_str())
  })
}

// Convert e into a pattern by replacing all symbols where is_var holds with wildcards
pub fn to_pattern<'a, P>(e: &'a Expr, is_var: P) -> Pat
where
  P: Fn(&'a Symbol) -> bool,
{
  let mut pattern_ast = PatternAst::default();
  for n in e.as_ref() {
    if is_var(&n.op) {
      pattern_ast.add(ENodeOrVar::Var(to_wildcard(&n.op)));
    } else {
      pattern_ast.add(ENodeOrVar::ENode(n.clone()));
    }
  }
  Pattern::from(pattern_ast)
}

/// Create a Subst by looking up the given variables in the given egraph
pub fn lookup_vars<'a, I: Iterator<Item = &'a Symbol>, A: Analysis<SymbolLang>>(
  egraph: &EGraph<SymbolLang, A>,
  vars: I,
) -> IdSubst {
  let mut subst = IndexMap::new();
  for var in vars {
    match egraph.lookup(SymbolLang::leaf(*var)) {
      Some(id) => subst.insert(*var, id),
      None => panic!("lookup_vars: variable {} not found in egraph", var),
    };
  }
  subst
}

// Environment: for now just a map from datatype names to constructor names
pub type Env = BTreeMap<Symbol, (Vec<String>, Vec<Symbol>)>;

// Type context
pub type Context = BTreeMap<Symbol, Type>;

// Function definitions
pub type Defns = BTreeMap<String, Vec<(Sexp, Sexp)>>;

pub fn mk_context(descr: &[(&str, &str)]) -> Context {
  let mut ctx = Context::new();
  for (name, ty) in descr {
    ctx.insert(Symbol::from(*name), ty.parse().unwrap());
  }
  ctx
}

#[derive(Clone, Debug)]
pub struct Equation {
  pub lhs: Sexp,
  pub rhs: Sexp,
}

impl Equation {
  /// NOTE: Equation used to handle ordering the lhs and rhs, but we now let Prop
  /// handle that.
  pub fn new(lhs: Sexp, rhs: Sexp) -> Self {
    Self {
      lhs,
      rhs
    }
  }

  pub fn from_exprs(lhs: &Expr, rhs: &Expr) -> Self {
    let lhs_string = lhs.to_string();
    let rhs_string = rhs.to_string();
    let lhs = symbolic_expressions::parser::parse_str(&lhs_string).unwrap();
    let rhs = symbolic_expressions::parser::parse_str(&rhs_string).unwrap();
    Self::new(lhs, rhs)
  }

}

impl Display for Equation {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{} === {}", self.lhs, self.rhs)
  }
}

// Can the vars of this expression be instantiated to the other expression?
fn cmp_sexp_by_instantiation<F>(sexp1: &Sexp, sexp2: &Sexp, is_var: F) -> Option<std::cmp::Ordering>
where F: FnOnce(&str) -> bool + Copy {
  let sexp1_leq_sexp2 = find_instantiations(sexp1, sexp2, is_var).is_some();
  let sexp2_leq_sexp1 = find_instantiations(sexp2, sexp1, is_var).is_some();
  match (sexp1_leq_sexp2, sexp2_leq_sexp1) {
    (true, true) => Some(std::cmp::Ordering::Equal),
    (true, false) => Some(std::cmp::Ordering::Less),
    (false, true) => Some(std::cmp::Ordering::Greater),
    (false, false) => None,
  }
}

// TODO: add a precondition
#[derive(Debug, Clone)]
pub struct Prop {
  pub eq: Equation,
  pub params: Vec<(Symbol, Type)>
}

impl Prop {
  /// Creates a new Prop, alpha normalizing the parameters and reordering the
  /// Equation and params so that the lhs is smaller than the rhs and the params
  /// occur in the order they appear in the original Equation.
  ///
  /// This makes two passes over each of the two Sexps in the Equation. The
  /// first pass is comparing them to each other lexicographically (although in
  /// expectation this will not take very long). The second pass is alpha
  /// renaming them.
  pub fn new(eq: Equation, params: Vec<(Symbol, Type)>) -> Self {
    // TODO: Could probably use a more efficient data structure since iteration
    // order isn't important here.
    let param_names: BTreeSet<String> = params.iter().map(|(p, _t)| p.to_string()).collect();
    let mut param_to_alpha_renamed: BTreeMap<String, String> = BTreeMap::default();
    // First we reorder the lhs and rhs based on their lexicographic order.
    let (reordered_lhs, reordered_rhs) =
      if cmp_sexp_lexicographic(&eq.lhs, &eq.rhs, |s| param_names.contains(s)) == std::cmp::Ordering::Greater {
        (&eq.rhs, &eq.lhs)
      } else {
        (&eq.lhs, &eq.rhs)
      };
    // Then we rename the lhs and rhs. This computes the new names on-demand for
    // efficiency's sake.
    let renamed_lhs = alpha_rename_sexp(reordered_lhs, &param_names, &mut param_to_alpha_renamed);
    let renamed_rhs = alpha_rename_sexp(reordered_rhs, &param_names, &mut param_to_alpha_renamed);
    // Then we rename the parameters using the names we generated renaming the
    // lhs and rhs.
    let mut renamed_params: Vec<(Symbol, Type)> = params.into_iter().map(|(p, t)| {
      let new_name: Symbol = param_to_alpha_renamed.get(p.as_str())
        .unwrap_or_else(|| {
          panic!("param {} does not occur in equation {} == {}", p, eq.lhs, eq.rhs);
        })
        .into();
      (new_name, t)
    }).collect();
    // Finally, we reorder the parameters by their name.
    renamed_params.sort_by_key(|(p, _t)| p.as_str());

    Self {
      eq: Equation::new(renamed_lhs, renamed_rhs),
      params: renamed_params,
    }
  }

  /// Creates a new Prop without performing any alpha normalization.
  pub fn new_trusted(eq: Equation, params: Vec<(Symbol, Type)>) -> Self {
    Self { eq, params }
  }

  pub fn size(&self) -> usize {
    sexp_size(&self.eq.lhs) + sexp_size(&self.eq.rhs)
  }

}

/// We create Props a lot, so it's worth it to make this kind of weirdly
/// specialized function.
///
/// This way, we can avoid making multiple traversals of the sexps whenever we
/// make a Prop.
fn alpha_rename_sexp(sexp: &Sexp, params: &BTreeSet<String>, param_to_alpha_renamed: &mut BTreeMap<String, String>) -> Sexp {
  match sexp {
    Sexp::Empty => Sexp::Empty,
    Sexp::String(s) => {
      if params.contains(s) {
        // param_to_order.len() is equal to the number of params we've seen so
        // far.
        let num_params_seen = param_to_alpha_renamed.len();
        let new_name = param_to_alpha_renamed
          .entry(s.to_string())
          .or_insert_with(|| format!("v{}", num_params_seen));
        Sexp::String(new_name.clone())
      } else {
        Sexp::String(s.clone())
      }
    }
    Sexp::List(list) => {
      let new_list =
        list.iter()
            .map(|s| alpha_rename_sexp(s, params, param_to_alpha_renamed))
            .collect();
      Sexp::List(new_list)
    }
  }
}

/// Performs a "lexicographic" comparison between Sexps.
///
/// Empty < String < List
///
/// String-to-string separates between vars and non-vars.
///
///   Vars < Non-vars.
///
///   Var-to-var is always equal.
///
///   Non-var-to-non-var is by string comparison.
///
/// List-to-List is done by a lexicographic comparison
// NOTE: It might be faster and still good enough in practice to not distinguish
// between vars. The lookups might start to add up.
fn cmp_sexp_lexicographic<F>(sexp1: &Sexp, sexp2: &Sexp, is_var: F) -> std::cmp::Ordering
where F: FnOnce(&str) -> bool + Copy {
  match (sexp1, sexp2) {
    (Sexp::Empty, Sexp::Empty) => std::cmp::Ordering::Equal,
    (Sexp::Empty, _) => std::cmp::Ordering::Less,
    (_, Sexp::Empty) => std::cmp::Ordering::Greater,
    (Sexp::String(s1), Sexp::String(s2)) => {
      let s1_is_var = is_var(s1);
      let s2_is_var = is_var(s2);
      match (s1_is_var, s2_is_var) {
        // Non-vars just compare normally
        (false ,false) => s1.cmp(s2),
        (true, false) => std::cmp::Ordering::Less,
        (false, true) => std::cmp::Ordering::Greater,
        // Vars are always considered equal
        (true, true) => std::cmp::Ordering::Equal,
      }
    }
    (Sexp::String(_), Sexp::List(_)) => std::cmp::Ordering::Less,
    (Sexp::List(_), Sexp::String(_)) => std::cmp::Ordering::Greater,
    (Sexp::List(lst1), Sexp::List(lst2)) => {
      for (s1, s2) in lst1.iter().zip(lst2.iter()) {
        let comparison = cmp_sexp_lexicographic(s1, s2, is_var);
        if comparison != std::cmp::Ordering::Equal {
          return comparison;
        }
      }
      std::cmp::Ordering::Equal
    }
  }
}

impl PartialEq for Prop {
    fn eq(&self, other: &Self) -> bool {
      self.partial_cmp(other) == Some(std::cmp::Ordering::Equal)
    }
}

impl PartialOrd for Prop {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
      // let vars: BTreeSet<String> = self.params.iter().chain(other.params.iter()).map(|(var, _)| var.to_string()).collect();
      let is_var = |s: &str| {
        // vars.contains(s)
        self.params.iter().chain(other.params.iter()).any(|(var, _)| s == &var.to_string())
      };
      let lhs_cmp = cmp_sexp_by_instantiation(&self.eq.lhs, &other.eq.lhs, is_var);
      let rhs_cmp = cmp_sexp_by_instantiation(&self.eq.rhs, &other.eq.rhs, is_var);
      // They should be the same result, otherwise, they aren't equal
      if lhs_cmp == rhs_cmp {
        lhs_cmp
      } else {
        None
      }
    }
}

impl Eq for Prop {}

impl Display for Prop {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let formatted_params: String = self.params.iter().map(|(p, t)| {
      format!("{}: {}. ", p, t)
    }).collect();
    write!(f, "forall {}{}", formatted_params, self.eq)
  }
}

impl Hash for Prop {
  /// Props hash using their display string for simplicity's sake.
  ///
  /// This relies on the fact that we do our best to alpha-normalize and reorder
  /// the lhs and rhs such that equivalent props hash to the same value.
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    format!("{}", self).hash(state)
  }
}

pub fn sexp_size(sexp: &Sexp) -> usize {
  match sexp {
    Sexp::Empty => 0,
    Sexp::String(_) => 1,
    Sexp::List(xs) => xs.iter().map(sexp_size).sum::<usize>() + 1,
  }
}

// CK: Function is unused and I didn't feel like extending it to account for the change from
//     Env = HashMap<Symbol, Vec<Symbol>>
// to
//     Env = HashMap<Symbol, (Vec<String>, Vec<Symbol>)>
//
// pub fn mk_env(descr: &[(&str, &str)]) -> Env {
//   let mut env = Env::new();
//   for (name, cons) in descr {
//     env.insert(Symbol::from(*name), cons.split_whitespace().map(|s| Symbol::from(s)).collect());
//   }
//   env
// }
