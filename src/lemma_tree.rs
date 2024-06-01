use serde::{Serialize, Serializer, ser::{SerializeStruct, SerializeSeq}};
use std::{collections::{BTreeMap, BTreeSet, VecDeque, HashMap, HashSet}, borrow::Borrow, str::FromStr, time::Instant};

use egg::{Symbol, Id, Pattern, SymbolLang, Subst, Searcher, Var};
use itertools::{iproduct, Itertools};
use symbolic_expressions::Sexp;

use crate::{goal::{Eg, LemmaProofState, Outcome, LemmasState, Timer, Goal, GlobalSearchState, INVALID_LEMMA}, analysis::{cvecs_equal, has_counterexample_check, CanonicalForm, random_term_from_type}, ast::{Type, Equation, Prop, matches_subpattern, is_var}, goal_graph::{GoalGraph, GoalIndex, GoalNodeStatus}, config::CONFIG};

const HOLE_VAR_PREFIX: &str = "var_";
const HOLE_PATTERN_PREFIX: &str = "?";

type GoalName = Symbol;
/// We represent holes as n where n is >= 0.
///
/// By default, holes are rendered as pattern variables (e.g. ?0).
/// For example, `(add ?0 ?1)` has holes `?0` and `?1`.
///
/// However, when we make patterns containing holes into [`Sexp`]s to be used in
/// [`Prop`]s, we render them as `var_0`, `var_1`, etc.
type HoleIdx  = Symbol;

/// A pattern that corresponds to one side of a lemma. We draw inspiration from
/// Stitch's patterns.
///
/// Examples:
///     // A pattern corresponding to S (add Z Z). There are no holes in this pattern.
///     Node("S", [Node("add", [Node("Z", []), Node("Z", [])])])
///     // A pattern corresponding to S (add ?1 ?2). It has the holes ?1 and ?2.
///     Node("S", [Node("add", [Hole(1), Hole(2)])])
///
/// TODO: The representation could probably be made more efficient by use of
/// mutable references, etc.
#[derive(PartialEq, Eq, Clone)]
pub enum PatternWithHoles {
  /// A hole to be filled in eventually with another PatternWithHoles.
  Hole(HoleIdx),
  /// These are akin to the Nodes in SymbolLang.
  ///
  /// If they have 0 arguments then they are leaf nodes (constants such as Z,
  /// Nil, or variables).
  ///
  /// Otherwise they are internal nodes such as (Cons _ _) or (add _ _).
  Node(Symbol, Vec<Box<PatternWithHoles>>),
}

/// The side of the lemma
#[derive(Clone, Debug, PartialEq, Eq)]
enum Side {
  Left,
  Right,
  Both,
}

impl Side {
  /// Combine two sides: two differing sides produce `Side::Both`, otherwise the
  /// side is unchanged.
  fn merge(&self, other: &Side) -> Side {
    match (self, other) {
      (Side::Left,  Side::Left)  => Side::Left,
      (Side::Right, Side::Right) => Side::Right,
      _                          => Side::Both,
    }
  }

  /// Returns (new_lhs, new_rhs, num_substs)
  fn subst_pattern(&self, hole: HoleIdx, hole_pattern: &PatternWithHoles, (lhs, rhs): (&PatternWithHoles, &PatternWithHoles)) -> (PatternWithHoles, PatternWithHoles, usize) {
    match self {
      Self::Left => {
        let (new_lhs, lhs_substs) = lhs.subst_hole(hole, hole_pattern);
        (new_lhs, rhs.clone(), lhs_substs)
      }
      Self::Right => {
        let (new_rhs, rhs_substs) = rhs.subst_hole(hole, hole_pattern);
        (lhs.clone(), new_rhs, rhs_substs)
      }
      Self::Both => {
        let (new_lhs, lhs_substs) = lhs.subst_hole(hole, hole_pattern);
        let (new_rhs, rhs_substs) = rhs.subst_hole(hole, hole_pattern);
        (new_lhs, new_rhs, lhs_substs + rhs_substs)
      }
    }
  }
}

#[derive(Clone)]
pub struct LemmaPattern {
  lhs: PatternWithHoles,
  rhs: PatternWithHoles,
  // FIXME: The use of Side here is probably a premature optimization. Right now
  // the code does not even have the side threaded through everywhere so we have
  // to do lookups _anyway_ to figure out the side which might be more
  // inefficient that just trying to subst on both sides.
  holes: VecDeque<(HoleIdx, Type, Side)>,
  /// These are holes which we will not allow to be filled.
  locked_holes: Vec<(HoleIdx, Type, Side)>,
  next_hole_idx: usize,
  /// This is statically tracked.
  pub size: usize,
}

impl Serialize for LemmaPattern {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer {
    let mut lp = serializer.serialize_struct("LemmaPattern", 3)?;
    lp.serialize_field("pattern", &format!("{} = {}", self.lhs, self.rhs))?;
    let holes: Vec<String> = self.holes.iter().map(|(hole, _, _)| hole.to_string()).collect();
    lp.serialize_field("holes", &holes)?;
    let locked_holes: Vec<String> = self.locked_holes.iter().map(|(locked_hole, _, _)| locked_hole.to_string()).collect();
    lp.serialize_field("locked_holes", &locked_holes)?;
    lp.end()
  }
}

/// Receives args and result of a function as s-expressions and converts them to PatternWithHoles
pub fn parse_fn_defn(args: &Vec<Sexp>, to: &Sexp) -> (Vec<PatternWithHoles>, PatternWithHoles) {
  return (args.iter().map(sexp_to_pattern).collect_vec(), sexp_to_pattern(to));
}

/// Converts a Sexp to a PatternWithHoles
fn sexp_to_pattern(from: &Sexp) -> PatternWithHoles {
  match from {
    Sexp::Empty => {
      todo!("can't happen");
    }
    Sexp::String(s) => {
      if s.starts_with("?") {
        return PatternWithHoles::Hole(Symbol::from(s.to_string().clone()));
      }
      return PatternWithHoles::Node(Symbol::from(s), vec![]);
    }
    Sexp::List(args) => {
      let mut new_args = vec![];
      for arg in args[1..].into_iter() {
        new_args.push(Box::new(sexp_to_pattern(arg)));
      }
      return PatternWithHoles::Node(Symbol::from(args[0].string().unwrap()), new_args);
    }
  }
}

/// Maps from a function's name to each separate definition.
///
/// Each definition consists of a list of arguments that must match as well as a
/// substitution.
pub type FnDefs = HashMap<Symbol, Vec<(Vec<PatternWithHoles>, PatternWithHoles)>>;

impl PatternWithHoles {
  /// Finds the values we need to instantiate all holes to so self matches actual
  fn find_instantiations(&self, actual: &PatternWithHoles) -> Option<HashMap<HoleIdx, PatternWithHoles>> {
    let mut instantiations = HashMap::new();
    let successful_instantiation = self.find_instantiations_helper(&actual, &mut instantiations);
    if successful_instantiation {
      Some(instantiations)
    } else {
      // The instantiations are bogus/partial if it is not successful
      None
    }
  }

  fn find_instantiations_helper(&self, actual: &PatternWithHoles, instantiations_map: &mut HashMap<HoleIdx, PatternWithHoles>) -> bool {
    match (&self, actual) {
      (PatternWithHoles::Hole(hole_idx), _) => {
        // This pattern is just a hole that needs to be filled with actual
        let instantiation = actual.clone();
        if let Some(existing_instantiation) = instantiations_map.get(hole_idx) {
          // Past instantiations must agree
          &instantiation == existing_instantiation
        } else {
          instantiations_map.insert(hole_idx.clone(), instantiation);
          true
        }
      }
      (PatternWithHoles::Node(_, _), PatternWithHoles::Hole(_)) => {
        // Can't possibly match
        false
      }
      (PatternWithHoles::Node(name_self, args_self), PatternWithHoles::Node(name_actual, args_actual)) => {
        // Go over the args of both patterns and instantiate each arg
        if args_self.len() != args_actual.len() || name_self != name_actual {
          return false;
        }
        // Call this function for each arg in the pattern (with the corresponding arg from actual)
        args_self
            .iter()
            .zip(args_actual.iter())
            .all(|(arg_self, arg_actual)| {
              arg_self.find_instantiations_helper(arg_actual, instantiations_map)
            })
      }
    }
  }

  /// Receives function definitions and evaluates the pattern according to them,
  /// mutating the current pattern in the process.
  pub fn eval(&mut self, fn_defs: &FnDefs) {
    match self {
      // Cannot eval a hole
      Self::Hole(_) => {},
      Self::Node(name, actual_args) => {
        // First recursively evaluate all arguments.
        actual_args.iter_mut().for_each(|actual_arg| actual_arg.eval(fn_defs));
        // Then recursively evaluate the current if it is a function.
        //
        // NOTE: We assume that if it's not defined then it must be a
        // constructor (i.e. not in need of evaluation).
        if let Some(defs) = fn_defs.get(name) {
          for (def_args, def_rhs) in defs {
            let mut instantiations_map = HashMap::new();
            // Try to match all of the args against the actuals (mutating the map
            // in the process)
            if def_args.iter().zip(actual_args.iter()).all(|(def_arg, actual_arg)| {
              def_arg.find_instantiations_helper(actual_arg, &mut instantiations_map)
            }) {
              // If they all match, then perfrom the subst
              *self = def_rhs.subst_holes(&instantiations_map).0;
              // Continue evaluating
              self.eval(fn_defs);
              return;
            }
          }
        }
      }
    }
  }

  /// Is it a leaf (either a Hole or a Node without arguments)?
  fn is_leaf(&self) -> bool {
    match self {
      PatternWithHoles::Hole(_) => true,
      PatternWithHoles::Node(_, args) => args.is_empty(),
    }
  }

  /// Mutates the pattern to fill the hole.
  ///
  /// The usize indicates how many substitutions actually happened.
  fn fill_hole(&mut self, hole: HoleIdx, value: &PatternWithHoles) -> usize {
    match self {
      PatternWithHoles::Hole(h) if *h == hole => {
        *self = value.clone();
        1
      }
      PatternWithHoles::Hole(_) => {
        0
      }
      PatternWithHoles::Node(_, args) => {
        args.iter_mut().map(|arg| arg.fill_hole(hole, value)).sum()
      }
    }
  }

  /// Returns a new pattern where the hole is filled.
  ///
  /// The usize indicates how many substitutions actually happened.
  fn subst_hole(&self, hole: HoleIdx, value: &PatternWithHoles) -> (PatternWithHoles, usize) {
    match &self {
      PatternWithHoles::Hole(h) if *h == hole => {
        (value.clone(), 1)
      }
      PatternWithHoles::Hole(_) => {
        (self.clone(), 0)
      }
      PatternWithHoles::Node(op, args) => {
        let mut holes_filled = 0;
        let new_pat = PatternWithHoles::Node(*op, args.iter().map(|arg| {
          let (new_arg, arg_holes_filled) = arg.subst_hole(hole, value);
          holes_filled += arg_holes_filled;
          Box::new(new_arg)
        }).collect());
        (new_pat, holes_filled)
      }
    }
  }

  fn subst_holes(&self, subst: &HashMap<HoleIdx, PatternWithHoles>) -> (PatternWithHoles, usize) {
    match &self {
      PatternWithHoles::Hole(h) => {
        if let Some(new) = subst.get(&h) {
          (new.clone(), 1)
        } else {
          (self.clone(), 0)
        }
      }
      PatternWithHoles::Node(op, args) => {
        let mut holes_filled = 0;
        let new_pat = PatternWithHoles::Node(*op, args.iter().map(|arg| {
          let (new_arg, arg_holes_filled) = arg.subst_holes(subst);
          holes_filled += arg_holes_filled;
          Box::new(new_arg)
        }).collect());
        (new_pat, holes_filled)
      }
    }

  }

  /// Returns all holes in the Pattern
  ///
  /// TODO: Could probably be made into an iterator if we make an assumption
  /// that it is a set.
  fn holes(&self) -> BTreeSet<HoleIdx> {
    fn helper(pat: &PatternWithHoles, holes: &mut BTreeSet<HoleIdx>) {
      match pat {
        PatternWithHoles::Hole(idx) => {
          holes.insert(*idx);
        }
        PatternWithHoles::Node(_, args) => {
          args.iter().for_each(|arg| helper(arg, holes));
        }
      }
    }
    let mut holes = BTreeSet::new();
    helper(self, &mut holes);
    holes
  }

  /// Converts to a Pattern in egg, where each hole becomes a pattern variable.
  ///
  /// TODO: If this is used often, could this be more efficient than rendering
  /// as a String and re-parsing?
  fn to_pattern(&self) -> Pattern<SymbolLang> {
    self.to_string().parse().unwrap()
  }

  fn write_with_hole_prefix<T: std::fmt::Write>(&self, hole_prefix: &str, f: &mut T) -> std::fmt::Result {
    match self {
      PatternWithHoles::Hole(idx) => {
        write!(f, "{}{}", hole_prefix, idx)
      }
      PatternWithHoles::Node(op, args) => {
        if args.is_empty() {
          write!(f, "{}", op)
        } else {
          write!(f, "({}", op)?;
          args.iter().try_for_each(|arg| {
            write!(f, " ")?;
            arg.write_with_hole_prefix(hole_prefix, f)
          })?;
          write!(f, ")")
        }
      }
    }
  }

  fn to_sexp(&self) -> Sexp {
    let mut s = String::new();
    let _ = self.write_with_hole_prefix(HOLE_VAR_PREFIX, &mut s);
    symbolic_expressions::parser::parse_str(&s).unwrap()
  }

}

impl std::fmt::Display for PatternWithHoles {
  /// Formats the LemmaPattern as a sexp.
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    self.write_with_hole_prefix(HOLE_PATTERN_PREFIX, f)
  }
}

impl std::fmt::Display for LemmaPattern {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{} = {}", self.lhs, self.rhs)
  }
}

impl LemmaPattern {

  /// The root pattern of type `ty`; its LHS and RHS are unconstrained.
  pub fn empty_pattern(ty: Type) -> LemmaPattern {
    let hole_0 = Symbol::new("0");
    let hole_1 = Symbol::new("1");

    LemmaPattern {
      lhs: PatternWithHoles::Hole(hole_0),
      rhs: PatternWithHoles::Hole(hole_1),
      // In reverse order because we pop from the back (not that it really matters)
      holes: [(hole_1, ty.clone(), Side::Right), (hole_0, ty.clone(), Side::Left)].into(),
      locked_holes: vec!(),
      next_hole_idx: 2,
      size: 2,
    }
  }

  fn new_pattern_from_subst(&self, hole: HoleIdx, hole_pattern: &PatternWithHoles, hole_pattern_size: usize, side: &Side, new_holes: VecDeque<(HoleIdx, Type, Side)>, next_hole_idx: usize) -> LemmaPattern {
    let (lhs, rhs, num_substs) = side.subst_pattern(hole, hole_pattern, (&self.lhs, &self.rhs));
    // println!("current pattern {}, size {}, hole {}, hole pat {}, new size {}", self, self.size, hole, hole_pattern, self.size + (num_substs * (hole_pattern_size - 1)));
    LemmaPattern {
      lhs,
      rhs,
      holes: new_holes,
      locked_holes: self.locked_holes.clone(),
      next_hole_idx,
      // The size gets increased by (hole_pattern_size - 1) for each substitution.
      //
      // This is because holes have a size of 1 on their own.
      size: self.size + (num_substs * (hole_pattern_size - 1)),
    }
  }

  /// Returns a new [`LemmaPattern`] with `hole` filled with a new [`PatternWithHoles`]
  /// made from the constructor `node` with type `node_ty` (so unless the hole is
  /// being filled with a leaf, `node` will be a function and will have new holes
  /// added for it).
  ///
  /// Invariant: hole must not be locked.
  fn subst_hole(&self, hole: HoleIdx, node: Symbol, node_ty: &Type) -> LemmaPattern {
    // println!("substituting {} with {} in {}", hole, node, self);
    let (side, _) = self.hole_side_type(hole);
    let (arg_tys, _ret_ty) = node_ty.args_ret();
    let num_args = arg_tys.len();
    let mut new_holes: VecDeque<(HoleIdx, Type, Side)> = arg_tys
      .into_iter()
      .enumerate()
      .map(|(arg_idx, arg_ty)| {
        let new_hole = self.next_hole_idx + arg_idx;
        (Symbol::new(format!("{}", new_hole)), arg_ty, side.clone())
      }).collect();
    let next_hole_idx = self.next_hole_idx + num_args;
    let new_pattern = PatternWithHoles::Node(node, new_holes.iter().map(|(hole, _, _)| {
      Box::new(PatternWithHoles::Hole(*hole))
    }).collect()
    );
    let mut holes_without_subst_hole = self.holes.iter()
                          .filter(|(curr_hole, _, _)| curr_hole != &hole)
                          .cloned();
    // Add the current holes to the end (this is what we want because we pop
    // from the back).
    new_holes.extend(&mut holes_without_subst_hole);
    // The new size is the number of args + the constructor.
    //
    // FIXME:
    // HACK: we actually add an extra 1 to the sum if num_args > 0 because when
    // we represent this as an sexp it becomes a list and for sexp size we
    // add 1 to lists. it's dumb, i know, but we need to consistently
    // switch to using LemmaPatterns everywhere otherwise our size values
    // will be inconsistent.
    let new_pattern_size = if num_args == 0 {
      1
    } else {
      num_args + 2
    };
    self.new_pattern_from_subst(hole, &new_pattern, new_pattern_size, &side, new_holes, next_hole_idx)
  }

  /// Sets `hole_1` equal to `hole_2` in the new pattern.
  ///
  /// Invariant: `hole_1` must be not locked and `hole_2` must be locked.
  fn unify_holes(&self, hole_1: HoleIdx, hole_2: HoleIdx) -> LemmaPattern {
    // println!("unifying {} and {} in {}", hole_1, hole_2, self);
    let (hole_1_side, _) = self.hole_side_type(hole_1);
    // The types should be the same, so ignore the second one without loss of
    // generality.
    let (hole_2_side, _) = self.hole_side_type(hole_2);
    let unified_hole_side = hole_1_side.merge(hole_2_side);
    // Update hole_2's side with the new unified side.
    let new_locked_holes: Vec<_> = self.locked_holes.iter().map(|(curr_hole, curr_ty, curr_side)| {
      if *curr_hole == hole_2 {
        (*curr_hole, curr_ty.clone(), unified_hole_side.clone())
      } else {
        (*curr_hole, curr_ty.clone(), curr_side.clone())
      }
    }).collect();
    let new_holes: VecDeque<_> = self.holes.iter().filter(|(curr_hole, _, _)| *curr_hole != hole_1)
      .cloned().collect();
    let hole_2_pattern = PatternWithHoles::Hole(hole_2);
    let (lhs, rhs, _) = hole_1_side.subst_pattern(hole_1, &hole_2_pattern, (&self.lhs, &self.rhs));
    let lp = LemmaPattern {
      lhs,
      rhs,
      holes: new_holes,
      locked_holes: new_locked_holes,
      next_hole_idx: self.next_hole_idx,
      size: self.size,
    };
    // println!("unifying {} and {} in {} produces {}", hole_1, hole_2, self, lp);
    lp
  }

  fn hole_side_type(&self, hole: HoleIdx) -> (&Side, &Type) {
    // println!("looking for the {} hole on {}", hole, self);
    // println!("holes: {:?}, locked holes: {:?}", self.holes, self.locked_holes);

    // This lookup is in theory inefficient and we could restructure things by
    // having the ClassMatch not only its holes but what sides the holes come
    // from, but I expect the number of holes will be relatively small.
    self.holes.iter().chain(self.locked_holes.iter()).find_map(|(curr_hole, curr_ty, curr_side)| {
      if &hole == curr_hole {
        Some((curr_side, curr_ty))
      } else {
        None
      }
    }).unwrap()
  }

  pub fn to_lemma(&self) -> Prop {
    // Both holes and locked holes are paramters; whether a hole is locked is
    // just a implementation detail.
    let params = self.holes.iter()
                           .chain(self.locked_holes.iter())
                           .map(|(hole, hole_ty, _side)| {
      (Symbol::new(format!("{}{}", HOLE_VAR_PREFIX, hole)), hole_ty.clone())
    }).collect();
    let lhs = self.lhs.to_sexp();
    let rhs = self.rhs.to_sexp();
    // This does alpha-renaming.
    Prop::new(Equation::new(lhs, rhs), params)
  }

  fn is_consistent(&self) -> bool {
    let pattern_holes: BTreeSet<HoleIdx> = self.lhs.holes().union(&self.rhs.holes()).cloned().collect();
    let all_holes: BTreeSet<HoleIdx> = self.holes.iter().chain(self.locked_holes.iter()).map(|(hole, _, _)| {
      *hole
    }).collect();
    pattern_holes.is_subset(&all_holes) && all_holes.is_subset(&pattern_holes)
  }

  /// Does a simple congruence check to see if a simpler lemma exists.
  ///
  /// Example:
  ///
  ///     (add ?0 (add ?1 ?2)) = (add ?0 (add ?2 ?1))
  ///
  /// The above lemma has a simpler lemma:
  ///
  ///     (add ?1 ?2) = (add ?2 ?1)
  ///
  /// The simpler lemma implies the original one by congruence.
  ///
  /// So we check the LHS and RHS of the lemma to see if they start with the
  /// same symbol. If they do, we then check if all but one of their children
  /// are equal (or if all of them are equal, although this is a trivial case
  /// which shouldn't occur the way we generate lemmas). If this is true, then
  /// we know that a simpler lemma exists. This is because our cvec analysis is
  /// guaranteed to enumerate all pairs of e-classes with equal cvecs: the only
  /// mismatched pair of children should therefore also have been enumerated and
  /// we will already be proposing it as a lemma.
  fn has_simpler_lemma(&self) -> bool {
    match (&self.lhs, &self.rhs) {
      (PatternWithHoles::Node(op1, children1), PatternWithHoles::Node(op2, children2)) if op1 == op2 => {
        let mut au_pairs: Vec<_> = children1.iter().zip(children2.iter()).filter(|(child1, child2)| child1 != child2).collect();
        // All pairs match except for 1 or fewer
        if au_pairs.len() <= 1 {
          return true;
        }
        // Additionally, we will check to see if one pair being equal will imply
        // all the rest. Direction matters in this case.
        //
        // We want to consider the following lemma
        //
        // (add ?0 ?1) = add (?1 ?0)
        //
        // But not this lemma
        //
        // (add ?0 ?0) = (add ?1 ?1)
        //
        // Although it is not impossible that (?0 != ?1)
        // but (add ?0 ?0 = add ?1 ?1).
        let (au_child1, au_child2) = au_pairs.pop().unwrap();
        au_pairs.into_iter().all(|(child1, child2)| child1 == au_child1 && child2 == au_child2)
      }
      _ => false
    }
  }

}

/// A data structure that represents a multipattern match of a [`LemmaPattern`].
///
/// `lhs` and `rhs` match the LHS and RHS of the pattern.
///
/// TODO: Should we cache a map from `Id` to `Vec<HoleIdx>`? This will allow us
/// to more efficiently compute which holes we could possibly unify.
#[derive(Clone)]
pub struct ClassMatch {
  /// Which goal does this match come from?
  origin: GoalIndex,
  lhs: Id,
  rhs: Id,
  /// First field: what e-classes the holes in the pattern match to.
  ///
  /// Secon field: what e-classes have we visited on the path to the current
  /// hole and how many times have we visited them?
  subst: BTreeMap<HoleIdx, (Id, BTreeMap<Id, usize>)>,
  /// Whether the `lhs` and `rhs` cvecs are equal (we compute this once so we
  /// don't need to repeat the process).
  ///
  /// TODO: It seems rather unnecessary to consider pairs with unequal cvecs. We
  /// would expect that most are going to be unequal (even among pairs of the
  /// same type). We should see to what extent these types of matches are useful
  /// (I expect that they are mostly useful for filtering out way-too-general
  /// lemmas). However, the argument in favor of them is that because we
  /// enumerate them anyway, their propagation probably doesn't take too long
  /// and they are useful to clear out trivially invalid lemmas.
  cvecs_equal: bool,
  /// How many times have we generalized a term on this match?
  ///
  /// This corresponds to "locking" a hole on the match when the hole
  /// contains something that isn't a var.
  num_generalizations: usize,
}

impl ClassMatch {
  /// Constructs a top-level match (i.e. one for the top-level pattern, where
  /// lhs is the pattern ?0 and rhs is the pattern ?1).
  pub fn top_match(origin: GoalIndex, lhs: Id, rhs: Id, cvecs_equal: bool) -> Self {
    let mut subst = BTreeMap::default();
    subst.insert(Symbol::new("0"), (lhs, BTreeMap::default()));
    subst.insert(Symbol::new("1"), (rhs, BTreeMap::default()));
    Self {
      origin,
      lhs,
      rhs,
      subst,
      cvecs_equal,
      num_generalizations: 0,
    }
  }
}

/// FIXME: This information is out of date
/// These are the nodes which make up our overall lemma search tree. Each node
/// represents a lemma over universally quantified variables created from its
/// holes. A node's children are all lemmas that are less general than it,
/// because children are created by filling in a hole.
///
/// It's a little difficult to conceptualize a node's state, so here we discuss
/// its possiblities.
///
/// First, if a node's `has_matching_cvecs` is `false`, we will neither
/// conjecture a lemma from it nor will we propagate its `current_matches` to
/// its children. This is because we have no evidence that the lemma or its
/// child lemmas could plausibly be true (in fact, we may have evidence that the
/// lemma the node represents is false).
///
/// Otherwise, there must be some matching cvecs among the `current_matches`. If
/// there is any [`ClassMatch`] with _mismatching_ cvecs, we can immediately set
/// `lemma_status` to `Some(Invalid)` - this is because this match represents a
/// counterexample to the lemma's validity.
///
/// If there are only equal cvecs among the `current_matches` (and there is at
/// least one match - this should be guaranteed), we will attempt to prove the
/// lemma represented by this node.
///
/// Once we have finished trying to prove the lemma (or if it was invalidated),
/// we will check the lemma's status. If it is `Proven`, then this node is done.
/// Otherwise, we propagate the `current_matches` downwards, creating new
/// children.
///
/// TODO: since [`ClassMatch`]es contain information about which goal (and
/// subsequently, lemma), they come from, can we use this information to
/// discover which goals a lemma might be useful in. We might be able to do this
/// instead of tracking this information in the goal graph.
#[derive(Clone, Serialize)]
pub struct LemmaTreeNode {
  /// The pattern which represents the current lemma.
  pattern: LemmaPattern,
  /// The index of the lemma corresponding to this node in the LemmaTree
  pub lemma_idx: usize,
  /// The GoalIndex that is associated with this lemma in the GoalGraph.
  pub goal_index: GoalIndex,
  /// These matches are transient: we will propagate them through the e-graph if
  /// we cannot prove the lemma this node represents (or if it is an invalid
  /// lemma).
  ///
  /// When we create a `LemmaTreeNode`, it needs to have at least one match.
  #[serde(skip_serializing)]
  current_matches: VecDeque<ClassMatch>,
  /// What's the status of the lemma? (`None` if we haven't attempted this
  /// lemma).
  pub lemma_status: Option<LemmaStatus>,
  /// Are we allowed to propagate matches by filling a hole with the contents of
  /// its matched eclass?
  ///
  /// We force nodes created from unifying holes to only unify holes afterwards
  /// because otherwise we will have many duplicates.
  ///
  /// Consider the root ?0 = ?1
  ///
  /// In one branch, we could set ?0 = (S ?2) and ?1 = (S ?3), yielding the
  /// node (S ?2) = (S ?3). Then suppose we unify ?2 and ?3, yielding
  /// (S ?2) = (S ?2).
  ///
  /// In another branch, we could instead unify ?0 and ?1, yielding ?0 = ?0.
  /// If we allow propagation in this branch, then we could set ?0 = S ?2, yielding
  /// (S ?2) = (S ?2).
  match_enode_propagation_allowed: bool,
  /// Lemmas that are refinements of the `pattern` in this node. We identify
  /// them using the hole that was filled and what it was filled with.
  #[serde(serialize_with = "serialize_children_map")]
  children: BTreeMap<LemmaTreeEdge, LemmaTreeNode>,
  /// For debugging purposes only
  first_match: ClassMatch,
}

impl Serialize for ClassMatch {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer {
    let s = self.subst.iter().map(|(hole, (class, _past_classes))| format!("{}: {}", hole, class)).join(", ");
    serializer.serialize_str(&s)
  }
}

fn serialize_children_map<S>(children: &BTreeMap<LemmaTreeEdge, LemmaTreeNode>, serializer: S) -> Result<S::Ok, S::Error>
where S: Serializer {
  let mut s = serializer.serialize_seq(Some(children.len()))?;
  children.iter().try_for_each(|(edge, node)| {
    s.serialize_element(&(edge, node))
  })?;
  s.end()
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Serialize)]
pub enum LemmaStatus {
  Valid,
  Invalid,
  Inconclusive,
  InQueue,
  Dead,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Serialize)]
struct LemmaTreeEdge {
  #[serde(serialize_with = "crate::utils::serialize_symbol")]
  hole: HoleIdx,
  filled_with: FilledWith,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
/// What did we fill a hole with?
enum FilledWith {
  /// This represents a hole being instantiated to a function or constant in the
  /// e-graph. The `Symbol` is the name of this function or constant.
  ENode(Symbol),
  /// This represents the unification of two different holes.
  ///
  /// Philosophical question: can you fill a hole with another hole?
  AnotherHole(HoleIdx),
  /// Not exactly something that the hole is "filled with," this represents the
  /// hole never being allowed to be filled.
  Lock,
}

impl FilledWith {
  fn is_enode(&self) -> bool {
    match self {
      Self::ENode(_) => true,
      _ => false,
    }
  }
}

impl Serialize for FilledWith {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer {
    let s = match self {
      Self::ENode(symb) => {
        format!("ENode({})", symb)
      }
      Self::AnotherHole(hole_idx) => {
        format!("{}", hole_idx)
      }
      Self::Lock => {
        format!("Lock")
      }
    };
    serializer.serialize_str(&s)
  }
}

impl ClassMatch {
  /// Which pairs of holes could we unify while still keeping this match?
  fn unifiable_holes(&self) -> Vec<(HoleIdx, HoleIdx)> {
    let mut class_to_holes: HashMap<Id, Vec<HoleIdx>> = HashMap::new();
    for (hole, (class, _past_classes)) in self.subst.iter() {
      class_to_holes.entry(*class)
                    .and_modify(|holes| holes.push(*hole))
                    .or_insert(vec!(*hole));
    }
    class_to_holes.into_iter().flat_map(|(_class, holes)| {
      if holes.len() <= 1 {
        vec!()
      } else {
        iproduct!(&holes, &holes)
          // if hole_1 and hole_2 are distinct and map to the same e-class, we
          // only want to return one of (hole_1, hole_2) and (hole_2, hole_1).
          .filter(|(hole_1, hole_2)| hole_1 < hole_2)
          .map(|(hole_1, hole_2)| (*hole_1, *hole_2))
          .collect()
      }
    }).collect()
  }

  /// Which holes can unify with this hole (other than itself)?
  fn holes_unifiable_with<I: IntoIterator<Item = HoleIdx>>(&self, hole: HoleIdx, hole_candidates: I) -> Vec<HoleIdx> {
    let (hole_class, _past_classes) = &self.subst[&hole];
    hole_candidates.into_iter().filter_map(|other_hole| {
      if hole != other_hole && *hole_class == self.subst[&other_hole].0  {
        Some(other_hole)
      } else {
        None
      }
    }).collect()
  }
}

// FIXME: I think we no longer need this; all of the allocs were taking a lot of
// time. We aren't actually using its output so I think we can axe it.
#[derive(Default, Clone)]
pub struct PropagateMatchResult {
  // pub new_lemmas: Vec<(GoalIndex, Prop)>,
  // /// In theory we should only ever need the new lemmas, but these are used to
  // /// track dependencies in the goal graph.
  // ///
  // /// TODO: do a restructuring that obviates the need for this field - probably
  // /// we will want to thread the global lemma state through the lemma tree when
  // /// we propagate matches in order to annotate lemma tree nodes with their
  // /// lemma number as well as the parent relation that is tracked in the goal
  // /// graph.
  // ///
  // /// This also will probably mean putting all of the LemmaTreeNodes into a map
  // /// the same way we have all lemmas in a map somewhere so that we can jump
  // /// between them easily.
  // pub existing_lemmas: Vec<(GoalIndex, Prop)>,
  pub num_propagated_matches: usize,
}

impl PropagateMatchResult {
  fn merge(&mut self, rhs: Self) {
    // self.new_lemmas.append(&mut rhs.new_lemmas);
    // self.existing_lemmas.append(&mut rhs.existing_lemmas);
    self.num_propagated_matches += rhs.num_propagated_matches;
  }
}

impl LemmaTreeNode {
  // FIXME: lemma_depth is unused and should be replaced by a size.
  pub fn from_pattern(pattern: LemmaPattern, lemma_idx: usize, lemma_size: usize, first_match: ClassMatch) -> LemmaTreeNode {
    let goal_index = GoalIndex::from_lemma(Symbol::new(format!("lemma_{}", lemma_idx)), pattern.to_lemma().eq, lemma_idx, lemma_size);
    // (sort of)
    // HACK: if any hole does not appear on both sides, we consider it a free variable.
    // If there are more free variables than allowed (by default we only allow 1), we
    // will declare the lemma invalid immediately.
    //
    // While there are certainly some lemmas for which this might be relevant, such as
    //
    // mul x Z = Z
    //
    // The vast majority should not have free variables (or at most 1, like in
    // this example).
    //
    // FIXME: Figure out a better heuristic for invalidating intermediate lemmas
    // that are too general.
    let mut num_free_vars = 0;
    let mut has_arrow = false;
    pattern.holes.iter().chain(pattern.locked_holes.iter()).for_each(|(_hole, ty, side)| {
      if side != &Side::Both {
        num_free_vars += 1;
      }
      if ty.is_arrow() {
        has_arrow = true;
      }
    });
    let lemma_status = if pattern.has_simpler_lemma() {
      // HACK: if there is a simpler lemma, we will declare this pattern dead and not try it.
      Some(LemmaStatus::Dead)
    // } else if num_free_vars > CONFIG.num_free_vars_allowed {
    //   Some(LemmaStatus::Invalid)
    // // } else if !pattern.holes.is_empty() {
    // //   Some(LemmaStatus::Invalid)
    // NOTE: We don't know how to do a counterexample check for arrows.
    } else if has_arrow {
      Some(LemmaStatus::Dead)
    } else {
      None
    };
    // if !pattern.is_consistent() {
    //   panic!("Pattern {} is inconsistent! holes: {:?}, locked holes: {:?}", pattern, pattern.holes, pattern.locked_holes);
    // }
    LemmaTreeNode {
      pattern,
      lemma_idx,
      goal_index,
      current_matches: VecDeque::default(),
      lemma_status,
      match_enode_propagation_allowed: true,
      children: BTreeMap::default(),
      first_match,
    }
  }

  fn has_counterexample(&self, global_search_state: &GlobalSearchState) -> bool {
    // println!("{}", self.pattern);
    // let start_time = Instant::now();
    for _ in 0..CONFIG.cvec_size {
      let rand_subst = self.pattern.holes.iter().chain(self.pattern.locked_holes.iter())
        .map(|(hole, ty, _)| {
          let rand_sexp = random_term_from_type(ty, global_search_state.env, global_search_state.context, CONFIG.cvec_term_max_depth);
          (*hole, sexp_to_pattern(&rand_sexp))
      }).collect();
      let mut rand_subst_lhs = self.pattern.lhs.subst_holes(&rand_subst).0;
      rand_subst_lhs.eval(global_search_state.defs_for_eval);
      let mut rand_subst_rhs = self.pattern.rhs.subst_holes(&rand_subst).0;
      rand_subst_rhs.eval(global_search_state.defs_for_eval);
      if rand_subst_lhs != rand_subst_rhs {
        // let end_time = Instant::now();
        // println!("{}us to find counterexample", (end_time - start_time).as_micros());
        return true;
      }
    }
    // let end_time = Instant::now();
    // println!("{}us to fail to find counterexample", (end_time - start_time).as_micros());
    false
  }

  /// Attempts to propagate the match, returning the number of new
  /// [`LemmaTreeNode`]s we create in the process (`None` if there are no
  /// matches to propagate - this could either be because the matches ).
  ///
  /// FIXME: refactor this into separate parts for unifying holes using a match,
  /// "locking in" a hole, and propagating a match via its enodes.
  fn propagate_match<'a>(&mut self, timer: &Timer, m: ClassMatch, lemmas_state: &mut LemmasState, goal_graph: &mut GoalGraph, lemma_proofs: &BTreeMap<usize, LemmaProofState<'a>>) -> PropagateMatchResult {
    if timer.timeout() {
      return PropagateMatchResult::default();
    }
    // Nothing to propagate
    if self.pattern.holes.is_empty() {
      return PropagateMatchResult::default();
    }
    // The match isn't "live" any more because its corresponding lemma has been
    // (dis)proven.
    if let Some(lemma_proof_state) = lemma_proofs.get(&m.origin.lemma_id) {
      match lemma_proof_state.outcome {
        Some(Outcome::Valid) | Some(Outcome::Invalid) => {
          return PropagateMatchResult::default();
        }
        _ => {}
      }
    }
    let mut propagate_result = PropagateMatchResult::default();
    let (current_hole, _, _) = *self.pattern.holes.back().unwrap();
    // First, obtain the goal that this match comes from.
    //
    // TODO: refactor the goal graph to couple it better with the lemma tree.
    // This is incredibly gross.
    // let goal_node = goal_graph.goal_map[&m.origin.name].as_ref().borrow();
    let parent_lemma_state = &lemma_proofs[&goal_graph.goal_map[&m.origin.name].as_ref().borrow().lemma_id];
    // If this goal's lemma has been proven or invalidated, then we won't
    // propagate it.
    if parent_lemma_state.outcome == Some(Outcome::Valid) || parent_lemma_state.outcome == Some(Outcome::Invalid) {
      return PropagateMatchResult::default();
    }

    let goal = parent_lemma_state.goals.iter().find_map(|g| {
      if g.name == m.origin.name {
        Some(g)
      } else {
        None
      }
    }).unwrap();

    propagate_result.merge(self.propagate_match_lock_hole(timer, current_hole, &m, goal, lemmas_state, goal_graph, lemma_proofs));
    if !self.match_enode_propagation_allowed {
      // If we aren't allowed to propagate via enodes, just return what we have
      // so far.
      return propagate_result;
    }
    propagate_result.merge(self.propagate_match_fill_with_enode(timer, current_hole, &m, goal, lemmas_state, goal_graph, lemma_proofs));
    // if self.children.keys().any(|key| key.hole != current_hole) {
    //   println!("current pattern: {}, current holes: {:?}, current locked holes: {:?}", self.pattern, self.pattern.holes, self.pattern.locked_holes);
    //   self.children.keys().for_each(|key| {
    //     println!("child edge fills hole {} with {:?}", key.hole, key.filled_with);
    //   });
    //   panic!("somehow there's a key that isn't equal to the current hole!");
    // }
    propagate_result
  }

  fn propagate_match_lock_hole<'a>(&mut self, timer: &Timer, current_hole: HoleIdx, m: &ClassMatch, goal: &Goal<'a>, lemmas_state: &mut LemmasState, goal_graph: &mut GoalGraph, lemma_proofs: &BTreeMap<usize, LemmaProofState<'a>>) -> PropagateMatchResult {
    let mut propagate_result = PropagateMatchResult::default();
    // We will try to unify this hole with any existing locked holes.
    let unifiable_holes = m.holes_unifiable_with(current_hole, self.pattern.locked_holes.iter().map(|(hole, _, _)| *hole));
    for other_hole in unifiable_holes {
      let edge = LemmaTreeEdge {
        hole: current_hole,
        filled_with: FilledWith::AnotherHole(other_hole),
      };
      let mut new_match = m.clone();
      // Remove current_hole: we're replacing it with other_hole.
      let (_class, prev_classes) = new_match.subst.remove(&current_hole).unwrap();
      let (_, other_hole_prev_classes) = &mut new_match.subst.get_mut(&other_hole).unwrap();
      // Merge the prev_classes from the two holes
      prev_classes.into_iter().for_each(|(class, count)| {
        other_hole_prev_classes.entry(class)
                               .and_modify(|c| {
                                 *c = std::cmp::max(*c, count);
                               })
                               .or_insert(count);
      });
      if let Some(child_node) = self.children.get_mut(&edge) {
        propagate_result.merge(child_node.add_match(timer, new_match, lemmas_state, goal_graph, lemma_proofs));
        // propagate_result.existing_lemmas.push((m.origin.clone(), child_node.pattern.to_lemma()));
        propagate_result.num_propagated_matches += 1;
      // We only will create new nodes if there is a match.
      //
      // TODO: This means that matches with unequal cvecs have less power to
      // invalidate lemmas because there's an ordering issue. If we propagate a
      // match with unequal cvecs and discard a specialization of the match
      // because the child node doesn't yet exist, then if we add that node
      // later we might not discover it's invalid. However, this shouldn't be a
      // huge concern because 1) we should expect that most matches with equal
      // cvecs correspond to legitimate lemmas and 2) the cvec analysis for the
      // lemma will hopefully invalidate it, although generating the e-graph for
      // this lemma will probably take time.
      } else if m.cvecs_equal {
        let pattern = self.pattern.unify_holes(current_hole, other_hole);
        // TODO: look up the lemma's result if it has one.
        let lemma = pattern.to_lemma();
        // If any holes are not vars, then this is a generalized lemma.
        let is_generalized = new_match.subst.values().any(|(class, _)|{
          match goal.egraph[*class].data.canonical_form_data {
            CanonicalForm::Var(_) => false,
            _ => true,
          }
        });
        // FIXME: This is super hacky. We temporarily make the lemma node's
        // state invalid before righting it.
        let mut lemma_node = LemmaTreeNode::from_pattern(pattern, INVALID_LEMMA, self.goal_index.lemma_size, new_match.clone());
        if lemma_node.lemma_status.is_none() {
          // assert_eq!(is_generalized, new_match.num_generalizations > 0);
          if is_generalized && lemma_node.has_counterexample(&goal.global_search_state) {
            lemma_node.lemma_status = Some(LemmaStatus::Invalid);
          } else {
            let lemma_idx = lemmas_state.find_or_make_fresh_lemma(lemma.clone(), 0);
            lemma_node.lemma_idx = lemma_idx;
            lemma_node.goal_index.lemma_id = lemma_idx;
            lemma_node.goal_index.name = Symbol::new(&format!("lemma_{}", lemma_idx));
          }
        }
        // Kill the branch if it has a rejected subpattern.
        // if lemma_node.lemma_status.is_none() && lemmas_state.rejected_lemma_subpatterns.iter().any(|subpattern| matches_subpattern(&lemma.eq.lhs, subpattern, is_var) || matches_subpattern(&lemma.eq.rhs, subpattern, is_var) ) {
        //   lemma_node.lemma_status = Some(LemmaStatus::Dead);
        // }
        // We force nodes created from unifying holes to be a leaf because otherwise we will have
        // many duplicates.
        //
        // FIXME: this is no longer true due to a refactor, we should probably
        // just remove the field entirely.
        // lemma_node.match_enode_propagation_allowed = false;
        propagate_result.merge(lemma_node.add_match(timer, new_match, lemmas_state, goal_graph, lemma_proofs));
        // propagate_result.new_lemmas.push((m.origin.clone(), lemma_node.pattern.to_lemma()));
        // println!("current node pattern {}\n holes {:?}, locked holes {:?}", self.pattern, self.pattern.holes, self.pattern.locked_holes);
        // println!("new node pattern {}\n holes {:?}, locked holes {:?}", lemma_node.pattern, lemma_node.pattern.holes, lemma_node.pattern.locked_holes);
        self.children.insert(edge, lemma_node);
      }
    }

    // Next, we will create an edge corresponding to "locking" or preventing the
    // current hole from being filled.
    let lock_edge = LemmaTreeEdge {
      hole: current_hole,
      filled_with: FilledWith::Lock,
    };
    let mut new_match = m.clone();
    // If we lock a hole that isn't a variable, this means we are doing a
    // generalization.
    match &goal.egraph[new_match.subst[&current_hole].0].data.canonical_form_data {
      CanonicalForm::Var(_) => {},
      _ => {
        new_match.num_generalizations += 1;
      }
    }
    // The only time we can generalize is at this point (unifying a hole implies
    // that we do the same generalization in both places), so we check here that
    // we aren't doing too many first.
    if new_match.num_generalizations > CONFIG.max_num_generalizations {
      return propagate_result;
    }
    if let Some(child_node) = self.children.get_mut(&lock_edge) {
      propagate_result.merge(child_node.add_match(timer, new_match, lemmas_state, goal_graph, lemma_proofs));
      // The lemma for the child is the same, so we won't add it to the propagation list
      propagate_result.num_propagated_matches += 1;
    } else {
      // Create a new node where we move the current hole to the locked holes.
      //
      // We zero out the current matches and children but keep everything else
      // the same since the node is not fundamentally changed.
      let mut new_node = LemmaTreeNode {
        pattern: self.pattern.clone(),
        lemma_idx: self.lemma_idx,
        goal_index: self.goal_index.clone(),
        current_matches: VecDeque::default(),
        lemma_status: self.lemma_status.clone(),
        match_enode_propagation_allowed: self.match_enode_propagation_allowed,
        children: BTreeMap::default(),
        first_match: self.first_match.clone(),
      };
      let (hole_loc, _) = new_node.pattern.holes.iter().find_position(|(hole, _, _)| *hole == current_hole).unwrap();
      let hole_info = new_node.pattern.holes.remove(hole_loc).unwrap();
      new_node.pattern.locked_holes.push(hole_info);
      // Now propagate the match.
      propagate_result.merge(new_node.add_match(timer ,new_match, lemmas_state, goal_graph, lemma_proofs));
      propagate_result.num_propagated_matches += 1;
      // println!("current node pattern {}\n holes {:?}, locked holes {:?}", self.pattern, self.pattern.holes, self.pattern.locked_holes);
      // println!("new node pattern {}\n holes {:?}, locked holes {:?}", new_node.pattern, new_node.pattern.holes, new_node.pattern.locked_holes);
      // if !new_node.pattern.is_consistent() {
      //   panic!("inconsistent pattern")
      // }
      self.children.insert(lock_edge, new_node);
    }
    propagate_result
  }

  fn propagate_match_fill_with_enode<'a>(&mut self, timer: &Timer, current_hole: HoleIdx, m: &ClassMatch, goal: &Goal<'a>, lemmas_state: &mut LemmasState, goal_graph: &mut GoalGraph, lemma_proofs: &BTreeMap<usize, LemmaProofState<'a>>) -> PropagateMatchResult {
    let mut propagate_result = PropagateMatchResult::default();
    // Create/lookup each new LemmaTreeNode that comes from a refinement
    // of the current hole's matched class in the e-graph. For each e-node in
    // the e-class create or lookup a new LemmaTreeNode whose edge is the hole
    // being filled with that e-node's symbol.
    let (class, prev_classes) = &m.subst[&current_hole];
    for node in &goal.egraph[*class].nodes {
      let edge = LemmaTreeEdge {
        hole: current_hole,
        filled_with: FilledWith::ENode(node.op),
      };
      let mut new_match = m.clone();
      new_match.subst.remove(&current_hole);
      node.children.iter().enumerate().for_each(|(child_idx, child_eclass)| {
        // The nexts holes that get created are determinisitc, so as long as
        // we create and assign them in the same order we will construct the
        // new match correctly.
        let new_hole = self.pattern.next_hole_idx + child_idx;
        let mut new_prev_classes = prev_classes.clone();
        // Add 1 to the current eclass's count.
        new_prev_classes.entry(*class).and_modify(|count| {
          *count += 1;
        }).or_insert(1);
        new_match.subst.insert(Symbol::new(&format!("{}", new_hole)), (*child_eclass, new_prev_classes));
      });
      if let Some(child_node) = self.children.get_mut(&edge) {
        propagate_result.merge(child_node.add_match(timer, new_match, lemmas_state, goal_graph, lemma_proofs));
        // propagate_result.existing_lemmas.push((m.origin.clone(), child_node.pattern.to_lemma()));
      } else if m.cvecs_equal {
        // We only will follow this branch if it leads to something in the global vocabulary.
        //
        // This explicitly excludes variables, but that's what we want: holes
        // already can be generalized into variables.
        //
        // TODO: Does this handle partial application ($)?
        if let Some(ty) = goal.global_search_state.context.get(&node.op) {
          // println!("holes: {:?}, locked holes: {:?}", self.pattern.holes, self.pattern.locked_holes);
          let pattern = self.pattern.subst_hole(current_hole, node.op, ty);
          let lemma = pattern.to_lemma();
          // FIXME: This is super hacky. We temporarily make the lemma node's
          // state invalid before righting it.
          let mut lemma_node = LemmaTreeNode::from_pattern(pattern, INVALID_LEMMA, self.goal_index.lemma_size, new_match.clone());
          // If any holes are not vars, then this is a generalized lemma.
          let is_generalized = new_match.subst.values().any(|(class, _)|{
            match goal.egraph[*class].data.canonical_form_data {
              CanonicalForm::Var(_) => false,
              _ => true,
            }
          });
          if lemma_node.lemma_status.is_none() {
            // assert_eq!(is_generalized, new_match.num_generalizations > 0);
            if is_generalized && lemma_node.has_counterexample(&goal.global_search_state) {
              lemma_node.lemma_status = Some(LemmaStatus::Invalid);
            } else {
              let lemma_idx = lemmas_state.find_or_make_fresh_lemma(lemma.clone(), 0);
              lemma_node.lemma_idx = lemma_idx;
              lemma_node.goal_index.lemma_id = lemma_idx;
              lemma_node.goal_index.name = Symbol::new(&format!("lemma_{}", lemma_idx));
            }
          }
          // Kill the branch if it has a rejected subpattern.
          // if lemma_node.lemma_status.is_none() && lemmas_state.rejected_lemma_subpatterns.iter().any(|subpattern| matches_subpattern(&lemma.eq.lhs, subpattern, is_var) || matches_subpattern(&lemma.eq.rhs, subpattern, is_var) ) {
          //   lemma_node.lemma_status = Some(LemmaStatus::Dead);
          // }
          propagate_result.merge(lemma_node.add_match(timer, new_match, lemmas_state, goal_graph, lemma_proofs));

          self.children.insert(edge, lemma_node);
        }
      }
    }
    propagate_result

  }

  /// Attempts to propagate the next match, returning the number of new
  /// [`LemmaTreeNode`]s we create in the process (`None` if there are no
  /// matches to propagate - this could either be because the matches ).
  fn propagate_next_match<'a>(&mut self, timer: &Timer, lemmas_state: &mut LemmasState, goal_graph: &mut GoalGraph, lemma_proofs: &BTreeMap<usize, LemmaProofState<'a>>) -> PropagateMatchResult {
    match self.current_matches.pop_back() {
      Some(m) => {
        self.propagate_match(timer, m, lemmas_state, goal_graph, lemma_proofs)
      }
      None => PropagateMatchResult::default()
    }
  }

  fn propagate_all_matches<'a>(&mut self, timer: &Timer, lemmas_state: &mut LemmasState, goal_graph: &mut GoalGraph, lemma_proofs: &BTreeMap<usize, LemmaProofState<'a>>) -> PropagateMatchResult {
    let mut propagation_result = PropagateMatchResult::default();
    while let Some(m) = self.current_matches.pop_back() {
      propagation_result.merge(self.propagate_match(timer, m, lemmas_state, goal_graph, lemma_proofs));
    }
    propagation_result
  }

  /// Adds the match to the current node:
  ///
  /// If the node has been attempted already (indicated by `lemma_status` being
  /// `Some(_)`), then we send the match along to the node's children.
  ///
  /// If the node has not been attempted already, we add it to its matches.
  pub fn add_match<'a>(&mut self, timer: &Timer, m: ClassMatch, lemmas_state: &mut LemmasState, goal_graph: &mut GoalGraph, lemma_proofs: &BTreeMap<usize, LemmaProofState<'a>>) -> PropagateMatchResult {
    // if self.pattern.size != self.goal_index.get_cost() {
    //   panic!("{}, {}", self.pattern, self.goal_index.full_exp);
    // }
    let mut propagate_result = PropagateMatchResult::default();
    if timer.timeout() {
      return propagate_result;
    }
    // We will lazily update the status of this node based on the proof state.
    self.update_lemma_status(lemma_proofs);
    // Once a lemma is proven (and therefore no longer active), don't propagate
    // its matches.
    if goal_graph.goal_map[&m.origin.name].as_ref().borrow().status != GoalNodeStatus::Unknown || lemmas_state.proven_goal_names.contains(&m.origin.name){
      return propagate_result;
    }
    // If we've followed a cycle too much, don't consider this match.
    if m.subst.values().any(|(_, prev_classes)| {
      prev_classes.values().any(|count| *count > CONFIG.max_num_cycles_followed)
    }) {
      return propagate_result;
    }
    if !m.cvecs_equal {
      // We shouldn't have proven the lemma valid.
      assert!(self.lemma_status != Some(LemmaStatus::Valid));
      // The match serves as a counterexample to the lemma's
      // validity.
      self.lemma_status = Some(LemmaStatus::Invalid);
    }
    match self.lemma_status {
      Some(LemmaStatus::InQueue) | Some(LemmaStatus::Inconclusive) => {
        if m.cvecs_equal {
          goal_graph.record_connector_lemma(&m.origin, &self.goal_index);
        }
      }
      _ => {}
    }
    // Defer doing anything more with the match if this node is outside the
    // size we are willing to consider. We will revisit it later.
    if self.pattern.size > lemmas_state.max_lemma_size {
      propagate_result.num_propagated_matches += 1;
      self.current_matches.push_front(m);
      return propagate_result;
    }
    // println!("{}, {}, {}", self.goal_index.get_cost(), self.pattern.to_lemma().size(), lemmas_state.max_lemma_size);
    match self.lemma_status {
      Some(LemmaStatus::Valid) | Some(LemmaStatus::Dead) => {
        // Nothing to do here: the node is valid so we don't need any more
        // matches.
        self.current_matches.clear();
      }
      Some(_) => {
        // Recursively propagate this match downwards
        propagate_result.merge(self.propagate_match(timer, m, lemmas_state, goal_graph, lemma_proofs));
        // In case we just invalidated this node, we also need to flush its
        // other matches; otherwise, they'll be stuck forever. In most cases
        // this list should be empty so this will be a no-op.
        self.propagate_all_matches(timer, lemmas_state, goal_graph, lemma_proofs);
      }
      None => {
        self.current_matches.push_front(m);
        propagate_result.num_propagated_matches += 1;
      }
    }
    propagate_result
  }

  /// FIXME: this is needlessly inefficient
  pub fn find_all_new_lemmas<'a>(&mut self, timer: &Timer, lemmas_state: &mut LemmasState, goal_graph: &mut GoalGraph, lemma_proofs: &BTreeMap<usize, LemmaProofState<'a>>) -> Vec<(GoalIndex, usize, Prop, usize)> {
    if self.pattern.size > lemmas_state.max_lemma_size {
      return vec!()
    }
    if timer.timeout() {
      return vec!()
    }
    // We will lazily update the status of this node based on the proof state.
    self.update_lemma_status(lemma_proofs);
    match self.lemma_status {
      // We haven't tried this lemma yet
      None => {
        self.lemma_status = Some(LemmaStatus::InQueue);
        let mut goal_idxs: HashMap<Symbol, GoalIndex> = HashMap::default();
        self.current_matches.iter().for_each(|m| {
          goal_idxs.entry(m.origin.name).or_insert_with(|| m.origin.clone());
        });
        goal_idxs.into_values().map(|goal_idx| (goal_idx, self.lemma_idx, self.pattern.to_lemma(), self.pattern.size)).collect()
      }
      // It's been proven, no need to try it.
      //
      // Or it's already in the queue, so we don't need to try it.
      //
      // Or it's dead, so we don't need to try it.
      Some(LemmaStatus::Valid) | Some(LemmaStatus::InQueue) | Some(LemmaStatus::Dead) => {
        vec!()
      }
      // We've attempted it but don't have any results, so we should check its
      // children.
      Some(LemmaStatus::Inconclusive) | Some(LemmaStatus::Invalid) => {
        // Propagate its matches if they are now within the proper depth.
        self.propagate_all_matches(timer, lemmas_state, goal_graph, lemma_proofs);
        // NOTE: I think this doesn't make any sense because of the fact that
        // matches exhibit symmetry, i.e. there may be one branch where we have
        // (add ?0 ?1) = ?2 expanding ?0 into (S _) and in another we have ?0 =
        // (add ?1 ?2) expanding ?1 into Z. This would imply it is valid to
        // consider the generalization, but we never would because the lemma
        // exists in two separate branches.
        //
        // let num_enode_edges: usize = self.children.keys().map(|edge| {
        //   if edge.filled_with.is_enode() {
        //     1
        //   } else {
        //     0
        //   }
        // }).sum();
        // // HACK: Prefer trying the single enode edge if there is only one. If
        // // we've already tried it, we will allow trying other edges.
        // //
        // // The thought is that if there are multiple enode edges, the
        // // generalized lemma would apply to different places in the e-graph; if
        // // not, then we should try its specialization first.
        // let skip_non_enode_edges = if num_enode_edges == 1 {
        //   let (_, sole_enode_child) = self.children.iter().find(|(edge, _)| edge.filled_with.is_enode()).unwrap();
        //   sole_enode_child.lemma_status != Some(LemmaStatus::Inconclusive) && sole_enode_child.lemma_status != Some(LemmaStatus::Invalid)
        // } else {
        //   false
        // };
        self.children.iter_mut().flat_map(|(edge, child)| {
          // skip_non_enode_edges => edge has to be an enode
          if true || edge.filled_with.is_enode() {
            child.find_all_new_lemmas(timer, lemmas_state, goal_graph, lemma_proofs)
          } else {
            vec!()
          }
        }).collect()
      }
    }
  }

  /// FIXME: this is needlessly inefficient
  pub fn record_lemma_result(&mut self, lemma_idx: usize, result: LemmaStatus) {
    // Base case: set the status
    if self.lemma_idx == lemma_idx {
      self.lemma_status = Some(result);
      if result == LemmaStatus::Valid {
        self.mark_branch_valid();
      }
      return;
    }

    // If the lemma hasn't been attempted or has been proven valid, we don't
    // need to check its children.
    match self.lemma_status {
      None | Some(LemmaStatus::Valid) | Some(LemmaStatus::InQueue) | Some(LemmaStatus::Dead) => {
        return;
      }
      _ => {}
    }

    // Look for the result in the children.
    self.children.values_mut().for_each(|child| child.record_lemma_result(lemma_idx, result));
  }

  fn mark_branch_valid(&mut self) {
    // This branch is valid (and therefore so are its children), so we can clear
    // any work we've done.
    self.lemma_status = Some(LemmaStatus::Valid);
    // Remove the current matches.
    self.current_matches.clear();
    // Do the same for all children.
    self.children.clear();
  }

  fn update_lemma_status<'a>(&mut self, lemma_proofs: &BTreeMap<usize, LemmaProofState<'a>>) {
    if let Some(proof_state) = lemma_proofs.get(&self.lemma_idx) {
      self.lemma_status = proof_state.outcome.as_ref().map(|outcome| {
        match outcome {
          Outcome::Valid => {
            assert!(self.lemma_status != Some(LemmaStatus::Invalid));
            LemmaStatus::Valid
          }
          Outcome::Invalid => {
            assert!(self.lemma_status != Some(LemmaStatus::Valid));
            LemmaStatus::Invalid
          }
          Outcome::Timeout | Outcome::Unknown => {
            assert!(self.lemma_status.is_none() || self.lemma_status == Some(LemmaStatus::Inconclusive));
            LemmaStatus::Inconclusive
          }
        }
      });
    }
  }
}
