use std::{collections::{BTreeMap, BTreeSet, VecDeque, HashMap, HashSet}, borrow::Borrow, str::FromStr};

use egg::{Symbol, Id, Pattern, SymbolLang, Subst, Searcher, Var};
use itertools::iproduct;
use symbolic_expressions::Sexp;

use crate::{goal::{Eg, LemmaProofState, Outcome, LemmasState}, analysis::cvecs_equal, ast::{Type, Equation, Prop}, goal_graph::{GoalGraph, GoalIndex}};

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
type HoleIdx  = usize;

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
enum PatternWithHoles {
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
#[derive(Clone)]
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
}

#[derive(Clone)]
pub struct LemmaPattern {
  lhs: PatternWithHoles,
  rhs: PatternWithHoles,
  // FIXME: The use of Side here is probably a premature optimization. Right now
  // the code does not even have the side threaded through everywhere so we have
  // to do lookups _anyway_ to figure out the side which might be more
  // inefficient that just trying to subst on both sides.
  holes: Vec<(HoleIdx, Type, Side)>,
  next_hole_idx: usize,
}

impl PatternWithHoles {
  /// Is the pattern concrete (i.e. does it have no Holes)?
  fn is_concrete(&self) -> bool {
    match self {
      PatternWithHoles::Hole(_) => false,
      PatternWithHoles::Node(_, args) => args.iter().all(|arg| arg.is_concrete()),
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
  fn fill_hole(&mut self, hole: HoleIdx, value: &PatternWithHoles) -> bool {
    match self {
      PatternWithHoles::Hole(h) if *h == hole => {
        *self = value.clone();
        true
      }
      PatternWithHoles::Hole(_) => {
        false
      }
      PatternWithHoles::Node(_, args) => {
        args.iter_mut().any(|arg| arg.fill_hole(hole, value))
      }
    }
  }

  /// Returns a new pattern where the hole is filled.
  ///
  /// The bool indicates whether a substitution actually happened.
  fn subst_hole(&self, hole: HoleIdx, value: &PatternWithHoles) -> (PatternWithHoles, bool) {
    match &self {
      PatternWithHoles::Hole(h) if *h == hole => {
        (value.clone(), true)
      }
      PatternWithHoles::Hole(_) => {
        (self.clone(), false)
      }
      PatternWithHoles::Node(op, args) => {
        let mut hole_filled = false;
        let new_pat = PatternWithHoles::Node(*op, args.iter().map(|arg| {
          let (new_arg, arg_hole_filled) = arg.subst_hole(hole, value);
          hole_filled |= arg_hole_filled;
          Box::new(new_arg)
        }).collect());
        (new_pat, hole_filled)
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
    let hole_0 = 0;
    let hole_1 = 1;

    LemmaPattern {
      lhs: PatternWithHoles::Hole(hole_0),
      rhs: PatternWithHoles::Hole(hole_1),
      holes: vec!((hole_0, ty.clone(), Side::Left), (hole_1, ty.clone(), Side::Right)),
      next_hole_idx: 2,
    }
  }

  fn new_pattern_from_subst(&self, hole: HoleIdx, hole_pattern: &PatternWithHoles, side: &Side, new_holes: Vec<(HoleIdx, Type, Side)>, next_hole_idx: usize) -> LemmaPattern {
    match side {
      Side::Left => {
        LemmaPattern {
          lhs: self.lhs.subst_hole(hole, &hole_pattern).0,
          rhs: self.rhs.clone(),
          holes: new_holes,
          next_hole_idx,
        }
      }
      Side::Right => {
        LemmaPattern {
          lhs: self.lhs.clone(),
          rhs: self.rhs.subst_hole(hole, &hole_pattern).0,
          holes: new_holes,
          next_hole_idx,
        }
      }
      Side::Both => {
        LemmaPattern {
          lhs: self.rhs.subst_hole(hole, &hole_pattern).0,
          rhs: self.rhs.subst_hole(hole, &hole_pattern).0,
          holes: new_holes,
          next_hole_idx,
        }
      }
    }

  }

  /// Returns a new [`LemmaPattern`] with `hole` filled with a new [`PatternWithHoles`]
  /// made from the constructor `node` with type `node_ty` (so unless the hole is
  /// being filled with a leaf, `node` will be a function and will have new holes
  /// added for it).
  fn subst_hole(&self, hole: HoleIdx, node: Symbol, node_ty: &Type) -> LemmaPattern {
    let side = self.hole_side(hole);
    let (arg_tys, _ret_ty) = node_ty.args_ret();
    let num_args = arg_tys.len();
    let mut new_holes: Vec<(HoleIdx, Type, Side)> = arg_tys
      .into_iter()
      .enumerate()
      .map(|(arg_idx, arg_ty)| {
        let new_hole = self.next_hole_idx + arg_idx;
        (new_hole, arg_ty, side.clone())
      }).collect();
    let next_hole_idx = self.next_hole_idx + num_args;
    let new_pattern = PatternWithHoles::Node(node, new_holes.iter().map(|(hole, _, _)| {
      Box::new(PatternWithHoles::Hole(*hole))
    }).collect()
    );
    let mut holes_without_subst_hole = self.holes.iter()
                          .filter(|(curr_hole, _, _)| curr_hole != &hole)
                          .cloned()
                          .collect();
    new_holes.append(&mut holes_without_subst_hole);
    self.new_pattern_from_subst(hole, &new_pattern, &side, new_holes, next_hole_idx)
  }

  /// Unifies `hole_1` and `hole_2` in the new pattern.
  fn unify_holes(&self, hole_1: HoleIdx, hole_2: HoleIdx) -> LemmaPattern {
    // FIXME: bug here
    let hole_1_side = self.hole_side(hole_1);
    let hole_2_side = self.hole_side(hole_2);
    let new_side  = hole_1_side.merge(hole_2_side);
    let new_holes = self.holes.iter().filter_map(|(curr_hole, ty, side)| {
      // Remove hole_1, we're substituting it
      if curr_hole == &hole_1 {
        None
      } else if curr_hole == &hole_2 {
        Some((curr_hole.clone(), ty.clone(), new_side.clone()))
      } else {
        Some((curr_hole.clone(), ty.clone(), side.clone()))
      }
    }).collect();
    let hole_2_pattern = PatternWithHoles::Hole(hole_2);
    // We'll substitute on this without loss of generality. I suppose we could
    // do an analysis to identify the better side to substitute if we wanted to
    // be efficient.
    self.new_pattern_from_subst(hole_1, &hole_2_pattern, hole_1_side, new_holes, self.next_hole_idx)
  }

  fn hole_side(&self, hole: HoleIdx) -> &Side {
    // This lookup is in theory inefficient and we could restructure things by
    // having the ClassMatch not only its holes but what sides the holes come
    // from, but I expect the number of holes will be relatively small.
    self.holes.iter().find_map(|(curr_hole, _, curr_side)| {
      if &hole == curr_hole {
        Some(curr_side)
      } else {
        None
      }
    }).unwrap()
  }

  pub fn to_lemma(&self) -> Prop {
    let params = self.holes.iter().map(|(hole, hole_ty, _side)| {
      (Symbol::new(format!("{}{}", HOLE_VAR_PREFIX, hole)), hole_ty.clone())
    }).collect();
    let lhs = self.lhs.to_sexp();
    let rhs = self.rhs.to_sexp();
    // This does alpha-renaming.
    Prop::new(Equation::new(lhs, rhs), params)
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
  /// What e-classes the holes in the pattern match to.
  subst: BTreeMap<HoleIdx, Id>,
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
}

impl ClassMatch {
  /// Constructs a top-level match (i.e. one for the top-level pattern, where
  /// lhs is the pattern ?0 and rhs is the pattern ?1).
  pub fn top_match(origin: GoalIndex, lhs: Id, rhs: Id, cvecs_equal: bool) -> Self {
    let mut subst = BTreeMap::default();
    subst.insert(0, lhs);
    subst.insert(1, rhs);
    Self {
      origin,
      lhs,
      rhs,
      subst,
      cvecs_equal
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
pub struct LemmaTreeNode {
  /// The pattern which represents the current lemma.
  pattern: LemmaPattern,
  /// The index of the lemma corresponding to this node in the LemmaTree
  lemma_idx: usize,
  /// These matches are transient: we will propagate them through the e-graph if
  /// we cannot prove the lemma this node represents (or if it is an invalid
  /// lemma).
  ///
  /// When we create a `LemmaTreeNode`, it needs to have at least one match.
  current_matches: VecDeque<ClassMatch>,
  /// What's the status of the lemma? (`None` if we haven't attempted this
  /// lemma).
  lemma_status: Option<LemmaStatus>,
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
  children: BTreeMap<LemmaTreeEdge, LemmaTreeNode>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum LemmaStatus {
  Valid,
  Invalid,
  Inconclusive,
  InQueue,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
struct LemmaTreeEdge {
  hole: HoleIdx,
  filled_with: FilledWith,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
/// What did we fill a hole with?
enum FilledWith {
  /// This represents a hole being instantiated to a function or constant in the
  /// e-graph. The `Symbol` is the name of this function or constant.
  ENode(Symbol),
  /// This represents the unification of two different holes.
  ///
  /// Philosophical question: can you fill a hole with another hole?
  AnotherHole(HoleIdx),
}

impl ClassMatch {
  /// Which pairs of holes could we unify while still keeping this match?
  fn unifiable_holes(&self) -> Vec<(HoleIdx, HoleIdx)> {
    let mut class_to_holes: HashMap<Id, Vec<HoleIdx>> = HashMap::new();
    for (hole, class) in self.subst.iter() {
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
}

#[derive(Default, Clone)]
pub struct PropagateMatchResult {
  pub new_lemmas: Vec<(GoalIndex, Prop)>,
  /// In theory we should only ever need the new lemmas, but these are used to
  /// track dependencies in the goal graph.
  ///
  /// TODO: do a restructuring that obviates the need for this field - probably
  /// we will want to thread the global lemma state through the lemma tree when
  /// we propagate matches in order to annotate lemma tree nodes with their
  /// lemma number as well as the parent relation that is tracked in the goal
  /// graph.
  ///
  /// This also will probably mean putting all of the LemmaTreeNodes into a map
  /// the same way we have all lemmas in a map somewhere so that we can jump
  /// between them easily.
  pub existing_lemmas: Vec<(GoalIndex, Prop)>,
  pub num_propagated_matches: usize,
}

impl PropagateMatchResult {
  fn merge(&mut self, mut rhs: Self) {
    self.new_lemmas.append(&mut rhs.new_lemmas);
    self.existing_lemmas.append(&mut rhs.existing_lemmas);
    self.num_propagated_matches += rhs.num_propagated_matches;
  }
}

impl LemmaTreeNode {
  pub fn from_pattern(pattern: LemmaPattern, lemma_idx: usize) -> LemmaTreeNode {
    LemmaTreeNode {
      pattern,
      lemma_idx,
      current_matches: VecDeque::default(),
      lemma_status: None,
      match_enode_propagation_allowed: true,
      children: BTreeMap::default(),
    }
  }

  /// Attempts to propagate the match, returning the number of new
  /// [`LemmaTreeNode`]s we create in the process (`None` if there are no
  /// matches to propagate - this could either be because the matches ).
  fn propagate_match<'a>(&mut self, m: ClassMatch, lemmas_state: &mut LemmasState, goal_graph: &GoalGraph, lemma_proofs: &BTreeMap<usize, LemmaProofState<'a>>) -> PropagateMatchResult {
    // First, obtain the goal that this match comes from.
    //
    // TODO: refactor the goal graph to couple it better with the lemma tree.
    // This is incredibly gross.
    let goal_node = goal_graph.goal_map[&m.origin.name].as_ref().borrow();
    let parent_lemma_state = &lemma_proofs[&goal_node.lemma_id];
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
    let mut propagate_result = PropagateMatchResult::default();
    // Next, create/lookup each new LemmaTreeNode that comes from unifying each
    // pair of holes, adding the current match to it where we remove the hole
    // that was substituted out from `subst`.
    let unifiable_holes = m.unifiable_holes();
    for (hole, other_hole) in unifiable_holes {
      let edge = LemmaTreeEdge {
        hole,
        filled_with: FilledWith::AnotherHole(other_hole),
      };
      let mut new_match = m.clone();
      new_match.subst.remove(&hole);
      if let Some(child_node) = self.children.get_mut(&edge) {
        child_node.add_match(new_match, lemmas_state, goal_graph, lemma_proofs);
        propagate_result.existing_lemmas.push((m.origin.clone(), child_node.pattern.to_lemma()));
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
        let pattern = self.pattern.unify_holes(hole, other_hole);
        // We always will make a lemma, even though we might suspect it is
        // invalid.
        //
        // TODO: look up its result if it has one.
        let lemma_idx = lemmas_state.find_or_make_fresh_lemma(pattern.to_lemma(), 0);
        let mut lemma_node = LemmaTreeNode::from_pattern(pattern, lemma_idx);
        // We force nodes created from unifying holes to be a leaf because otherwise we will have
        // many duplicates.
        lemma_node.match_enode_propagation_allowed = false;
        propagate_result.merge(lemma_node.add_match(new_match, lemmas_state, goal_graph, lemma_proofs));
        propagate_result.new_lemmas.push((m.origin.clone(), lemma_node.pattern.to_lemma()));
        self.children.insert(edge, lemma_node);
      }
    }
    if !self.match_enode_propagation_allowed {
      // If we aren't allowed to propagate via enodes, just return what we have
      // so far.
      return propagate_result;
    }
    // Then, create/lookup each new LemmaTreeNode that comes from a refinement
    // of a hole's matched class in the e-graph. Essentially, pick a hole and
    // look at its e-class. Then for each e-node in the e-class create or lookup
    // a new LemmaTreeNode whose edge is the hole being filled with that
    // e-node's symbol.
    for (hole, class) in &m.subst {
      for node in &goal.egraph[*class].nodes {
        let edge = LemmaTreeEdge {
          hole: *hole,
          filled_with: FilledWith::ENode(node.op),
        };
        let mut new_match = m.clone();
        new_match.subst.remove(hole);
        node.children.iter().enumerate().for_each(|(child_idx, child_eclass)| {
          // The nexts holes that get created are determinisitc, so as long as
          // we create and assign them in the same order we will construct the
          // new match correctly.
          let new_hole = self.pattern.next_hole_idx + child_idx;
          new_match.subst.insert(new_hole, *child_eclass);
        });
        if let Some(child_node) = self.children.get_mut(&edge) {
          propagate_result.merge(child_node.add_match(new_match, lemmas_state, goal_graph, lemma_proofs));
          propagate_result.existing_lemmas.push((m.origin.clone(), child_node.pattern.to_lemma()));
        } else if m.cvecs_equal {
          // We only will follow this branch if it leads to something in the global vocabulary.
          //
          // This explicitly excludes variables, but that's what we want: holes
          // already can be generalized into variables.
          //
          // TODO: Does this handle partial application ($)?
          if let Some(ty) = goal.global_search_state.context.get(&node.op) {
            let pattern = self.pattern.subst_hole(*hole, node.op, ty);
            let lemma_idx = lemmas_state.find_or_make_fresh_lemma(pattern.to_lemma(), 0);
            let mut lemma_node = LemmaTreeNode::from_pattern(pattern, lemma_idx);
            propagate_result.merge(lemma_node.add_match(new_match, lemmas_state, goal_graph, lemma_proofs));
            propagate_result.new_lemmas.push((m.origin.clone(), lemma_node.pattern.to_lemma()));
            self.children.insert(edge, lemma_node);
          }
        }
      }
    }
    propagate_result
  }

  /// Attempts to propagate the next match, returning the number of new
  /// [`LemmaTreeNode`]s we create in the process (`None` if there are no
  /// matches to propagate - this could either be because the matches ).
  fn propagate_next_match<'a>(&mut self, lemmas_state: &mut LemmasState, goal_graph: &GoalGraph, lemma_proofs: &BTreeMap<usize, LemmaProofState<'a>>) -> PropagateMatchResult {
    match self.current_matches.pop_back() {
      Some(m) => {
        self.propagate_match(m, lemmas_state, goal_graph, lemma_proofs)
      }
      None => PropagateMatchResult::default()
    }
  }

  fn propagate_all_matches<'a>(&mut self, lemmas_state: &mut LemmasState, goal_graph: &GoalGraph, lemma_proofs: &BTreeMap<usize, LemmaProofState<'a>>) -> PropagateMatchResult {
    let mut propagation_result = PropagateMatchResult::default();
    while let Some(m) = self.current_matches.pop_back() {
      propagation_result.merge(self.propagate_match(m, lemmas_state, goal_graph, lemma_proofs));
    }
    propagation_result
  }

  /// Adds the match to the current node:
  ///
  /// If the node has been attempted already (indicated by `lemma_status` being
  /// `Some(_)`), then we send the match along to the node's children.
  ///
  /// If the node has not been attempted already, we add it to its matches.
  pub fn add_match<'a>(&mut self, m: ClassMatch, lemmas_state: &mut LemmasState, goal_graph: &GoalGraph, lemma_proofs: &BTreeMap<usize, LemmaProofState<'a>>) -> PropagateMatchResult {
    let mut propagate_result = PropagateMatchResult::default();
    if !m.cvecs_equal {
      // We shouldn't have proven the lemma valid.
      assert!(self.lemma_status != Some(LemmaStatus::Valid));
      // The match serves as a counterexample to the lemma's
      // validity.
      self.lemma_status = Some(LemmaStatus::Invalid);
    }
    match self.lemma_status {
      Some(LemmaStatus::Valid) => {
        // Nothing to do here: the node is valid so we don't need any more
        // matches.
      }
      Some(_) => {
        // Recursively propagate this match downwards
        propagate_result.merge(self.propagate_match(m, lemmas_state, goal_graph, lemma_proofs));
        // In case we just invalidated this node, we also need to flush its
        // other matches; otherwise, they'll be stuck forever. In most cases
        // this list should be empty so this will be a no-op.
        self.propagate_all_matches(lemmas_state, goal_graph, lemma_proofs);
      }
      None => {
        self.current_matches.push_front(m);
        propagate_result.num_propagated_matches += 1;
      }
    }
    propagate_result
  }

  /// FIXME: this is needlessly inefficient
  pub fn find_all_new_lemmas(&mut self) -> Vec<(GoalIndex, usize, Prop)> {
    match self.lemma_status {
      // We haven't tried this lemma yet
      None => {
        self.lemma_status = Some(LemmaStatus::InQueue);
        let mut goal_idxs: HashMap<Symbol, GoalIndex> = HashMap::default();
        self.current_matches.iter().for_each(|m| {
          goal_idxs.entry(m.origin.name).or_insert_with(|| m.origin.clone());
        });
        goal_idxs.into_values().map(|goal_idx| (goal_idx, self.lemma_idx, self.pattern.to_lemma())).collect()
      }
      // It's been proven, no need to try it.
      //
      // Or it's already in the queue, so we don't need to try it.
      Some(LemmaStatus::Valid) | Some(LemmaStatus::InQueue) => {
        vec!()
      }
      // We've attempted it but don't have any results, so we should check its
      // children.
      Some(LemmaStatus::Inconclusive) | Some(LemmaStatus::Invalid) => {
        self.children.values_mut().flat_map(|child| child.find_all_new_lemmas()).collect()
      }
    }
  }

  /// FIXME: this is needlessly inefficient
  pub fn record_lemma_result(&mut self, lemma_idx: usize, result: LemmaStatus) {
    // Base case: set the status
    if self.lemma_idx == lemma_idx {
      self.lemma_status = Some(result);
      return;
    }

    // If the lemma hasn't been attempted or has been proven valid, we don't
    // need to check its children.
    match self.lemma_status {
      None | Some(LemmaStatus::Valid) | Some(LemmaStatus::InQueue) => {
        return;
      }
      _ => {}
    }

    // Look for the result in the children.
    self.children.values_mut().for_each(|child| child.record_lemma_result(lemma_idx, result));
  }
}
