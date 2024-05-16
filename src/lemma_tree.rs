use std::{collections::{BTreeMap, BTreeSet, VecDeque, HashMap}, borrow::Borrow, str::FromStr};

use egg::{Symbol, Id, Pattern, SymbolLang, Subst, Searcher, Var};
use itertools::iproduct;

use crate::{goal::{Eg, LemmaProofState}, analysis::cvecs_equal, ast::{Type, Equation, Prop}, goal_graph::GoalGraph};

type GoalName = Symbol;
/// For compatibility with egg's Vars, we represent holes as ?n where n is >= 0.
///
/// For example, (add ?0 ?1) has holes ?0 and ?1.
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
struct LemmaPattern {
  lhs: PatternWithHoles,
  rhs: PatternWithHoles,
  // FIXME: The use of Side here is probably a premature optimization. Right now
  // the code does not even have the side threaded through everywhere so we have
  // to do lookups _anyway_ to figure out the side which might be more
  // inefficient that just trying to subst on both sides.
  holes: Vec<(HoleIdx, Side)>,
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

}

impl std::fmt::Display for PatternWithHoles {
  /// Formats the LemmaPattern as a sexp.
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      PatternWithHoles::Hole(idx) => {
        write!(f, "{}", idx)
      }
      PatternWithHoles::Node(op, args) => {
        if args.is_empty() {
          write!(f, "{}", op)
        } else {
          write!(f, "({}", op)?;
          args.iter().try_for_each(|arg| {
            write!(f, " ")?;
            arg.fmt(f)
          })?;
          write!(f, ")")
        }
      }
    }
  }
}

impl std::fmt::Display for LemmaPattern {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{} = {}", self.lhs, self.rhs)
  }
}

impl LemmaPattern {

  /// The root pattern of type `ty`; its LHS and RHS are unconstrained.
  fn empty_pattern() -> LemmaPattern {
    let hole_0 = Symbol::new("?0");
    let hole_1 = Symbol::new("?1");

    LemmaPattern {
      lhs: PatternWithHoles::Hole(hole_0),
      rhs: PatternWithHoles::Hole(hole_1),
      holes: vec!((hole_0, Side::Left), (hole_1, Side::Right)),
      next_hole_idx: 2,
    }
  }

  fn new_pattern_from_subst(&self, hole: HoleIdx, hole_pattern: &PatternWithHoles, side: &Side, new_holes: Vec<(HoleIdx, Side)>, next_hole_idx: usize) -> LemmaPattern {
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
  fn subst_hole(&self, hole: HoleIdx, node: Symbol, num_args: usize) -> LemmaPattern {
    let side = self.hole_side(hole);
    let mut new_holes: Vec<(HoleIdx, Side)> = (self.next_hole_idx..self.next_hole_idx + num_args)
      .into_iter().map(|next_hole_idx| {
      let new_hole = Symbol::new(format!("?{}", next_hole_idx));
      (new_hole, side.clone())
    }).collect();
    let next_hole_idx = self.next_hole_idx + num_args;
    let new_pattern = PatternWithHoles::Node(node, new_holes.iter().map(|(hole, _)| {
      Box::new(PatternWithHoles::Hole(*hole))
    }).collect()
    );
    let mut holes_without_subst_hole = self.holes.iter()
                          .filter(|(curr_hole, _)| curr_hole != &hole)
                          .cloned()
                          .collect();
    new_holes.append(&mut holes_without_subst_hole);
    self.new_pattern_from_subst(hole, &new_pattern, &side, new_holes, next_hole_idx)
  }

  /// Unifies `hole_1` and `hole_2` in the new pattern.
  fn unify_holes(&self, hole_1: HoleIdx, hole_2: HoleIdx) -> LemmaPattern {
    let hole_1_side = self.hole_side(hole_1);
    let hole_2_side = self.hole_side(hole_2);
    let new_side  = hole_1_side.merge(hole_2_side);
    let new_holes = self.holes.iter().filter(|(curr_hole, _)| curr_hole != &hole_1).cloned().collect();
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
    self.holes.iter().find_map(|(curr_hole, curr_side)| {
      if &hole == curr_hole {
        Some(curr_side)
      } else {
        None
      }
    }).unwrap()
  }

  fn to_lemma(&self) -> Prop {
    // This will require two refactors:
    //
    // 1. Add type information to the holes.
    // 2. Separate e-classes by their type.
    //
    // The former should be easy. The latter I think is best done by adding an
    // analysis for type information.
    todo!()
  }

}

/// A data structure that represents a multipattern match of a [`LemmaPattern`].
///
/// `lhs` and `rhs` match the LHS and RHS of the pattern.
///
/// TODO: Should we cache a map from `Id` to `Vec<HoleIdx>`? This will allow us
/// to more efficiently compute which holes we could possibly unify.
#[derive(Clone)]
struct ClassMatch {
  goal: GoalName,
  lhs: Id,
  rhs: Id,
  /// What e-classes the holes in the pattern match to.
  subst: BTreeMap<HoleIdx, Id>,
  /// Whether the `lhs` and `rhs` cvecs are equal (we compute this once so we
  /// don't need to repeat the process).
  cvecs_equal: bool,
}

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
/// If there are only matching cvecs among the `current_matches` (and there is
/// at least one match - this should be guaranteed), we will attempt to prove
/// the lemma represented by this node.
///
/// Once we have finished trying to prove the lemma (or if it was invalidated),
/// we will check the lemma's status. If it is `Proven`, then this node is done.
/// Otherwise, we propagate the `current_matches` downwards, creating new
/// children.
struct LemmaTreeNode {
  /// The pattern which represents the current lemma.
  pattern: LemmaPattern,
  /// These matches are transient: we will propagate them through the e-graph if
  /// we cannot prove the lemma this node represents (or if it is an invalid
  /// lemma).
  current_matches: Vec<ClassMatch>,
  /// What's the status of the lemma? (`None` if we haven't attempted this
  /// lemma or finished attempting it).
  lemma_status: Option<LemmaStatus>,
  /// Did any of the [`ClassMatch`]es have matching cvecs? If none do, there is
  /// no point in investigating the children of this node, as they cannot
  /// possibly be valid lemmas.
  has_matching_cvecs: bool,
  /// Lemmas that are refinements of the `pattern` in this node. We identify
  /// them using the hole that was filled and what it was filled with.
  children: BTreeMap<LemmaTreeEdge, LemmaTreeNode>,
}

enum LemmaStatus {
  Valid,
  Invalid,
  Inconclusive,
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

impl LemmaTreeNode {
  fn from_pattern(pattern: LemmaPattern) -> LemmaTreeNode {
    LemmaTreeNode {
      pattern,
      current_matches: Vec::default(),
      lemma_status: None,
      has_matching_cvecs: false,
      children: BTreeMap::default(),
    }
  }

  /// Attempts to propagate the next match, returning the number of new
  /// [`LemmaTreeNode`]s we create in the process (`None` if there are no
  /// matches to propagate).
  fn propagate_next_match<'a>(&mut self, goal_graph: &GoalGraph, lemma_proofs: &BTreeMap<usize, LemmaProofState<'a>>) -> Option<usize> {
    if self.current_matches.is_empty() {
      return None;
    }
    let mut num_new_children = 0;
    let m = self.current_matches.pop().unwrap();
    // First, create/lookup each new LemmaTreeNode that comes from unifying each
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
        child_node.add_match(new_match);
      } else {
        let mut lemma_node = LemmaTreeNode::from_pattern(self.pattern.unify_holes(hole, other_hole));
        lemma_node.add_match(new_match);
        self.children.insert(edge, lemma_node);
        num_new_children += 1;
      }
    }
    // Obtain the e-graph corresponding the the match's goal.
    //
    // TODO: refactor the goal graph to couple it better with the lemma tree.
    // This is incredibly gross.
    let goal_node = goal_graph.goal_map[&m.goal].as_ref().borrow();
    let parent_lemma_state = &lemma_proofs[&goal_node.lemma_id];
    let goal = parent_lemma_state.goals.iter().find_map(|g| {
      if g.name == m.goal {
        Some(g)
      } else {
        None
      }
    }).unwrap();
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
          let hole_idx = self.pattern.next_hole_idx + child_idx;
          let new_hole = Symbol::new(&format!("?{}", hole_idx));
          new_match.subst.insert(new_hole, *child_eclass);
        });
        if let Some(child_node) = self.children.get_mut(&edge) {
          child_node.add_match(new_match);
        } else {
          let mut lemma_node = LemmaTreeNode::from_pattern(self.pattern.subst_hole(*hole, node.op, node.children.len()));
          lemma_node.add_match(new_match);
          self.children.insert(edge, lemma_node);
          num_new_children += 1;
        }
      }
    }
    Some(num_new_children)
  }

  fn add_match(&mut self, m: ClassMatch) {
    // Set this field to true if `m` has matching cvecs.
    self.has_matching_cvecs |= m.cvecs_equal;
    self.current_matches.push(m);
  }
}
