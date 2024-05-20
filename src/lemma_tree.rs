use serde::{Serialize, Serializer, ser::{SerializeStruct, SerializeSeq}};
use std::{collections::{BTreeMap, BTreeSet, VecDeque, HashMap, HashSet}, borrow::Borrow, str::FromStr};

use egg::{Symbol, Id, Pattern, SymbolLang, Subst, Searcher, Var};
use itertools::{iproduct, Itertools};
use symbolic_expressions::Sexp;

use crate::{goal::{Eg, LemmaProofState, Outcome, LemmasState}, analysis::cvecs_equal, ast::{Type, Equation, Prop}, goal_graph::{GoalGraph, GoalIndex}, config::CONFIG};

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

  fn subst_pattern(&self, hole: HoleIdx, hole_pattern: &PatternWithHoles, (lhs, rhs): (&PatternWithHoles, &PatternWithHoles)) -> (PatternWithHoles, PatternWithHoles) {
    match self {
      Self::Left => {
        (lhs.subst_hole(hole, hole_pattern).0, rhs.clone())
      }
      Self::Right => {
        (lhs.clone(), rhs.subst_hole(hole, hole_pattern).0)
      }
      Self::Both => {
        (lhs.subst_hole(hole, hole_pattern).0, rhs.subst_hole(hole, hole_pattern).0)
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
}

impl Serialize for LemmaPattern {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer {
    serializer.serialize_str(&format!("{} = {}", self.lhs, self.rhs))
  }
}

impl PatternWithHoles {
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
      // In reverse order because we pop from the back (not that it really matters)
      holes: [(hole_1, ty.clone(), Side::Right), (hole_0, ty.clone(), Side::Left)].into(),
      locked_holes: vec!(),
      next_hole_idx: 2,
    }
  }

  fn new_pattern_from_subst(&self, hole: HoleIdx, hole_pattern: &PatternWithHoles, side: &Side, new_holes: VecDeque<(HoleIdx, Type, Side)>, next_hole_idx: usize) -> LemmaPattern {
    let (lhs, rhs) = side.subst_pattern(hole, hole_pattern, (&self.lhs, &self.rhs));
    LemmaPattern {
      lhs,
      rhs,
      holes: new_holes,
      locked_holes: self.locked_holes.clone(),
      next_hole_idx,
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
        (new_hole, arg_ty, side.clone())
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
    self.new_pattern_from_subst(hole, &new_pattern, &side, new_holes, next_hole_idx)
  }

  /// Unifies `hole_1` and `hole_2` in the new pattern.
  ///
  /// If either hole is locked, does nothing.
  fn unify_holes(&self, hole_1: HoleIdx, hole_2: HoleIdx) -> LemmaPattern {
    // println!("unifying {} and {} in {}", hole_1, hole_2, self);
    // FIXME: there are a lot of hacks to deal with locked holes.
    let unified_hole_is_locked = self.locked_holes.iter().any(|(locked_hole, _, _)| {
      *locked_hole == hole_1 || *locked_hole == hole_2
    });
    let (hole_1_side, hole_ty) = self.hole_side_type(hole_1);
    // The types should be the same, so ignore the second one without loss of
    // generality.
    let (hole_2_side, _) = self.hole_side_type(hole_2);
    let unified_hole_side = hole_1_side.merge(hole_2_side);
    let fresh_hole = self.next_hole_idx;
    // Remove hole_1 and hole_2 in all holes.
    // Even though
    let mut new_holes: VecDeque<_> = self.holes.iter().filter(|(curr_hole, _, _)| {
      curr_hole != &hole_1 && curr_hole != &hole_2
    }).cloned().collect();
    let mut new_locked_holes: Vec<_> = self.locked_holes.iter().filter(|(curr_hole, _, _)| {
      curr_hole != &hole_1 && curr_hole != &hole_2
    }).cloned().collect();
    if unified_hole_is_locked {
      new_locked_holes.push((fresh_hole, hole_ty.clone(), unified_hole_side));
    } else {
      // HACK: we push the unified hole to the back because presumably one of
      // the two holes was at the back before. There might be a better thing to do here.
      new_holes.push_back((fresh_hole, hole_ty.clone(), unified_hole_side));
    }
    let fresh_hole_pattern = PatternWithHoles::Hole(fresh_hole);
    let (lhs, rhs) = hole_1_side.subst_pattern(hole_1, &fresh_hole_pattern, (&self.lhs, &self.rhs));
    let (lhs, rhs) = hole_2_side.subst_pattern(hole_2, &fresh_hole_pattern, (&lhs, &rhs));
    let lp = LemmaPattern {
      lhs,
      rhs,
      holes: new_holes,
      locked_holes: new_locked_holes,
      next_hole_idx: self.next_hole_idx + 1,
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
#[derive(Clone, Serialize)]
pub struct LemmaTreeNode {
  /// The pattern which represents the current lemma.
  pattern: LemmaPattern,
  /// The index of the lemma corresponding to this node in the LemmaTree
  lemma_idx: usize,
  /// The GoalIndex that is associated with this lemma in the GoalGraph.
  goal_index: GoalIndex,
  /// These matches are transient: we will propagate them through the e-graph if
  /// we cannot prove the lemma this node represents (or if it is an invalid
  /// lemma).
  ///
  /// When we create a `LemmaTreeNode`, it needs to have at least one match.
  #[serde(skip_serializing)]
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
  #[serde(serialize_with = "serialize_children_map")]
  children: BTreeMap<LemmaTreeEdge, LemmaTreeNode>,
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
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Serialize)]
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
  /// Not exactly something that the hole is "filled with," this represents the
  /// hole never being allowed to be filled.
  Lock,
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
  pub fn from_pattern(pattern: LemmaPattern, lemma_idx: usize, lemma_depth: usize) -> LemmaTreeNode {
    let goal_index = GoalIndex::from_lemma(Symbol::new(format!("lemma_{}", lemma_idx)), pattern.to_lemma().eq, lemma_idx, lemma_depth);
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
    pattern.holes.iter().chain(pattern.locked_holes.iter()).for_each(|(_hole, _ty, side)| {
      if side != &Side::Both {
        num_free_vars += 1;
      }
    });
    let lemma_status = if num_free_vars > CONFIG.num_free_vars_allowed {
      Some(LemmaStatus::Invalid)
    } else {
      None
    };
    LemmaTreeNode {
      pattern,
      lemma_idx,
      goal_index,
      current_matches: VecDeque::default(),
      lemma_status,
      match_enode_propagation_allowed: true,
      children: BTreeMap::default(),
    }
  }

  /// Attempts to propagate the match, returning the number of new
  /// [`LemmaTreeNode`]s we create in the process (`None` if there are no
  /// matches to propagate - this could either be because the matches ).
  ///
  /// FIXME: refactor this into separate parts for unifying holes using a match,
  /// "locking in" a hole, and propagating a match via its enodes.
  fn propagate_match<'a>(&mut self, m: ClassMatch, lemmas_state: &mut LemmasState, goal_graph: &GoalGraph, lemma_proofs: &BTreeMap<usize, LemmaProofState<'a>>) -> PropagateMatchResult {
    if self.pattern.holes.is_empty() {
      return PropagateMatchResult::default();
    }
    let (current_hole, _, _) = self.pattern.holes.back().unwrap();
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
      if hole != *current_hole {
        continue;
      }
      let edge = LemmaTreeEdge {
        hole: *current_hole,
        filled_with: FilledWith::AnotherHole(other_hole),
      };
      let mut new_match = m.clone();
      let class = new_match.subst.remove(&hole).unwrap();
      new_match.subst.remove(&other_hole);
      // HACK: we know what the index of the fresh hole that will unify the two
      // is going to be, so we just insert the class at that hole here.
      new_match.subst.insert(self.pattern.next_hole_idx, class);
      if let Some(child_node) = self.children.get_mut(&edge) {
        propagate_result.merge(child_node.add_match(new_match, lemmas_state, goal_graph, lemma_proofs));
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
        // TODO: look up the lemma's result if it has one.
        let lemma_idx = lemmas_state.find_or_make_fresh_lemma(pattern.to_lemma(), 0);
        // The lemma depth does not increase because we're just unifying holes.
        let mut lemma_node = LemmaTreeNode::from_pattern(pattern, lemma_idx, self.goal_index.lemma_depth);
        // We force nodes created from unifying holes to be a leaf because otherwise we will have
        // many duplicates.
        lemma_node.match_enode_propagation_allowed = false;
        propagate_result.merge(lemma_node.add_match(new_match, lemmas_state, goal_graph, lemma_proofs));
        propagate_result.new_lemmas.push((m.origin.clone(), lemma_node.pattern.to_lemma()));
        self.children.insert(edge, lemma_node);
      }
    }
    // Next, we will create an edge corresponding to "locking" or preventing the
    // current hole from being filled.
    let lock_edge = LemmaTreeEdge {
      hole: *current_hole,
      filled_with: FilledWith::Lock,
    };
    if let Some(child_node) = self.children.get_mut(&lock_edge) {
      propagate_result.merge(child_node.add_match(m.clone(), lemmas_state, goal_graph, lemma_proofs));
      // The lemma for the child is the same, so we won't add it to the propagation list
      propagate_result.num_propagated_matches += 1;
    } else {
      // Create a new node where we move the current hole to the locked holes.
      let mut new_node = self.clone();
      let (hole_loc, _) = new_node.pattern.holes.iter().find_position(|(hole, _, _)| hole == current_hole).unwrap();
      let hole_info = new_node.pattern.holes.remove(hole_loc).unwrap();
      new_node.pattern.locked_holes.push(hole_info);
      // Everything else about this new node will be the same except we will
      // zero out its matches (they will presumably get propagated).
      //
      // TODO: do a shallow clone that doesn't copy the current matches since we
      // don't use them.
      new_node.current_matches = VecDeque::default();
      // Now propagate the match.
      propagate_result.merge(new_node.add_match(m.clone(), lemmas_state, goal_graph, lemma_proofs));
      propagate_result.num_propagated_matches += 1;
      self.children.insert(lock_edge, new_node);
    }
    if !self.match_enode_propagation_allowed {
      // If we aren't allowed to propagate via enodes, just return what we have
      // so far.
      return propagate_result;
    }
    // Then, create/lookup each new LemmaTreeNode that comes from a refinement
    // of the current hole's matched class in the e-graph. For each e-node in
    // the e-class create or lookup a new LemmaTreeNode whose edge is the hole
    // being filled with that e-node's symbol.
    let class = m.subst[current_hole];
    for node in &goal.egraph[class].nodes {
      let edge = LemmaTreeEdge {
        hole: *current_hole,
        filled_with: FilledWith::ENode(node.op),
      };
      let mut new_match = m.clone();
      new_match.subst.remove(current_hole);
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
          let pattern = self.pattern.subst_hole(*current_hole, node.op, ty);
          let lemma_idx = lemmas_state.find_or_make_fresh_lemma(pattern.to_lemma(), 0);
          // The lemma depth increases because we do a subst.
          let mut lemma_node = LemmaTreeNode::from_pattern(pattern, lemma_idx, self.goal_index.lemma_depth + 1);
          propagate_result.merge(lemma_node.add_match(new_match, lemmas_state, goal_graph, lemma_proofs));

          self.children.insert(edge, lemma_node);
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
    // Defer doing anything more with the match if this node is outside the
    // depth we are willing to consider. We will revisit it later.
    if self.goal_index.lemma_depth > lemmas_state.max_lemma_depth {
      propagate_result.num_propagated_matches += 1;
      self.current_matches.push_front(m);
      return propagate_result;
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
  pub fn find_all_new_lemmas(&mut self, max_depth: usize) -> Vec<(GoalIndex, usize, Prop, usize)> {
    if self.goal_index.lemma_depth > max_depth {
      return vec!()
    }
    match self.lemma_status {
      // We haven't tried this lemma yet
      None => {
        self.lemma_status = Some(LemmaStatus::InQueue);
        let mut goal_idxs: HashMap<Symbol, GoalIndex> = HashMap::default();
        self.current_matches.iter().for_each(|m| {
          goal_idxs.entry(m.origin.name).or_insert_with(|| m.origin.clone());
        });
        goal_idxs.into_values().map(|goal_idx| (goal_idx, self.lemma_idx, self.pattern.to_lemma(), self.goal_index.lemma_depth)).collect()
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
        self.children.values_mut().flat_map(|child| child.find_all_new_lemmas(max_depth)).collect()
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
      None | Some(LemmaStatus::Valid) | Some(LemmaStatus::InQueue) => {
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
    self.children.values_mut().for_each(|child| child.mark_branch_valid());
  }
}
