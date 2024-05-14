use std::collections::{BTreeMap, BTreeSet, VecDeque};

use egg::{Symbol, Id, Pattern, SymbolLang, Subst, Searcher, Var};

use crate::{goal::Eg, analysis::cvecs_equal, ast::Type};

type GoalName = String;
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

#[derive(Clone)]
struct LemmaPattern {
  lhs: PatternWithHoles,
  rhs: PatternWithHoles,
  holes: VecDeque<(HoleIdx, Side, Type)>,
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
  fn empty_pattern(ty: Type) -> LemmaPattern {
    let hole_0 = Symbol::new("?0");
    let hole_1 = Symbol::new("?1");

    LemmaPattern {
      lhs: PatternWithHoles::Hole(hole_0),
      rhs: PatternWithHoles::Hole(hole_1),
      holes: VecDeque::from_iter([(hole_0, Side::Left, ty.clone()), (hole_1, Side::Right, ty.clone())].into_iter()),
      next_hole_idx: 2,
    }
  }

  fn next_hole(&self) -> Option<(HoleIdx, Side, Type)> {
    self.holes.back().cloned()
  }

  /// Returns a new [`LemmaPattern`] with `hole` filled with a new [`PatternWithHoles`]
  /// made from the constructor `node` with type `node_ty` (so unless the hole is
  /// being filled with a leaf, `node` will be a function and will have new holes
  /// added for it).
  ///
  /// `side` being passed is somewhat of an implementation detail; we use it to
  /// avoid pointlessly substituting.
  fn subst_hole(&self, hole: HoleIdx, node: Symbol, node_ty: Type, side: Side) -> LemmaPattern {
    let (arg_tys, _ret_ty) = node_ty.args_ret();
    let mut next_hole_idx = self.next_hole_idx;
    let mut new_holes: VecDeque<(HoleIdx, Side, Type)> = arg_tys.into_iter().map(|arg_ty| {
      let new_hole = Symbol::new(format!("?{}", self.next_hole_idx));
      next_hole_idx += 1;
      (new_hole, side.clone(), arg_ty)
    }).collect();
    let new_pattern = PatternWithHoles::Node(node, new_holes.iter().map(|(hole, _, _)| {
      Box::new(PatternWithHoles::Hole(*hole))
    }).collect()
    );
    let mut holes_without_subst_hole = self.holes.iter()
                          .filter(|(curr_hole, _, _)| curr_hole != &hole)
                          .cloned()
                          .collect();
    new_holes.append(&mut holes_without_subst_hole);
    match &side {
      Side::Left => {
        LemmaPattern {
          lhs: self.lhs.subst_hole(hole, &new_pattern).0,
          rhs: self.rhs.clone(),
          holes: new_holes,
          next_hole_idx,
        }
      }
      Side::Right => {
        LemmaPattern {
          lhs: self.lhs.clone(),
          rhs: self.rhs.subst_hole(hole, &new_pattern).0,
          holes: new_holes,
          next_hole_idx,
        }
      }
      Side::Both => {
        LemmaPattern {
          lhs: self.rhs.subst_hole(hole, &new_pattern).0,
          rhs: self.rhs.subst_hole(hole, &new_pattern).0,
          holes: new_holes,
          next_hole_idx,
        }
      }
    }
  }

}

/// A data structure that represents a multipattern match of a [`LemmaPattern`].
///
/// `lhs` and `rhs` match the LHS and RHS of the pattern.
struct ClassMatch {
  goal: GoalName,
  lhs: Id,
  rhs: Id,
  /// What e-classes the holes in the pattern match to.
  /// TODO: We should consider using our own Subst that we have control over
  /// instead of egg's. It is perhaps inefficient anyway since their Subst is just
  /// a small Vec.
  subst: Subst,
  /// Whether the `lhs` and `rhs` cvecs are equal (we compute this once so we
  /// don't need to repeat the process).
  cvecs_equal: bool,
}

struct LemmaTreeNode {
  /// The pattern which represents the current lemma.
  pattern: LemmaPattern,
  /// All pairs of classes this pattern matches.
  matches: Vec<ClassMatch>,
  /// What's the status of the lemma? (`None` if we haven't attempted this lemma).
  lemma_status: Option<LemmaStatus>,
  /// Do we attempt this search?
  search_status: SearchStatus,
  /// Lemmas which are refinements of the patterns in this node.
  children: Vec<(LemmaTreeEdge, LemmaTreeNode)>,
}

enum LemmaStatus {
  Valid,
  Invalid,
  Inconclusive,
}

enum SearchStatus {
  Active,
  Inactive,
}

struct LemmaTreeEdge {
  /// Which hole was filled?
  hole: HoleIdx,
  /// What was it filled with?
  pattern: PatternWithHoles,
}

impl PatternAndMatches {
  /// For a given goal egraph, refine the current matched eclasses based upon
  /// the assumption that we file hole with pattern.
  fn refine_matched_eclasses(&self, hole: HoleIdx, pattern: Pattern<SymbolLang>, goal_name: GoalName, goal_egraph: &Eg) -> EClassMatches {
    let hole_var: Var = hole.as_str().parse().unwrap();
    let hole_eclasses: BTreeSet<Id> = self
      .matched_eclasses[&goal_name]
      .values()
      .flat_map(|substs| substs.iter().map(|subst| subst[hole_var])).collect();
    // These are the substitutions for each hole eclass when we match the
    // pattern against it.
    //
    // The eclasses used as keys here are _not_ the top-level eclasses that the
    // full pattern matches! We will do further work to transform those after
    // building this map.
    let hole_eclass_to_substs: EClassMatches = hole_eclasses.into_iter().map(|eclass| {
      let substs = pattern.search_eclass(goal_egraph, eclass).map_or(vec!(), |search_matches| {
        search_matches.substs
      });
      (eclass, substs)
    }).collect();
    let orig_holes = self.pattern.holes();
    let num_holes_in_pattern = pattern.vars().len();
    // We build the matched eclasses by first iterating over each (eclass, subst) pair
    self.matched_eclasses[&goal_name].iter().filter_map(|(eclass, substs)| {
      // We construct all of the new substitutes that map to this eclass
      let new_substs: Vec<Subst> = substs.iter().flat_map(|subst| {
        // This subst template will have space for as many entries as the number
        // of holes in the original pattern + the number of holes in the new
        // pattern - 1.
        //
        // The - 1 accounts for the fact that we're filling one hole with the
        // new pattern.
        //
        // We initialize this subst to the original subst without the hole we're
        // filling. We'll add the holes in the new pattern after.
        let mut subst_template = Subst::with_capacity(orig_holes.len() + num_holes_in_pattern - 1);
        for orig_hole in &orig_holes {
          let orig_hole_var: Var = orig_hole.as_str().parse().unwrap();
          subst_template.insert(orig_hole_var, subst[orig_hole_var]);
        }
        let hole_eclass = subst[hole_var];
        // This is where we take the substs we found for the hole eclass and expand
        // them into a full subst for the pattern.
        hole_eclass_to_substs[&hole_eclass].iter().map(|hole_substs| {
          let mut new_subst = subst_template.clone();
          for var in pattern.vars() {
            new_subst.insert(var, hole_substs[var]);
          }
          new_subst
        }).collect::<Vec<Subst>>()
      }).collect();
      // If we do not have any substs for this eclass, we can no longer consider
      // it matched
      if new_substs.is_empty() {
        None
      } else {
        Some((*eclass, new_substs))
      }
    }).collect()
  }

  /// For a given goal egraph, find all matches for the entire pattern.
  ///
  /// This differs from refine_matched_eclasses because this method creates
  /// matches for &self whereas refine_matched_eclasses creates matches for a
  /// child PatternAndMatches.
  fn create_matches_from_scratch(&self, goal_egraph: &Eg) -> EClassMatches {
    self.pattern.to_pattern().search(goal_egraph).into_iter().map(|search_matches| {
      (search_matches.eclass, search_matches.substs)
    }).collect()
  }
}

impl LemmaTreeNode {
  /// Resets the status to inactive unless there are two distinct eclasses L in
  /// LHS and R in RHS such that cvec(L) == cvec(R).
  fn update_status_for_goal(&mut self, goal_name: GoalName, goal_egraph: &Eg) {
    self.status = LemmaTreeStatus::Inactive;
    for lhs_eclass in self.lhs.matched_eclasses.get(&goal_name).unwrap().keys() {
      for rhs_eclass in self.rhs.matched_eclasses.get(&goal_name).unwrap().keys() {
        if lhs_eclass == rhs_eclass {
          continue;
        }
        let lhs_cvec = &goal_egraph[*lhs_eclass].data.cvec_data;
        let rhs_cvec = &goal_egraph[*rhs_eclass].data.cvec_data;
        if cvecs_equal(&goal_egraph.analysis.cvec_analysis, lhs_cvec, rhs_cvec).unwrap_or(false) {
          self.status = LemmaTreeStatus::Active;
        }
      }
    }
  }
}
