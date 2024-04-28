use std::collections::{BTreeMap, BTreeSet};

use egg::{Symbol, Id};

use crate::{goal::Eg, analysis::cvecs_equal};

type GoalName = String;
type HoleIdx  = usize;

/// A pattern that corresponds to one side of a lemma. We draw inspiration from
/// Stitch's patterns.
///
/// Examples:
///     // A completed pattern corresponding to S (add x y)
///     Node("S", [Node("add", [Leaf("x"), Leaf("y")])])
///     // An incomplete pattern corresponding to S (add ??_1 ??_2)
///     Node("S", [Node("add", [Hole(1), Hole(2)])])
///
/// TODO: The representation could probably be made more efficient by use of
/// mutable references, etc.
#[derive(PartialEq, Eq, Clone)]
enum LemmaPattern {
  /// A hole to be filled in eventually with another LemmaPattern.
  ///
  /// If the LemmaPattern has no Holes, then we consider it complete, otherwise
  /// it is incomplete.
  Hole(HoleIdx),
  /// These are akin to the Nodes in SymbolLang.
  ///
  /// If they have 0 arguments then they are leaf nodes (constants such as Z,
  /// Nil, or variables).
  ///
  /// Otherwise they are internal nodes such as (Cons _ _) or (add _ _).
  Node(Symbol, Vec<Box<LemmaPattern>>),
}

impl LemmaPattern {
  /// Is the pattern complete (i.e. does it have no Holes)?
  pub fn is_complete(&self) -> bool {
    match self {
      LemmaPattern::Hole(_) => false,
      LemmaPattern::Node(_, args) => args.iter().all(|arg| arg.is_complete()),
    }
  }

  /// Is it a leaf (either a Hole or a Node without arguments)?
  pub fn is_leaf(&self) -> bool {
    match self {
      LemmaPattern::Hole(_) => true,
      LemmaPattern::Node(_, args) => args.is_empty(),
    }
  }

  /// Mutates the pattern to fill the hole.
  pub fn fill_hole(&mut self, hole: HoleIdx, value: &LemmaPattern) {
    match &self {
      LemmaPattern::Hole(h) if *h == hole => {
        *self = value.clone();
      }
      LemmaPattern::Hole(_) => {
      }
      LemmaPattern::Node(_, args) => {
        args.iter_mut().for_each(|arg| arg.fill_hole(hole, value));
      }
    }
  }

  /// Returns a new pattern where the hole is filled.
  pub fn subst_hole(&self, hole: HoleIdx, value: &LemmaPattern) -> LemmaPattern {
    match &self {
      LemmaPattern::Hole(h) if *h == hole => {
        value.clone()
      }
      LemmaPattern::Hole(_) => {
        self.clone()
      }
      LemmaPattern::Node(op, args) => {
        LemmaPattern::Node(*op, args.iter().map(|arg| Box::new(arg.subst_hole(hole, value))).collect())
      }
    }
  }

  /// Returns all holes in the Pattern
  ///
  /// TODO: Could probably be made into an iterator if we make an assumption
  /// that it is a set.
  pub fn holes(&self) -> BTreeSet<HoleIdx> {
    fn helper(pat: &LemmaPattern, holes: &mut BTreeSet<HoleIdx>) {
      match pat {
        LemmaPattern::Hole(idx) => {
          holes.insert(*idx);
        }
        LemmaPattern::Node(_, args) => {
          args.iter().for_each(|arg| helper(arg, holes));
        }
      }
    }
    let mut holes = BTreeSet::new();
    helper(self, &mut holes);
    holes
  }

}

impl std::fmt::Display for LemmaPattern {
  /// Formats the LemmaPattern as a sexp.
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      LemmaPattern::Hole(idx) => {
        write!(f, "?{}", idx)
      }
      LemmaPattern::Node(op, args) => {
        if args.is_empty() {
          write!(f, "{}", op)
        } else {
          write!(f, "({}", op)?;
          args.iter().try_for_each(|arg| {
            write!(f, " ")?;
            arg.fmt(f)
          });
          write!(f, ")")
        }
      }
    }
  }
}

/// A map from a hole to the eclasses that can go inside of it.
type HoleMatches   = BTreeMap<HoleIdx, Vec<Id>>;
/// A map from the eclasses a pattern matches to what eclasses go inside of its
/// holes to create a match. We expect that often there will only be one
/// HoleMatches per eclass.
type EClassMatches = BTreeMap<Id, Vec<HoleMatches>>;

struct LemmaTreeNode {
  lhs: LemmaPattern,
  rhs: LemmaPattern,
  /// For each goal, the eclasses that match the LHS.
  lhs_matched_eclasses: BTreeMap<GoalName, EClassMatches>,
  /// For each goal, the eclasses that match the RHS.
  rhs_matched_eclasses: BTreeMap<GoalName, EClassMatches>,
  /// We use this to ensure that our hole indices are fresh.
  next_hole_idx: HoleIdx,
  /// Is this branch active?
  status: LemmaTreeStatus,
}

enum LemmaTreeStatus {
  /// There are no pairs of distinct eclasses between the LHS and RHS that have
  /// the same cvec.
  Inactive,
  /// There are pairs of distinct eclasses between the LHS and RHS that have
  /// the same cvec.
  Active,
}

impl LemmaTreeNode {
  /// Resets the status to inactive unless there are two distinct eclasses L in
  /// LHS and R in RHS such that cvec(L) == cvec(R).
  fn update_status_for_goal(&mut self, goal_name: GoalName, goal_egraph: &Eg) {
    self.status = LemmaTreeStatus::Inactive;
    for lhs_eclass in self.lhs_matched_eclasses.get(&goal_name).unwrap().keys() {
      for rhs_eclass in self.rhs_matched_eclasses.get(&goal_name).unwrap().keys() {
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
