use std::cell::RefCell;
use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::rc::{Rc, Weak};
use colored::Colorize;
use egg::{Analysis, EGraph, Id, Language, Rewrite, Runner, SymbolLang, Symbol, Pattern, rewrite};
use itertools::{Itertools, Unique};
use serde::Serialize;
use symbolic_expressions::Sexp;
use regex::Regex;
use crate::ast::{Equation, Prop, sexp_size};
use crate::config::CONFIG;
use crate::goal::Goal;
use crate::egraph::get_all_expressions_with_loop;
use crate::goal::Outcome::Valid;
use crate::goal_graph::GoalNodeStatus::Unknown;

/**
 Interface of the current goal graph:
 0. fn new(root: &GoalIndex) -> GoalGraph
    Create the goalgraph with the root node of the target lemma.
 1. fn record_goal_result(&mut self, goal: &GoalIndex, res: GoalNodeStatus)
    Record the result every time when we prove/disprove a goal
 2. fn record_lemma_result(&mut self, lemma_id: usize, res: GoalNodeStatus)
    Record the result every time when we directly know the result of a lemma.
    Currently, the only such case is when the cvecs of a lemma do not match.
 3. fn record_case_split(&mut self, from: &GoalIndex, to: &Vec<GoalIndex>)
    Record the result of case-split
 4. fn record_connector_lemma(&mut self, from: &GoalIndex, root: &GoalIndex)
    Invoke this function every time we find a cc-lemma, "from" denotes the source goal,
    while "root" denotes the root goal of the found lemma.
 5. fn is_lemma_proven(&self, lemma_id: usize) -> bool
    Check whether a lemma is proven by id
 6. fn get_frontier_goals(&self) -> Vec<GoalIndex>
    Get the list of frontier (or active) goals
 7. fn get_waiting_goals(&self, raw_active_lemmas: Option<&HashSet<usize>>) -> Vec<GoalIndex>
    Get the list of waiting (or inactive) goals that have "direct" dependencies with a list
    of newly proven lemmas (raw_active_lemmas).
**/

#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum GoalNodeStatus {
    Unknown, Valid, Invalid
}

type StrongGoalRef = Rc<RefCell<GoalNode>>;
type WeakGoalRef = Weak<RefCell<GoalNode>>;

pub struct GoalNode {
    name: Symbol, // The same as the corresponding goal
    pub lemma_id: usize,
    full_exp: Equation,
    father: Option<WeakGoalRef>,
    pub status: GoalNodeStatus,
    connect_lemmas: Vec<usize>,
    sub_goals: Vec<StrongGoalRef>,
    lemma_size: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct GoalIndex {
    #[serde(serialize_with = "crate::utils::serialize_symbol")]
    pub name: Symbol,
    pub lemma_id: usize,
    #[serde(skip_serializing)]
    pub full_exp: Equation,
    /// The size of the parent lemma (its own cost may be different because it
    /// may be case split)
    ///
    /// FIXME: This should eventually be used in lieu of the lemma AST size we use
    /// in our goal priority queue. Or we should switch to using something like
    /// https://github.com/mlb2251/lambdas.
    pub lemma_size: usize,
}

impl GoalIndex {
    pub fn get_cost(&self) -> usize {
        sexp_size(&self.full_exp.lhs) + sexp_size(&self.full_exp.rhs)
        // self.lemma_depth
    }
    pub fn from_node(node: &GoalNode) -> GoalIndex {
        GoalIndex {
            name: node.name,
            lemma_id: node.lemma_id,
            full_exp: node.full_exp.clone(),
            lemma_size: node.lemma_size,
        }
    }
    pub fn from_goal(goal: &Goal, lemma_id: usize, lemma_size: usize) -> GoalIndex {
        GoalIndex {
            name: goal.name,
            lemma_id, full_exp: goal.full_expr.clone(),
            lemma_size,
        }
    }

    pub fn from_lemma(lemma_name: Symbol, expr: Equation, lemma_id: usize, lemma_size: usize) -> GoalIndex {
        GoalIndex {
            name: lemma_name, full_exp: expr, lemma_id, lemma_size
        }
    }
}

impl GoalNode {
    fn new(goal: &GoalIndex, father: Option<WeakGoalRef>) -> GoalNode {
        GoalNode {
            name: goal.name, lemma_id: goal.lemma_id,
            full_exp: goal.full_exp.clone(),
            father, status: GoalNodeStatus::Unknown,
            connect_lemmas: Vec::new(), sub_goals: Vec::new(),
            lemma_size: goal.lemma_size,
        }
    }
}

pub struct LemmaInfo {
    root: StrongGoalRef,
    lemma_id: usize,
    enodes: Option<(Id, Id)>
}

impl LemmaInfo {
    fn new(root: StrongGoalRef, lemma_id: usize, enodes: Option<(Id, Id)>) -> LemmaInfo {
        LemmaInfo {
            root, lemma_id, enodes
        }
    }

    fn get_status(&self) -> GoalNodeStatus {
        self.root.borrow().status
    }
}

pub struct GoalGraph {
    lemma_map: HashMap<usize, LemmaInfo>,
    pub goal_map: HashMap<Symbol, StrongGoalRef>,
    egraph: EGraph<SymbolLang, ()>,
    lemma_rewrites: Vec<Rewrite<SymbolLang, ()>>,
    proven_lemmas: HashSet<usize>
}

impl GoalGraph {
    pub fn new(root: &GoalIndex) -> GoalGraph{
        let goal = Rc::new(RefCell::new(GoalNode::new(root, None)));
        GoalGraph {
            goal_map: HashMap::from([(root.name, Rc::clone(&goal))]),
            lemma_map: HashMap::from([(root.lemma_id, LemmaInfo::new(goal, root.lemma_id, None))]),
            egraph: EGraph::default(),
            lemma_rewrites: Vec::default(),
            proven_lemmas: HashSet::default()
        }
    }

    /* Record new results */
    pub fn record_goal_result(&mut self, goal: &GoalIndex, res: GoalNodeStatus) {
        match res {
            GoalNodeStatus::Unknown => return,
            _ => {
                let goal_node = &self.goal_map[&goal.name];
                goal_node.borrow_mut().status = res;
                if let Some(father) = &goal_node.borrow().father {
                    Self::propagate_goal_status(father.upgrade().unwrap().as_ref());
                }
            }
        }
    }

    pub fn record_lemma_result(&mut self, lemma_id: usize, res: GoalNodeStatus) {
        match res {
            GoalNodeStatus::Unknown => return,
            _ => {
                let goal_node = &self.lemma_map[&lemma_id].root;
                goal_node.borrow_mut().status = res;
                if let Some(father) = &goal_node.borrow().father {
                    Self::propagate_goal_status(father.upgrade().unwrap().as_ref());
                }
            }
        }
    }

    fn propagate_goal_status(node: &RefCell<GoalNode>) {
        let mut status = node.borrow().status;
        if status != GoalNodeStatus::Unknown {return;}
        let sub_status: Vec<_> = node.borrow().sub_goals.iter().map(
            |sub_node| {sub_node.borrow().status}
        ).collect();

        if sub_status.iter().all(|s| *s == GoalNodeStatus::Valid) {
            status = GoalNodeStatus::Valid;
        }
        if sub_status.iter().any(|s| *s == GoalNodeStatus::Invalid) {
            status = GoalNodeStatus::Invalid;
        }

        if status != GoalNodeStatus::Unknown {
            node.borrow_mut().status = status;
            if let Some(father) = &node.borrow().father {
                Self::propagate_goal_status(father.upgrade().unwrap().as_ref());
            }
        }
    }

    pub fn record_case_split(&mut self, from: &GoalIndex, to: &Vec<GoalIndex>) {
        let goal_node = self.goal_map.get(&from.name).unwrap();
        let mut sub_goals = Vec::new();
        for sub_goal in to {
            let weak_goal: Weak<RefCell<GoalNode>> = Rc::downgrade(goal_node);
            let sub_node = Rc::new(RefCell::new(GoalNode::new(sub_goal, Some(weak_goal))));
            goal_node.borrow_mut().sub_goals.push(sub_node.clone());
            sub_goals.push((sub_goal.name, sub_node));
        }
        self.goal_map.extend(sub_goals.into_iter());
    }

    fn get_lemma_enodes(&mut self, goal: &GoalIndex) -> (Id, Id){
        let lhs = goal.full_exp.lhs.to_string().parse().unwrap();
        let rhs = goal.full_exp.rhs.to_string().parse().unwrap();
        (self.egraph.add_expr(&lhs), self.egraph.add_expr(&rhs))
    }

    pub fn record_connector_lemma(&mut self, from: &GoalIndex, root: &GoalIndex) {
        if !self.lemma_map.contains_key(&root.lemma_id) {
            // println!("New cc lemma {}", root.full_exp);
            let goal = Rc::new(RefCell::new(GoalNode::new(root, None)));
            self.goal_map.insert(root.name, Rc::clone(&goal));
            let enodes = self.get_lemma_enodes(root);
            self.lemma_map.insert(root.lemma_id, LemmaInfo::new(goal, root.lemma_id, Some(enodes)));
        }

        let goal_node = self.goal_map.get(&from.name).unwrap();
        goal_node.borrow_mut().connect_lemmas.push(root.lemma_id);
    }

    pub fn is_lemma_proven(&self, lemma_id: usize) -> bool {
        let root = self.lemma_map.get(&lemma_id).unwrap();
        root.get_status() == GoalNodeStatus::Valid
    }

    fn get_working_goals(&mut self) -> (Vec<StrongGoalRef>, Vec<StrongGoalRef>) {
        self.update_proven_lemmas();

        let mut visited_lemmas = HashSet::new();
        let mut queue = VecDeque::new();
        let mut frontier_goals = Vec::new();
        let mut waiting_goals = Vec::new();

        let start = self.lemma_map[&0usize].root.clone();
        visited_lemmas.insert(0usize);
        queue.push_back(start);

        while let Some(current_goal) = queue.pop_front() {
            let node = current_goal.borrow();

            if node.status != Unknown {continue;}
            for related_lemma in node.connect_lemmas.iter() {
                let lemma_info = self.lemma_map.get(related_lemma).unwrap();
                if lemma_info.get_status() != Unknown || visited_lemmas.contains(related_lemma) {
                    continue;
                }
                visited_lemmas.insert(*related_lemma);
                queue.push_back(self.lemma_map[related_lemma].root.clone());
            }

            if node.sub_goals.is_empty() {
                frontier_goals.push(current_goal.clone());
            } else {
                waiting_goals.push(current_goal.clone());
                for child in node.sub_goals.iter() {
                    queue.push_back(child.clone());
                }
            }
        }
        (waiting_goals, frontier_goals)
    }
    pub fn get_frontier_goals(&mut self) -> Vec<GoalIndex> {
        self.get_working_goals().1.iter().map(
            |raw_node| {
                let node = raw_node.borrow();
                GoalIndex::from_node(&node)
            }
        ).collect()
    }

    pub fn get_waiting_goals(&mut self, raw_active_lemmas: Option<&HashSet<usize>>) -> Vec<GoalIndex> {
        let mut res = self.get_working_goals().0;
        if CONFIG.saturate_only_parent {
            if let Some(active_lemmas) = raw_active_lemmas {
                res = res.clone().into_iter().filter(|info| {
                    info.borrow().connect_lemmas.iter().any(|w| {active_lemmas.contains(w)})
                }).collect();
            }
        }
        res.iter().map(|raw_node| {
            let node = raw_node.borrow();
            GoalIndex::from_node(&node)
        }).collect()
    }

    pub fn saturate(&mut self) {
        self.egraph = EGraph::default();

        for (index, lemma_info) in self.lemma_map.iter_mut() {
            if lemma_info.enodes.is_some() {
                let full_exp = &lemma_info.root.borrow().full_exp;
                let lhs = full_exp.lhs.to_string().parse().unwrap();
                let rhs = full_exp.rhs.to_string().parse().unwrap();
                lemma_info.enodes = Some((self.egraph.add_expr(&lhs), self.egraph.add_expr(&rhs)));
            }
        }

        let runner = Runner::default()
            .with_egraph(self.egraph.clone())
            .run(&self.lemma_rewrites);
        self.egraph = runner.egraph;
    }

    fn get_new_id(&self, id: (Id, Id)) -> (Id, Id) {
        let x = self.egraph.find(id.0);
        let y = self.egraph.find(id.1);
        if x < y {(x, y)} else {(y, x)}
    }

    pub fn relink_related_lemmas(&mut self) {
        self.saturate();
        let mut repr_map = HashMap::new();
        for lemma in self.lemma_map.values() {
            if lemma.enodes.is_none() { continue; }
            let nodes = lemma.enodes.unwrap();
            let classes = self.get_new_id(nodes);
            // println!("{} {}.{}", lemma.root.borrow().full_exp, classes.0, classes.1);

            match repr_map.get_mut(&classes) {
                None => {
                    repr_map.insert(classes, lemma.lemma_id);
                },
                Some(id) => if *id > lemma.lemma_id {
                    *id = lemma.lemma_id;
                }
            }
        }

        let mut repr_id_map = HashMap::new();
        let mut removed = HashSet::new();
        for (index, lemma) in self.lemma_map.iter() {
            if lemma.enodes.is_none () {
                repr_id_map.insert(lemma.lemma_id, lemma.lemma_id);
                continue;
            }
            let classes = self.get_new_id(lemma.enodes.unwrap());
            if classes.0 == classes.1 {
                removed.insert(*index);
            } else {
                repr_id_map.insert(lemma.lemma_id, repr_map[&classes]);
                if lemma.lemma_id != repr_map[&classes] {
                    removed.insert(*index);
                }
            }
        }

        for goal in self.goal_map.values() {
            let mut existing = HashSet::new();
            for lemma in goal.borrow().connect_lemmas.iter() {
                if let Some(new_id) = repr_id_map.get(lemma) {
                    existing.insert(*new_id);
                }
            }
            goal.borrow_mut().connect_lemmas = existing.into_iter().collect();
        }
        for removed_id in removed.iter() {
            self.lemma_map.remove(removed_id);
        }
    }

    pub fn add_bidir_lemma(&mut self, lhs: Sexp, rhs: Sexp) {
        // println!("New bid lemma {} <=> {}", lhs, rhs);
        let id = self.lemma_rewrites.len();
        let lhs: Pattern<_> = lhs.to_string().parse().unwrap();
        let rhs: Pattern<_> = rhs.to_string().parse().unwrap();
        let left_rewrite = Rewrite::new(format!("left-{}", id), lhs.clone(), rhs.clone()).unwrap();
        self.lemma_rewrites.push(left_rewrite);
        let right_rewrite = Rewrite::new(format!("right-{}", id), rhs.clone(), lhs.clone()).unwrap();
        self.lemma_rewrites.push(right_rewrite);
        self.relink_related_lemmas();
    }

    fn update_proven_lemmas(&mut self) {
        let mut new_rewrites = Vec::new();
        // println!("#lemmas {}, size(e-graph) {}", self.lemma_map.values().len(), self.egraph.total_number_of_nodes());
        for lemma in self.lemma_map.values() {
            if self.is_lemma_proven(lemma.lemma_id) && !self.proven_lemmas.contains(&lemma.lemma_id) {
                self.proven_lemmas.insert(lemma.lemma_id);
                // println!("try proven lemmas {} <=> {}", lemma.root.borrow().full_exp.lhs, lemma.root.borrow().full_exp.rhs);
                let (left_vars, left_pattern) = build_pattern(&lemma.root.borrow().full_exp.lhs);
                let (right_vars, right_pattern) = build_pattern(&lemma.root.borrow().full_exp.rhs);
                // We only will use bidirectional lemmas to shrink our candidate
                // lemma set. It is unsound to use unidirectional lemmas.
                //
                // A simple example: suppose you prove the lemma a => b that is unidirectional.
                //
                // If you have candidates
                //
                // a = c
                // b = c
                //
                // Our analysis will use this unidirectional lemma to observe
                // that these candidates are the same and pick one of the two
                // arbitrarily.
                //
                // However, we only know for sure that under the lemma a => b, a
                // = c implies b = c. We don't know the opposite direction holes
                // because we don't have the lemma b => a.
                //
                // Ideally, we would somehow track which lemma we can eliminate
                // (perhaps via an e-class analysis), but we don't yet.
                if left_vars == right_vars {
                    new_rewrites.push((left_pattern, right_pattern));
                }
            }
        }
        for (left, right) in new_rewrites.into_iter() {
            self.add_bidir_lemma(left, right);
        }
    }
}

fn build_pattern(exp: &Sexp) -> (BTreeSet<String>, Sexp) {
    match exp {
        Sexp::String(s) => {
            let re = Regex::new(r"v\d+$").unwrap();
            if re.is_match(s) {
                let new_name = format!("?{}", s);
                ([new_name.clone()].into(), Sexp::String(new_name))
            } else {
                ([].into(), exp.clone())
            }
        }
        Sexp::List(lists) => {
            let mut res = Vec::new();
            let mut res_set = BTreeSet::new();

            for (sub_set, sub_res) in lists.iter().map(|sub_exp| build_pattern(sub_exp)) {
                res_set.extend(sub_set);
                res.push(sub_res);
            }
            (res_set, Sexp::List(res))
        }
        Sexp::Empty => {
            panic!("unexpected exp")
        }
    }
}
