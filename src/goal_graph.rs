use std::cell::RefCell;
use std::cmp::{Ordering, Reverse};
use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::{Rc, Weak};
use colored::Colorize;
use egg::{Analysis, EGraph, Id, Language, Rewrite, Runner, SymbolLang};
use itertools::Unique;
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
    name: String, // The same as the corresponding goal
    lemma_id: usize,
    full_exp: Equation,
    father: Option<WeakGoalRef>,
    status: GoalNodeStatus,

    connect_lemmas: Vec<usize>,
    sub_goals: Vec<StrongGoalRef>
}

#[derive(Clone, Debug)]
pub struct GoalIndex {
    pub name: String,
    pub lemma_id: usize,
    pub full_exp: Equation
}

impl GoalIndex {
    pub fn get_cost(&self) -> usize {
        sexp_size(&self.full_exp.lhs) + sexp_size(&self.full_exp.rhs)
    }
    pub fn from_node(node: &GoalNode) -> GoalIndex {
        GoalIndex {
            name: node.name.clone(),
            lemma_id: node.lemma_id,
            full_exp: node.full_exp.clone()
        }
    }
    pub fn from_goal(goal: &Goal, lemma_id: usize) -> GoalIndex {
        GoalIndex {
            name: goal.name.clone(),
            lemma_id, full_exp: goal.full_expr.clone()
        }
    }

    pub fn from_lemma(lemma_name: String, expr: Equation, lemma_id: usize) -> GoalIndex {
        GoalIndex {
            name: lemma_name, full_exp: expr, lemma_id
        }
    }
}

impl GoalNode {
    fn new(goal: &GoalIndex, father: Option<WeakGoalRef>) -> GoalNode {
        GoalNode {
            name: goal.name.clone(), lemma_id: goal.lemma_id,
            full_exp: goal.full_exp.clone(),
            father, status: GoalNodeStatus::Unknown,
            connect_lemmas: Vec::new(), sub_goals: Vec::new()
        }
    }
}

pub struct LemmaInfo {
    root: StrongGoalRef,
    lemma_id: usize
}

impl LemmaInfo {
    fn new(root: StrongGoalRef, lemma_id: usize) -> LemmaInfo {
        LemmaInfo {
            root, lemma_id
        }
    }

    fn get_status(&self) -> GoalNodeStatus {
        self.root.borrow().status
    }
}

pub struct GoalGraph {
    lemma_map: HashMap<usize, LemmaInfo>,
    goal_map: HashMap<String, StrongGoalRef>
}

impl GoalGraph {
    pub fn new(root: &GoalIndex) -> GoalGraph{
        let goal = Rc::new(RefCell::new(GoalNode::new(root, None)));
        GoalGraph {
            goal_map: HashMap::from([(root.name.clone(), Rc::clone(&goal))]),
            lemma_map: HashMap::from([(root.lemma_id, LemmaInfo::new(goal, root.lemma_id))])
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
            sub_goals.push((sub_goal.name.clone(), sub_node));
        }
        self.goal_map.extend(sub_goals.into_iter());
    }

    pub fn record_connector_lemma(&mut self, from: &GoalIndex, root: &GoalIndex) {
        if !self.lemma_map.contains_key(&root.lemma_id) {
            let goal = Rc::new(RefCell::new(GoalNode::new(root, None)));
            self.goal_map.insert(root.name.clone(), Rc::clone(&goal));
            self.lemma_map.insert(root.lemma_id, LemmaInfo::new(goal, root.lemma_id));
        }

        let goal_node = self.goal_map.get(&from.name).unwrap();
        goal_node.borrow_mut().connect_lemmas.push(root.lemma_id);
    }

    pub fn is_lemma_proven(&self, lemma_id: usize) -> bool {
        let root = self.lemma_map.get(&lemma_id).unwrap();
        root.get_status() == GoalNodeStatus::Valid
    }

    fn get_working_goals(&self) -> (Vec<StrongGoalRef>, Vec<StrongGoalRef>) {
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
    pub fn get_frontier_goals(&self) -> Vec<GoalIndex> {
        self.get_working_goals().1.iter().map(
            |raw_node| {
                let node = raw_node.borrow();
                GoalIndex::from_node(&node)
            }
        ).collect()
    }

    pub fn get_waiting_goals(&self, raw_active_lemmas: Option<&HashSet<usize>>) -> Vec<GoalIndex> {
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
}