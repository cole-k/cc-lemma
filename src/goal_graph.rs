use std::cmp::{Ordering, Reverse};
use std::collections::{HashMap, HashSet, VecDeque};
use egg::{EGraph, Id, Rewrite, Runner, SymbolLang};
use itertools::Unique;
use crate::ast::{Prop, sexp_size};
use crate::config::CONFIG;
use crate::goal::Goal;
use crate::goal_graph::GraphProveStatus::{Subsumed, Unknown, Valid};

#[derive(PartialEq, Eq, Debug)]
pub enum GraphProveStatus {
    Unknown, Valid, Invalid, Subsumed
}

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct GoalInfo {
    pub name: String,
    pub lemma_id: usize,
    pub full_exp: String,
    pub size: usize
}

impl GoalInfo {
    pub fn new(goal: &Goal, lemma_id: usize) -> Self{
        GoalInfo {
            name: goal.name.clone(),
            lemma_id,
            full_exp: goal.full_expr.to_string(),
            size: sexp_size(&goal.full_expr.lhs) + sexp_size(&goal.full_expr.rhs)
        }
    }
}

impl PartialOrd for GoalInfo {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Reverse(self.size).partial_cmp(&Reverse(other.size))
    }
}

impl Ord for GoalInfo {
    fn cmp(&self, other: &Self) -> Ordering {
        Reverse(self.size).cmp(&Reverse(other.size))
    }
}

pub struct GoalNode {
    info: GoalInfo,
    split_children: Option<Vec<GoalInfo>>,
    father: Option<GoalInfo>,
    pub status: GraphProveStatus,
    related_lemmas: HashSet<usize>
}

impl GoalNode {
    fn new(info: &GoalInfo, father: Option<&GoalInfo>) -> GoalNode {
        GoalNode {
            info: info.clone(),
            split_children: None,
            father: father.cloned(),
            status: GraphProveStatus::Unknown,
            related_lemmas: HashSet::default()
        }
    }
}

pub struct LemmaNode {
    pub goals: Vec<GoalInfo>,
    lemma_id: usize,
    status: GraphProveStatus,
    nodes: Option<(Id, Id)>
}

impl LemmaNode {
    fn new(root: &GoalInfo, nodes: Option<(Id, Id)>) -> LemmaNode {
        LemmaNode {
            goals: vec![root.clone()],
            lemma_id: root.lemma_id,
            status: GraphProveStatus::Unknown,
            nodes /* TODO: rewrite names of properties */
        }
    }
}

#[derive(Default)]
pub struct GoalGraph {
    goal_index_map: HashMap<GoalInfo, GoalNode>,
    lemma_index_map: HashMap<usize, LemmaNode>,
    egraph: EGraph<SymbolLang, ()>,
    lemma_rewrites: Vec<Rewrite<SymbolLang, ()>>
}

impl GoalGraph {
    fn get_goal_mut(&mut self, info: &GoalInfo) -> &mut GoalNode {
        self.goal_index_map.get_mut(info).unwrap()
    }
    fn get_lemma_mut(&mut self, id: usize) -> &mut LemmaNode {
        self.lemma_index_map.get_mut(&id).unwrap()
    }
    pub fn get_goal(&self, info: &GoalInfo) -> &GoalNode {
        self.goal_index_map.get(info).unwrap()
    }
    pub fn get_lemma(&self, id: usize) -> &LemmaNode {
        self.lemma_index_map.get(&id).unwrap()
    }

    fn new_goal(&mut self, info: &GoalInfo, father: Option<&GoalInfo>)  {
        self.goal_index_map.insert(
            info.clone(),
            GoalNode::new(info, father)
        );
    }

    fn get_prop_id(&mut self, prop: &Prop) -> (Id, Id) {
        let lhs = prop.eq.lhs.to_string().parse().unwrap();
        let rhs = prop.eq.rhs.to_string().parse().unwrap();
        (self.egraph.add_expr(&lhs), self.egraph.add_expr(&rhs))
    }

    fn saturate(&mut self) {
        let runner = Runner::default().with_egraph(self.egraph.clone()).run(&self.lemma_rewrites);
        self.egraph = runner.egraph;
    }
    pub fn new_lemma(&mut self, root: &GoalInfo, prop: Option<&Prop>) {
        self.new_goal(root, None);
        let prop_id = prop.map(|p| {self.get_prop_id(p)});
        self.lemma_index_map.insert(
            root.lemma_id,
            LemmaNode::new(root, prop_id)
        );
    }
    pub fn exclude_bid_reachable_lemmas(&mut self, prop_list: &Vec<(usize, Prop)>) -> Vec<(usize, Prop)> {
        let id_list: Vec<_> = prop_list.iter().map(|(_,prop)| {self.get_prop_id(prop)}).collect();
        self.saturate();

        let mut visited = HashMap::new();
        for (prop, (x, y)) in prop_list.iter().zip(id_list.iter()) {
            let x = self.egraph.find(*x);
            let y = self.egraph.find(*y);
            let feature = if x < y {(x, y)} else {(y, x)};
            match visited.get_mut(&feature) {
                None => {
                    visited.insert(feature, prop.clone());
                },
                Some(pre) => if prop.1.to_string().len() < pre.1.to_string().len() {*pre = prop.clone();}
            }
        }
        visited.into_iter().map(|(a, b)| {b}).collect()
    }

    pub fn record_case_split(&mut self, from: &GoalInfo, to: &Vec<GoalInfo>) {
        self.get_goal_mut(from).split_children = Some(to.clone());
        for child in to.iter() {
            self.new_goal(child, Some(from));
            self.get_lemma_mut(from.lemma_id).goals.push(child.clone())
        }
    }

    fn get_new_id(&self, id: (Id, Id)) -> (Id, Id){
        let classes = (self.egraph.find(id.0), self.egraph.find(id.1));
        if classes.0 > classes.1 {(classes.1, classes.0)} else {classes}
    }

    pub fn relink_related_lemmas(&mut self) {
        self.saturate();

        let mut repr_map = HashMap::new();
        for lemma in self.lemma_index_map.values() {
            if lemma.nodes.is_none() {continue;}
            let nodes = lemma.nodes.unwrap();
            let classes = self.get_new_id(nodes);
            let start_size = lemma.goals.first().unwrap().size;

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
        for lemma in self.lemma_index_map.values() {
            if lemma.nodes.is_none() {
                repr_id_map.insert(lemma.lemma_id, lemma.lemma_id);
                continue;
            }
            let classes = self.get_new_id(lemma.nodes.unwrap());
            repr_id_map.insert(lemma.lemma_id, repr_map[&classes]);
        }

        for goal in self.goal_index_map.values_mut() {
            goal.related_lemmas = goal.related_lemmas.iter().map(
                |lemma_id| {repr_id_map[lemma_id]}
            ).collect();
        }
    }

    pub fn add_bid_rewrites(&mut self, lhs: Rewrite<SymbolLang, ()>, rhs: Rewrite<SymbolLang, ()>) {
        self.lemma_rewrites.push(lhs);
        self.lemma_rewrites.push(rhs);
        self.relink_related_lemmas();
    }

    pub fn record_related_lemmas(&mut self, from: &GoalInfo, lemmas: &Vec<(GoalInfo, Prop)>) {
        for (lemma_root, prop) in lemmas.iter() {
            if !self.lemma_index_map.contains_key(&lemma_root.lemma_id) {
                self.new_lemma(lemma_root, Some(prop));
            }
        }
        let node = self.get_goal_mut(from);
        for (lemma_root, _) in lemmas.iter() {
            node.related_lemmas.insert(lemma_root.lemma_id);
        }
        if CONFIG.exclude_bid_reachable {
            self.relink_related_lemmas();
        }
    }

    fn check_split_finished(&mut self, info: &GoalInfo) {
        let node = self.get_goal(info);
        if node.status != Unknown {return;}
        let father = node.father.clone();
        let children = node.split_children.clone().unwrap();

        if children.into_iter().all(|child| self.get_goal(&child).status == GraphProveStatus::Valid) {
            self.get_goal_mut(info).status = GraphProveStatus::Valid;
            if father.is_some() {
                self.check_split_finished(&father.unwrap());
            }
        }
    }

    pub fn record_node_status(&mut self, node: &GoalInfo, status: GraphProveStatus) {
        assert!(status == GraphProveStatus::Valid || status == GraphProveStatus::Invalid);

        if status == GraphProveStatus::Invalid {
            self.get_lemma_mut(node.lemma_id).status = GraphProveStatus::Invalid;
            return;
        }

        let goal_node = self.get_goal_mut(node);
        if goal_node.status != Unknown {return;}
        goal_node.status = status;

        let mut queue = VecDeque::new();
        queue.push_back(node.clone());

        while let Some(info) = queue.pop_front() {
            if let Some(children) = self.get_goal(&info).split_children.clone() {
                for child in children {
                    self.get_goal_mut(&child).status = Subsumed;
                    queue.push_back(child);
                }
            }
        }

        if let Some(father) = self.get_goal(node).father.clone() {
            self.check_split_finished(&father);
        }
    }

    pub fn send_subsumed_check(&self) -> Vec<usize> {
        self.lemma_index_map.iter().filter_map(
            |(id, node)| {
                if node.status == Unknown {Some(*id)} else {None}
            }
        ).collect()
    }

    pub fn receive_subsumed_check(&mut self, subsumed_lemmas: Vec<usize>) {
        for lemma_id in subsumed_lemmas {
            self.get_lemma_mut(lemma_id).status = Subsumed;
        }
    }

    fn get_working_goals(&self) -> (Vec<GoalInfo>, Vec<GoalInfo>) {
        let mut visited_lemmas = HashSet::new();
        let mut queue = VecDeque::new();
        let mut frontier_goals = Vec::new();
        let mut waiting_goals = Vec::new();
        queue.push_back(self.get_lemma(0).goals[0].clone());
        visited_lemmas.insert(0usize);

        while let Some(current_goal) = queue.pop_front() {
            let node = self.get_goal(&current_goal);
            // println!("goal [{}] {} {:?} {}", node.info.lemma_id, node.info.full_exp, node.status, node.split_children.is_none());
            if node.status != Unknown {continue;}
            for related_lemma in node.related_lemmas.iter() {
                let lemma_node = self.get_lemma(*related_lemma);
                if lemma_node.status != Unknown || visited_lemmas.contains(related_lemma) {
                    continue;
                }
                visited_lemmas.insert(*related_lemma);
                queue.push_back(lemma_node.goals[0].clone());
            }
            if node.split_children.is_none() {
                frontier_goals.push(current_goal);
            } else {
                waiting_goals.push(current_goal);
                for child in node.split_children.as_ref().unwrap() {
                    queue.push_back(child.clone())
                }
            }
        }
        (waiting_goals, frontier_goals)
    }

    pub fn is_root(&self, info: &GoalInfo) -> bool {
        let lemma_node = self.get_lemma(info.lemma_id);
        let root_goal = lemma_node.goals.first().unwrap();
        info.full_exp == root_goal.full_exp
    }
    pub fn get_frontier_goals(&self) -> Vec<GoalInfo> {
        self.get_working_goals().1
    }

    pub fn get_waiting_goals(&self, raw_active_lemmas: Option<&HashSet<usize>>) -> Vec<GoalInfo> {
        let raw_res = self.get_working_goals().0;
        if CONFIG.saturate_only_parent {
            if let Some(active_lemmas) = raw_active_lemmas {
                let mut res = Vec::new();
                for info in raw_res {
                    if self.get_goal(&info).related_lemmas.iter().any(|w| { active_lemmas.contains(w) }) {
                        res.push(info);
                    }
                }
                return res;
            }
        }
        raw_res
    }

    pub fn is_lemma_proved(&self, lemma_id: usize) -> bool {
        let root_info = &self.get_lemma(lemma_id).goals[0];
        self.get_goal(root_info).status == Valid
        /*let mut queue = VecDeque::new();
        queue.push_back(&self.get_lemma(lemma_id).goals[0]);

        while let Some(info) = queue.pop_front() {
            let goal_node = self.get_goal(info);
            if goal_node.status == Unknown {
                if goal_node.split_children.is_none() {return false;}
                for child in goal_node.split_children.as_ref().unwrap() {
                    queue.push_back(child);
                }
            } else if goal_node.status == GraphProveStatus::Valid {
                continue;
            } else {
                return false;
            }
        }
        return true;*/
    }

    pub fn set_lemma_res(&mut self, lemma_id: usize, status: GraphProveStatus) {
        self.get_lemma_mut(lemma_id).status = status;
    }
}