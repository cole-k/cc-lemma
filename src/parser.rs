use egg::*;
use std::char;
use std::collections::BTreeSet;
use symbolic_expressions::*;

use crate::ast::*;
use crate::config::CONFIG;
use crate::egraph::{ConditionalSearcher, DestructiveApplier};
use crate::goal::*;

fn make_rewrite_for_defn<A>(name: &str, args: &Sexp, value: &Sexp, is_axiom: bool) -> Rewrite<SymbolLang, A>
  where
      A: Analysis<SymbolLang>
{
  let name_sexp = Sexp::String(name.to_string());
  let pattern_with_name = match args {
    Sexp::Empty => name_sexp,
    Sexp::List(args) => {
      let mut new_list = vec![name_sexp];
      new_list.extend(args.iter().cloned());
      Sexp::List(new_list)
    }
    arg @ Sexp::String(_) => Sexp::List(vec![name_sexp, arg.clone()]),
  };
  let lhs = pattern_with_name.to_string();
  let rhs = value.to_string();
  // println!("rewrite rule: {} => {}", lhs, rhs);
  let searcher: Pattern<SymbolLang> = lhs.parse().unwrap();
  let applier: Pattern<SymbolLang> = rhs.parse().unwrap();
  if CONFIG.destructive_rewrites && !is_axiom {
    Rewrite::new(lhs, searcher.clone(), DestructiveApplier::new(searcher, applier)).unwrap()
  } else {
    Rewrite::new(lhs, searcher, applier).unwrap()
  }

}

pub struct RawGoal {
  pub name: String,
  pub prop: Prop,
  pub premise: Option<Equation>,
  pub local_rules: Vec<Rw>,
  pub local_searchers: Vec<ConditionalSearcher<Pattern<SymbolLang>, Pattern<SymbolLang>>>
}

#[derive(Default)]
pub struct ParserState {
  pub env: Env,
  pub context: Context,
  pub defns: Defns,
  pub rules: Vec<Rw>,
  pub cvec_rules: Vec<CvecRw>,
  pub raw_goals: Vec<RawGoal>,
}

impl ParserState {
  /// Return all function definitions used in exprs,
  /// including the functions transitively used in those definitions.
  fn used_names_and_definitions(&self, exprs: &Vec<Expr>) -> (BTreeSet<Symbol>, Vec<Rw>) {
    let mut used_names = BTreeSet::new();
    let mut used_defs = vec![];
    let mut worklist = vec![];
    for expr in exprs {
      let expr_as_nodes_or_var: Vec<ENodeOrVar<SymbolLang>> = expr
          .as_ref()
          .iter()
          .map(|n| ENodeOrVar::ENode(n.clone()))
          .collect();
      let expr_as_pattern: PatternAst<SymbolLang> = PatternAst::from(expr_as_nodes_or_var);
      self.add_functions(&expr_as_pattern, &mut used_names, &mut worklist);
    }
    while let Some(s) = worklist.pop() {
      let def_rules = self.definition(&s);
      for rule in def_rules {
        used_defs.push(rule.clone());
        let rhs = rule.applier.get_pattern_ast().unwrap();
        self.add_functions(rhs, &mut used_names, &mut worklist);
      }
    }
    (used_names, used_defs)
  }

  /// Add all functions mentioned in e to used_names and worklist.
  fn add_functions(
    &self,
    e: &PatternAst<SymbolLang>,
    used_names: &mut BTreeSet<Symbol>,
    worklist: &mut Vec<Symbol>,
  ) {
    for node_or_var in e.as_ref() {
      if let ENodeOrVar::ENode(node) = node_or_var {
        let s = node.op;
        if self.context.contains_key(&s)
            && !is_constructor(&s.to_string())
            && !used_names.contains(&s)
        {
          used_names.insert(s);
          worklist.push(s);
        }
      }
    }
  }

  /// Name of the rule that converts a partial application of name into a first-order application.
  fn is_part_app_rule(rule_name: &Symbol, name: &Symbol) -> bool {
    let prefix = format!("apply-{}-", name);
    rule_name.to_string().starts_with(&prefix)
  }

  fn get_part_app_rule(name: &Symbol, id: usize) -> String {
    format!("apply-{}-{}", name, id)
  }


  /// Return all rules that define the function name,
  /// including the rule that defines conversion from partial to first-order application.
  fn definition(&self, name: &Symbol) -> Vec<&Rw> {
    let mut res = Vec::new();
    for r in &self.rules {
      if Self::is_part_app_rule(&r.name, name) {
      //if r.name.to_string() == ParserState::part_app_rule(name) {
        res.push(r);
      } else {
        let lhs_pat = r.searcher.get_pattern_ast().unwrap();
        let lhs_head = lhs_pat.as_ref().iter().last().unwrap();
        if let ENodeOrVar::ENode(n) = lhs_head {
          if n.op == *name {
            res.push(r);
          }
        }
      }
    }
    res
  }

  /// If type_ is an arrow type, return a rewrite that allows converting partial applications into regular first-order applications,
  /// that is: ($ ... ($ name ?x0) ... ?xn) => (name ?x0 ... ?xn).
  fn partial_application<A>(name: &Symbol, type_: &Type) -> Option<Vec<Rewrite<SymbolLang, A>>>
    where
        A: Analysis<SymbolLang>
  {
    let (args, _) = type_.args_ret();
    if args.is_empty() {
      // This is not a function, so we can't partially apply it
      None
    } else {
      let wildcard = |i: usize| format!("?x{}", i).parse().unwrap();
      // RHS is a full first-order application of name to as many wildcards as there are arguments:
      let mut pre_rhs = name.to_string();
      let mut res: Vec<Rewrite<SymbolLang, A>> = vec![];
      for num in 0..args.len() {
        let rhs = format!(
          "({} {})",
          name,
          (0..=num)
              .map(wildcard)
              .collect::<Vec<String>>()
              .join(" ")
        );
        let mut lhs = format!("({} {} ?x{})", APPLY, pre_rhs, num);
        pre_rhs = rhs.clone();
        let rhs: Pat = rhs.parse().unwrap();
        let lhs: Pat = lhs.parse().unwrap();
        res.push(Rewrite::new(ParserState::get_part_app_rule(name, num), lhs.clone(), DestructiveApplier::new(lhs, rhs)).unwrap());
      }
      Some(res)
    }
  }

  /// This is done after parsing because that way the order we parse does not
  /// affect whether a goal has all definitions in scope.
  pub fn get_reductions_and_definitions(
    &self,
    goal: &RawGoal,
    local_rules: Vec<Rw>,
  ) -> (Vec<Rw>, Defns) {
    let lhs: Expr = goal.prop.eq.lhs.to_string().parse().unwrap();
    let rhs: Expr = goal.prop.eq.rhs.to_string().parse().unwrap();
    let mut roots = vec![lhs, rhs];
    if let Some(premise) = &goal.premise {
      let premise_lhs: Expr = premise.lhs.to_string().parse().unwrap();
      let premise_rhs: Expr = premise.rhs.to_string().parse().unwrap();
      roots.push(premise_lhs);
      roots.push(premise_rhs);
    }
    let (names, mut rules) = self.used_names_and_definitions(&roots);
    let filtered_defns = self
        .defns
        .iter()
        .filter_map(|(defn_name, defn_cases)| {
          if names.contains(&Symbol::from(defn_name)) {
            Some((defn_name.clone(), defn_cases.clone()))
          } else {
            None
          }
        })
        .collect();
    rules.extend(local_rules);
    (rules, filtered_defns)
  }
}

fn validate_identifier(identifier: &str) {
  // Important: we disallow the use of underscore in our identifiers so that
  // autogenerated names like for guards or variable splits will not conflict
  // with variable names.
  assert!(!identifier.contains('_'));
}

fn validate_datatype(datatype: &str) {
  validate_identifier(datatype);
  assert!(datatype.starts_with(char::is_uppercase));
}

fn validate_variable(variable: &str) {
  validate_identifier(variable);
  assert!(variable.starts_with(char::is_lowercase));
}

/// Parsing the file returns the whole parser state.
///
/// There are two advantages to this from the previous approach, which was returning a Vec<Goal>.
///
/// 1. We can now put propositions anywhere in the file and not worry about
///    definitions being missed since we parse all definitions before we create
///    goals for props.
/// 2. We can now avoid a lot of cloning that happens when we create new sub-goals because several
///    global items that we use (such as the global context) can now be passed as references.
///
/// This comes with the minor disadvantage of having to create goals in main.rs from the raw_goals,
/// but most of the work is done ahead of time.
pub fn parse_file(filename: &str) -> Result<ParserState, SexpError> {
  let mut state = ParserState::default();
  let sexpr = parser::parse_file(filename).unwrap();

  for decl in sexpr.list()? {
    let decl_kind = decl.list()?[0].string()?.as_str();
    match decl_kind {
      "data" => {
        // This is a datatype declaration: parse name, type variables, and constructor list:
        let name = decl.list()?[1].string()?;
        let mut cons_index = 2;
        // We'll allow no type variables to be given, in which case the second
        // argument must be the constructor list.
        let mangled_type_var_names = if decl.list()?.len() == 3 {
          vec![]
        } else {
          // The length should be 4.
          assert_eq!(decl.list()?.len(), 4);
          cons_index += 1;
          let type_vars = decl.list()?[2].list()?;
          type_vars
              .iter()
              .map(|x| {
                let var_name = x.string()?;
                validate_variable(var_name);
                // FIXME: We should really only mangle names in the emitted
                // explanations. If this is fixed, please change the config so
                // that it does not implicitly adjust the maximum split depth to
                // account for the additional underscore.
                Ok(mangle_name(var_name))
              })
              .collect::<Result<Vec<String>, SexpError>>()?
        };
        let cons = decl.list()?[cons_index].list()?;
        let mangled_cons_symbs = cons
            .iter()
            .map(|x| {
              let cons_name = x.string()?;
              validate_datatype(cons_name);
              Ok(Symbol::from(&mangle_name(cons_name)))
            })
            .collect::<Result<Vec<Symbol>, SexpError>>()?;
        validate_datatype(name);
        state.env.insert(
          Symbol::from(&mangle_name(name)),
          (mangled_type_var_names, mangled_cons_symbs),
        );
      }
      "::" => {
        // This is a type binding: parse name and type:
        let name = decl.list()?[1].string()?;
        // This could be either a function or a datatype.
        validate_identifier(name);
        let mangled_name = Symbol::from(&mangle_name(name));
        // Mangle each of the elements in the sexp.
        let mangled_type = Type::new(mangle_sexp(&decl.list()?[2]));
        if let Some(rw) = ParserState::partial_application(&mangled_name, &mangled_type) {
          state.rules.extend(rw)
        }
        // HACK: add the exact same rule to a vector of different types because
        // we can't store universally quantified types.
        if let Some(rw) = ParserState::partial_application(&mangled_name, &mangled_type) {
          state.cvec_rules.extend(rw);
        }
        state.context.insert(mangled_name, mangled_type);
      }
      "let" | "axiom" => {
        // This is a definition
        let name = decl.list()?[1].string()?;
        validate_variable(name);
        let mangled_name = mangle_name(name);
        // Extract the args and value
        let mangled_args = mangle_sexp(&decl.list()?[2]);
        let mangled_value = mangle_sexp(&decl.list()?[3]);
        // Add to the rewrites
        state.rules.push(make_rewrite_for_defn(
          &mangled_name,
          &mangled_args,
          &mangled_value,
          decl_kind == "axiom"
        ));
        // HACK: add the same rules to a list of rewrites for cvecs. This is
        // only done because we don't have a good way of storing rules that can
        // work as both Rw and CvecRw.
        if decl_kind != "axiom" {
          state.cvec_rules.push(make_rewrite_for_defn(&mangled_name, &mangled_args, &mangled_value, false));
        }

        // Add to the hashmap
        if let Some(cases) = state.defns.get_mut(&mangled_name) {
          cases.push((mangled_args, mangled_value));
        } else {
          state
              .defns
              .insert(mangled_name, vec![(mangled_args, mangled_value)]);
        }
      }
      "===" | "==>" => {
        // This is a goal: parse name, parameter names, parameter types;
        // if the goal is conditional, parse the lhs and rhs of the premise;
        // then parse the lhs and rhs of the goal;
        // finally, if there's more elements, parse a list of lemmas.
        //
        // Goal names are allowed to have underscores so we won't validate them. The
        // worst this can do is have a goal wrongly match a variable name, which should
        // hopefully never happen.
        let name = decl.list()?[1].string()?.to_string();
        let param_name_list = decl.list()?[2].list()?;
        let mangled_param_names = param_name_list
            .iter()
            .map(|x| {
              let var_name = x.string()?;
              validate_variable(var_name);
              Ok(Symbol::from(&mangle_name(var_name)))
            })
            .collect::<Result<Vec<Symbol>, SexpError>>()?;
        let param_type_list = decl.list()?[3].list()?;
        let mangled_param_types = param_type_list.iter().map(|x| Type::new(mangle_sexp(x)));
        let params = mangled_param_names
            .into_iter()
            .zip(mangled_param_types)
            .collect();

        let mut index = 4;
        let premise = if decl_kind == "==>" {
          let lhs: Sexp = mangle_sexp(&decl.list()?[index]);
          let rhs: Sexp = mangle_sexp(&decl.list()?[index + 1]);
          index += 2;
          Some(Equation::new(lhs, rhs))
        } else {
          None
        };

        let lhs: Sexp = mangle_sexp(&decl.list()?[index]);
        let rhs: Sexp = mangle_sexp(&decl.list()?[index + 1]);
        index += 2;
        let equation = Equation::new(lhs, rhs);

        let mut local_rules = vec![];
        let mut local_searchers = vec![];
        // If there's more to parse, these must be lemmas.
        if decl.list()?.len() > index {
          // Lemmas we are using to aid this proof
          for rule_sexp in decl.list()?[index].list()? {
            let lhs = mangle_sexp(&rule_sexp.list()?[1]);
            let rhs = mangle_sexp(&rule_sexp.list()?[2]);
            let searcher: Pattern<SymbolLang> = lhs.to_string().parse().unwrap();
            let applier: Pattern<SymbolLang> = rhs.to_string().parse().unwrap();
            // check if this is a bidirectional rewrite
            match rule_sexp.list()?[0].string()?.as_str() {
              "=>" => {
                let rw = Rewrite::new(
                  format!("hyp-lemma-{}", lhs),
                  searcher.clone(),
                  applier.clone(),
                )
                    .unwrap();
                local_rules.push(rw);
                // println!("adding rewrite rule: {} => {}", lhs, rhs);
              }
              "<=>" => {
                let rw = Rewrite::new(
                  format!("hyp-lemma-{}", lhs),
                  searcher.clone(),
                  applier.clone(),
                )
                    .unwrap();
                local_rules.push(rw);
                let rw = Rewrite::new(
                  format!("hyp-lemma-{}", rhs),
                  applier.clone(),
                  searcher.clone(),
                )
                    .unwrap();
                local_rules.push(rw);
              }
              "=?>" => {
                let s = ConditionalSearcher {
                  searcher,
                  condition: applier,
                };
                local_searchers.push(s);
              }
              _ => panic!("unknown rewrite rules: {}", rule_sexp),
            }
          }
        }
        let raw_goal = RawGoal {
          name,
          premise,
          prop: Prop::new_trusted(equation, params),
          local_rules,
          local_searchers,
        };
        state.raw_goals.push(raw_goal);
      }
      "//" => {
        // comment
      }
      _ => panic!("unknown declaration: {}", decl),
    }
  }
  Ok(state)
}
