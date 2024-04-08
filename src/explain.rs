use egg::*;
use itertools::{EitherOrBoth, Itertools};
use std::collections::BTreeMap;
use std::str::FromStr;
use symbolic_expressions::Sexp;

use crate::ast::{map_sexp, Context, Defns, Env, Type, find_instantiations};
use crate::config::CONFIG;
use crate::goal::{ETermEquation, ProofState, ProofTerm, IH_EQUALITY_PREFIX, ProofInfo, ProofLeaf, GlobalSearchState, Outcome};

/// Constants from (Liquid)Haskell
const EQUALS: &str = "=";
const UNIT: &str = "()";
const LH_EQUALS: &str = "==.";
const LH_USING_LEMMA: &str = "?";
const LH_FINISH_PROOF: &str = "***";
const LH_QED: &str = "QED";
const LH_PROOF: &str = "Proof";
const DATA: &str = "data";
const WHERE: &str = "where";
const MODULE: &str = "module";
const TAB_WIDTH: usize = 2;

const PRAGMA_GADT_SYNTAX: &str = "{-# LANGUAGE GADTSyntax #-}";
const PRAGMA_LH_REFLECTION: &str = "{-@ LIQUID \"--reflection\" @-}";
const PRAGMA_LH_PLE: &str = "{-@ LIQUID \"--ple\" @-}";
const IMPORT_LH_EQUATIONAL: &str = "import Language.Haskell.Liquid.Equational";

const LH_ANNOT_BEGIN: &str = "{-@";
const LH_ANNOT_END: &str = "@-}";
const LH_AUTOSIZE: &str = "autosize";
const LH_REFLECT: &str = "reflect";
const COMMENT: &str = "--";
// const HAS_TYPE: &str = "::";
// For adding nice spacing.
const JOINING_HAS_TYPE: &str = " :: ";
const JOINING_ARROW: &str = " -> ";

/// Custom constants
const UNREACHABLE: &str = "unreachable";
const UNREACHABLE_DEF: &str = "{-@ unreachable :: {v: a | false} -> b @-}\nunreachable :: a -> b\nunreachable x = error \"unreachable\"";

/// Constants from cyclegg
const APPLY: &str = "$";
const ARROW: &str = "->";
const FORWARD_ARROW: &str = "=>";
const BACKWARD_ARROW: &str = "<=";
const LEMMA_SEPARATOR: &str ="-";

/// A rewrite can be forward or backward, this specifies which direction it
/// goes.
enum RwDirection {
  Forward,
  Backward,
}

#[derive(Debug)]
struct LemmaInfo {
  name: String,
  // (param_name, param_type)
  params: Vec<(String, String)>,
  // lhs: Sexp,
  // rhs: Sexp,
}

/// Capitalizes each part of the goal name and removes underscores.
///
/// prop_50_no_cyclic -> Prop50NoCyclic
pub fn goal_name_to_filename(goal_name: &str) -> String {
  goal_name
    .split('_')
    .into_iter()
    .map(|chunk| {
      let mut chars_iter = chunk.chars();
      let mut new_string = String::new();
      if let Some(first_char) = chars_iter.next() {
        new_string.push(first_char.to_ascii_uppercase());
      }
      new_string.extend(chars_iter);
      new_string
    })
    .collect()
}

fn add_header_and_defns(
  filename: &str,
  goal: &str,
  eq: &ETermEquation,
  global_search_state: GlobalSearchState,
) -> String {
  let mut str_explanation = String::new();

  // Haskell pragmas
  str_explanation.push_str(PRAGMA_GADT_SYNTAX);
  str_explanation.push('\n');
  str_explanation.push_str(PRAGMA_LH_REFLECTION);
  str_explanation.push('\n');
  str_explanation.push_str(PRAGMA_LH_PLE);
  str_explanation.push('\n');
  str_explanation.push('\n');

  // Comment explaining the file
  str_explanation.push_str(COMMENT);
  str_explanation.push(' ');
  str_explanation.push_str(goal);
  str_explanation.push_str(": ");
  str_explanation.push_str(&eq.lhs.sexp.to_string());
  str_explanation.push_str(" = ");
  str_explanation.push_str(&eq.rhs.sexp.to_string());
  str_explanation.push('\n');

  // Haskell module declaration + imports
  str_explanation.push_str(MODULE);
  str_explanation.push(' ');
  str_explanation.push_str(filename);
  str_explanation.push(' ');
  str_explanation.push_str(WHERE);
  str_explanation.push('\n');
  str_explanation.push_str(IMPORT_LH_EQUATIONAL);
  str_explanation.push('\n');
  str_explanation.push('\n');

  // Haskell data declarations
  str_explanation.push_str(&add_data_definitions(global_search_state.env, global_search_state.context));

  // Add custom unreachable definition.
  str_explanation.push_str(UNREACHABLE_DEF);
  str_explanation.push('\n');
  str_explanation.push('\n');

  // Haskell definitions
  str_explanation.push_str(&add_definitions(global_search_state.defns, global_search_state.context));

  str_explanation

}

fn explain_body(
  goal: &str,
  proof_info: &mut ProofInfo,
  lhs: &Sexp,
  rhs: &Sexp,
  params: &[(Symbol, Type)],
  lemma_map: &mut BTreeMap<String, LemmaInfo>,
) -> String {
  let mut str_explanation = String::new();
  // (arg name, arg type), to be used in creating the type.
  let args: Vec<(String, String)> = params
    .iter()
    .map(|(var, ty)| (var.to_string(), convert_ty(&ty.repr)))
    .collect();
  // println!("{:?}", args);

  // Add the types and function definition stub
  str_explanation.push_str(&add_proof_types_and_stub(
    goal,
    &lhs,
    &rhs,
    &args,
  ));
  str_explanation.push('\n');

  // Finally, we can do the proof explanation

  let proof_exp = explain_proof(1, goal, proof_info, goal, lemma_map);
  str_explanation.push_str(&proof_exp);
  str_explanation.push('\n');

  str_explanation
}

pub fn explain_top(
  filename: &str,
  goal: &str,
  state: &mut ProofState,
  ih_lemma_number: usize,
  eq: &ETermEquation,
  params: &[Symbol],
  top_level_vars: &BTreeMap<Symbol, Type>,
  global_search_state: GlobalSearchState,
) -> String {
  let mut str_explanation = String::new();

  // Add the boilerplate and definitions
  str_explanation.push_str(&add_header_and_defns(filename, goal, eq, global_search_state));

  // (arg name, arg type), to be used in creating the type.
  let args: Vec<(Symbol, Type)> = params
    .iter()
    .map(|param| (param.clone(), top_level_vars[param].clone()))
    .collect();

  // Finally, we can do the proof explanation

  // Maps the rewrite rule string corresponding to a lemma to
  // (fresh_lemma_name, lemma_vars).
  // In the beginning add only the top-level inductive hypothesis.
  // TODO: still need to handle the inverted IH? (RHS => LHS)
  let mut lemma_map = BTreeMap::new();
  // let pat_lhs: Pattern<SymbolLang> = to_pattern(&eq.lhs.expr, |v| top_level_vars.contains_key(v));
  // let pat_rhs: Pattern<SymbolLang> = to_pattern(&eq.rhs.expr, |v| top_level_vars.contains_key(v));

  // let ih_lemma_name = format!("lemma_{}", ih_lemma_number);
  // let lemma_info = LemmaInfo {
  //   name: ih_lemma_name.clone(),
  //   params: params
  //     .iter()
  //     .map(|param| {
  //       let param_type = top_level_vars.get(param).unwrap();
  //       (param.to_string(), param_type.to_string())
  //     })
  //     .collect(),
  //   // lhs: symbolic_expressions::parser::parse_str(&pat_lhs.to_string()).unwrap(),
  //   // rhs: symbolic_expressions::parser::parse_str(&pat_rhs.to_string()).unwrap(),
  // };
  // lemma_map.insert(ih_lemma_name.clone(), lemma_info);

  for (lemma_number, lemma_proof) in state.lemma_proofs.iter() {
    if lemma_proof.outcome != Some(Outcome::Valid) {
      continue;
    }
    let lemma_info = LemmaInfo {
      name: format!("lemma_{}", lemma_number),
      params: lemma_proof.prop.params.iter().map(|(param, ty)| {
        (param.to_string(), convert_ty(&ty.repr))
      }).collect(),
    };
    lemma_map.insert(lemma_info.name.clone(), lemma_info);
  }

  // let body_exp = explain_body(goal, &mut state.proof_info, &eq.lhs.sexp, &eq.rhs.sexp, &args, &mut lemma_map);
  // str_explanation.push_str(&body_exp);
  // str_explanation.push('\n');

  for (lemma_number, lemma_proof) in state.lemma_proofs.iter_mut() {
    if lemma_proof.outcome != Some(Outcome::Valid) {
      continue;
    }
    // TODO: Perform reachability analysis from the main theorem to figure out
    // which proofs we actually need to emit.
    //
    // Right now this dumps all valid proofs.
    let lemma_name = format!("lemma_{}", lemma_number);
    let lemma_exp = explain_body(&lemma_name, &mut lemma_proof.lemma_proof, &lemma_proof.prop.eq.lhs, &lemma_proof.prop.eq.rhs, &lemma_proof.prop.params, &mut lemma_map);
    str_explanation.push_str(&lemma_exp);
    str_explanation.push('\n');
  }

  str_explanation
}

fn add_proof_types_and_stub(
  goal: &str,
  lhs: &Sexp,
  rhs: &Sexp,
  args: &Vec<(String, String)>,
) -> String {
  let mut str_explanation = String::new();

  // Technically we only need to fix uses of $ in the LHS/RHS, but
  // converting vars is fine too.
  let fixed_lhs = fix_value(lhs);
  let fixed_rhs = fix_value(rhs);

  // LH type
  str_explanation.push_str(LH_ANNOT_BEGIN);
  str_explanation.push(' ');
  str_explanation.push_str(goal);
  str_explanation.push_str(JOINING_HAS_TYPE);
  // Join with arrows each of the arguments
  let args_str = args
    .iter()
    .map(|(arg_name, arg_ty)| format!("{}: {}", arg_name, arg_ty))
    .collect::<Vec<String>>()
    .join(JOINING_ARROW);
  str_explanation.push_str(&args_str);
  // Refined type of the proof
  let proof_str = format!("{{ {} = {} }}", fixed_lhs, fixed_rhs);
  if !args.is_empty() {
    str_explanation.push_str(JOINING_ARROW);
  }
  str_explanation.push_str(&proof_str);
  str_explanation.push(' ');
  str_explanation.push_str(LH_ANNOT_END);
  str_explanation.push('\n');

  // Haskell type
  str_explanation.push_str(goal);
  str_explanation.push_str(JOINING_HAS_TYPE);
  // Same deal as with the LH type but now we just include the types
  let arg_tys_str = args
    .iter()
    .map(|(_, arg_ty)| arg_ty.to_string())
    .collect::<Vec<String>>()
    .join(JOINING_ARROW);
  str_explanation.push_str(&arg_tys_str);
  if !args.is_empty() {
    str_explanation.push_str(JOINING_ARROW);
  }
  // This time we just use the Proof type
  str_explanation.push_str(LH_PROOF);
  str_explanation.push('\n');

  // Haskell function definition
  str_explanation.push_str(goal);
  str_explanation.push(' ');
  // Now we include just the arguments and separate by spaces
  let arg_names_str = args
    .iter()
    .map(|(arg_name, _)| arg_name.to_string())
    .collect::<Vec<String>>()
    .join(" ");
  str_explanation.push_str(&arg_names_str);
  if !args.is_empty() {
    str_explanation.push(' ');
  }
  str_explanation.push_str(EQUALS);

  str_explanation
}

fn add_data_definitions(env: &Env, global_context: &Context) -> String {
  let mut data_defns_str = String::new();

  // The definition will look like
  //
  // {-@ autosize List @-}
  // data List a where
  //   Nil :: List a
  //   Cons :: a -> List a -> List a
  //
  // We will use GADTSyntax for convenience
  for (datatype, (type_vars, constrs)) in env.iter() {
    // {-@ autosize DATATYPE @-}
    data_defns_str.push_str(LH_ANNOT_BEGIN);
    data_defns_str.push(' ');
    data_defns_str.push_str(LH_AUTOSIZE);
    data_defns_str.push(' ');
    data_defns_str.push_str(&datatype.to_string());
    data_defns_str.push(' ');
    data_defns_str.push_str(LH_ANNOT_END);
    data_defns_str.push('\n');
    // data DATATYPE TYPE_VARS where
    data_defns_str.push_str(DATA);
    data_defns_str.push(' ');
    data_defns_str.push_str(&datatype.to_string());
    data_defns_str.push(' ');
    if !type_vars.is_empty() {
      data_defns_str.push_str(&type_vars.join(" "));
      data_defns_str.push(' ');
    }
    data_defns_str.push_str(WHERE);
    data_defns_str.push('\n');

    // CONSTRUCTOR :: CONSTRUCTOR_TYPE
    for constr in constrs {
      add_indentation(&mut data_defns_str, 1);
      data_defns_str.push_str(&constr.to_string());
      data_defns_str.push_str(JOINING_HAS_TYPE);
      data_defns_str.push_str(&convert_ty(&global_context[constr].repr));
      data_defns_str.push('\n');
    }
    data_defns_str.push('\n');
  }

  data_defns_str
}

fn add_definitions(defns: &Defns, global_context: &Context) -> String {
  let mut defns_str = String::new();

  // The definition will look like
  //
  // {-@ reflect listLen @-}
  // listLen :: List a -> Natural
  // listLen Nil = Z
  // listLen (Cons x xs) = S (listLen xs)
  for (name, cases) in defns.iter() {
    // {-@ reflect DEFN_NAME @-}
    defns_str.push_str(LH_ANNOT_BEGIN);
    defns_str.push(' ');
    defns_str.push_str(LH_REFLECT);
    defns_str.push(' ');
    defns_str.push_str(name);
    defns_str.push(' ');
    defns_str.push_str(LH_ANNOT_END);
    defns_str.push('\n');

    // DEFN_NAME :: DEFN_TYPE
    defns_str.push_str(name);
    defns_str.push_str(JOINING_HAS_TYPE);
    // Hacky conversion to symbol to extract from the global context
    defns_str.push_str(&convert_ty(
      &global_context[&Symbol::from_str(name).unwrap()].repr,
    ));
    defns_str.push('\n');

    for (args, value) in cases.iter() {
      defns_str.push_str(name);
      defns_str.push(' ');
      // This match is necessary to strip the parens
      match fix_vars(args) {
        Sexp::Empty => {}
        Sexp::String(arg) => {
          defns_str.push_str(&arg);
          defns_str.push(' ');
        }
        Sexp::List(args) => {
          defns_str.push_str(&args.iter().map(|arg| arg.to_string()).join(" "));
          defns_str.push(' ');
        }
      };
      defns_str.push_str(EQUALS);
      defns_str.push(' ');
      defns_str.push_str(&fix_value(value).to_string());
      defns_str.push('\n');
    }
    defns_str.push('\n');
  }

  defns_str
}

fn explain_proof(
  depth: usize,
  goal: &str,
  proof_info: &mut ProofInfo,
  top_goal_name: &str,
  lemma_map: &mut BTreeMap<String, LemmaInfo>,
) -> String {
  match proof_info.solved_goal_proofs.get_mut(goal) {
    Some(proof_leaf) => {
      // We have a proper explanation
      return match proof_leaf {
        ProofLeaf::Contradiction(expl) => {
            let mut str_explanation = String::new();
            add_indentation(&mut str_explanation, depth);
            str_explanation.push_str(UNREACHABLE);
            // Open paren (we will pass the proof to unreachable to prove by contradiction)
            str_explanation.push(' ');
            str_explanation.push('(');
            str_explanation.push('\n');
            let proof = explain_goal(
              // Increase depth of the proof because we want `unreachable` to
              // be at a lower depth.
              depth + 1,
              expl,
              top_goal_name,
              lemma_map,
            );
            // Add the proof itself
            str_explanation.push_str(&proof);
            // Close the paren
            add_indentation(&mut str_explanation, depth);
            str_explanation.push(')');
            str_explanation.push('\n');
            str_explanation.push('\n');
            str_explanation
        }
        ProofLeaf::Refl(expl) => {
          // Just use this proof on its own.
          explain_goal(depth, expl, top_goal_name, lemma_map)
        }
        // It doesn't matter what we do here
        ProofLeaf::Todo => todo!("Proof not implemented for proof of {}", goal),
      };
    }
    None => {}// unreachable!("Missing proof explanation for {}", goal),
  }
  // If it's not in the proof tree, it must be a leaf.
  if !proof_info.proof.contains_key(goal) {
  }
  // Need to clone to avoid borrowing... unfortunately this is all because we need
  // a mutable reference to the explanations for some annoying reason
  let proof_term = proof_info.proof.get(goal).expect(&format!("Missing proof term: {}", goal)).clone();
  let mut str_explanation = String::new();
  let mut proof_depth = depth;
  let mut case_depth = depth + 1;
  if let ProofTerm::ITESplit(var, condition, _) = &proof_term {
    add_indentation(&mut str_explanation, proof_depth);
    str_explanation.push_str(&format!("let {} = {} in", var, condition));
    str_explanation.push('\n');
    case_depth += 1;
    proof_depth += 1;
  };
  match &proof_term {
    ProofTerm::CaseSplit(var, cases) | ProofTerm::ITESplit(var, _, cases) => {
      add_indentation(&mut str_explanation, proof_depth);
      str_explanation.push_str(&format!("case {} of", var));
      str_explanation.push('\n');
      for (case_constr, case_goal) in cases {
        add_indentation(&mut str_explanation, case_depth);
        str_explanation.push_str(&format!("{} ->", case_constr));
        str_explanation.push('\n');
        // Recursively explain the proof
        str_explanation.push_str(&explain_proof(
          case_depth + 1,
          case_goal,
          proof_info,
          top_goal_name,
          lemma_map,
        ));
      }
      str_explanation
    }
  }
}

fn explain_goal(
  depth: usize,
  explanation: &mut Explanation<SymbolLang>,
  top_goal_name: &str,
  lemma_map: &mut BTreeMap<String, LemmaInfo>,
) -> String {
  let mut str_explanation: String = String::new();
  let flat_terms = explanation.make_flat_explanation();
  let next_flat_term_iter = flat_terms.iter().skip(1);
  let flat_term_and_next = flat_terms.iter().zip_longest(next_flat_term_iter);
  // Render each of the terms in the explanation.
  // The first term is the equality of the previous term and itself (rendered for CONFIG.verbose_proofs).
  // The second term is the lemma, if used (rendered always).
  // The third time is the comment string explaining the equality (rendered for CONFIG.verbose_proofs).
  let explanation_lines: Vec<(String, Option<String>, Option<String>)> = flat_term_and_next
    .map(|flat_term_and_next| {
      let (flat_term, next_term_opt) = match flat_term_and_next {
        EitherOrBoth::Both(flat_term, next_term) => (flat_term, Some(next_term)),
        EitherOrBoth::Left(flat_term) => (flat_term, None),
        EitherOrBoth::Right(_) => {
          unreachable!("next_flat_term_iter somehow is longer than flat_term_iter")
        }
      };
      let mut item = String::new();
      let comment = extract_rule_name(flat_term).map(|(rule_name, rw_dir)| {
        let mut comment_str = String::new();
        comment_str.push_str(COMMENT);
        comment_str.push(' ');
        if let RwDirection::Backward = rw_dir {
          comment_str.push_str(BACKWARD_ARROW);
          comment_str.push(' ');
        }
        comment_str.push_str(&rule_name);
        if let RwDirection::Forward = rw_dir {
          comment_str.push(' ');
          comment_str.push_str(FORWARD_ARROW);
        }
        comment_str
      });
      // These aren't necessary with PLE and generate spurious constraints so we omit them.
      if CONFIG.verbose_proofs {
        // First we convert to a sexp, then fix its operators. fix_value also
        // fixes variables which is unnecessary but won't cause harm.
        item.push_str(&fix_value(&flat_term_to_sexp(flat_term)).to_string());
      }
      let lemma = next_term_opt.and_then(|next_term| {
        // We don't care about the direction of the rewrite because lemmas
        // and the IH prove equalities which are bidirectional.
        extract_rule_name(next_term).and_then(|(rule_name, rw_dir)| {
          if rule_name.starts_with(IH_EQUALITY_PREFIX) {
            let args = extract_ih_arguments(&rule_name);
            Some(add_lemma_invocation(top_goal_name, args.iter().cloned()))
          } else if rule_name.contains(LEMMA_SEPARATOR) {
            // println!("extracting lemma from {} {} {}", rule_name, flat_term, next_term);
            rule_name.split_once(LEMMA_SEPARATOR).and_then(|(lemma_name, lemma_rest)|{
              if lemma_map.contains_key(lemma_name) {
                Some(extract_lemma_invocation(
                  lemma_name,
                  lemma_rest,
                  &rw_dir,
                  flat_term,
                  next_term,
                  lemma_map,
                ))
              } else {
                None
              }
            })
          } else {
            None
          }
        })
      });
      (item, lemma, comment)
    })
    .collect();
  // if CONFIG.verbose_proofs {
  //   // Construct a joiner that intersperses newlines and properly spaced
  //   // LH_EQUALS operators.
  //   let mut joiner = "\n".to_string();
  //   add_indentation(&mut joiner, depth);
  //   joiner.push_str(LH_EQUALS);
  //   joiner.push('\n');

  //   // Individual terms joined by LH_EQUALS.
  //   str_explanation.push_str(&explanation_lines.join(&joiner));
  //   str_explanation.push('\n');
  //   add_indentation(&mut str_explanation, depth);
  //   // This is just required by LH to finish it.
  //   str_explanation.push_str(AND_THEN);
  //   str_explanation.push('\n');
  //   add_indentation(&mut str_explanation, depth);
  //   str_explanation.push_str(QED);
  //   str_explanation.push('\n');
  // } else {

  // It is a bit redundant to have two ways of emitting lines, but
  // the logic is simpler to debug.
  if CONFIG.verbose_proofs {
    for (line, (item, lemma, comment)) in explanation_lines.iter().enumerate() {
      add_comment(&mut str_explanation, comment.as_ref(), depth);
      add_indentation(&mut str_explanation, depth);
      if line > 0 {
        str_explanation.push_str(LH_EQUALS);
        str_explanation.push(' ');
      }
      str_explanation.push_str(item);
      str_explanation.push('\n');
      if let Some(lemma_str) = lemma {
        add_indentation(&mut str_explanation, depth);
        str_explanation.push_str(LH_USING_LEMMA);
        str_explanation.push(' ');
        str_explanation.push_str(lemma_str);
        str_explanation.push('\n');
      }
    }
    // There will always be at least one line of explanation, so we don't need
    // to handle the empty case.
    add_indentation(&mut str_explanation, depth);
    str_explanation.push_str(LH_FINISH_PROOF);
    str_explanation.push('\n');
    add_indentation(&mut str_explanation, depth);
    str_explanation.push_str(LH_QED);
    str_explanation.push('\n');
  } else {
    let mut is_first_lemma = true;
    for (_, lemma, comment) in explanation_lines.iter() {
      add_comment(&mut str_explanation, comment.as_ref(), depth);
      if let Some(lemma_str) = lemma {
        add_indentation(&mut str_explanation, depth);
        if !is_first_lemma {
          str_explanation.push_str(LH_USING_LEMMA);
          str_explanation.push(' ');
        } else {
          is_first_lemma = false;
        }
        str_explanation.push_str(lemma_str);
        str_explanation.push('\n');
      }
    }
    // It might be that there are no lines in this proof
    if is_first_lemma {
      add_indentation(&mut str_explanation, depth);
      str_explanation.push_str(UNIT);
      str_explanation.push('\n');
    }
  }

  str_explanation
}

fn add_comment(str_explanation: &mut String, comment: Option<&String>, depth: usize) {
  if CONFIG.proof_comments {
    if let Some(comment_str) = comment {
      add_indentation(str_explanation, depth);
      str_explanation.push_str(comment_str);
      str_explanation.push('\n');
    }
  }
}

fn add_lemma_invocation<L>(lemma_name: &str, lemma_arguments: L) -> String
where
  L: Iterator<Item = String>,
{
  let mut lemma_str = String::new();
  lemma_str.push_str(lemma_name);
  for arg in lemma_arguments {
    lemma_str.push_str(" (");
    lemma_str.push_str(&arg);
    lemma_str.push(')');
  }
  lemma_str
}

fn extract_lemma_invocation(
  // The name of the lemma
  lemma_name: &str,
  // The part after the LEMMA_SEPARATOR, this is two sexps split by =
  lemma_rest: &str,
  rw_dir: &RwDirection,
  curr_term: &FlatTerm<SymbolLang>,
  next_term: &FlatTerm<SymbolLang>,
  lemma_map: &mut BTreeMap<String, LemmaInfo>,
) -> String {
  let mut rewrite_pos: Vec<i32> = vec![];
  let trace = find_rewritten_term(&mut rewrite_pos, next_term).unwrap();
  let (rewritten_to, rewritten_from) = match rw_dir {
    RwDirection::Forward => (
      get_flat_term_from_trace(&trace, next_term),
      get_flat_term_from_trace(&trace, curr_term),
    ),
    RwDirection::Backward => (
      get_flat_term_from_trace(&trace, curr_term),
      get_flat_term_from_trace(&trace, next_term),
    ),
  };
  // println!("lemma {} and rest: {}", lemma_name, lemma_rest);
  let lemma_info = lemma_map.get(lemma_name).unwrap();
  let lemma: Vec<&str> = lemma_rest
    .split(EQUALS)
    .collect();

  let lhs_sexp = symbolic_expressions::parser::parse_str(lemma[0]).unwrap();
  let rhs_sexp = symbolic_expressions::parser::parse_str(lemma[1]).unwrap();
  // println!("lhs: {:?}, rhs: {:?}, params: {:?}", lhs_sexp, rhs_sexp, lemma_info.params);
  // println!("lhs_term: {:?}, rhs_term: {:?}", &flat_term_to_sexp(&rewritten_from), &flat_term_to_sexp(&rewritten_to));
  // HACK: It's a variable if it is a lemma parameter without the ?
  //
  // We actually know the LHS and RHS of the lemma, but we don't know what order
  // they were applied in. We should record which direction the rewrite was in
  // so we don't have to do some hacky unification on the rewrite string itself.
  let is_var = |s: &str| lemma_info.params.iter().any(|(param, _param_ty)| param == s.trim_start_matches("?"));
  let mut lhsmap = find_instantiations(&lhs_sexp, &flat_term_to_sexp(&rewritten_from), is_var).unwrap();
  let rhsmap = find_instantiations(&rhs_sexp, &flat_term_to_sexp(&rewritten_to), is_var).unwrap();
  // let mut lhsmap = map_variables(lemma[0], &flat_term_to_sexp(&rewritten_from).to_string());
  // let rhsmap = map_variables(lemma[1], &flat_term_to_sexp(&rewritten_to).to_string());

  // println!("lhs: {}, rhs: {}", lemma[0], lemma[1]);
  // println!("lhs_term: {}, rhs_term: {}", &flat_term_to_sexp(&rewritten_from).to_string(), &flat_term_to_sexp(&rewritten_to).to_string());
  // println!("lhs_map: {:?}, rhs_map: {:?}", lhsmap, rhsmap);

  let rhsmap_valid = rhsmap
    .iter()
    .all(|(key, value)| lhsmap.get(key) == Some(value));
  let lhsmap_valid = lhsmap
    .iter()
    .all(|(key, value)| rhsmap.get(key) == Some(value));
  assert!(rhsmap_valid || lhsmap_valid);

  // take the union of both maps
  lhsmap.extend(rhsmap);

  // println!("lemma {}", lemma_name);
  // println!("params {:?}", lemma_info.params);
  // Map lhsmap over the lemma's params.
  // We need to do this because the lemma could be the top level IH,
  // whose parameters are not in the same order as they are stored in lhsmap.
  add_lemma_invocation(
    &lemma_info.name,
    lemma_info
      .params
      .iter()
      .map(|(param, _)|{
        // HACK: putting ? in front to extract the right pattern
        lhsmap.get(&format!("?{}", param)).unwrap().to_string()
      }),
  )
}

fn add_indentation(s: &mut String, depth: usize) {
  s.push_str(&" ".repeat(depth * TAB_WIDTH));
}

fn flat_term_to_sexp(flat_term: &FlatTerm<SymbolLang>) -> Sexp {
  let op_sexp = Sexp::String(flat_term.node.op.to_string());
  // This is a leaf
  if flat_term.node.children.is_empty() {
    op_sexp
  // This is an interior node
  } else {
    let mut child_sexps: Vec<Sexp> = vec![op_sexp];
    for child in &flat_term.children {
      child_sexps.push(flat_term_to_sexp(child));
    }
    Sexp::List(child_sexps)
  }
}

fn extract_rule_name(flat_term: &FlatTerm<SymbolLang>) -> Option<(String, RwDirection)> {
  let forward = flat_term
    .forward_rule
    .map(|rule| (rule.to_string(), RwDirection::Forward));
  let backward = flat_term
    .backward_rule
    .map(|rule| (rule.to_string(), RwDirection::Backward));
  // Find the first Some
  let rule_from_child = flat_term
    .children
    .iter()
    .map(extract_rule_name)
    .find(Option::is_some)
    .flatten();
  forward.or(backward).or(rule_from_child)
}

fn convert_op(op_str: &str) -> Sexp {
  // Special case for converting `$`, which is used internally in cyclegg for
  // partial application, to the corresponding prefix operator `($)` in
  // Haskell.
  if op_str == APPLY {
    // This is a really ugly hack to wrap `$` in parens.
    Sexp::List(vec![Sexp::String(op_str.to_string())])
  } else {
    Sexp::String(op_str.to_string())
  }
}

/// Basically the same as ty.repr.to_string() but we make arrows infix
fn convert_ty(ty: &Sexp) -> String {
  // println!("ty: {:?}, fixed: {:?}", ty, fix_arrows(&fix_vars(ty)));
  fix_arrows(&fix_vars(ty))
}

fn fix_vars(sexp: &Sexp) -> Sexp {
  match sexp {
    Sexp::Empty => Sexp::Empty,
    Sexp::String(s) => {
      let mut new_s = String::new();
      let mut s_chars = s.chars();
      if let Some(c) = s_chars.next() {
        match c {
          // Skip a question mark prefix on a var
          '?' => {}
          _ => new_s.push(c),
        };
      }
      // Add the rest
      new_s.push_str(s_chars.as_str());
      Sexp::String(new_s)
    }
    Sexp::List(children) => Sexp::List(children.iter().map(fix_vars).collect()),
  }
}

fn fix_value(value: &Sexp) -> Sexp {
  map_sexp(convert_op, &fix_vars(value))
}

fn fix_arrows(ty: &Sexp) -> String {
  match ty {
    Sexp::String(str) => str.clone(),
    Sexp::List(children) => {
      // Handle the arrow case, making it infix
      if children.len() == 3 {
        if let Sexp::String(op) = &children[0] {
          if *op == ARROW {
            if let Sexp::List(args) = children[1].clone() {
              let mut arg_tys: Vec<String> = args.iter().map(fix_arrows).collect();
              let return_ty = fix_arrows(&children[2]);
              arg_tys.push(return_ty);
              return format!("({})", arg_tys.join(JOINING_ARROW));
            } else {
              return format!(
                "({} {} {})",
                fix_arrows(&children[1]),
                ARROW,
                fix_arrows(&children[2])
              );
            }
          }
        }
      }
      let converted: String = children
        .iter()
        .map(fix_arrows)
        .collect::<Vec<String>>()
        .join(" ");
      format!("({})", converted)
    }
    Sexp::Empty => String::new(),
  }
}

fn extract_ih_arguments(rule_name: &str) -> Vec<String> {
  rule_name
    .strip_prefix(IH_EQUALITY_PREFIX)
    .unwrap()
    .split(',')
    .into_iter()
    .map(|pair| {
      // println!("{}", pair);
      let args: Vec<&str> = pair.split('=').into_iter().collect();
      // This should just be x=(Constructor c1 c2 c3)
      assert_eq!(args.len(), 2);
      args[1].to_string()
    })
    .collect()
}
/// Given a FlatTerm, locates the subterm that was rewritten by looking for a backward / forward rule
/// and returns a trace of indices to that term.
fn find_rewritten_term(trace: &mut Vec<i32>, flat_term: &FlatTerm<SymbolLang>) -> Option<Vec<i32>> {
  if flat_term.backward_rule.is_some() || flat_term.forward_rule.is_some() {
    Some(trace.to_vec())
  } else {
    for (i, child) in flat_term.children.iter().enumerate() {
      if child.has_rewrite_backward() || child.has_rewrite_forward() {
        trace.push(i as i32);
        return find_rewritten_term(trace, child);
      }
    }
    None
  }
}

fn get_flat_term_from_trace(
  trace: &Vec<i32>,
  flat_term: &FlatTerm<SymbolLang>,
) -> FlatTerm<SymbolLang> {
  let mut current_flat_term = flat_term;
  for i in trace {
    current_flat_term = &current_flat_term.children[*i as usize];
  }
  current_flat_term.clone()
}
