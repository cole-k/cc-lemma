use ast::{Equation, Prop};
use colored::Colorize;
use std::fs::*;
use std::io::{Result, Write};
use std::time::{Duration, Instant};

pub mod ast;
pub mod config;
pub mod analysis;
pub mod egraph;
pub mod explain;
pub mod goal;
pub mod parser;
pub mod utils;
mod goal_graph;

use config::{ARGS, CONFIG};
use explain::explain_top;
use goal::*;
use parser::*;

use crate::{explain::goal_name_to_filename, goal::Goal};

fn main() -> Result<()> {
  simple_logger::init_with_level(CONFIG.log_level).unwrap();

  let parser_state = parse_file(&ARGS.filename).unwrap();

  let mut result_file = if CONFIG.save_results {
    Some(File::create(CONFIG.output_directory.join("results.csv"))?)
  } else {
    None
  };
  result_file.iter_mut().for_each(|file| {
    file.write(format!("name,result,time,num_lemmas,num_lemmas_attempted,num_lemmas_proven,result_cyclic,time_cyclic,num_lemmas_cyclic,num_attempted_lemmas_cyclic,num_proven_lemmas_cyclic\n").as_bytes()).expect("failed to write header");
  });
  let mut num_goals_attempted = 0;
  let mut num_differing_goals = 0;
  let mut cyclic_num_valid = 0;
  let mut non_cyclic_num_valid = 0;
  for raw_goal in parser_state.raw_goals.iter() {
    let (reductions, defns) =
      parser_state.get_reductions_and_definitions(raw_goal, raw_goal.local_rules.clone());
    if let Some(prop_name) = &CONFIG.prop {
      if &raw_goal.name != prop_name {
        continue;
      }
    }
    let global_search_state = GlobalSearchState::new(&parser_state.env, &parser_state.context, &reductions, &parser_state.cvec_rules, &defns, &raw_goal.local_searchers);

    let mut goal = Goal::top(
      &raw_goal.name,
      &raw_goal.prop,
      &raw_goal.premise,
      global_search_state,
    );
    num_goals_attempted += 1;
    println!(
      "{} {}: {}",
      "Proving begin".blue(),
      raw_goal.name.blue(),
      goal
    );

    let (result, duration, num_lemmas, num_attempted_lemmas, num_proven_lemmas) = if ARGS.do_uncyclic() {
      prove_goal(goal.clone(), raw_goal.prop.clone(), raw_goal.premise.clone(), global_search_state, false)?
    } else {
      (Outcome::Unknown, Duration::from_secs(0), 0, 0, 0)
    };
    let (result_cyclic, duration_cyclic, num_lemmas_cyclic, num_attempted_lemmas_cyclic, num_proven_lemmas_cyclic) = if ARGS.do_cyclic() {
      goal.name = format!("{}_cyclic", goal.name);
      prove_goal(goal.clone(), raw_goal.prop.clone(), raw_goal.premise.clone(), global_search_state, true)?
    } else {
      (Outcome::Unknown, Duration::from_secs(0), 0, 0, 0)
    };

    if CONFIG.verbose {
      println!(
        "{} {}: {}",
        "Proving end".blue(),
        raw_goal.name.blue(),
        goal
      );
    }

    if ARGS.do_uncyclic() {
      println!("(uncyclic) Theorized {} lemmas, fully attempted {} lemmas, proved {} lemmas", num_lemmas, num_attempted_lemmas, num_proven_lemmas);
    }
    if ARGS.do_cyclic() {
      println!("(cyclic) Theorized {} lemmas, fully attempted {} lemmas, proved {} lemmas", num_lemmas_cyclic, num_attempted_lemmas_cyclic, num_proven_lemmas_cyclic);
    }

    if ARGS.do_cyclic() && ARGS.do_uncyclic() {
      println!(
        "{} uncyclic: {} ({:.2} ms) cyclic: {} ({:.2} ms)",
        raw_goal.name.blue(),
        result,
        duration.as_millis(),
        result_cyclic,
        duration_cyclic.as_millis()
      );
      if result_cyclic != result {
        num_differing_goals += 1;
        println!("{}", "Differing results".red());
      }
    } else if ARGS.do_cyclic() {
      println!(
        "{} cyclic: {} ({:.2} ms)",
        raw_goal.name.blue(),
        result_cyclic,
        duration_cyclic.as_millis()
      );
    } else if ARGS.do_uncyclic() {
      println!(
        "{} uncyclic: {} ({:.2} ms)",
        raw_goal.name.blue(),
        result,
        duration.as_millis()
      );
    }
    if let Outcome::Valid = result_cyclic {
      cyclic_num_valid += 1;
    }
    if let Outcome::Valid = result {
      non_cyclic_num_valid += 1;
    }
    if let Some(ref mut file) = result_file {
      let line = format!(
        "{},{:?},{},{},{},{},{:?},{},{},{},{}\n",
        raw_goal.name,
        result,
        // Convert to ms
        1000. * duration.as_secs_f32(),
        num_lemmas,
        num_attempted_lemmas,
        num_proven_lemmas,
        result_cyclic,
        // Convert to ms
        1000. * duration_cyclic.as_secs_f32(),
        num_lemmas_cyclic,
        num_attempted_lemmas_cyclic,
        num_proven_lemmas_cyclic,
      );
      file.write_all(line.as_bytes())?;
    }
  }
  println!("Attempted {} goals:", num_goals_attempted);
  if ARGS.do_cyclic() && ARGS.do_uncyclic() {
    println!("  {} differing results", num_differing_goals);
  }
  if ARGS.do_uncyclic() {
    println!("  {} solved (no cyclic)", non_cyclic_num_valid);
  }
  if ARGS.do_cyclic() {
    println!("  {} solved (cyclic)", cyclic_num_valid);
  }
  Ok(())
}

/// Prove a goal using either cyclic or uncyclic mode;
/// record the duration and emit the proof.
fn prove_goal<'a>(goal: Goal<'a>, goal_prop: Prop, goal_premise: Option<Equation>, global_search_state: GlobalSearchState<'a>, cyclic: bool) -> Result<(Outcome, Duration, usize, usize, usize)> {
  CONFIG.set_cyclic(cyclic);
  let start_time = Instant::now();
  if CONFIG.verbose {
    println!("{}", "Reductions".cyan());
    for rule in global_search_state.reductions {
      println!("  {:?}", rule);
    }
  }
  let (result, mut proof_state) = goal::prove_top(goal_prop, goal_premise, global_search_state);
  let mut num_lemmas = 0;
  let mut num_proven_lemmas = 0;
  let mut num_lemmas_not_attempted = 0;
  for (lemma_number, lemma_proof_state) in proof_state.lemma_proofs.iter() {
    if lemma_number == &0 {
      continue;
    }
    num_lemmas += 1;
    if lemma_proof_state.outcome == Some(Outcome::Valid) {
      num_proven_lemmas += 1;
    }
    if lemma_proof_state.outcome == None {
      num_lemmas_not_attempted += 1;
    }
  }
  let duration = start_time.elapsed();
  if CONFIG.emit_proofs {
    if let Outcome::Valid = result {
      let filename = goal_name_to_filename(&goal.name);
      let explanation = explain_top(
        &filename,
        &goal.name,
        &mut proof_state,
        // FIXME: remove magic number
        // (the first lemma - i.e. the main theorem - should be lemma 0)
        0,
        &goal.eq,
        &goal.top_level_params,
        &goal.local_context,
        goal.global_search_state,
      );
      let mut file = File::create(CONFIG.proofs_directory.join(format!("{}.hs", filename)))?;
      file.write_all(explanation.as_bytes())?;
    }
  }
  // if result == Outcome::Timeout || result == Outcome::Unknown {
  //   for (i, chain) in proof_state.lemmas_state.possible_lemmas.chains.iter().enumerate() {
  //     println!("Chain {}", i);
  //     for elem in chain.chain.iter() {
  //       println!("Possible lemma: {} === {}", elem.eq.lhs, elem.eq.rhs);
  //     }
  //   }
  // }
  // for (i, chain) in proof_state.lemmas_state.proven_lemmas.chains.iter().enumerate() {
  //   println!("Chain {}", i);
  //   for elem in chain.chain.iter() {
  //     println!("Proven lemma: {} === {}", elem.eq.lhs, elem.eq.rhs);
  //   }
  // }

  Ok((result, duration, num_lemmas, num_lemmas - num_lemmas_not_attempted, num_proven_lemmas))
}
