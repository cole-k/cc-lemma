use std::{fs::create_dir_all, path::PathBuf, sync::Mutex};

use clap::Parser;
use lazy_static::lazy_static;
use log::Level;

#[derive(Parser)]
pub struct Args {
  pub filename: String,
  #[clap(short = 'd', long = "max-depth", default_value = "1000")]
  pub max_split_depth: usize,
  #[clap(short = 's', long = "single-rhs")]
  pub single_rhs: bool,
  #[clap(short = 'i', long = "irreducible")]
  pub irreducible_only: bool,
  #[clap(short = 'c', long = "no-cond-split")]
  pub no_cond_split: bool,
  /// Mode
  #[clap(long = "cyclic")]
  pub cyclic: bool,
  #[clap(long = "no-uncyclic")]
  pub no_uncyclic: bool,
  /// Timeout
  #[clap(short = 't', long = "timeout", default_value = "0")]
  pub timeout: u64,
  /// Logging
  #[clap(short = 'l', long = "log", default_value = "ERROR")]
  pub log_level: String,
  #[clap(short = 'g', long = "save-graphs")]
  pub save_graphs: bool,
  #[clap(short = 'r', long = "save-results")]
  pub save_results: bool,
  /// Emit proofs under the proofs directory in the output directory
  #[clap(short = 'p', long = "emit-proofs")]
  pub emit_proofs: bool,
  #[clap(short = 'v', long = "verbose")]
  pub verbose: bool,
  #[clap(long = "verbose-proofs")]
  pub verbose_proofs: bool,
  /// Where to save outputs other than proofs
  #[clap(short = 'o', long = "output-directory", default_value = "target")]
  pub output_directory: PathBuf,
  /// Where to save proofs
  #[clap(long = "proofs-directory", default_value = "target/proofs")]
  pub proofs_directory: PathBuf,
  /// Only relevant when -p or --emit-proofs is passed.
  ///
  /// By default, when emitting proofs we prepend Cyclegg_ to data types and
  /// cyclegg_ to functions and variables so that Haskell doesn't complain about
  /// name clashes.
  ///
  /// This disables the name mangling for ease of debugging.
  #[clap(long = "unmangled-names")]
  pub unmangled_names: bool,
  /// Do not emit comments in proofs
  #[clap(long = "no-proof-comments")]
  pub no_proof_comments: bool,
  /// Only prove the proposition with this name
  #[clap(long = "prop")]
  pub prop: Option<String>,
  #[clap(long = "no-blocking-analysis")]
  pub no_blocking_analysis: bool,
  /// Number of terms to put into the cvecs used to propose equalities between
  /// e-classes.
  #[clap(long = "cvec-size", default_value = "30")]
  pub cvec_size: usize,
  /// Maximum depth for the random terms we generate for the cvecs.
  #[clap(long = "cvec-term-max-depth", default_value = "4")]
  pub cvec_term_max_depth: usize,
  /// Number of times we try to make a new distinct term when generating
  /// the random terms for a type that are used for cvecs of that type.
  ///
  /// If we try this many times and don't find a distinct value, we add
  /// it to the list anyway.
  #[clap(long = "cvec-num-rolls", default_value = "10")]
  pub cvec_num_rolls: usize,
  /// The number of random terms we generate for each type. We select randomly
  /// from these each time we generate a cvec for a variable.
  #[clap(long = "cvec-num-random-terms-per-type", default_value = "30")]
  pub cvec_num_random_terms_per_type: usize,
  /// We won't consider lemmas with a total AST size (sum of LHS and RHS AST
  /// size) greater than this. If 0, we will allow any size.
  #[clap(long = "max-lemma-size", default_value = "0")]
  pub max_lemma_size: usize,
  #[clap(long = "no-grounding")]
  pub no_grounding: bool,
  /// Do not apply reductions destructively.
  #[clap(long = "no-destructive-rewrites")]
  pub no_destructive_rewrites: bool,
  /// Number of times we will try to recursively prove props
  ///
  /// Depth 2 means that we will try to prove lemmas of lemmas, but not anything
  /// more.
  #[clap(long = "proof-depth", default_value = "2")]
  pub proof_depth: usize,
  /// Does not generalize goals based on our blocking expression analysis.
  ///
  /// Note that even if this is turned off, we will still generalize lemmmas
  /// used in the cvec analysis. Pass the flag --no-cc-lemma-generalization for
  /// to disable this.
  #[clap(long = "no-generalization")]
  pub no_generalization: bool,
  /// Do not propose lemmas based on the cvec analysis. Pass --no-cc-lemmas-generalization
  /// to just disable generalization for these lemmas.
  #[clap(long = "no-cc-lemmas")]
  pub no_cc_lemmas: bool,
  /// Do not generalize cc lemmas after theorizing them.
  #[clap(long = "no-cc-lemmas-generalization")]
  pub no_cc_lemmas_generalization: bool,
  /// Our termination check will skip variables that are not blocking. Use this
  /// flag to disable skipping this check.
  #[clap(long = "no-better-termination")]
  pub no_better_termination: bool,

  #[clap(long = "only-generalize")]
  pub only_generalize: bool,

  #[clap(long = "exclude-bid-reachable")]
  pub exclude_bid_reachable: bool,

  #[clap(long = "saturate-only-parent")]
  pub saturate_only_parent: bool,

  #[clap(long = "reduce-proven-lemmas")]
  pub reduce_proven_lemmas: bool
}

impl Args {
  pub fn do_cyclic(&self) -> bool {
    self.cyclic
  }

  pub fn do_uncyclic(&self) -> bool {
    !self.no_uncyclic
  }
}

pub struct Config {
  pub prop: Option<String>,
  // This is a mutex because we want to be able to change it
  cyclic_mode: Mutex<bool>,
  // proof search parameters
  pub max_split_depth: usize,
  pub split_conditionals: bool,
  pub single_rhs: bool,
  pub irreducible_only: bool,
  // timeout
  pub timeout: Option<u64>,
  // logging
  pub log_level: Level,
  pub save_graphs: bool,
  pub save_results: bool,
  pub emit_proofs: bool,
  pub verbose: bool,
  pub verbose_proofs: bool,
  pub output_directory: PathBuf,
  pub proofs_directory: PathBuf,
  pub mangle_names: bool,
  pub proof_comments: bool,
  pub blocking_vars_analysis: bool,
  pub max_lemma_size: usize,
  // This could maybe be its own struct?
  pub cvec_size: usize,
  pub cvec_term_max_depth: usize,
  pub cvec_num_rolls: usize,
  pub cvec_num_random_terms_per_type: usize,
  pub add_grounding: bool,
  pub destructive_rewrites: bool,
  pub proof_depth: usize,
  pub generalization: bool,
  pub cc_lemmas: bool,
  pub cc_lemmas_generalization: bool,
  pub better_termination: bool,
  pub only_generalize: bool,
  pub extraction_loop_limit: usize,
  pub extraction_allow_end_loop: bool,
  pub extraction_max_depth: usize,
  pub extraction_max_size: usize,
  pub extraction_max_num: usize,
  pub exclude_bid_reachable: bool,
  pub symbolic_max_term: usize,
  pub saturate_only_parent: bool,
  pub reduce_proven_lemma: bool
}

impl Config {
  fn from_args(args: &Args) -> Self {
    // Make the output directory if it doesn't exist.
    create_dir_all(&args.output_directory).unwrap();
    let emit_proofs = args.emit_proofs;
    if emit_proofs {
      // Make the proofs directory if it doesn't exist.
      create_dir_all(&args.proofs_directory).unwrap();
    }
    let mangle_names = !args.unmangled_names && emit_proofs;
    Self {
      cyclic_mode: Mutex::new(false),
      max_split_depth: if mangle_names {
        // Why the +1? Because mangling the names prepends a Cyclegg_ to
        // everything, which means that our depth check (which naively looks at
        // how many underscores there are) will return 1 greater than it should.
        args.max_split_depth + 1
      } else {
        args.max_split_depth
      },
      split_conditionals: !args.no_cond_split,
      single_rhs: args.single_rhs,
      irreducible_only: args.irreducible_only,
      timeout: if args.timeout == 0 {
        None
      } else {
        Some(args.timeout)
      },
      log_level: args.log_level.parse().unwrap(),
      save_graphs: args.save_graphs,
      save_results: args.save_results,
      emit_proofs,
      verbose: args.verbose,
      verbose_proofs: args.verbose_proofs,
      output_directory: args.output_directory.clone(),
      proofs_directory: args.proofs_directory.clone(),
      mangle_names,
      proof_comments: !args.no_proof_comments,
      prop: args.prop.clone(),
      blocking_vars_analysis: !args.no_blocking_analysis,
      max_lemma_size: args.max_lemma_size,
      cvec_size: args.cvec_size,
      cvec_term_max_depth: args.cvec_term_max_depth,
      cvec_num_rolls: args.cvec_num_rolls,
      cvec_num_random_terms_per_type: args.cvec_num_random_terms_per_type,
      add_grounding: !args.no_grounding,
      destructive_rewrites: !args.no_destructive_rewrites,
      proof_depth: args.proof_depth,
      generalization: !args.no_generalization,
      cc_lemmas: !args.no_cc_lemmas,
      cc_lemmas_generalization: !args.no_cc_lemmas_generalization,
      better_termination: !args.no_better_termination,
      only_generalize: args.only_generalize,
      extraction_loop_limit: 0,
      extraction_allow_end_loop: true,
      extraction_max_depth: 10,
      extraction_max_size: 20,
      extraction_max_num: 1000,
      symbolic_max_term: 100,
      exclude_bid_reachable: args.exclude_bid_reachable,
      saturate_only_parent: args.saturate_only_parent,
      reduce_proven_lemma: args.reduce_proven_lemmas
    }
  }

  pub fn is_cyclic(&self) -> bool {
    *self.cyclic_mode.lock().unwrap()
  }

  pub fn set_cyclic(&self, cyclic: bool) {
    *self.cyclic_mode.lock().unwrap() = cyclic;
  }
}

lazy_static! {
  pub static ref ARGS: Args = Args::parse();
  pub static ref CONFIG: Config = Config::from_args(&ARGS);
}
