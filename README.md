![C.C. Lemma's logo](img/logo.svg)

> [!WARNING]
> Rewrite in progress: check back later for a new version

C.C. Lemma is a tool for automating inductive equational proofs. Its main
selling point is its ability to discover and effortlessly wield lemmas in
service of making a proof.

## The progress so far

This repository has been initialized from `6fe83e3` from the main branch of
https://github.com/cole-k/cyclegg.

I pruned all the files that are not directly necessary to the rewrite, although
I kept the examples directory because it will be necessary for tests.

## The plan

In addition to doing changes to generally improve code quality, we have some
major changes we want to make the main proof search algorithm, specifically how
lemma discovery is done. Although we don't expect that this will change our
theoretical capability, we expect there may be (significant) efficiency gains.
Or losses...

After we do this, we'll merge the history of the remaining files back in.

## Current TODOs

* Everything
  - Clean up.
  - Remove cruft.
  - Rework to support major changes.
* ast.rs
  - Use the `sexp` library instead of `symbolic_expression`.
  - Make a new `Language` that isn't `SymbolLang`.
* analysis.rs
  - Use type information in the language to create c-vecs on demand instead of
    having a two-phase c-vec creation process.
  - Consider not having c-vecs be stored in an e-graph and evalutaed using one,
    but instead evaluated on-demand.
  - Can we do the blocking variable analysis as an e-graph analysis instead of
    on the contents of the e-graph itself?
* config.rs
  - Remove useless flags.
  - Read from a config file (use `confy`?) and have user-supplied flags override
    values in the config.
* explain.rs
  - Rework to support new data structures.
  - Consider outputting to an intermediate data structure and adding translators
    to different backends.
* goal.rs
  - Completely rewrite.
* goal\_graph.rs
  - Completely rewrite.
* Cargo.toml
  - Remove unnecessary deps.
