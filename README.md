![C.C. Lemma's logo](img/logo.svg)

C.C. Lemma is a tool for automating inductive equational proofs. Its main
selling point is its ability to discover and effortlessly wield lemmas in
service of making a proof.

This is an artifact generated from the
[`icfp-24`](https://github.com/cole-k/cc-lemma/tree/icfp-24) branch of the
`cc-lemma` repository.

> [!WARNING]
> Research code ahead

# I want to see it in action

```
$ cargo run --release -- examples/add.ceg
```

This will run and prove several sample properties about different add functions
on Peano numbers.

There will be several lemmas proved for some which are also output.

# Pre-requisites

Below we list instructions for installing and building all of the other tools,
but this has already been done in the artifact.

After installing a tool, configure `scripts/config.py` to add its path (C.C.
Lemma is not exempt; the dataset root is C.C. Lemma's `benchmarks` folder).

## C.C. Lemma

Install `cargo` and Rust using [rustup](https://rustup.rs/).

For running the experiments, we expect an enviroment and shell that supports
typical commands (`cd`, `rm`, `ulimit`, and `timeout`). This is true of most
Unix distributions.

## CVC4

A prebuilt binary from the 2015 VMCAI paper is included. We don't know how to
build this version.

## HipSpec

Clone [https://github.com/cole-k/hipspec](https://github.com/cole-k/hipspec) and
follow its installation instructions (noting that you need to install an older
version of stack; we assume it is named `stack-1.9.3`).

## TheSy

Clone
[https://github.com/eytans/TheSy/tree/releases/cav2021](https://github.com/eytans/TheSy/tree/releases/cav2021)
and follow its installation instructions.

Build it using

```
$ cargo fix --bin TheSy
$ cargo build --release --features "stats"
```

The first command is due to a breaking change in compiler versions since TheSy's
release.

The stats flag in the second one is so that we can collect stats for TheSy
(instead of having a runtime flag it is a compile-time flag).

# Building

Use

```
$ cargo build --release
```

to build

and

```
$ cargo run --release -- FILENAME
```

to run.

Make sure to include `--release` otherwise it will be much slower.

The artifact comes with the code already built. To build it yourself, run

```
$ cargo clean
```

# Running the benchmarks

The benchmarks we ran for our evaluation live in [benchmarks](./benchmarks).

We include both a runner ([runner.py](./runner.py)) to run the benchmarks as
well as a tool to generate our plots and tables from their results
([generate-plots.py](./generate-plots.py)).

Here is how you can use them to generate plots for C.C. Lemma and save them
under the `results` folder.

```
$ python3 runner.py 
$ python3 generate-plots.py results/summary -o results --exclude-tools thesy cvc4 hipspec
```

This should only take a few minutes at most because we set the timeout to 2s.

Use the following command to now run for CVC4 and HipSpec and generate a plot
for all three. We don't include TheSy because the results are not competitive
enough to put in the effort to parse its outputs; however, TheSy is included in
the artifact and you can run it. We describe how you can evaluate its results in
a later section.

```
$ python3 runner.py --tools cvc4 hipspec
$ python3 generate-plots.py results/summary -o results --exclude-tools thesy
```

This should only take a few minutes too. Note that you might need to increase
the timeout for HipSpec if you're getting 0 proved properties -- especially so
on a VM: it is slower to start than either CVC4 or C.C. Lemma.

If you wish to run other tools, pass them to `runner.py` under the `--tools`
argument. Depending on which tools you have run, you can also then remove them
from ` --exclude-tools` to generate plots for them too.

Both scripts have a `--help` command explaining their usage.

## Sample data

You can also run `generate-plots.py` on sample data we have included under
[precomputed-results](./precomputed-results).

If you run

```
$ python3 generate-plots.py precomputed-results --exclude-tools hipspec cvc4 thesy
```

you should get plots that match those in our paper.

Note that there is one datapoint which does appear for any tool but C.C. Lemma
among this data: `mtp-base`, which corresponds to the motivating example in
section 1 of our paper. We ran it individually for each tool and none could
solve it but C.C. Lemma, so we copied just its result into C.C. Lemma's results
for the optimization benchmarks.

## Configuring the runner

The runner takes some commandline arguments and additionally has some
configurations under [scripts/config.py](./scripts/config.py).

You shouldn't really need to touch the flags passed to each of the tools (and in
fact if you tinker with them you might break something), but if you configure
the tools for running you can put their path in the config and then you can also
run them.

The settings most important to reproducing our total evaluation are putting

```
timeout = 60
memory_limit = 16
```

but be warned that this can take a long time. If a full timeout is reached on
most props, it will take close to 2.5 hours -- per tool! In practice it doesn't
typically take this long for C.C. Lemma, but do expect a runtime above one hour.
For other tools, the runtime is generally longer.

# Running on your own

There are several example files in [examples](./examples) for you to peruse and
try C.C. Lemma on if you so desire.

If you want to try it on your own examples, please see refer to existing
examples and the [docs](./docs/file-format.md).

There are also many feature flags supported, most of which are for
debugging/ablations. [scripts/config.py][./scripts/config.py], which contains
the flags we use for our evaluation, should contain

```
--no-generalization --exclude-bid-reachable --saturate-only-parent -r
```

The first three are tweaks to the algorithm that turn off and on features we
ended up using; the last is just for outputting a results file.

In addition, there are several flags you may wish to know about.

```
-t, --timeout:      sets a timeout in seconds (default 0 for unlimited time)
-r, --save-results: saves the results in a file called results.csv in target.
-p, --emit-proofs:  emits a proof in Liquid Haskell under target/proofs.
                    Experimental. We recommend running with --unmangled-names and
                    --verbose-proofs, which will give the most readable proofs.
```

and of course `--help` will give the full list of options.

# Addendum: evaluating TheSy's results

TheSy support in the plot generation is experimental (I only tested for the
IsaPlanner suite), but should work; we do not guarantee that it is accurate to
the results in the paper. Below are instructions for manually verifying TheSy's
results should the plot generation fail or produce unexpected results.

To quickly get a sense of how many properties TheSy proves, you can use this
one-liner (assuming you're in the root of `cc-lemma`). Change `isaplanner` to
whichever test suite you want to compare with. This checks for the string "done
in" which to my knowledge TheSy prints if it succeeds.

```
cat results/thesy/isaplanner/*.out | grep 'Found all lemmas' | wc
```

There is one caveat: we run TheSy on more properties than we compare to. This is
handled in other tools by the results parser,  using the below code that
generates the range of properties for CLAM we keep: to ensure that you make the
same comparison you will want to filter TheSy's results that you only have these
(e.g. don't check `goal36.out`).

``` python
    '''
    All of our CLAM datasets have more properties than the original 50
    (labeled with prefix T in the paper, these are properties 1-50 in our dataset).

    These additional properties correspond to lemmas thought to be necessary
    to prove the originals (labeled with L and G).

    We do not use T1-T50, but instead a combination of the T and G properties
    which are thought to require lemmas. If you are familiar with CVC4's
    benchmarks, these are the goals which have "sg" versions, i.e. lemmas thought
    to be necessary to prove them.
    '''
    # Range from 1 to 35 inclusive
    range1 = map(str, range(1, 36))
    # Handle the case where there's a prefix 0 (hacky, I know)
    range_single_digit = map(lambda x: '0' + str(x), range(1,10))
    # Range from 48 to 50 inclusive
    range2 = map(str, range(48, 51))
    # Range from 75 to 86 inclusive
    range3 = map(str, range(75, 87))
```

To visually scan the results, you could use this one-liner instead of the above

```
find results/thesy/clam -name '*.out' -exec grep -H 'Found all lemmas' {} \;
```

and then filter based upon the filename.
