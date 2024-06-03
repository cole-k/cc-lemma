![C.C. Lemma's logo](img/logo.svg)

C.C. Lemma is a tool for automating inductive equational proofs. Its main
selling point is its ability to discover and effortlessly wield lemmas in
service of making a proof.

> [!WARNING]
> Research code ahead

# I want to see it in action

```
$ cargo run --release -- examples/add.ceg
```

This will run and prove several sample properties about different add functions
on Peano numbers.

There will be several lemmas proved for some which are also output.

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

Use the following command to now run for cvc4 and hipspec and generate a plot
for all three (we don't include TheSy because the results are not competitive
enough to put in the effort to build and parse its outputs).

```
$ python3 runner.py  --tools cvc4 hipspec
$ python3 generate-plots.py results/summary -o results --exclude-tools thesy
```

This should only take a few minutes too.

If you wish to run other tools, pass them to `runner.py` under the `--tools`
argument. Depending on which tools you have run, you can also then remove them
from ` --exclude-tools` to generate plots for them too.

Both scripts have a `--help` command explaining their usage.

## Sample data

You can also run `generate-plots.py` on sample data we have included under
[precomputed-results](./precomputed-results).

If you run

```
$ python3 generate-plots.py results/summary --exclude-tools hipspec cvc4 thesy
```

you should get plots that exactly match those in our paper.

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
