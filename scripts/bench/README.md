# FLT benchmark suite

This directory contains the FLT benchmark suite.
It is built around [radar](github.com/leanprover/radar)
and benchmark results can be viewed
on the [Lean FRO radar instance](https://radar.lean-lang.org/repos/flt).

To execute the benchmark suite, run `scripts/bench/run` from the repo root.
All measurements will be placed into `measurements.jsonl` in the repo root.

Radar sums any duplicated measurements with matching metrics.
To post-process the `measurements.jsonl` file this way,
run `scripts/bench/combine.py measurements.jsonl -o measurements_combined.jsonl`
in the repo root after executing the benchmark suite.

The `*.py` symlinks exist only so the python files are a bit nicer to edit
in text editors that rely on the file ending.

## Adding a benchmark

To add a benchmark to the suite, follow these steps:

1. Create a new folder containing a `run` script and a `README.md` file describing the benchmark,
   as well as any other files required for the benchmark.
2. Edit `scripts/bench/run` to call the `run` script of your new benchmark.

The following environment variables are available to an individual benchmark's `run` script:

- `ROOT_DIR`: absolute path to the root of the repo
- `BENCH_DIR`: absolute path to this directory (`scripts/bench`).
- `OUTPUT_FILE`: absolute path to the `measurements.jsonl` file
  that benchmarks should append their measurements to
