# Formal verification

The entry point is [FinitePatternConvergence.lean](FinitePatternConvergence.lean), in namespace `CollatzPositiveProgression`.

- `every_finite_pattern_has_equal_first_hitting_times` gives arbitrarily large translates of every finite natural-offset pattern with a common finite first hitting time of 1 and a common odd count.
- `arbitrarily_long_consecutive_equal_first_hitting_times` specializes to `Finset.range length`.

The map, iterates, and odd count are defined in [PositiveProgressionCoalescence.lean](PositiveProgressionCoalescence.lean). The odd branch is `(3*n + 1)/2`. Every earlier iterate is explicitly required to exceed 1 in the final theorem. No hypothesis of convergence appears.

## Prerequisites and pinned dependencies

Use Linux x86_64, Git, Python 3.10 or later, and [Elan](https://github.com/leanprover/elan#installation), which supplies `lean` and `lake`. The checker pins Lean 4.27.0, its compiler commit, and a Release build. The retained run used:

```text
Lean (version 4.27.0, x86_64-unknown-linux-gnu, commit db93fe1608548721853390a10cd40580fe7d22ae, Release)
```

The mathlib revision is `a3a10db0e9d66acbebf76c5e6a135066525ac900`. Its `lake-manifest.json` has SHA-256 `6c24676b690a32627317b1d6dd58cf9318d689c5481e1edc53d07c93c892632f` and pins the remaining packages. The checker verifies those package revisions and requires no tracked changes in their Git checkouts.

From the standalone artifact directory, prepare a separate mathlib checkout:

```sh
elan toolchain install leanprover/lean4:v4.27.0
mkdir -p .deps
git clone https://github.com/leanprover-community/mathlib4.git .deps/mathlib4
git -C .deps/mathlib4 checkout --detach a3a10db0e9d66acbebf76c5e6a135066525ac900
```

Then obtain mathlib's compiled dependencies using its [documented cache command](https://github.com/leanprover-community/mathlib4/tree/a3a10db0e9d66acbebf76c5e6a135066525ac900#downloading-cached-build-files):

```sh
cd .deps/mathlib4
lake exe cache get
cd ../..
```

Keep the pinned manifest unchanged. The repository uses an external mathlib checkout rather than its own Lake project; the standalone checker assembles and compiles the local dependency closure.

## Run the independent check

From the `equal-collatz-heights/` directory:

```sh
mkdir -p .build
python3 verify.py \
  --mathlib-root "$PWD/.deps/mathlib4" \
  --build-root "$PWD/.build" \
  --workers 4 \
  --report "$PWD/.build/rebuild.json"
```

Use a new report filename for each run. The checker rebuilds all nine local modules in a fresh directory and audits all 66 public theorem/lemma declarations plus eight definitions. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. It rejects proof placeholders, additional axioms, unexpected compiler output, cached local dependencies, or changes to guarded sources during the run.

The [retained report](../verification/rebuild.json) contains the exact source inventory, hashes, compiler outputs, and axiom reports. The checker has no dependency on historical reports or on the matrix paper's formal files. The [appendix](../paper/lean-statement-appendix.tex) reproduces the definitions and principal theorem types, while the [claim map](../paper/lean-claims.md) connects the proof steps to declarations.

Kernel acceptance checks the formal proposition; matching it to the paper's statement remains a separate reading task. The prose conversion from shortcut time `H` and odd count `R` to unshortened time `H + R` is an elementary consequence; the Lean endpoints themselves use the shortcut map.
