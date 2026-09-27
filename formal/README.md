# Formal verification

The entry point is [FullTwoCoordinate.lean](FullTwoCoordinate.lean). In namespace `CollatzResearch.FullTwo`, it proves:

| Declaration | Conclusion |
| --- | --- |
| `forward_all_gaps_zero` | All eleven forward first-offset gaps vanish. |
| `reversed_all_gaps_zero` | All eleven reversed first-offset gaps vanish. |
| `full_two_coordinate_obstruction` | Both implications, with their weak-rule hypotheses kept separate. |

Every declaration assumes seven nonnegative real affine maps in two coordinates, with first diagonal entry at least one for **every** symbol, including both boundaries. The result excludes a first rule removal in this format. It does not cover arbitrary TOP interpretations or arctic arithmetic, and it does not prove Collatz.

## Prerequisites and pinned dependencies

Use Linux x86_64, Git, Python 3.10 or later, and [Elan](https://github.com/leanprover/elan#installation), which supplies `lean` and `lake`. The checker pins Lean 4.27.0, its compiler commit, and a Release build. The retained run used:

```text
Lean (version 4.27.0, x86_64-unknown-linux-gnu, commit db93fe1608548721853390a10cd40580fe7d22ae, Release)
```

The mathlib revision is `a3a10db0e9d66acbebf76c5e6a135066525ac900`. Its `lake-manifest.json` has SHA-256 `6c24676b690a32627317b1d6dd58cf9318d689c5481e1edc53d07c93c892632f` and pins the remaining packages. The checker verifies those package revisions and requires no tracked changes in their Git checkouts.

From the repository root, prepare a separate mathlib checkout:

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

## Run the combined check

From the repository root:

```sh
mkdir -p .build
python3 verify.py \
  --mathlib-root "$PWD/.deps/mathlib4" \
  --build-root "$PWD/.build" \
  --workers 4 \
  --report "$PWD/.build/rebuild.json"
```

Use a new report filename for each run. The script accepts one to four workers and gives each Lean process one thread. The build root must exist and be writable.

The checker rebuilds all 51 local modules in a fresh temporary directory using the pinned compiled mathlib dependencies. It inventories and queries the axioms of all 225 public theorems and lemmas, including the three final obstruction declarations and three soundness lemmas. It rejects proof placeholders, additional axioms, unexpected compiler output, cached local modules on the library path, and changes to guarded sources or dependencies during the run. The JSON report retains compiler output, commands, inventories, hashes, and axiom results. Temporary compiled modules are removed on completion.

The [retained combined report](../verification/rebuild.json) describes the environment of its run. The checker resolves the current source directory independently and has no dependency on historical reports or other checking scripts.

## Supplemental soundness lemmas

[FullTwoSoundness.lean](FullTwoSoundness.lean) treats a fixed decrement `δ`: `Gap δ x y` means `y 0 + δ ≤ x 0` and `y 1 ≤ x 1`. Its three public declarations prove preservation by admissible maps for `δ ≥ 0`, evaluation of weak coefficientwise comparisons with an offset gap on nonnegative inputs, and well-foundedness of the decrease relation for `δ > 0`.

These lemmas and their dependencies are included in the combined check. The main obstruction alone has 50 modules and 222 public declarations; the combined closure adds one module and three declarations.

## Read the statement

The [paper appendix](../paper/lean-statement-appendix.tex) reproduces the definitions and exact theorem type. The [claim map](../paper/lean-claims.md) identifies the supporting lemmas.

Lean's kernel checks proof terms under the reported foundational axioms. Matching the formal proposition to the paper remains a separate reading task. The Collatz equivalence is attributed to Yolcu–Aaronson–Heule; this artifact does not re-formalize that equivalence or the general rule-removal theorem.
