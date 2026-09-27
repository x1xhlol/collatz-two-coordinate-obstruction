# Formal verification

The entry point is [FullTwoCoordinate.lean](FullTwoCoordinate.lean). In namespace `CollatzResearch.FullTwo`, it proves:

| Declaration | Conclusion |
| --- | --- |
| `forward_all_gaps_zero` | All eleven forward first-offset gaps vanish. |
| `reversed_all_gaps_zero` | All eleven reversed first-offset gaps vanish. |
| `full_two_coordinate_obstruction` | Both implications, with their weak-rule hypotheses kept separate. |

Every declaration assumes seven nonnegative real affine maps in two coordinates, with first diagonal entry at least one for **every** symbol, including both boundaries. The result excludes a first rule removal in this format. It does not cover arbitrary TOP interpretations or arctic arithmetic, and it does not prove Collatz.

## Prerequisites and pinned dependencies

Use Linux x86_64, Git, Python 3.10 or later, and [Elan](https://github.com/leanprover/elan#installation), which supplies `lean` and `lake`. The check compares the full Lean version string with the retained evidence, including the target platform:

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

Keep the pinned manifest unchanged. The repository uses an external mathlib checkout rather than its own Lake project; the checking scripts assemble and compile the local dependency closure.

## Check the obstruction

Run from the repository root:

```sh
mkdir -p .build
python3 formal/check_full_two_coordinate.py \
  --mathlib-root "$PWD/.deps/mathlib4" \
  --build-root "$PWD/.build" \
  --workers 4 \
  --report "$PWD/.build/obstruction-check.json"
```

Use a new report filename for each run. Existing reports are never overwritten. The script accepts one to four workers and gives each Lean process one thread; reduce `--workers` if memory is limited. The build root must already exist and be writable. An explicit build root also avoids depending on the default `/dev/shm` location.

The checker rebuilds all 50 local modules in a fresh temporary directory, using the pinned compiled mathlib dependencies. It inventories and queries the axioms of all 222 public theorems and lemmas, including the three final declarations. It rejects proof placeholders, additional axioms, unexpected compiler output, and source or dependency changes during the run. Temporary compiled modules are removed on completion; the JSON report retains the compiler output, commands, inventories, hashes, and axiom results.

The original report is [full-two-coordinate-lean-check.json](full-two-coordinate-lean-check.json). The [publication-directory rebuild](../verification/publication-rebuild.json) also passed for all 50 modules and 222 declarations. Absolute paths inside a retained report describe the environment of that run; the scripts resolve the current source directory independently.

## Check the supplemental soundness lemmas

`FullTwoSoundness.lean` treats a fixed decrement `δ`: `Gap δ x y` means `y 0 + δ ≤ x 0` and `y 1 ≤ x 1`. It proves that admissible affine maps preserve this relation for `δ ≥ 0`, weak coefficientwise comparisons give the asserted gap on nonnegative inputs, and the resulting decrease relation is well-founded for `δ > 0`.

The [separate soundness audit](../verification/soundness-rebuild.json) passed. To reproduce it, run from the repository root:

```sh
python3 formal/check_full_two_soundness.py \
  --mathlib-root "$PWD/.deps/mathlib4" \
  --build-root "$PWD/.build" \
  --workers 2 \
  --report "$PWD/.build/soundness-check.json"
```

The supplemental closure has eight modules and 65 public theorems and lemmas. These counts overlap the obstruction's dependencies; they are not additional disjoint results.

## Reading the evidence

The [statement review](full-two-coordinate-statement-review.md) compares the formal definitions and theorem type with the mathematical claim. The [paper appendix](../paper/lean-statement-appendix.tex) reproduces those declarations, and the [claim map](../paper/lean-claims.md) identifies the supporting lemmas.

Lean's kernel checks proof terms under the reported foundational axioms. Matching the formal proposition to the paper remains a separate reading task. The Collatz equivalence is attributed to Yolcu–Aaronson–Heule; the obstruction theorem does not require a new formalization of that equivalence.

The other checking scripts and pinned reports in this directory preserve the provenance required by the main checker. Reproduction of this paper uses the two entry points above.
