# Formal verification

For the theorem with diagonal bounds, the entry point is [FullTwoCoordinate.lean](FullTwoCoordinate.lean). In namespace `CollatzResearch.FullTwo`, it proves:

| Declaration | Conclusion |
| --- | --- |
| `forward_all_gaps_zero` | All eleven forward first-offset gaps vanish. |
| `reversed_all_gaps_zero` | All eleven reversed first-offset gaps vanish. |
| `full_two_coordinate_obstruction` | Both implications, with their weak-rule hypotheses kept separate. |

These three declarations assume seven nonnegative real affine maps in two coordinates, with first diagonal entry at least one for **every** symbol, including both boundaries. The result excludes a first rule removal in this format. The second entry point, [CollatzReversedRealTwoCoordinate.lean](CollatzReversedRealTwoCoordinate.lean), removes all diagonal bounds for the reversed eligible rules. In namespace `CollatzResearch.RealTwoCoordinate`, `reversed_eligible_offsets_equal` proves the vector equalities `(D.comp A).offset = D.offset` and `(D.comp B).offset = (D.comp G).offset` from seven nonnegativity assumptions and all eleven reversed weak comparisons. Its companion `no_positive_eligible_offset_gap` excludes a positive fixed decrement in either coordinate.

Together these results exclude the stated full-context format in both orientations and the unrestricted reversed TOP step in two coordinates. They do not settle forward TOP, arctic arithmetic, higher dimensions, or Collatz.

## Finite-pattern convergence

[FinitePatternConvergence.lean](FinitePatternConvergence.lean) proves `CollatzPositiveProgression.every_finite_pattern_has_equal_first_hitting_times`: for every finite `F : Finset ℕ` and lower bound, some larger `x > 1` makes every `x + n`, `n ∈ F`, first reach 1 at a common finite time `H`, with a common odd count `R`. Its second declaration specializes to consecutive runs of every length.

The underlying [coalescence theorem](FinitePatternCoalescence.lean) constructs `K, R, a, b`, with `a, b > 0`, such that every `a + 2^K*t + n` reaches `b + 3^R*t` after `K` steps with odd count `R`, for all `t ≥ 0` and `n ∈ F`. Nine new modules form the full dependency closure of the convergence entry point. They define and reason about the shortcut map itself: even `n` maps to `n/2`, odd `n` to `(3n+1)/2`. No convergence hypothesis appears in either theorem. The translating integer is existential; the result does not settle convergence from arbitrary fixed starts.

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

The checker rebuilds all 137 local modules in a fresh temporary directory using the pinned compiled mathlib dependencies. It inventories and queries the axioms of all 633 public theorems and lemmas and all 93 definitions in the inventory, for 726 audited declarations. These include both final obstruction families, the forward growth and contraction result, the three soundness lemmas, finite-pattern coalescence and convergence, and four auxiliary modules on conditional stationary profiles. The latter are retained as checked algebra rather than contributions claimed by the manuscript. It rejects proof placeholders, additional axioms, unexpected compiler output, cached local modules on the library path, and changes to guarded sources or dependencies during the run. The JSON report retains compiler output, commands, inventories, hashes, and axiom results. Temporary compiled modules are removed on completion.

The [retained combined report](../verification/rebuild.json) describes the environment of its run. The checker resolves the current source directory independently and has no dependency on historical reports or other checking scripts.

## Supplemental soundness lemmas

[FullTwoSoundness.lean](FullTwoSoundness.lean) treats a fixed decrement `δ`: `Gap δ x y` means `y 0 + δ ≤ x 0` and `y 1 ≤ x 1`. Its three public declarations prove preservation by admissible maps for `δ ≥ 0`, evaluation of weak coefficientwise comparisons with an offset gap on nonnegative inputs, and well-foundedness of the decrease relation for `δ > 0`.

These lemmas and their dependencies are included in the combined check. The unrestricted reversed obstruction has a 119-module dependency closure, which already includes the 50 modules supporting the theorem with diagonal bounds. The soundness file adds one module and three public declarations.

## Read the statement

The [paper appendix](../paper/lean-statement-appendix.tex) reproduces the definitions and principal theorem types. The [claim map](../paper/lean-claims.md) identifies the supporting lemmas.

Lean's kernel checks proof terms under the reported foundational axioms. Matching the formal proposition to the paper remains a separate reading task. The Collatz equivalence is attributed to Yolcu–Aaronson–Heule; this artifact does not re-formalize that equivalence or the general rule-removal theorem.


The additional forward results are in `CollatzForwardRealWordGrowth.lean` and `CollatzForwardRealTwoCoordinateNecessary.lean`, supported by `CollatzForwardFiveCover.lean` and `CollatzForwardRealContraction.lean`. They assume six nonnegative affine maps and nine forward weak comparisons; neither dynamic boundary comparison is required. An auxiliary reversed theorem, not used in the manuscript, is `RealWeakStationaryObstruction.weak_stationary_profile_excludes_strict`. It assumes all eleven reversed weak comparisons, separated matrix scales, a bounded normalized binary observation, and eventual stationarity of a normalized ternary orbit on a positive vector. The ordered-power lemmas remove the need for a commutation equality. No assertion deriving these orbit hypotheses in general is part of the theorem.

The separate basin-density development is in [formal-basins](../formal-basins/README.md). Select it with `verify.py --scope basins`; its partial coverage and verification report are separate from the 137-module matrix/synchronization closure described here.
