# Two-coordinate obstruction paper

Lucas Valbuena, *A two-coordinate obstruction for affine interpretations of the Yolcu–Aaronson–Heule Collatz system*.

[Read the paper](two-coordinate-obstruction.pdf) or inspect the [LaTeX source](two-coordinate-obstruction.tex).

For seven affine maps with nonnegative real coefficients and first diagonal entry at least one, all eleven weak rules of the Yolcu–Aaronson–Heule system force every first-coordinate offset gap to vanish. The result holds separately for the original rules and their word reversals. It excludes a first rule removal in this strictly monotone format, with no coefficient bound. The relaxed TOP setting remains unresolved by this theorem. The result does not prove Collatz.

The paper credits the original rewriting construction and termination equivalence, states the interpretation and soundness conditions, presents the mathematical argument, and reproduces the exact final Lean theorem type in its appendix. The [claim map](lean-claims.md) connects its results with the formal declarations. The [artifact review](artifact-review.md) records the source checks, citation checks, visual review, and final file hashes, with the scope of the AI-assisted review stated explicitly.

## Verification

The [original obstruction audit](../formal/full-two-coordinate-lean-check.json) passed on 27 September 2026 at 11:36:58 UTC. It rebuilt 50 local modules and audited all 222 public theorem and lemma declarations. The [separate soundness audit](../verification/soundness-rebuild.json) passed at 12:02:58 UTC, covering eight modules and 65 declarations. Both reports permit only `propext`, `Classical.choice`, and `Quot.sound` and record zero SAT-solver calls. Their dependency counts overlap.

The [additional obstruction rebuild in the publication directory](../verification/publication-rebuild.json) also passed for all 50 modules and 222 declarations.

## Build the paper

The retained PDF has ten A4 pages and was built with **Tectonic 0.17.0**. The Lean appendix requires the **FreeMono** font, provided by `fonts-freefont-ttf` on Debian/Ubuntu. From the repository root:

```sh
cd paper
tectonic --keep-logs --untrusted two-coordinate-obstruction.tex
```

Tectonic handles repeated passes for cross-references. The bibliography is included in the source. The final log contains no box warnings, undefined references, or missing characters.

## Reproduce the Lean check

Use Lean **4.27.0** and mathlib revision **`a3a10db0e9d66acbebf76c5e6a135066525ac900`**. The scripts verify the complete version string, manifest, and dependency revisions against the retained reports. Run from the repository root, with an existing writable build directory and an unused report destination:

```sh
python3 formal/check_full_two_coordinate.py \
  --mathlib-root /path/to/pinned/mathlib \
  --build-root /path/to/temporary/builds \
  --report /path/to/fresh-obstruction-check.json
```

For the supplemental fixed-decrement lemmas:

```sh
python3 formal/check_full_two_soundness.py \
  --mathlib-root /path/to/pinned/mathlib \
  --build-root /path/to/temporary/builds \
  --report /path/to/fresh-soundness-check.json
```

Both scripts refuse to overwrite existing reports. The publication repository is [x1xhlol/collatz-two-coordinate-obstruction](https://github.com/x1xhlol/collatz-two-coordinate-obstruction).
