# A two-coordinate obstruction for affine interpretations of the Yolcu–Aaronson–Heule Collatz system

This repository contains the paper, Lean proofs, and verification scripts for an obstruction to the first rule-removal step for the eleven-rule Yolcu–Aaronson–Heule system.

For each of its seven symbols, let `F_s(x) = M_s x + v_s`, where the 2×2 matrix and offset vector have nonnegative real entries and `(M_s)₀₀ ≥ 1`. If all eleven rules are weakly oriented coefficientwise, the first-coordinate offset gap of every rule is zero. The theorem holds separately for the original rules and their word reversals. It has no coefficient bound, integrality requirement, or invertibility assumption.

This excludes a first removal using the stated strictly monotone affine format. It does not prove the Collatz conjecture. The relaxed TOP setting, which does not require strict monotonicity of every symbol, remains unresolved by this theorem. Arctic interpretations and higher dimensions are outside its scope.

## Read the result

- [Paper (PDF)](paper/two-coordinate-obstruction.pdf) and [LaTeX source](paper/two-coordinate-obstruction.tex)
- [Exact Lean theorem](formal/FullTwoCoordinate.lean)
- [Definitions and theorem type reproduced in the paper](paper/lean-statement-appendix.tex)
- [Paper claims mapped to Lean declarations](paper/lean-claims.md)
- [Formal verification instructions](formal/README.md)

The main theorem is `CollatzResearch.FullTwo.full_two_coordinate_obstruction`. Its two implications each assume all eleven weak comparisons and conclude eleven first-offset equalities.

## Verification status

The [retained obstruction audit](formal/full-two-coordinate-lean-check.json) reports PASS for a fresh build of 50 local modules and an axiom audit of 222 public theorems and lemmas. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. The verification makes no SAT-solver calls.

The [publication-directory rebuild](verification/publication-rebuild.json) also passed for all 50 modules and 222 declarations. It verifies the sources distributed in this repository.

The supplemental [soundness audit](verification/soundness-rebuild.json) passed for eight modules and 65 public declarations. `FullTwoSoundness.lean` proves preservation of a fixed positive decrement, evaluation of weak affine comparisons with an offset gap, and well-foundedness on nonnegative vectors. It is checked separately from the 50-module obstruction closure; the dependency counts overlap.

## Reproduce the checks

The pinned environment is Lean **4.27.0** and mathlib commit **`a3a10db0e9d66acbebf76c5e6a135066525ac900`**. See [formal/README.md](formal/README.md) for dependency setup and both checking commands. The scripts create fresh build directories and refuse to overwrite an existing report.

The paper was built with [Tectonic 0.17.0](https://tectonic-typesetting.github.io/en-US/install.html) and the **FreeMono** font, provided by `fonts-freefont-ttf` on Debian/Ubuntu. From the repository root:

```sh
cd paper
tectonic --keep-logs --untrusted two-coordinate-obstruction.tex
```

Tectonic resolves cross-references and downloads its TeX support files as needed. The bibliography is included in the source; no BibTeX step is needed.

## Prior work and citation

The rewriting system and its equivalence to the Collatz conjecture are due to Emre Yolcu, Scott Aaronson, and Marijn J. H. Heule, [An Automated Approach to the Collatz Conjecture, Journal of Automated Reasoning 67(2), Article 15 (2023)](https://doi.org/10.1007/s10817-022-09658-8). We use the ASCII symbol names from their [implementation](https://github.com/emreyolcu/rewriting-collatz).

Citation metadata for this paper and artifact is in [CITATION.cff](CITATION.cff). The paper discloses the use of OpenAI Codex in mathematical exploration, Lean development, verification scripts, and manuscript preparation.

The earlier derivation notes linked from `two-coordinate-affine-obstruction.md` are retained for the statement review. The paper and the final Lean declarations state the published result.
