# A two-coordinate obstruction for affine interpretations of the Yolcu–Aaronson–Heule Collatz system

This repository contains the paper, Lean proofs, and a verification script for an obstruction to the first rule-removal step for the eleven-rule Yolcu–Aaronson–Heule system.

For each of its seven symbols, let `F_s(x) = M_s x + v_s`, where the 2×2 matrix and offset vector have nonnegative real entries and `(M_s)₀₀ ≥ 1`. If all eleven rules are weakly oriented coefficientwise, the first-coordinate offset gap of every rule is zero. The theorem holds separately for the original rules and their word reversals. It has no coefficient bound, integrality requirement, or invertibility assumption.

This excludes a first removal using the stated strictly monotone affine format. It does not prove the Collatz conjecture. The relaxed TOP setting, which does not require strict monotonicity of every symbol, remains unresolved by this theorem. Arctic interpretations and higher dimensions are outside its scope.

## Read the result

- [Paper (PDF)](paper/two-coordinate-obstruction.pdf) and [LaTeX source](paper/two-coordinate-obstruction.tex)
- [Exact Lean theorem](formal/FullTwoCoordinate.lean)
- [Definitions and theorem type reproduced in the paper](paper/lean-statement-appendix.tex)
- [Paper claims mapped to Lean declarations](paper/lean-claims.md)
- [Formal verification instructions](formal/README.md)

The main theorem is `CollatzResearch.FullTwo.full_two_coordinate_obstruction`. Its two implications each assume all eleven weak comparisons and conclude eleven first-offset equalities.

## Verify the proof

The standalone [verify.py](verify.py) rebuilds the complete dependency closure of the main obstruction and the three fixed-decrement soundness lemmas: **51 Lean modules and 225 public theorem/lemma declarations**. It permits only `propext`, `Classical.choice`, and `Quot.sound` and makes no SAT-solver calls. The [retained report](verification/rebuild.json) records the build and axiom audit.

Use Lean **4.27.0** and mathlib commit **`a3a10db0e9d66acbebf76c5e6a135066525ac900`**. After the dependency setup in [formal/README.md](formal/README.md), run from the repository root:

```sh
mkdir -p .build
python3 verify.py \
  --mathlib-root "$PWD/.deps/mathlib4" \
  --build-root "$PWD/.build" \
  --report "$PWD/.build/rebuild.json"
```

Each run uses a fresh temporary build and requires an unused report filename. Every Lean file in `formal/` belongs to the dependency closure of `FullTwoCoordinate` or `FullTwoSoundness`.

## Build the paper

The source uses XeLaTeX and loads the appendix font as `DejaVuSansMono.ttf`, available in TeX Live 2025. From `paper/`, run `xelatex two-coordinate-obstruction.tex` twice. [Tectonic 0.17.0](https://tectonic-typesetting.github.io/en-US/install.html) also works:

```sh
cd paper
tectonic --keep-logs --untrusted two-coordinate-obstruction.tex
```

The bibliography is included in the source. No BibTeX step is needed.

## Prior work and citation

The rewriting system and its equivalence to the Collatz conjecture are due to Emre Yolcu, Scott Aaronson, and Marijn J. H. Heule, [An Automated Approach to the Collatz Conjecture, Journal of Automated Reasoning 67(2), Article 15 (2023)](https://doi.org/10.1007/s10817-022-09658-8). We use the ASCII symbol names from their [implementation](https://github.com/emreyolcu/rewriting-collatz).

Citation metadata for this paper and artifact is in [CITATION.cff](CITATION.cff). The paper discloses the use of OpenAI Codex in mathematical exploration, Lean development, verification scripts, and manuscript preparation.
