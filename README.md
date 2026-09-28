# Two-coordinate obstructions for affine interpretations of the Yolcu–Aaronson–Heule Collatz system

This repository contains the paper, Lean proofs, and a verification script for obstructions to the first rule-removal step for the eleven-rule Yolcu–Aaronson–Heule system and an independent second proof of Said Duran’s equal-height runs theorem in Section 9.

For each of its seven symbols, let `F_s(x) = M_s x + v_s`, where the 2×2 matrix and offset vector have nonnegative real entries and `(M_s)₀₀ ≥ 1`. If all eleven rules are weakly oriented coefficientwise, the first-coordinate offset gap of every rule is zero. The theorem holds separately for the original rules and their word reversals. It has no coefficient bound, integrality requirement, or invertibility assumption.

A second theorem removes the diagonal bounds for the reversed system. Nonnegativity and all eleven weak comparisons alone force equality of the full offset vectors in `da → d` and `db → dg`. This excludes either eligible first TOP removal in two nonnegative real affine coordinates. It does not force the other nine reversed gaps to vanish.

**Section 9 is an independent second proof of Omar Javier Said Duran’s theorem** on arbitrarily long consecutive runs with equal finite Collatz height and equal odd-step counts. Priority belongs to his [preprint](https://doi.org/10.5281/zenodo.23003526), dated 27 September 2026 and posted on Zenodo at 01:10:30 UTC on 28 September, with its [Lean archive](https://doi.org/10.5281/zenodo.23003500). The finite-pattern formulation is equivalent, since every finite set of offsets fits inside a sufficiently long run. Our proof directly synchronizes affine families on a dyadic progression and then chooses a power-of-two common endpoint. It constructs suitable translating integers; it does not establish convergence from an arbitrary prescribed start.

These results do not prove the Collatz conjecture. The unrestricted forward TOP problem, arctic interpretations, and unrestricted higher-dimensional interpretations remain unresolved.

## Read the result

- [Paper (PDF)](paper/two-coordinate-obstruction.pdf) and [LaTeX source](paper/two-coordinate-obstruction.tex)
- [Theorem with diagonal bounds](formal/FullTwoCoordinate.lean)
- [Reversed TOP theorem without diagonal bounds](formal/CollatzReversedRealTwoCoordinate.lean)
- [Finite-pattern convergence and consecutive-run theorem](formal/FinitePatternConvergence.lean)
- [Finite-pattern coalescence on a dyadic progression](formal/FinitePatternCoalescence.lean)
- [Definitions and theorem type reproduced in the paper](paper/lean-statement-appendix.tex)
- [Paper claims mapped to Lean declarations](paper/lean-claims.md)
- [Formal verification instructions](formal/README.md)

The theorem with diagonal bounds is `CollatzResearch.FullTwo.full_two_coordinate_obstruction`. Its two implications each assume all eleven weak comparisons and conclude eleven first-offset equalities. The unrestricted reversed theorem is `CollatzResearch.RealTwoCoordinate.reversed_eligible_offsets_equal`; it concludes two vector equalities using only nonnegativity and the reversed weak rules.

## Verify the proof

The paper also proves a forward growth and contraction result in arbitrary finite dimension. Under only the six digit swaps and three root comparisons, the observed repeated-`e` value dominates `floor(n/5)` times the sum of the three eligible offset gaps. A positive left row contracted by the binary matrix `A` makes those gaps vanish, yielding an explicit two-coordinate corollary. This treats a different regime from the main theorem's diagonal lower bound and requires no contraction condition on the other digit matrices.

The standalone [verify.py](verify.py) rebuilds the complete dependency closure of the paper's results, the three fixed-decrement soundness lemmas, and four auxiliary modules on conditional stationary profiles. Those auxiliary results remain available as checked algebra; they are not presented as contributions of the manuscript. The combined inventory has **137 Lean modules, 633 public theorem/lemma declarations, and 93 definitions included in the axiom audit**. It permits only `propext`, `Classical.choice`, and `Quot.sound` and makes no SAT-solver calls. The [retained report](verification/rebuild.json) records the build and axiom audit.

Use Lean **4.27.0** and mathlib commit **`a3a10db0e9d66acbebf76c5e6a135066525ac900`**. After the dependency setup in [formal/README.md](formal/README.md), run from the repository root:

```sh
mkdir -p .build
python3 verify.py \
  --mathlib-root "$PWD/.deps/mathlib4" \
  --build-root "$PWD/.build" \
  --report "$PWD/.build/rebuild.json"
```

Each run uses a fresh temporary build and requires an unused report filename. Every Lean file in `formal/` belongs to the combined closure of the six entry points listed in `verify.py`: the two main obstruction families, the soundness lemmas, the forward contraction result, the auxiliary stationary-profile result, and finite-pattern convergence.

## Build the paper

The source uses XeLaTeX and loads the appendix font as `DejaVuSansMono.ttf`, available in TeX Live 2025. From `paper/`, run `xelatex two-coordinate-obstruction.tex` twice. [Tectonic 0.17.0](https://tectonic-typesetting.github.io/en-US/install.html) also works:

```sh
cd paper
tectonic --keep-logs --untrusted two-coordinate-obstruction.tex
```

The bibliography is included in the source. No BibTeX step is needed.

## Prior work and citation

The rewriting system and its equivalence to the Collatz conjecture are due to Emre Yolcu, Scott Aaronson, and Marijn J. H. Heule, [An Automated Approach to the Collatz Conjecture, Journal of Automated Reasoning 67(2), Article 15 (2023)](https://doi.org/10.1007/s10817-022-09658-8). We use the ASCII symbol names from their [implementation](https://github.com/emreyolcu/rewriting-collatz). Their paper also proves an impossibility result for natural matrix interpretations of a different, unary Collatz system in every finite dimension, including a residual dependency-pair problem. The two main obstructions concern their mixed binary–ternary system, allow nonnegative real coefficients, and are restricted to two coordinates. One treats all eleven rules with diagonal bounds; the other treats the two reversed TOP rules without those bounds. The manuscript explains these differences in its related-work discussion.

Citation metadata for this paper and artifact is in [CITATION.cff](CITATION.cff). The paper discloses the use of OpenAI Codex in mathematical exploration, Lean development, verification scripts, and manuscript preparation.
