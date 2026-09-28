# Arbitrarily long runs of consecutive integers with equal Collatz height

For every prescribed length and lower bound, there is a larger interval of consecutive positive integers whose members first reach 1 at the same finite time, with equal odd-step counts. Height here uses the shortcut map: even `n` maps to `n/2`, odd `n` to `(3n+1)/2`. Equal first hitting times for the unshortened map follow as well.

The paper explicitly cites Garner’s 1985 run-length conjecture, with its attribution corroborated by Lagarias’s bibliography, and distinguishes it from Garner’s separate pair-classification conjecture. It makes no claim of historical priority.

The proof establishes the stronger statement for every finite set of nonnegative offsets. It first coalesces the entire pattern on one dyadic progression, then specializes its common endpoint to a power of two. This constructs suitable translating integers; it does not prove the Collatz conjecture.

- [Short paper (PDF)](paper/equal-collatz-heights.pdf) and [LaTeX source](paper/equal-collatz-heights.tex)
- [Finite-pattern and consecutive-run theorem](formal/FinitePatternConvergence.lean)
- [Coalescence theorem](formal/FinitePatternCoalescence.lean)
- [Exact definitions and theorem statements](paper/lean-statement-appendix.tex)
- [Claim-to-declaration map](paper/lean-claims.md)
- [Formal verification instructions](formal/README.md)

This directory is an independent artifact. Its nine Lean modules have 66 public theorem/lemma declarations and eight definitions, all included in the 74-declaration axiom audit. The checker permits only `propext`, `Classical.choice`, and `Quot.sound`. It rebuilds all local dependencies in a fresh directory using Lean 4.27.0 and pinned mathlib commit `a3a10db0e9d66acbebf76c5e6a135066525ac900`. It does not import the matrix paper's formal sources.

The [retained verification report](verification/rebuild.json) records source hashes, compiler output, and all axiom checks. See [formal/README.md](formal/README.md) for dependency setup, then run from this directory with a new report path:

```sh
mkdir -p .build
python3 verify.py \
  --mathlib-root /path/to/pinned/mathlib4 \
  --build-root "$PWD/.build" \
  --report "$PWD/.build/rebuild.json"
```

To build the paper, run XeLaTeX twice from `paper/`, or use Tectonic 0.17.0:

```sh
cd paper
tectonic --keep-logs --untrusted equal-collatz-heights.tex
```

The source includes its bibliography and uses the DejaVu Sans Mono font for Lean excerpts. Citation metadata is in [CITATION.cff](CITATION.cff). The paper discloses the use of OpenAI Codex in mathematical exploration, formalization, and writing.
