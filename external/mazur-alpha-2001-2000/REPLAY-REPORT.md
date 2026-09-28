# Actual second-scale replay: alpha = 2001/2000

The actual-real Proposition 1.11 rate theorem was compiled successfully at
`alpha = 2001/2000`. The checked declaration is
`Erdos1135.Tao.taoProp111RealFirstPassageStabilizationRate_checked`.
Its axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`.
`RootAudit.lean` also proves the exact identity
`Erdos1135.Tao.taoAlpha = (2001 : ℝ) / 2000`.

The original source is the companion to Mazur's
[Natural-Density Almost-Bounded Collatz Orbits in Logarithmic Time](https://www.proofatlas.ai/formalizations/natural-density-log-time-collatz/),
pinned at `ca3dd0d63920411213403092aecc6946619eb082`.
This is an independently modified and checked specialization of that companion.
It does not assert that the upstream publication already supplied this second
scale or proved a theorem uniform over arbitrary alpha.

## Checked interface

The theorem supplies nonnegative error functions and constants `C ≥ 0`, `c > 0`
such that, eventually in real `x`, the two no-hit probabilities are bounded by
`C * x ^ (-c)` and the first-passage law distance is bounded by
`C * (Real.log x) ^ (-c)`. Its sources are the odd logarithmic distributions
on the two consecutive windows with endpoints
`x^alpha`, `x^(alpha^2)`, and `x^(alpha^3)`.
The probability, first-passage, real-window, and public rate-statement
definitions are unchanged except for their dependence on the new `taoAlpha`.
The upstream failed-passage default remains `1`; `taoTV` remains the full L1
distance. The manuscript's translation to its own first-passage convention is
a separate interface argument.

This replay checks the real first-passage rate root. It does not replay the
natural-density logarithmic-time `ND.RhinUnconditional` root at this new
alpha. The separate original-alpha baseline check covers that root.

## Changes

The portable patch changes ten existing Lean files and adds one helper file.
Each carries a modification notice; the upstream Apache-2.0 LICENSE and
Advameg NOTICE are retained.

- `taoAlpha` becomes `2001/2000`.
- The definition `M0(B) = floor(((alpha - 1)/100) * log B)` is retained.
  Its evaluated denominator becomes `200000`. Schedule, interior-width,
  reverse-prefix, and rate lower-bound constants are adjusted accordingly.
- A quarter-width rounded-window log-mass lemma is proved under the stronger
  log-width threshold `12`. Increasing the eventual log cutoff to `24000`
  preserves the original public normalizer lower bound `log B / 8000` and
  the downstream public TV constants.
- The existing upper estimate `M0(B) ≤ log B / 100000` is retained by weakening
  the new stronger floor estimate. No first-passage map or law is redefined.

`alpha-2001-2000.patch` applies with zero fuzz to the pinned original files.
Every resulting byte was compared with the compiled source snapshot; see
`patch-roundtrip-check.json`.

## Build provenance

The closure has 382 first-party modules, including the new helper. The first
successful replay compiled 58 modules in the isolated output directory and
copied 324 modules from the original-alpha baseline only after checking that
their entire first-party dependency closures were unchanged, their source
bytes matched, their object hashes matched, and their toolchain pins matched.

After adding redistribution notices, all 55 affected dependency-closure
modules were freshly recompiled. The other 327 modules were reused only after
checking their recursive dependency fingerprints and object hashes. The
final source snapshot and the root axiom audit were checked again.
`rebuild-record.json` is the final record; the earlier pre-notice record and
the complete baseline record preserve the provenance of reused objects.

The parameterized verifier was then run in existing-object audit mode: it
independently rechecked all 382 source, dependency, and object hashes, checked
all toolchain/dependency pins, and freshly compiled `RootAudit.lean`.
This check passed with the same standard axiom report. Its record is
`portable-audit-record.json`.

The companion includes an unused open-problem registry theorem with `sorry`
in `FormalConjectures.Wikipedia.CollatzConjecture`. The checked root does not
depend on `sorryAx`. No claim is made that the entire upstream package is
placeholder-free.

## Replay

Use Lean `4.30.0-rc2`, commit
`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, and mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`. The source manifest also pins
mathlib's dependency manifest and every package revision. Prepare that
mathlib environment and its compiled third-party dependencies first. The
checker does not download dependencies or write into the mathlib checkout.

The default command freshly compiles every first-party module into a new
output directory:

```sh
python3 verify_replay.py \
  --mathlib /path/to/pinned/mathlib4 \
  --lean /path/to/lean-4.30.0-rc2/bin/lean \
  --output /path/to/new-replay-output \
  --jobs 2
```

An existing passing replay may be checked without copying its objects:

```sh
python3 verify_replay.py \
  --mathlib /path/to/pinned/mathlib4 \
  --lean /path/to/lean-4.30.0-rc2/bin/lean \
  --output /path/to/new-audit-output \
  --reuse-record /path/to/prior-output/rebuild-record.json \
  --audit-existing
```

The prior record must have a sibling `modules` directory containing the
matching artifacts. A fresh run of this portable checker names its record
`replay-record.json`; either filename is accepted. Existing-object audit
requires a complete matching closure and still freshly compiles the root
audit. Without `--audit-existing`, `--reuse-record` copies only independently
validated exact dependency closures and compiles the rest.

The distribution contains source, patches, licenses, manifests, logs, and
audit records. It contains no compiled Lean objects.
