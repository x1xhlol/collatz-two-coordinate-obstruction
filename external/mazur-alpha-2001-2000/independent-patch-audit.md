# Independent audit of the α = 2001/2000 first-passage replay

Audit date: 2026-09-28. Result: **PASS for the stated fixed-scale first-passage interface and the mathematical integrity of the patch.**

This is a read-only source, patch, and build-record review. It does not claim a second independent execution of the complete Lean build. The producer's completed isolated build was inspected, and its source and object hashes were independently checked.

## Scope and pinned inputs

- Original package: `ca3dd0d63920411213403092aecc6946619eb082`.
- Original source: `/dev/shm/collatz-mazur-rebuild/source`.
- Replay: `/home/ubuntu/collatz-global-descent-20260927/mazur-alpha-2001-2000`.
- Root module: `Erdos1135.Tao.Section3.Prop111RealRate`.
- Root declaration: `Erdos1135.Tao.taoProp111RealFirstPassageStabilizationRate_checked`.
- Patch SHA-256: `a4fd6bebb47493455881af354ec52cb166f6ab7d457f479222aabf441348f99d`.
- Completed rebuild-record SHA-256: `94e09a052b15c5a4b3c1aaeec72e43390bd9321b142a3a30fdb085d1bb2ece79`.

All 381 original source files used by the replay match the original package manifest. The replay has 382 modules: precisely ten original source files differ, and one source file is added. Every replay source hash matches the completed rebuild record. Independently applying the patch with `patch --batch --fuzz=0 -p1` to temporary copies of the original sources reproduced all eleven touched files byte for byte.

## Fixed exponent and preserved definitions

`Probability/LogWindowEndpoints.lean` changes only the fixed exponent and its descriptive comment, apart from a modification notice:

```lean
noncomputable def taoAlpha : ℝ := (2001 : ℝ) / 2000
```

The endpoint definitions remain `Nat.ceil y` and `Nat.floor (y ^ alpha)`. The support remains the inclusive odd integers in this interval. `logNatWeight n` is exactly `1/n` for positive `n`, and `oddLogWindowPMF` divides these weights by their finite sum. Thus the source is precisely the paper's logarithmic distribution on odd integers in `[y,y^α]`.

`Section5/PassSchedule.lean` retains the definition

```lean
taoSection5M0 B = Nat.floor (((taoAlpha - 1) / 100) * Real.log B)
```

Its simplified denominator changes from 100000 to 200000, as required by the new exponent. It is not replaced by an unrelated step-back schedule. The eventual half-main-term bound consequently has denominator 400000. The other changed constants follow this smaller linear margin: the lower schedule coefficient, interval-width coefficient, interior-buffer threshold, reverse-prefix budgets, and eventual logarithmic cutoffs are adjusted accordingly. The old upper bound `M0 ≤ log B / 100000` is deliberately retained where it suffices; the new proof derives it from the stronger floor bound with denominator 200000.

No passage map, no-hit event, source probability, total-variation definition, or statement socket is changed. In particular, `Section3.lean`, `Syracuse/FirstPassage.lean`, `Syracuse/RealFirstPassage.lean`, and the final `Section3/Prop111RealRate.lean` are byte-identical to the pinned original.

## New quarter-width mass estimate

The added `Probability/LogWindowQuarterMass.lean` proves, for `y ≥ 2`, `α > 1`, valid ordered rounded endpoints, and `w = (α−1) log y ≥ 12`,

\[
\sum_{\substack{\lceil y\rceil\le n\le\lfloor y^\alpha\rfloor\\n\text{ odd}}}\frac1n\ge\frac w4.
\]

The argument is a valid strengthening of the original one-eighth-width lemma under a stronger width hypothesis. Let `a = ceil y` and `b = floor(y^α)`. Rounding gives `a ≤ 2y` and `b ≥ y^α/2`. The unchanged harmonic-sum lemma gives

\[
\text{mass}\ge\frac12(\log b-\log a)-2
\ge\frac w2-\log2-2\ge\frac w2-3.
\]

For `w ≥ 12`, the final expression is at least `w/4`. The new Lean proof follows precisely these inequalities and adds no axiom or assumed mass bound.

At `α−1 = 1/2000`, the coefficient `(α−1)/4` is exactly `1/8000`. This preserves the existing normalized mass bound `log B / 8000`, after raising the eventual cutoff from `log B ≥ 8000` to `log B ≥ 24000`. It therefore legitimately avoids propagating a weaker source-normalization constant through the rest of the formalization. The change in `PowerInteriorBoundaryMass.lean` uses the same argument, and `PassNormalizer.lean` merely obtains its older weaker cutoff from the new stronger one.

## Exact first-passage interface

The checked root is an assumption-free proof of `TaoProp111RealFirstPassageStabilizationRateStatement`, whose window pair is the following, with the fixed `α` supplied by the replay:

\[
y_1=x^\alpha,\qquad y_2=x^{\alpha^2},\qquad
Q_{y_i}=\operatorname{Log}(\{n\text{ positive odd}:y_i\le n\le y_i^\alpha\}).
\]

There exist `C ≥ 0` and `c > 0` such that, eventually as real `x → ∞`, each no-hit probability is at most `C x^(−c)` and the distance between the two totalized first-passage laws is at most `C (log x)^(−c)`. The socket stores its error functions at `floor x`, but the asymptotic inequalities themselves are in the genuine real variable `x`. The real-threshold bridge proves that an integer orbit value is at most `x` exactly when it is at most `floor x`; no threshold error is being omitted. Positive source masses are eventually established in the dependency chain rather than supplied as an unproved eventual premise.

**The failure landing value is already 1 in both original and replay.** `syracusePassLocationAtMostOrOne` returns the first landing if a hit exists and returns `⟨1,hB⟩` otherwise. The real law uses this exact totalizer at `floor x`. There is no zero-to-one relabelling to justify and no associated additional error term. On the positive odd source, successful Syracuse iterates are positive and odd, so the law agrees with the paper's positive-odd landing law.

`taoTV` is the full L1 sum `Σ |p−q|`. If the paper's `dTV` denotes half L1, the formal estimate is stronger than necessary; if it denotes full L1, it is the same estimate. This convention affects at most a harmless constant in either use.

The natural-to-real transport, unchanged in the replay, explicitly pays one normalized floor-window perturbation per no-hit probability and four such perturbations for the pairwise L1 estimate. Its floor-source error is `96000 / (B log B)`. These terms are absorbed into the stated powers. They are not silently discarded.

The original build at `α = 1001/1000` and this replay at `α = 2001/2000` therefore provide the two independent scale inputs used by the paper. They do **not** constitute a Lean proof for every exponent in the whole interval `[1.0005,1.001]`. Any interval-wide claim has the separate written parameter argument as its justification. The downstream two-scale averaging application needs only the two checked endpoints.

## Build-record and dependency review

The final replay record reports `PASS` on Lean `4.30.0-rc2` with mathlib revision `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. All 382 recorded module entries have exit code zero. All 382 object hashes match the actual replay `.olean` files, and all recorded module-source hashes agree with the inspected sources.

The producer reused 324 objects only under the rule that their entire first-party dependency closure was unchanged; 58 entries were compiled in the isolated replay. An independent traversal of the source import graph identified 55 modules reaching one of the eleven touched sources, and none of these was classified as baseline-object reuse. Thus this source review found no path by which an object depending on the old `taoAlpha` was accepted as unchanged.

The root audit log reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` in the audited root's dependencies. The imported companion's separate unused open-problem registry must not be confused with this root's dependency audit.

## Attribution

The imported companion is supplied under **Apache License 2.0**, with the Advameg notice; it is not an MIT-licensed companion. The replay's `LICENSE` and `NOTICE` match the original manifest byte for byte:

- `LICENSE`: `cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30`.
- `NOTICE`: `78d24afa82e943d2bd65af48accb0a802d1debc12043394e398899fdaacb3a3c`.

All eleven touched files carry a dated modification notice naming this replay and the original pin. The added mass lemma explicitly identifies the original one-eighth-width proof from which it was adapted. The retained notice also preserves the separate licensing status of mathlib, Formal Conjectures material, and cited papers.

No source or manuscript edits were made during this audit.
