# Artifact review record

Mathematical source review: **PASS**. Original obstruction audit: **PASS**. Supplemental soundness audit: **PASS**. Obstruction rebuild in the publication directory: **PASS**.

This record describes a separate AI review pass within the same assisted research session. It is not external human peer review. The reviewer read the paper, compared its claims with the Lean sources, checked the cited primary literature, and inspected the verification scripts. The linked compiler reports provide the kernel-verification evidence; this review did not run the Lean builds.

## Mathematical statement and attribution

The [paper](two-coordinate-obstruction.tex) states the obstruction with precisely seven admissible maps, eleven weak rules, and eleven first-offset equalities in each orientation. Admissibility includes nonnegative real matrices and offsets and a first diagonal entry of at least one for every symbol, including both boundaries. Forward and reversed orientations are separate implications. The statement has no coefficient cap, integrality requirement, or invertibility assumption.

The five numbered results and their substantive proof steps agree with the formal sources. The review covered the determinant split, singular common-row argument, scalar lower-triangular exceptions, positive and zero upper slopes, both upper exceptional patterns, boundary normalization, and affine word reversal. The resonance statement includes its required positivity assumptions. The paper identifies the compressed case analyses as proof outlines.

The attribution and symbol correspondence were checked against Yolcu–Aaronson–Heule's [journal article](https://doi.org/10.1007/s10817-022-09658-8) and [implementation](https://github.com/emreyolcu/rewriting-collatz). Theorem 3.17 supplies the Collatz equivalence; Theorems 2.6 and 2.15 support the rule-removal discussion. The dimension-five examples are described as search outcomes, without a minimality claim. The paper distinguishes the stated strictly monotone format from the relaxed TOP setting, arctic arithmetic, other strict orders, and higher dimensions.

The fixed-decrement argument agrees with [FullTwoSoundness.lean](../formal/FullTwoSoundness.lean). It uses a fixed `δ > 0` on nonnegative vectors, preservation under admissible maps, and a natural-number measure `floor(x₀/δ)`. The three supplemental declarations prove preservation, evaluation, and well-foundedness. They do not formalize the general rule-removal theorem or the prior equivalence with Collatz.

All eight blocks in the [Lean appendix](lean-statement-appendix.tex) match the source excerpts. The last block stops at the final theorem type, as the appendix explains. All 48 local links in the [claims map](lean-claims.md) resolve. The [statement review](../formal/full-two-coordinate-statement-review.md) supplies a separate comparison of the definitions and all eleven rule pairs. No remaining mathematical, citation, or scope correction was identified.

## Verification evidence

The [original obstruction audit](../formal/full-two-coordinate-lean-check.json), completed on 27 September 2026 at 11:36:58 UTC, records 50 freshly rebuilt local modules and 222 public theorem/lemma axiom audits. Only `propext`, `Classical.choice`, and `Quot.sound` occur, and the report records zero SAT-solver calls. Its SHA-256 is `3e4c23a484105a3f2132e531c8647faf8497847f7724cf684befa75b307f2b55`.

The [supplemental soundness audit](../verification/soundness-rebuild.json), completed at 12:02:58 UTC, records eight freshly rebuilt modules and 65 public theorem/lemma axiom audits under the same axiom restriction. Its SHA-256 is `7754ed4551db12aa8c99a3a287c6f3c0a1069af9ed5f1659868c15ec68949c76`. The review independently rehashed its 91 guarded files and found no mismatch; the recorded before/after guards also agree. These modules overlap the obstruction's dependency closure.

The [separate obstruction rebuild in the publication directory](../verification/publication-rebuild.json) also passed for all 50 modules and 222 declarations. Its SHA-256 is `0eef2a10627b30cf02d8977906896aa2e07a5447fec51ae95df264b214ccc815`. After completion, the lead agent checked all retained source hashes, compiler exit codes, and the complete standard-axiom inventory against the distributed files.

Both checking scripts passed source review. They use fresh source snapshots and local module output directories, audit the public declaration inventory, restrict axioms, and check provenance before and after compilation. Style-linter flags do not disable kernel checking. No proof source, checker, or retained report was edited during this review.

## Typesetting and visual review

Tectonic 0.17.0 produced the ten-page A4 PDF using FreeMono for the Lean appendix. The retained log has no overfull or underfull boxes, undefined references, missing-character entries, or LaTeX warnings.

The lead agent visually reviewed all ten rendered pages. A table interrupted a sentence on page two; paragraph separation corrected it. The final rendering was pixel-identical on pages one and three through ten, and the changed second page was inspected again. This source reviewer verified the final PDF metadata and log; the visual inspection is attributed to that separate pass.

## Reviewed snapshots

| Artifact | SHA-256 |
| --- | --- |
| `two-coordinate-obstruction.tex` | `d8b54a72cc06f179dcc58e2b2dc8e0f619ccfe1d1ace51551b5df482055446ea` |
| `two-coordinate-obstruction.pdf` | `a7fa57d609aefda89cf6a0dff7b59fdb36eb59b7b0f0c49956934916a7cf66e6` |
| `lean-statement-appendix.tex` | `ed072ca7ed2510e7d51186221bf646107c8c7a2f472572b8314d776d89fffad8` |
| `lean-claims.md` | `8747b72e4abace379cea306d3ff87a8624cbbb69d19c68627b55ee6c3868b0c7` |
| `../formal/FullTwoCoordinate.lean` | `429785555eecec277248380fe0c2e767c8c7303cf0e2712de29878dda2bd29a0` |
| `../formal/FullTwoSoundness.lean` | `7e97553622f5ebffe692ff3654e5bcdd1011b702bb6973263d44517176565664` |
| `../formal/check_full_two_coordinate.py` | `e6918179ac2df045944dc12a750a44952cb2d7ce2ef1dab42034da4f43a573e0` |
| `../formal/check_full_two_soundness.py` | `f2d40b72924d2678800617f0d5776ac0cc402e0b2c9b568757fbdde66be9f0ce` |
| `../formal/full-two-coordinate-lean-check.json` | `3e4c23a484105a3f2132e531c8647faf8497847f7724cf684befa75b307f2b55` |
| `../verification/soundness-rebuild.json` | `7754ed4551db12aa8c99a3a287c6f3c0a1069af9ed5f1659868c15ec68949c76` |
| `../verification/publication-rebuild.json` | `0eef2a10627b30cf02d8977906896aa2e07a5447fec51ae95df264b214ccc815` |

The result is an obstruction to the specified interpretation class. It is not a proof of the Collatz conjecture.
