# Basin paper: Lean coverage

**The full paper is not yet formalized.** The current Lean development checks the complete abstract two-scale averaging lemma and several arithmetic, counting, and infinite-series steps. The first-passage inputs and the downstream density and canonical-limit theorem chain remain separate obligations.

The [paper](tao-basin-densities.tex) is standalone; it originated as Section 10 of the combined manuscript. Its proof files are in [formal-basins](../formal-basins/). The pinned inventory is [basin-sources.json](../verification/basin-sources.json), and the fresh build and axiom audit are recorded in [basin-rebuild.json](../verification/basin-rebuild.json). Use `python3 verify.py --scope basins` with the dependency arguments in the repository README.

## Checked statements

| Paper step | Lean source and declaration | Exact coverage |
| --- | --- | --- |
| Two-scale averaging, Lemma 3 | [LogTimeMean.lean](../formal-basins/LogTimeMean.lean), `CollatzCanonical.TwoScale.two_scale_averaging`, supported by [TwoScaleAveraging.lean](../formal-basins/TwoScaleAveraging.lean) | Complete Banach-valued analytic implication, including the original `A(t)/t` formulation, arbitrary positive cutoff, and every rate `η < min(c,1)`. Both moving-window estimates are explicit hypotheses. |
| Numerical scale separation | [IncommensurableScales.lean](../formal-basins/IncommensurableScales.lean), `CollatzCanonical.Scales.logarithms_incommensurable` | Unconditional irrationality of `log(1001/1000) / log(2001/2000)`. |
| Counting-recursion bootstrap in Lemma 1 | [OrbitPackingPowerRecurrence.lean](../formal-basins/OrbitPackingPowerRecurrence.lean), supported by [OrbitPackingBootstrap.lean](../formal-basins/OrbitPackingBootstrap.lean) | The displayed recurrence with `floor(3 n^c)` and `floor(log₂ n)` gives one power-bound constant uniform over an indexed family. Derives the eventual contraction and logarithmic error bound. The trajectory/parity recurrence itself remains to be supplied. |
| Affine correction and endpoint counting | [OptimalCylinderPacking.lean](../formal-basins/OptimalCylinderPacking.lean), `CollatzCylinderPacking.scaled_bounds`, `odd_endpoint_card_bound`, `endpointCount_scaled_bound` | Bounds for the actual shortcut map and the count of odd starts with prescribed length, odd count, and endpoint. |
| Positive exponent words | [AdmissibleCylinderWords.lean](../formal-basins/AdmissibleCylinderWords.lean), `admissible_tuple_scaled_card_bound` | Encoding, decoder, and injectivity for words certified by actual integer trajectories. The certificate does not contain a probabilistic or numerical bound. |
| Finite head of the cylinder estimate | [CylinderHeadBound.lean](../formal-basins/CylinderHeadBound.lean), `endpoint_head_bound` | The head with total exponent from `k` through `5k−1` is at most `(2k+2)/2^k`. |
| Infinite geometric-word tail | [GeometricWordTail.lean](../formal-basins/GeometricWordTail.lean), `geometric_tail_le_half_pow` | Actual countable sums: total mass one, tilted mass `3^k`, and tail at total exponent at least `5k` bounded by `(32/81)^k ≤ 2^(-k)`. |
| Assembly of the cylinder upper bound | [CylinderExpansionBound.lean](../formal-basins/CylinderExpansionBound.lean), `cylinder_bound_of_expansion` | Proves `(2k+3)/2^k` from an **explicit expansion equality** into a certified finite head and filtered geometric tail. No numerical bound is assumed. Identifying this expansion with the stationary cylinder measure remains unformalized. |
| Map bridge for Mazur’s predecessor input | [BasinMapBridges.lean](../formal-basins/BasinMapBridges.lean), `raw_hit_double_implies_shortcut_hit` | Every ordinary orbit reaching `2N` has a shortcut iterate equal to `N`. This inclusion already appears in Mazur’s equation (1.3); the proof here adds a local Lean check. |
| Targets divisible by three | [BasinMapBridges.lean](../formal-basins/BasinMapBridges.lean), `hit_multiple_of_three_iff` | If `3` divides `N`, then `T^k(n)=N` exactly when `n=2^k N`. |

## Remaining theorem-level obligations

The following are not certified by the current local artifact:

- The full trajectory packing estimate and reciprocal tail in Lemma 1, including their parity/entropy input.
- Proposition 2’s parameterized Tao first-passage estimates. Mazur’s checked source fixes `α=1001/1000`; it does not supply the second scale automatically.
- Lemma 4’s local time, valuation, and small-landing estimates.
- Propositions 5–7’s countable-label laws, basin densities, and weighted densities.
- Theorem 8’s Green limit and Proposition 9’s uniform basin boundary estimate.
- Propositions 10–11’s first-hit clock laws.
- Proposition 12’s stationary-measure expansion, matching lower bound, and maximal-rate conclusion as statements about that measure.
- Lemma 13’s endpoint tail and Theorem 14’s identification of the cylinder and Green limits.
- Proposition 15’s forward-component characterization.
- Theorems 16–17’s natural-density and positivity deductions from the additional Mazur inputs. Only the elementary map bridges listed above are locally checked.

A successful build of this scope establishes exactly the inventoried Lean statements. It does not turn an explicit expansion hypothesis into a proved stationary-measure identity, import a second arithmetic scale, or certify the remaining written proofs. The old matrix/synchronization report is a different proof scope.
