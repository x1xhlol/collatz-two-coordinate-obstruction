# Basin paper: Lean coverage

**The full paper is not yet formalized.** The local development checks the complete abstract two-scale averaging lemma, the uniform trajectory packing and correction-product estimates, and the finite Syracuse residue laws. Density existence and the Green/cylinder limit identification remain separate obligations.

The [paper](tao-basin-densities.tex) is standalone; it originated as Section 10 of the combined manuscript. Its local proof files are in [formal-basins](../formal-basins/). The pinned inventory is [basin-sources.json](../verification/basin-sources.json), and the fresh build and axiom audit are recorded in [basin-rebuild.json](../verification/basin-rebuild.json). This scope contains **35 modules, 251 public theorem/lemma declarations, and 55 audited definitions**. Use `python3 verify.py --scope basins` with the dependency arguments in the repository README.

## Checked local statements

| Paper step | Lean source and declaration | Exact coverage |
| --- | --- | --- |
| Two-scale averaging, Lemma 3 | [LogTimeMean.lean](../formal-basins/LogTimeMean.lean), `CollatzCanonical.TwoScale.two_scale_averaging`, supported by [TwoScaleAveraging.lean](../formal-basins/TwoScaleAveraging.lean) | Complete Banach-valued analytic implication, including the original `A(t)/t` formulation, arbitrary positive cutoff, and every rate `η < min(c,1)`. Both moving-window estimates are explicit hypotheses. |
| Numerical scale separation | [IncommensurableScales.lean](../formal-basins/IncommensurableScales.lean), `CollatzCanonical.Scales.logarithms_incommensurable` | Unconditional irrationality of `log(1001/1000) / log(2001/2000)`. |
| Uniform trajectory packing, Lemma 1 | [UniformOrbitPacking.lean](../formal-basins/UniformOrbitPacking.lean), `CollatzUniformOrbitPacking.uniform_finite_path_packing` | One constant for all finite positive distinct shortcut paths and all real height cutoffs. The actual parity count, entropy estimate, contraction parameters, and counting recurrence are proved in its dependency closure. No recurrence is left as a hypothesis. |
| Reciprocal sum and tail, Lemma 1 | [UniformOrbitReciprocalPacking.lean](../formal-basins/UniformOrbitReciprocalPacking.lean), `CollatzUniformOrbitReciprocalPacking.uniform_finite_path_reciprocal_bounds` | Uniform total reciprocal budget and `M^(b−1)` tail for every finite positive distinct path. |
| Correction products, Lemma 1 and Proposition 15 ingredients | [UniformOrbitCorrection.lean](../formal-basins/UniformOrbitCorrection.lean), `CollatzCanonical.UniformCorrection.exists_uniform_finite_and_infinite_product_bound`, `distinct_orbit_forward_product_tendsto_one` | One absolute product bound for all finite distinct paths and all positive injective infinite orbits; reciprocal summability follows from injectivity. Also proves actual infinite-product convergence, exact prefix/tail factorization, and forward-tail limit one. Does not prove the density characterization in Proposition 15. |
| Prefix product above a barrier | [UniformOrbitCorrection.lean](../formal-basins/UniformOrbitCorrection.lean), `uniform_finite_path_correction_bounds` | The sharper exponential bound needs only the odd source states to exceed the cutoff. |
| Affine correction and endpoint counting | [OptimalCylinderPacking.lean](../formal-basins/OptimalCylinderPacking.lean), `CollatzCylinderPacking.scaled_bounds`, `odd_endpoint_card_bound`, `endpointCount_scaled_bound` | Actual shortcut map and count of odd starts with prescribed length, odd count, and endpoint. |
| Arithmetic inverse trajectories | [ArithmeticInverseTuples.lean](../formal-basins/ArithmeticInverseTuples.lean), supported by [ArithmeticInverseBlocks.lean](../formal-basins/ArithmeticInverseBlocks.lean) | Integrality-certified inverse tuples give actual positive shortcut trajectories with the stated itinerary. The target may be even. |
| Full arithmetic word law | [ArithmeticCylinderLaw.lean](../formal-basins/ArithmeticCylinderLaw.lean) | Defines the complete countable geometric-word mass, proves its summability and head/tail expansion, and derives the upper bound `(2k+3)/2^k` for positive integer targets. The expansion is proved. |
| Lower atom and residue invariance | [ArithmeticCylinderLower.lean](../formal-basins/ArithmeticCylinderLower.lean), [ArithmeticCylinderResidues.lean](../formal-basins/ArithmeticCylinderResidues.lean) | The all-one exponent tuple gives mass at least `2^(-k)` at `3^k−1`. Positive representatives congruent modulo `3^k` have equal mass. |
| Finite residue probability law | [FiniteCylinderResidueLaw.lean](../formal-basins/FiniteCylinderResidueLaw.lean), supported by [ArithmeticCylinderCongruence.lean](../formal-basins/ArithmeticCylinderCongruence.lean) | Defines the actual pushforward law on `ZMod (3^k)`, proves nonnegative masses with total one, and identifies every positive integer representative with the arithmetic word mass. |
| Explicit Syracuse series | [FiniteSyracuseSeriesClosedForm.lean](../formal-basins/FiniteSyracuseSeriesClosedForm.lean) | The finite residue is the explicit sum `Σ(j<k) 3^j 2^(−Σ(i≤j) a_i)` as well as its recursive grouping. |
| Maximum finite residue mass | [FiniteCylinderMaximum.lean](../formal-basins/FiniteCylinderMaximum.lean) | For `k>0`, the actual maximum is between `2^(-k)` and `(2k+3)2^(-k)`. |
| Map bridge for Mazur’s predecessor input | [BasinMapBridges.lean](../formal-basins/BasinMapBridges.lean), `raw_hit_double_implies_shortcut_hit` | Every ordinary orbit reaching `2N` has a shortcut iterate equal to `N`. This inclusion already appears in Mazur’s equation (1.3); the proof here adds a local Lean check. |
| Targets divisible by three | [BasinMapBridges.lean](../formal-basins/BasinMapBridges.lean), `hit_multiple_of_three_iff` | If `3` divides `N`, then `T^k(n)=N` exactly when `n=2^k N`. |

The parity-vector module adapts M. Sharpe’s MIT-licensed proof at commit `ec8174b567d5cab4960024782210b5f5db02bd3a` of [msharpe248/collatz](https://github.com/msharpe248/collatz). Its full attribution and license notice are retained in [OrbitPackingParityCount.lean](../formal-basins/OrbitPackingParityCount.lean).

## Separate external replays

The [replay report](../external/mazur-alpha-2001-2000/REPLAY-REPORT.md) provides the sources, patch, build records, independent interface audit, and portable verification command.

Mazur’s source package `ca3dd0d63920411213403092aecc6946619eb082` was rebuilt with Lean 4.30.0-rc2 and mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. The 578-module closure for `Erdos1135.Tao.taoProp111RealFirstPassageStabilizationRate_checked` and `Erdos1135.ND.ndRhinRate_sameD` compiled afresh. Both root axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

A separate adaptation changes Tao’s fixed scale from `1001/1000` to `2001/2000` and checks the same actual real-threshold first-passage rate theorem. These two builds supply the two numerical scales in Proposition 2. They do not machine-check a continuum of scales or connect the external theorem namespaces to this local analytic development.

The source convention already sends failed passage to 1 and uses the same inclusive odd logarithmic windows as the paper. Its distance is full ℓ¹, which implies the paper’s total-variation bound. The upstream bundle contains an unrelated open-conjecture registry declaration with `sorry`; the audited theorem roots do not depend on it or on `sorryAx`. The external bundle is therefore not described as placeholder-free.

## Remaining theorem-level obligations

The following are not certified by the current local artifact:

- The connection from the separately replayed arithmetic inputs to the hypotheses of the local averaging theorem.
- Lemma 4’s local time, valuation, and small-landing estimates.
- Propositions 5–7’s countable-label laws, basin densities, and weighted densities.
- Theorem 8’s Green limit and Proposition 9’s uniform basin boundary estimate.
- Propositions 10–11’s first-hit clock laws.
- The identification of the finite residue laws with the infinite stationary probability measure on the 3-adic integers in Proposition 12, and the stated limit for its maximal exponential rate.
- Lemma 13’s endpoint tail and Theorem 14’s identification of the cylinder and Green limits.
- Proposition 15’s forward-component density characterization, beyond its checked correction-product ingredients.
- Theorems 16–17’s natural-density and positivity deductions from the additional Mazur inputs. Only the elementary map bridges listed above are locally checked.

A successful build establishes exactly the inventoried statements. It does not certify the remaining written proofs. The matrix/synchronization report and the external replay reports have distinct proof scopes.
