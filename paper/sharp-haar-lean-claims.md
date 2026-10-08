# Quadratic cylinder energy and integrability: Lean claim map

This map accompanies *Quadratic cylinder energy and integrability of the Syracuse law* by Lucas Valbuena. “Public endpoint” means a declaration not marked `private` in Lean.

All 362 internal source modules and the generated complete declaration audit were freshly compiled and individually kernel checked, with 726 successful commands. The audit covers 10,465 module/constant rows, 10,445 distinct names and 736 encoded private rows; only `propext`, `Classical.choice` and `Quot.sound` occur as axioms. The complete external input inventories agree before and after. External compiled libraries were fingerprinted and reused, not rebuilt from source. [Replay evidence](../formal-sharp-haar/evidence/README.md) preserves the successful record, the earlier failed attempt, and subsequent setup-reuse and fresh-process verification, including relocation. The fresh dependency-download branch was not exercised.

All module links below point into the [standalone proof bundle](../formal-sharp-haar/README.md). Write `FE` for `CollatzCylinderPacking.Arithmetic.FairEnergy` and `T` for `Erdos1135.Tao`.

| Paper statement | Public Lean endpoint | Source |
| --- | --- | --- |
| Theorem 1.1(1): `N_k ≤ 24k + 8k² ≤ 32k²`, `k ≥ 1` | `FE.residue_energy_le_linear_quadratic`, `FE.residue_energy_le_thirtytwo_quadratic` | [FairEnergyQuadraticBound.lean](../formal-sharp-haar/source/FairEnergyQuadraticBound.lean) |
| Identification with actual Haar energy and its bound | `T.canonicalPadicRho_sq_integral_eq_energy`, `T.canonicalPadicRho_sq_integral_le_linear_quadratic`, `T.canonicalPadicRho_sq_integral_le_thirtytwo_quadratic` | [CanonicalHaarEnergy.lean](../formal-sharp-haar/source/CanonicalHaarEnergy.lean) |
| Theorem 1.1(2): one normalized density for all `1 ≤ p < 2` | `T.canonicalSyracuseMeasure_has_subcritical_density`, `T.canonicalHaarDensity_memLp_of_lt_two` | [CanonicalHaarLp.lean](../formal-sharp-haar/source/CanonicalHaarLp.lean) |
| Uniform finite-level bound for `1 < p < 2`, `n ≥ 1` | `T.exists_canonicalPadicRho_uniform_eLpNorm_bound` | [CanonicalHaarLp.lean](../formal-sharp-haar/source/CanonicalHaarLp.lean) |
| Actual stationary density equation | `T.canonicalHaarDensity_stationary` | [CanonicalHaarStationarity.lean](../formal-sharp-haar/source/CanonicalHaarStationarity.lean) |
| Theorem 1.1(3): failure of `L²` | `T.canonicalHaarDensity_not_memLp_two` | [CanonicalHaarNotL2.lean](../formal-sharp-haar/source/CanonicalHaarNotL2.lean) |
| Exact real-exponent range for the same density | `T.canonicalHaarDensity_memLp_iff_lt_two`, `T.canonicalSyracuseMeasure_has_sharp_lp_density` | [CanonicalHaarNotL2.lean](../formal-sharp-haar/source/CanonicalHaarNotL2.lean) |

The uniform finite-level theorem literally quantifies over `1 < p < 2` and `n ≥ 1`. The paper includes `n=0` and `p=1` as assembled consequences. `T.canonicalPadicRho_memLp` supplies a finite norm at depth zero, so taking the maximum with that norm extends the bound to `n=0`. At `p=1`, `T.canonicalPadicRho_nonneg` and `T.canonicalPadicRho_integral` give norm one at every depth; `T.canonicalHaarL1_norm` records the same identity for the L¹ class. These declarations are in [CanonicalHaarEnergy.lean](../formal-sharp-haar/source/CanonicalHaarEnergy.lean), [CanonicalHaarTwoScale.lean](../formal-sharp-haar/source/CanonicalHaarTwoScale.lean), and [CanonicalHaarDensity.lean](../formal-sharp-haar/source/CanonicalHaarDensity.lean). No single new named endpoint packages both extra boundary cases.

The density statement provides one nonnegative function of integral one, equality of the actual canonical measure with its Haar `withDensity` measure, and the asserted membership for that same function. The non-L² endpoint is unconditional: it imports the checked actual stationary equation. Its helper `canonicalHaarDensity_not_memLp_two_of_stationary` is private and is not substituted for the public result. Exponents `p ≥ 2` are excluded by finite-measure Lp monotonicity.

| Supporting result | Public Lean endpoints | Source |
| --- | --- | --- |
| Lemma 2.1: exact word-order bridge and numerator decoding | `FE.wordPNatList_reverse_numerator`, `FE.affineNumerator_injective_of_wordLength` | [FairEnergyWordReversal.lean](../formal-sharp-haar/source/FairEnergyWordReversal.lean) |
| Lemma 2.1: distinct natural quotients on a fixed-total residue fibre | `FE.numerator_quotient_injective_on_fiber`, `FE.numerator_quotient_le_translation` | [FairEnergyWordSeparation.lean](../formal-sharp-haar/source/FairEnergyWordSeparation.lean) |
| Lemma 2.2: quotient counting | `FE.nat_card_mul_succ_le_twice_sum`, `FE.card_sq_le_twice_quotient_weight` | [QuotientFiberBounds.lean](../formal-sharp-haar/source/QuotientFiberBounds.lean) |
| Lemma 2.2 and Lemma 3.1: fixed-total count and finite energy reduction | `FE.fixed_total_fiber_card_sq_le_twice`, `FE.finite_residue_energy_le_quadratic_moment` | [FairEnergyQuadraticFinite.lean](../formal-sharp-haar/source/FairEnergyQuadraticFinite.lean) |
| Lemma 3.2: summability and quadratic moment estimate | `FE.quadraticMomentTerm_summable`, `FE.quadraticMomentTerm_tsum_le` | [FairEnergyMoments.lean](../formal-sharp-haar/source/FairEnergyMoments.lean) |
| Lemma 5.1: positive overlap and critical square obstruction | `T.positive_overlap_integral`, `T.critical_sq_identity_impossible` | [StationarySupportOverlap.lean](../formal-sharp-haar/source/StationarySupportOverlap.lean) |

The infinite-expectation display in Lemma 3.1 is assembled within the final energy proof from the finite inequality, summability and the directed-limit lemmas in [FairEnergyLimit.lean](../formal-sharp-haar/source/FairEnergyLimit.lean); it is not a separately named endpoint. The moment argument uses an auxiliary normalized `3·4^(-a)` product law solely for estimating a sum. The stationary law throughout the theorem is the actual fair `2^(-a)` law. The manuscript's prefix-tilt calculation and the source's native word recursion agree through the explicit reversal identity.

Tao's Proposition 1.14 supplies fine-scale mixing; his Remark 1.13 identifies the law, and Lemma 6.2 supplies offset injectivity. These are credited inputs, with their formal dependency sources included in the bundle. The results concern full additive Haar measure. They assert no linear-energy asymptotic, numerical limiting coefficient, integer trace estimate, or individual-orbit conclusion. Automated proof development and review are disclosed in the paper and do not constitute external peer review or an exhaustive priority search.
