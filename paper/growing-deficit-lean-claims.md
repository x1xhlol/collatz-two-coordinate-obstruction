# Fourier manuscript: theorem coverage

The six numbered statements in *Fourier decay for truncated Syracuse affine laws* are represented by the sources below. Unless stated otherwise, theorem names are in `Erdos1135.Tao`. The source bundle uses Lean 4.35.0-rc3 and the exact package revisions in its [dependency pins](../formal-growing-deficit/dependency-pins.json).

| Paper statement | Lean theorem | Source and scope |
|---|---|---|
| Theorem 1 — conductor-deficit estimate | `trap_unconditional_affineTwistedExpectation_deficit_all_powers` | [TrapMicrocanonicalDeficit](../formal-growing-deficit/source/TrapMicrocanonicalDeficit.lean). One constant for each natural exponent works for every positive conductor, every length at most that conductor, every primitive frequency, every affine seed, and every unit-modulus function of the total exponent. |
| Theorem 2 — exact conditioning bound | `trap_unconditional_conditionedAffinePMF_deficit_all_powers` | [TrapMicrocanonicalDeficit](../formal-growing-deficit/source/TrapMicrocanonicalDeficit.lean). The actual filtered geometric source is mapped through the affine offset. Its Fourier coefficient is the slice numerator divided by the positive slice mass. |
| Theorem 2 — polynomial deficit with a mass floor | `trap_unconditional_conditionedAffinePMF_polynomial_deficit_mass_floor` | [TrapMicrocanonicalMassFloor](../formal-growing-deficit/source/TrapMicrocanonicalMassFloor.lean). For each fixed output power, mass-floor power, and `0 < β < 1`, one constant is uniform in `k ≥ 1`, `d ≤ k^β`, seed, primitive frequency, and every slice with mass at least `k^(-B)`. |
| Corollary 3 — central slice | `trap_unconditional_centralConditionedAffinePMF_polynomial_deficit` | [TrapCentralMicrocanonical](../formal-growing-deficit/source/TrapCentralMicrocanonical.lean). The central mass is positive and at least `1/(4k)`; for `k ≥ 4` it supplies the required `k^(-2)` floor. |
| Proposition 4 — finite-cover obstruction | `eventually_no_bounded_native_black_trap_families` | [TrapBoundedUniform](../formal-growing-deficit/source/TrapBoundedUniform.lean). The cutoff is uniform over all primitive frequencies and all families with a fixed bound on their number of triangles, exact signed schedules, and a sublinear error budget. Its Subspace Theorem dependency is included as proved source. |
| Proposition 5 — uniform qualitative contraction | `trap_native_envelope_qualitative` | [TrapNativeQualitativeDecay](../formal-growing-deficit/source/TrapNativeQualitativeDecay.lean). The sole parameter hypothesis is the strict entropy inequality `log 3 < 2 * θ * log 2`; the triangle, concentration, and renewal inputs are discharged. |
| Lemma 6 — scalar bootstrap | `CollatzResearch.trap_deficit_bootstrap` | [TrapDeficitBootstrap](../formal-growing-deficit/source/TrapDeficitBootstrap.lean). This abstract lemma retains exactly the boundedness, recursion, and qualitative contraction assumptions stated in the paper. The unconditional application discharges them at `θ = 5/6`. |

The main identities and supporting steps have these additional roots:

| Step | Lean source |
|---|---|
| Source restriction, affine map, and exact Fourier normalization | [TrapMicrocanonicalSource](../formal-growing-deficit/source/TrapMicrocanonicalSource.lean), including `unitSourceConditionedAffinePMF_dft_eq_normalized`. |
| Geometric total-exponent mass | `unitSourceExponentMass_eq_choose` in [TrapExactExponentMass](../formal-growing-deficit/source/TrapExactExponentMass.lean). |
| Central binomial mass bound | [TrapCentralBinomial](../formal-growing-deficit/source/TrapCentralBinomial.lean) and `unitSourceExponentMass_central_lower` in [TrapCentralMicrocanonical](../formal-growing-deficit/source/TrapCentralMicrocanonical.lean). |
| Full-cutoff renewal moment, including a first stop at time zero | [Lemma79AllRBound](../formal-growing-deficit/source/Erdos1135/Tao/Renewal/Lemma79AllRBound.lean), with the one-step proof in [Lemma79OneStepBound](../formal-growing-deficit/source/Erdos1135/Tao/Renewal/Lemma79OneStepBound.lean). |
| Short horizontal horizon charged to the full-cutoff moment | [TrapNativeStoppedWhiteTail](../formal-growing-deficit/source/TrapNativeStoppedWhiteTail.lean) and [TrapCanonicalStoppedWhiteTail](../formal-growing-deficit/source/TrapCanonicalStoppedWhiteTail.lean). |
| Re-anchored triangle family and exact error/span estimates | [TrapFewWhiteFamily](../formal-growing-deficit/source/TrapFewWhiteFamily.lean), [TrapGoodPathForcesStops](../formal-growing-deficit/source/TrapGoodPathForcesStops.lean), and [TrapGoodPathFromTube](../formal-growing-deficit/source/TrapGoodPathFromTube.lean). |
| Concentration and the uniform few-white probability bound | [TrapConcentrationChoice](../formal-growing-deficit/source/TrapConcentrationChoice.lean) and [TrapGoodPathProbabilityReduction](../formal-growing-deficit/source/TrapGoodPathProbabilityReduction.lean). |
| Exact conductor recursion and its application | [TrapNativeEnvelopeRecursion](../formal-growing-deficit/source/TrapNativeEnvelopeRecursion.lean), [TrapNativeEnvelopeBootstrap](../formal-growing-deficit/source/TrapNativeEnvelopeBootstrap.lean), and [TrapUnconditionalDeficit](../formal-growing-deficit/source/TrapUnconditionalDeficit.lean). |

The [reproduction instructions](../formal-growing-deficit/README.md) distinguish the fresh rebuild of all bundled application and Subspace modules from the pinned external library caches. The package audit enumerates every compiled constant, including private and generated declarations, and permits only `propext`, `Classical.choice`, and `Quot.sound` as logical axioms.

These are finite random affine-law theorems. Neither a raw integer-occupation upper bound nor convergence of every deterministic Collatz orbit follows from them. The constants have no asserted effective numerical values, and the growing-deficit bound supplies no inverse power of the conductor at a fixed positive deficit ratio.
