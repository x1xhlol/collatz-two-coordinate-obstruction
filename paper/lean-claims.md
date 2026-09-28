# Paper claims and Lean declarations

This companion maps the formalized results and substantive proof steps in
Sections 2–9 of [the paper](two-coordinate-obstruction.tex) to their Lean sources.
Section 10's first-passage, density, time, and canonical-limit arguments are
ordinary mathematical proofs and are **not included in the Lean artifact**.
The verification report below does not establish those analytic results or
formalize their external input from Tao's theorem.
The paper states the supporting classifications and gives the algebraic arguments used in the proof. The table below maps those steps to the formal declarations. The [combined verification report](../verification/rebuild.json) records a fresh build of all 137 local modules and an axiom audit of 633 public theorems and lemmas plus 93 definitions. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. The standalone entry point is [verify.py](../verify.py).

The fixed-decrement soundness remarks in Section 2.1 are formalized in [FullTwoSoundness.lean](../formal/FullTwoSoundness.lean), namespace `CollatzResearch.FullTwoSoundness`. The declarations `admissible_preserves_gap`, `weak_rule_gives_gap`, and `gap_wellFounded` are included in the combined audit. The general rule-removal theorem and the prior equivalence with Collatz are cited, not re-formalized by this artifact.

The following prefixes abbreviate exact Lean namespaces:

| Prefix | Namespace |
|---|---|
| `FT` | `CollatzResearch.FullTwo` |
| `M` | `CollatzCertificate.FullTwoMatrix` |
| `L` | `CollatzResearch.FullTwoLower` |
| `S` | `CollatzResearch.FullTwoLowerScalar` |
| `U` | `CollatzResearch.FullTwoUpper` |
| `C` | `CollatzCertificate` |

All references below expand these prefixes. The scope of the first theorem is seven
nonnegative real affine maps on `Fin 2`, each with matrix entry `(0,0)`
at least one, and all eleven coefficientwise weak rules in the selected
orientation. The conclusion is equality of the first offsets for every
rule. Forward and reversed orientations are separate implications. The second theorem drops every diagonal bound and concludes two full offset-vector equalities for the reversed eligible rules, under nonnegativity and the same eleven reversed weak comparisons.

| Paper result | Exact declarations and sources | Scope and presentation |
|---|---|---|
| Main theorem: complete obstruction | `FT.forward_all_gaps_zero`, `FT.reversed_all_gaps_zero`, `FT.full_two_coordinate_obstruction` in [FullTwoCoordinate.lean](../formal/FullTwoCoordinate.lean) | Full scope above, with arbitrary admissible boundary maps. The paper gives a short assembly proof; Lean supplies the complete dependency chain. |
| Matrix reduction: common triangular orientation and unit first diagonals | `M.forward_common_orientation_and_first_diagonals`, `M.reversed_common_orientation_and_first_diagonals` in [FullTwoMatrixReduction.lean](../formal/FullTwoMatrixReduction.lean) | Matrix hypotheses only; the orientation is common to the five digits in the original coordinates. The paper gives the classification statements and their algebraic proofs. |
| Lower triangular affine case | `L.lower_forward_gaps_zero` in [FullTwoLowerForward.lean](../formal/FullTwoLowerForward.lean); `L.lower_reversed_gaps_zero` in [FullTwoLowerReversed.lean](../formal/FullTwoLowerReversed.lean) | Unit first diagonals and lower triangular digits; arbitrary admissible `C,D`. The paper states and proves the scalar classification, reversed cancellation, and exceptional-shape lemmas before applying them to both orientations. |
| Aggregate cancellation | `U.aggregate_nonneg`, `U.negative_aggregate_exact`, `U.exact_of_negative` in [FullTwoUpperBasic.lean](../formal/FullTwoUpperBasic.lean) | Exact affine swaps follow when a displayed aggregate coefficient is negative and both total `q` and total `k` are positive. The paper includes the algebraic argument. |
| Normalized upper case | `U.zero_gaps` in [FullTwoUpper.lean](../formal/FullTwoUpper.lean), combining `U.positive_zero_gaps` and `U.zero_binary_zero_gaps` | All 22 parameters are nonnegative; secondary slopes may vanish. The paper gives the classification statements and their algebraic proofs. |

The matrix proof in Section 3 uses the following declarations. These
intermediate statements carry their displayed branch hypotheses; those
hypotheses are derived or split exhaustively in the final reduction.

| Proof step | Declarations and source locations |
|---|---|
| Trace cancellation and exact swaps when both aggregate offdiagonals are positive | `C.commutator_power_trace_zero`, `C.nonnegative_commutator_zero_at_return` in [ReversedSwapRecurrence.lean](../formal/ReversedSwapRecurrence.lean); `M.exact_swaps_of_total_offdiagonal_positive` in [FullTwoMatrixAggregate.lean](../formal/FullTwoMatrixAggregate.lean). |
| Singular `F`: common left actions and a strictly positive row | `M.singular_middle_common_left` in [FullTwoMatrixSingularAlgebra.lean](../formal/FullTwoMatrixSingularAlgebra.lean); `M.common_left_row_positive` and `M.singular_middle_lower_entry_positive` in [FullTwoMatrixSingularSupport.lean](../formal/FullTwoMatrixSingularSupport.lean). |
| Singular `F`: recover right actions, squeeze the eigenvalues, and contradict rank one | `M.common_positive_left_product_fixed` in [FullTwoMatrixStationary.lean](../formal/FullTwoMatrixStationary.lean) requires the positive common left row, positive binary `(0,0)` entries, and both product-fixed identities. `M.common_actions_force_eigenvalues_one` and `M.singular_middle_contradiction` complete the branch in [FullTwoMatrixSingularSupport.lean](../formal/FullTwoMatrixSingularSupport.lean) and [FullTwoMatrixSingular.lean](../formal/FullTwoMatrixSingular.lean). |
| Exhaustive determinant split when `F` is invertible | `M.invertible_middle_determinant_cases` in [FullTwoMatrixDeterminants.lean](../formal/FullTwoMatrixDeterminants.lean). |
| Singular equal binary matrices | `M.equal_singular_common_actions`, `M.equal_singular_boundary_contradiction` in [FullTwoMatrixSingularEqual.lean](../formal/FullTwoMatrixSingularEqual.lean), using `M.common_rankone_contradiction` in [FullTwoMatrixCommonRankOne.lean](../formal/FullTwoMatrixCommonRankOne.lean). |
| Singular unequal binary matrices: projection shape and boundary contradiction | `M.singular_binary_unequal_shape` in [FullTwoMatrixSingularBinaryShape.lean](../formal/FullTwoMatrixSingularBinaryShape.lean); `M.binary_projection_boundary_impossible` in [FullTwoMatrixBinaryProjectionBoundary.lean](../formal/FullTwoMatrixBinaryProjectionBoundary.lean). The product order is `AB = αA`, `BA = αB`. |
| Nonsingular equal binary matrices | `M.nonsingular_digits_contradiction` in [FullTwoMatrixNonsingular.lean](../formal/FullTwoMatrixNonsingular.lean) derives `E = F = G`; `M.repeated_digits_contradiction` in [FullTwoMatrixRepeated.lean](../formal/FullTwoMatrixRepeated.lean) handles the boundaries. |
| Nonsingular unequal matrices: shape, nonnegative shifts, and the `μ ≤ 1/2` contradiction | `M.nonsingular_unequal_shape` in [FullTwoMatrixNonsingularShape.lean](../formal/FullTwoMatrixNonsingularShape.lean); `M.shifted_matrix_nonnegative`, `M.nonsingular_boundary_core`, `M.nonsingular_shape_boundary_impossible` in [FullTwoMatrixNonsingularBoundary.lean](../formal/FullTwoMatrixNonsingularBoundary.lean). |
| Triangular first diagonals and reversed matrix rules | `M.upper_first_diagonals_one`, `M.lower_first_diagonals_one` in [FullTwoMatrixFirstDiagonal.lean](../formal/FullTwoMatrixFirstDiagonal.lean); `M.reversed_rules_transpose` in [FullTwoMatrixTranspose.lean](../formal/FullTwoMatrixTranspose.lean). Transposition is used for matrix parts only. |

The lower and upper triangular analyses retain all affine cross terms and cover the following cases.

| Proof step | Declarations and source locations |
|---|---|
| Lower scalar classifications, including zero slopes | `S.forward_classification`, `S.forward_gaps_zero`, `S.reversed_gaps_zero` in [FullTwoLowerScalar.lean](../formal/FullTwoLowerScalar.lean); `S.reversed_offset_shape` in [FullTwoLowerScalarReverseShape.lean](../formal/FullTwoLowerScalarReverseShape.lean). Their application to arbitrary boundaries is in `L.lower_forward_parameters` and `L.lower_reversed_parameters`. |
| Exact boundary normalization and return to the original gaps | `FT.normalize_outer_weak`, `FT.normalize_inner_weak`, `FT.normalize_outer_gap_back`, `FT.normalize_inner_gap_back` in [FullTwoNormalize.lean](../formal/FullTwoNormalize.lean); the four assembled `FT.normalize_forward`, `FT.normalize_reversed`, `FT.denormalize_forward_gaps`, `FT.denormalize_reversed_gaps` in [FullTwoBoundaryTransfer.lean](../formal/FullTwoBoundaryTransfer.lean). |
| Transfer to the 22-parameter upper system | `FT.toUpperData_weak`, `FT.toUpperData_gaps` in [FullTwoUpperTransfer.lean](../formal/FullTwoUpperTransfer.lean), using `U.Weak` and `U.ZeroGaps` in [FullTwoUpperBasic.lean](../formal/FullTwoUpperBasic.lean). |
| Zero total `q` or zero total `k` | `U.q_zero_gaps`, `U.k_zero_gaps` in [FullTwoUpperDegenerate.lean](../formal/FullTwoUpperDegenerate.lean). No secondary-slope restriction is imposed. |
| Resonance, projected offsets, common fixed height, and matching-boundary contradiction | `U.triangular_resonance`, `U.common_form`, `U.projected_equalities`, `U.projected_zero_k`, `U.fixed_form_zero_k`, `U.matching_boundary_zero_k` in [FullTwoUpperAlgebra.lean](../formal/FullTwoUpperAlgebra.lean). The resonance lemma requires `α,β,ρ > 0`. The paper derives the resonant alternative by subtraction. Its fixed-height argument evaluates `cf` at `(0,η)` and gives the same conclusion as `fixed_form_zero_k`; the matching-boundary lemma is `matching_boundary_zero_k`. |
| Positive binary slopes, including zero ternary slopes and the `(1/2,1/3)` exception | `U.positive_slope_partition`, `U.zero_ternary_zero_k`, `U.positive_small_zero_k`, `U.low_ternary_zero_q`, `U.high_ternary_zero_k` in [FullTwoUpperPositive.lean](../formal/FullTwoUpperPositive.lean). The exceptional matching-boundary calculation is an internal branch of `positive_small_zero_k`. `U.unit_zero_gaps` in [FullTwoUpperUnit.lean](../formal/FullTwoUpperUnit.lean) handles all unit slopes. |
| One or both binary slopes zero | `U.zero_a_large_b_q`, `U.zero_b_large_a_q`, `U.zero_a_exact_zero_k`, `U.zero_b_exact_zero_k`, `U.both_zero_exact_zero_k` in [FullTwoUpperZero.lean](../formal/FullTwoUpperZero.lean). The `(0,0,0,1,0)` exceptional ternary pattern is an internal branch of `both_zero_exact_zero_k`. |
| Affine product reversal after upper normalization | `FT.flip_comp`, `FT.flip_weak`, `FT.flip_offset`, `FT.flip_reversed_weak` in [FullTwoFlip.lean](../formal/FullTwoFlip.lean); `FT.flip_forward_gaps_back` in [FullTwoBoundaryTransfer.lean](../formal/FullTwoBoundaryTransfer.lean); `FT.upper_reversed_gaps_zero` in [FullTwoUpperAffine.lean](../formal/FullTwoUpperAffine.lean). |
| Final affine assembly | `FT.forward_gaps_zero_of_triangular`, `FT.reversed_gaps_zero_of_triangular` in [FullTwoTriangular.lean](../formal/FullTwoTriangular.lean), followed by the three main declarations. |


The unrestricted reversed result in Section 7 uses the following declarations.
All names in this table start with `CollatzResearch`, except the explicitly
qualified `CollatzCertificate` names. No diagonal floor, coefficient cap,
normalization hypothesis, prescribed boundary shape, or invertibility
hypothesis remains in the final theorem.

| Proof step | Exact declarations and sources |
|---|---|
| Final vector equalities and exclusion of either strict eligible rule | `RealTwoCoordinate.reversed_eligible_offsets_equal`, `RealTwoCoordinate.strict_reversed_two_coordinate_contradiction`, and `RealTwoCoordinate.no_positive_eligible_offset_gap` in [CollatzReversedRealTwoCoordinate.lean](../formal/CollatzReversedRealTwoCoordinate.lean). |
| Growth under a fixed mixed-digit prefix | `RealMixedGrowth.real_reversed_mixed_row_growth` in [CollatzReversedRealMixedGrowth.lean](../formal/CollatzReversedRealMixedGrowth.lean). The paper supplies an elementary proof from the even/odd rank inequalities, using a finite negative-integer parity segment in the strict-odd case. |
| The binary products cannot satisfy `AB ≤ BA` under a strict eligible gap | `RealOrderedTwo.ordered_binary_matrices_exclude_two_dimensions` and `RealOrderedTwo.two_dimensional_binary_product_decrease` in [CollatzReversedRealOrderedTwo.lean](../formal/CollatzReversedRealOrderedTwo.lean). The paper reorders the support argument to use the already established nonzero readout row, then gives every forced matrix entry and the final offset contradiction. |
| Return paths and common triangular orientation under a strict eligible rule | `RealAllReturns.strict_reversed_all_returns_contradiction` in [CollatzReversedRealAllReturns.lean](../formal/CollatzReversedRealAllReturns.lean); `RealTriangularNecessity.strict_reversed_common_triangular_orientation` in [CollatzReversedRealTriangularNecessity.lean](../formal/CollatzReversedRealTriangularNecessity.lean). |
| Coordinate exchange preserves the original output coordinate of the strict gap | `RealCoordinateSwap.swap_coordinates_reversed_weak`, `RealCoordinateSwap.swap_coordinates_strict`, and `RealCoordinateSwap.lower_digits_swap_upper` in [CollatzReversedRealCoordinateSwap.lean](../formal/CollatzReversedRealCoordinateSwap.lean). The digits and `C` are conjugated; `D` receives only the input change. |
| Zero middle first diagonal | `RealTriangularZero.strict_upper_zero_middle_diagonal_contradiction` in [CollatzReversedRealTriangularZero.lean](../formal/CollatzReversedRealTriangularZero.lean). |
| Active diagonal values and contraction of the second coordinate | `RealTriangularPositive.positive_active_diagonal_values` in [CollatzReversedRealTriangularPositive.lean](../formal/CollatzReversedRealTriangularPositive.lean); `RealTriangularContracting.strict_upper_second_diagonal_lt_one` in [CollatzReversedRealTriangularContracting.lean](../formal/CollatzReversedRealTriangularContracting.lean). |
| Unit binary and ternary first diagonals | `RealTriangularUnit.upper_unit_first_diagonals_exclude_strict` in [CollatzReversedRealTriangularUnit.lean](../formal/CollatzReversedRealTriangularUnit.lean). This derives a modified model to which the theorem with diagonal bounds applies; it does not assume those bounds for the original boundaries. |
| Unit binary, subunit ternary first diagonals | `RealTriangularSubunit.upper_unit_stationary_row` and `RealTriangularSubunit.strict_upper_unit_subunit_ternary_contradiction` in [CollatzReversedRealTriangularSubunit.lean](../formal/CollatzReversedRealTriangularSubunit.lean). |
| Positive binary prefix, ternary bounds, and incompatible growth rates | `RealTriangularPrefix.positive_first_binary_prefix_of_nonzero_offset` and `RealTriangularPrefix.first_coordinate_binary_prefix_lower` in [CollatzReversedRealTriangularPrefix.lean](../formal/CollatzReversedRealTriangularPrefix.lean); `RealTriangularExpanding.strict_upper_expanding_active_diagonal_contradiction` in [CollatzReversedRealTriangularExpanding.lean](../formal/CollatzReversedRealTriangularExpanding.lean), using [ReversedTriangularTernaryBounds.lean](../formal/ReversedTriangularTernaryBounds.lean), [ReversedUpperTriangularRay.lean](../formal/ReversedUpperTriangularRay.lean), and [ReversedTriangularGrowthArithmetic.lean](../formal/ReversedTriangularGrowthArithmetic.lean). |
| Exhaustive upper-triangular case split | `RealTriangular.strict_upper_triangular_contradiction` in [CollatzReversedRealTriangular.lean](../formal/CollatzReversedRealTriangular.lean). |

The interpretation and gap definitions are in
[FullTwoBasic.lean](../formal/FullTwoBasic.lean),
[ReversedRealNormalization.lean](../formal/ReversedRealNormalization.lean),
and [ReversedBinaryPowerClosure.lean](../formal/ReversedBinaryPowerClosure.lean).
The [exact appendix](lean-statement-appendix.tex) reproduces the definitions and principal theorem types.

This obstruction concerns the specified first-offset strictness criterion.
It does not establish equality of full affine maps, exclude higher
dimensions or proper subsystems, or prove the Collatz conjecture.


Section 8 gives the following forward growth and contraction results. All names below start with `CollatzResearch`.

| Paper result or proof step | Exact declarations and sources | Scope |
|---|---|---|
| Every five conversion stages contain each root carry | `ForwardFiveCover.five_stage_cover` in [CollatzForwardFiveCover.lean](../formal/CollatzForwardFiveCover.lean); `ForwardRealWordGrowth.stage_five_cover` and `stage_five_cover_fin` in [CollatzForwardRealWordGrowth.lean](../formal/CollatzForwardRealWordGrowth.lean) | The seventeen rational cases include every endpoint; uniqueness of binary normalization transfers the cover to the conversion schedule. |
| Quantitative observed forward growth | `ForwardRealWordGrowth.Data.repeated_e_growth` in [CollatzForwardRealWordGrowth.lean](../formal/CollatzForwardRealWordGrowth.lean) | Any finite coordinate set, six nonnegative affine maps, and exactly nine weak comparisons in `Data`. The observed value includes the offset of `C`. No dynamic boundary map is assumed. |
| Contraction of the binary matrix A excludes all three forward root gaps | `ForwardRealContraction.observed_ternary_bounded_of_positive_subeigenrow` in [CollatzForwardRealContraction.lean](../formal/CollatzForwardRealContraction.lean); `ForwardRealWordGrowth.Data.eligible_offsets_eq_of_positive_subeigenrow` | A strictly positive left row for `A` has multiplier in `[0,1)`. The proof requires no corresponding contraction condition on `B`. |
| Explicit two-coordinate necessary condition | `ForwardRealTwoCoordinateNecessary.positive_subeigenrow_of_two_coordinate_bounds` and `positive_eligible_gap_requires_noncontraction` in [CollatzForwardRealTwoCoordinateNecessary.lean](../formal/CollatzForwardRealTwoCoordinateNecessary.lean) | A positive gap requires `A00 >= 1`, `A11 >= 1`, or `(1-A00)(1-A11) <= A01*A10`. This is necessary, not sufficient. |

These additions do not prove a complete unrestricted forward or higher-dimensional obstruction. The four forward modules are included in the same fresh combined verification as the main theorems. The artifact also retains four auxiliary reversed modules, described below, that are not used in the manuscript. The original 120 Lean files remain byte-identical to the preceding revision.


## Auxiliary checked algebra outside the manuscript

The following conditional results are retained for reproducibility. They are not claimed as contributions of the paper. In particular, the boundedness and eventual-stationarity assumptions in the last row are not consequences established for general reversed interpretations.

| Auxiliary result | Exact declarations and sources | Scope |
|---|---|---|
| Every observed maximal ternary power is nonzero under reversed strictness | `RealStationaryObstruction.strict_reversed_maximal_ternary_row_nonzero` in [CollatzReversedRealStationaryObstruction.lean](../formal/CollatzReversedRealStationaryObstruction.lean) | All finite dimensions; follows from the existing mixed-row growth theorem, including exponent zero. |
| Ordered powers and stationary observation | `RealOrderedPowers.ordered_scaled_row_power_le` and `ordered_stationary_profile_row_zero` in [CollatzReversedRealOrderedPowers.lean](../formal/CollatzReversedRealOrderedPowers.lean) | Uses `XY <= YX`, a nonnegative row, and the displayed scaled row inequality. Stationarity and boundedness are explicit hypotheses. |
| Final reversed stationary-profile obstruction | `RealWeakStationaryObstruction.weak_stationary_profile_excludes_strict` in [CollatzReversedRealWeakStationaryObstruction.lean](../formal/CollatzReversedRealWeakStationaryObstruction.lean) | Eleven reversed weak rules; `B = alpha X`, `G = beta Y`, `0 <= alpha < beta`; nonnegative `X,Y`, positive `v`, bounded `r X^n v`, and eventually stationary `Y^n v`. The original weak `GB` rule supplies the ordered matrix relation. No commutation equality or automatic stationarity is assumed. |

## Section 9: independent second proof of Said Duran’s theorem

The declarations in this table refer to the actual shortcut Collatz map on natural numbers, with odd step `(3*n + 1)/2`. `CPP` abbreviates `CollatzPositiveProgression`, `CAS` abbreviates `CollatzAffineSynchronization`, and `CPT` abbreviates `CollatzPowerTwo`.

| Paper claim | Lean declaration and source | Scope |
| --- | --- | --- |
| Dyadic progression law for iterates and odd counts | `CPP.iterate_oddCount_progression` in [CollatzAffineProgressions.lean](../formal/CollatzAffineProgressions.lean) | For every `k,a,t`, the endpoint increases by `3^(oddCount k a)*t` when the start increases by `2^k*t`; the odd count is unchanged. |
| Every nonnegative gap has a positive coalescing progression | `CPP.every_gap_has_a_positive_coalescing_progression` in [PositiveProgressionCoalescence.lean](../formal/PositiveProgressionCoalescence.lean) | Common time and odd count, for every member of one dyadic progression. |
| Odd coefficients allow parameter refinement | `CollatzOddAffineParameter.exists_large_odd_affine_parameter` in [OddAffineParameter.lean](../formal/OddAffineParameter.lean) | Any prescribed residue modulo a power of two is attained with an arbitrarily large nonnegative parameter. |
| Synchronization of two affine families | `CAS.synchronizes_all` in [AffineFamilySynchronization.lean](../formal/AffineFamilySynchronization.lean) | Families `a + 3^r*t` and `b + 3^s*t` synchronize after restricting `t` to one dyadic progression; the exponents may differ. |
| Finite-pattern coalescence | `CPP.every_finite_pattern_coalesces` in [FinitePatternCoalescence.lean](../formal/FinitePatternCoalescence.lean) | Every finite set of natural offsets has a positive translating progression with a common endpoint progression and equal odd counts. |
| Power-of-two specialization | `CPT.power_two_in_every_unit_progression` in [PowerTwoModuloThree.lean](../formal/PowerTwoModuloThree.lean) | If `b % 3 ≠ 0`, then `b + 3^n*t = 2^s` for arbitrarily large `t`. |
| Unit endpoint and exclusion of an earlier hit | `CPP.coalescing_distinct_equal_count_endpoint_unit` and `CPP.common_progression_has_equal_first_hitting_times` in [ProgressionConvergenceSpecialization.lean](../formal/ProgressionConvergenceSpecialization.lean) | Distinct coalescing starts with equal odd counts force a common endpoint not divisible by three. Positive parameter values keep all earlier iterates above one. |
| Equal finite first hitting times for every finite pattern; consecutive-run corollary | `CPP.every_finite_pattern_has_equal_first_hitting_times` and `CPP.arbitrarily_long_consecutive_equal_first_hitting_times` in [FinitePatternConvergence.lean](../formal/FinitePatternConvergence.lean) | For every finite pattern and lower bound there exists a larger translating integer. Every member first reaches one at a common finite time, with the same odd count. This is an existence theorem for translates, not convergence from an arbitrary fixed start. |

The nine-module closure of these results is included in the combined fresh build and axiom audit. The prose consequence for the unaccelerated map follows by inserting the omitted even steps; the Lean theorem types use nonnegative offsets and the shortcut map. Priority for the equal-height existence theorem belongs to [Said Duran’s earlier preprint](https://doi.org/10.5281/zenodo.23003526). Section 9 gives an independent second proof. The finite-pattern statement is equivalent to the consecutive-run statement by restriction to a run containing the requested offsets.
