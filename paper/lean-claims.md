# Paper claims and Lean declarations

This companion maps the results and substantive proof steps in
[the paper](two-coordinate-obstruction.tex) to their Lean sources.
The paper states the supporting classifications and gives the algebraic arguments used in the proof. The table below maps those steps to the formal declarations. The [combined verification report](../verification/rebuild.json) records a fresh build of all 120 local modules and an axiom audit of 515 public theorems and lemmas plus 69 definitions. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. The standalone entry point is [verify.py](../verify.py).

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
The [exact appendix](lean-statement-appendix.tex) reproduces the definitions and both final theorem types.

This obstruction concerns the specified first-offset strictness criterion.
It does not establish equality of full affine maps, exclude higher
dimensions or proper subsystems, or prove the Collatz conjecture.
