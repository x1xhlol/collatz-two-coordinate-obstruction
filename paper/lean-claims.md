# Paper claims and Lean declarations

This companion maps the results and substantive proof steps in
[the paper](two-coordinate-obstruction.tex) to their Lean sources.
The numbered results are fully formalized; the paper compresses the algebraic case analyses. The [combined verification report](../verification/rebuild.json) records a fresh build of all 51 local modules and an axiom audit of all 225 public theorems and lemmas. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. The standalone entry point is [verify.py](../verify.py).

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

All references below expand these prefixes. The main scope is seven
nonnegative real affine maps on `Fin 2`, each with matrix entry `(0,0)`
at least one, and all eleven coefficientwise weak rules in the selected
orientation. The conclusion is equality of the first offsets for every
rule. Forward and reversed orientations are separate implications.

| Paper result | Exact declarations and sources | Scope and presentation |
|---|---|---|
| Theorem 1: complete obstruction | `FT.forward_all_gaps_zero`, `FT.reversed_all_gaps_zero`, `FT.full_two_coordinate_obstruction` in [FullTwoCoordinate.lean](../formal/FullTwoCoordinate.lean) | Full scope above, with arbitrary admissible boundary maps. The paper gives a short assembly proof; Lean supplies the complete dependency chain. |
| Lemma 2: common triangular orientation and unit first diagonals | `M.forward_common_orientation_and_first_diagonals`, `M.reversed_common_orientation_and_first_diagonals` in [FullTwoMatrixReduction.lean](../formal/FullTwoMatrixReduction.lean) | Matrix hypotheses only; the orientation is common to the five digits in the original coordinates. The paper explicitly gives a proof outline. |
| Proposition 3: lower triangular affine case | `L.lower_forward_gaps_zero` in [FullTwoLowerForward.lean](../formal/FullTwoLowerForward.lean); `L.lower_reversed_gaps_zero` in [FullTwoLowerReversed.lean](../formal/FullTwoLowerReversed.lean) | Unit first diagonals and lower triangular digits; arbitrary admissible `C,D`. Both paper proofs compress the scalar classifications; all branches are formalized. |
| Lemma 4: aggregate cancellation | `U.aggregate_nonneg`, `U.negative_aggregate_exact`, `U.exact_of_negative` in [FullTwoUpperBasic.lean](../formal/FullTwoUpperBasic.lean) | Exact affine swaps follow when a displayed aggregate coefficient is negative and both total `q` and total `k` are positive. The paper includes the algebraic argument. |
| Proposition 5: normalized upper case | `U.zero_gaps` in [FullTwoUpper.lean](../formal/FullTwoUpper.lean), combining `U.positive_zero_gaps` and `U.zero_binary_zero_gaps` | All 22 parameters are nonnegative; secondary slopes may vanish. The paper explicitly gives a proof outline. |

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
| Resonance and projected common-form contradiction | `U.triangular_resonance`, `U.common_form`, `U.projected_equalities`, `U.projected_zero_k`, `U.fixed_form_zero_k`, `U.matching_boundary_zero_k` in [FullTwoUpperAlgebra.lean](../formal/FullTwoUpperAlgebra.lean). The resonance lemma requires `α,β,ρ > 0`. |
| Positive binary slopes, including zero ternary slopes and the `(1/2,1/3)` exception | `U.positive_slope_partition`, `U.zero_ternary_zero_k`, `U.positive_small_zero_k`, `U.low_ternary_zero_q`, `U.high_ternary_zero_k` in [FullTwoUpperPositive.lean](../formal/FullTwoUpperPositive.lean). The exceptional matching-boundary calculation is an internal branch of `positive_small_zero_k`. `U.unit_zero_gaps` in [FullTwoUpperUnit.lean](../formal/FullTwoUpperUnit.lean) handles all unit slopes. |
| One or both binary slopes zero | `U.zero_a_large_b_q`, `U.zero_b_large_a_q`, `U.zero_a_exact_zero_k`, `U.zero_b_exact_zero_k`, `U.both_zero_exact_zero_k` in [FullTwoUpperZero.lean](../formal/FullTwoUpperZero.lean). The `(0,0,0,1,0)` exceptional ternary pattern is an internal branch of `both_zero_exact_zero_k`. |
| Affine product reversal after upper normalization | `FT.flip_comp`, `FT.flip_weak`, `FT.flip_offset`, `FT.flip_reversed_weak` in [FullTwoFlip.lean](../formal/FullTwoFlip.lean); `FT.flip_forward_gaps_back` in [FullTwoBoundaryTransfer.lean](../formal/FullTwoBoundaryTransfer.lean); `FT.upper_reversed_gaps_zero` in [FullTwoUpperAffine.lean](../formal/FullTwoUpperAffine.lean). |
| Final affine assembly | `FT.forward_gaps_zero_of_triangular`, `FT.reversed_gaps_zero_of_triangular` in [FullTwoTriangular.lean](../formal/FullTwoTriangular.lean), followed by the three declarations of Theorem 1. |

The interpretation and gap definitions are in
[FullTwoBasic.lean](../formal/FullTwoBasic.lean),
[ReversedRealNormalization.lean](../formal/ReversedRealNormalization.lean),
and [ReversedBinaryPowerClosure.lean](../formal/ReversedBinaryPowerClosure.lean).
The [exact appendix](lean-statement-appendix.tex) reproduces the definitions and final theorem type.

This obstruction concerns the specified first-offset strictness criterion.
It does not establish equality of full affine maps, exclude higher
dimensions or proper subsystems, or prove the Collatz conjecture.
