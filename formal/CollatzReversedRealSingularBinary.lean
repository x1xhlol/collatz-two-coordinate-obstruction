import CollatzReversedRealMiddleRankExtension
import ReversedTwoDimensionalInvertibleMiddle
import CollatzReversedRealProjectionAlgebra
import CollatzReversedRealAbovePowers

namespace CollatzResearch.RealSingularBinary

open Matrix CollatzCertificate RealAffine
open TwoDimensionalSwapAlgebra TwoDimensionalInvertibleMiddle

set_option maxHeartbeats 800000

theorem zero_offdiagonal_power (M : M2) (i j : Fin 2)
    (hne : i ≠ j) (hz : M i j = 0) (n : ℕ) : (M ^ n) i j = 0 := by
  induction n with
  | zero => rw [pow_zero, Matrix.one_apply_ne hne]
  | succ n ih =>
    rw [pow_succ]
    fin_cases i <;> fin_cases j
    · exact False.elim (hne rfl)
    · change M 0 1 = 0 at hz
      change (M ^ n) 0 1 = 0 at ih
      change ((M ^ n) * M) 0 1 = 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two, hz, ih,
        mul_zero, zero_mul, add_zero]
    · change M 1 0 = 0 at hz
      change (M ^ n) 1 0 = 0 at ih
      change ((M ^ n) * M) 1 0 = 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two, hz, ih,
        mul_zero, zero_mul, add_zero]
    · exact False.elim (hne rfl)

theorem projection_positive_column_of_returns (A B E F G : M2) (α β : ℝ)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B)
    (hAA : A * A = α • A) (hAB : A * B = α • B)
    (hE : E = (β / α) • A) (hF : F = β • (1 : M2)) (hG : G = (β / α) • B)
    (hreturn : ∀ i j : Fin 2, ∃ k : ℕ, 0 < (((A + B) + (E + F + G)) ^ k) j i) :
    ∃ u : Vec (Fin 2), (∀ i, 0 < u i) ∧ A *ᵥ u = α • u := by
  let H := (A + B) + (E + F + G)
  have hpos (i j : Fin 2) (hne : i ≠ j) : 0 < (A + B) i j := by
    by_contra hp
    have hle : A i j + B i j ≤ 0 := le_of_not_gt hp
    have ha0 : 0 ≤ A i j := hA i j
    have hb0 : 0 ≤ B i j := hB i j
    have ha : A i j = 0 := by linarith only [hle, ha0, hb0]
    have hb : B i j = 0 := by linarith only [hle, ha0, hb0]
    have hh : H i j = 0 := by
      simp only [H, hE, hF, hG, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply_ne hne, ha, hb, mul_zero, add_zero]
    obtain ⟨k, hk⟩ := hreturn j i
    have hz := zero_offdiagonal_power H i j hne hh k
    change 0 < (H ^ k) i j at hk
    rw [hz] at hk
    exact (lt_irrefl 0) hk
  let u : Vec (Fin 2) := (A + B) *ᵥ (fun _ => 1)
  refine ⟨u, ?_, ?_⟩
  · intro i
    fin_cases i
    · change 0 < u 0
      dsimp [u]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_one]
      exact add_pos_of_nonneg_of_pos (add_nonneg (hA 0 0) (hB 0 0))
        (hpos 0 1 (by decide))
    · change 0 < u 1
      dsimp [u]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_one]
      exact add_pos_of_pos_of_nonneg (hpos 1 0 (by decide))
        (add_nonneg (hA 1 1) (hB 1 1))
  · dsimp [u]
    rw [mulVec_mulVec, Matrix.mul_add, hAA, hAB, ← smul_add, smul_mulVec]

theorem strict_reversed_binary_matrices_invertible_of_returns
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hreturn : ∀ i j : Fin 2, ∃ k : ℕ,
      0 < (((A.matrix + B.matrix) + (E.matrix + F.matrix + G.matrix)) ^ k) j i) :
    A.matrix.det ≠ 0 ∧ B.matrix.det ≠ 0 := by
  have hf := RealMiddleRankExtension.strict_reversed_middle_invertible_of_returns
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict hreturn
  have hs : ReversedExactSwaps A.matrix B.matrix E.matrix F.matrix G.matrix :=
    reversed_swap_equalities_of_all_returns A.matrix B.matrix E.matrix F.matrix G.matrix
      hA.1 hB.1 hE.1 hF.1 hG.1 h.ea.1 h.fa.1 h.ga.1 h.eb.1 h.fb.1 h.gb.1 hreturn
  have hdet : A.matrix.det = B.matrix.det := by
    have hh := forward_binary_invariants A.matrixᵀ B.matrixᵀ E.matrixᵀ F.matrixᵀ G.matrixᵀ
      (reversed_exact_swaps_transpose _ _ _ _ _ hs)
      (by simpa only [Matrix.det_transpose] using hf)
      (fun i j => hA.1 j i) (fun i j => hB.1 j i)
    simpa only [Matrix.det_transpose] using hh.1
  have hne : A.matrix * B.matrix ≠ B.matrix * A.matrix := by
    intro hc
    apply RealOrderedTwo.ordered_binary_matrices_exclude_two_dimensions
      A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict
    intro i j
    rw [hc]
  have hnA : A.matrix.det ≠ 0 := by
    intro ha
    have hb : B.matrix.det = 0 := hdet.symm.trans ha
    obtain ⟨α, β, hα, _hβ, _htA, _htB, hAA, hAB, hBA, hBB, hFI, hEA, hGB⟩ :=
      singular_binary_projection_of_no_shared_row A.matrix B.matrix E.matrix F.matrix G.matrix
        (D.matrix i₀) hs ha hb hf hA.1 hB.1 hF.1 hne
        (fun α hα heigen => RealAbovePowers.real_second_row_not_first_eigenrow
          A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict α hα heigen)
    obtain ⟨u, hu, hAu⟩ := projection_positive_column_of_returns
      A.matrix B.matrix E.matrix F.matrix G.matrix α β hA.1 hB.1
      hAA hAB hEA hFI hGB hreturn
    have hg := RealProjectionAlgebra.positive_binary_projection_gaps_zero
      A B C D E F G i₀ α (β / α) hA hB hC hD hE hF hG h
      hAA hAB hBA hBB hEA
      (by simpa only [div_mul_cancel₀ β (ne_of_gt hα)] using hFI)
      hGB u hu hAu
    rcases hstrict with ht | ht
    · exact (ne_of_gt ht) hg.1
    · exact (ne_of_gt ht) hg.2
  exact ⟨hnA, fun hb => hnA (hdet.trans hb)⟩

end CollatzResearch.RealSingularBinary

#print axioms CollatzResearch.RealSingularBinary.zero_offdiagonal_power
#print axioms CollatzResearch.RealSingularBinary.projection_positive_column_of_returns
#print axioms CollatzResearch.RealSingularBinary.strict_reversed_binary_matrices_invertible_of_returns
