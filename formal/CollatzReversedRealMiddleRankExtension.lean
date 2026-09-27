import ReversedTwoDimensionalMiddleRankExtension
import CollatzReversedRealMiddleRank
import CollatzReversedRealCommutatorTwo

namespace CollatzResearch.RealMiddleRankExtension

open Matrix CollatzCertificate RealAffine RealMixedGrowth
open TwoDimensionalSwapAlgebra TwoDimensionalMiddleRankExtension

theorem strict_reversed_mixed_matrix_nonzero
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (w : List MixedSupport.Digit) :
    matrixWord (fun k => (affineDigit A B E F G k).matrix) w ≠ 0 := by
  intro hz
  obtain ⟨j, hj, _⟩ := RealRowContraction.mixed_word_second_row_nondecrease
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict w
  simp [hz] at hj

theorem strict_reversed_middle_invertible_of_returns
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hreturn : ∀ i j : Fin 2, ∃ k : ℕ,
      0 < (((A.matrix + B.matrix) + (E.matrix + F.matrix + G.matrix)) ^ k) j i) :
    F.matrix.det ≠ 0 := by
  intro hd
  have ht := RealMiddleRank.strict_reversed_singular_middle_trace_positive
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict hd
  have haf : A.matrix * F.matrix ≠ 0 := by
    simpa only [matrixWord, affineDigit, Matrix.mul_one] using
      strict_reversed_mixed_matrix_nonzero A B C D E F G i₀
        hA hB hC hD hE hF hG h hstrict [.a, .f]
  have hbf : B.matrix * F.matrix ≠ 0 := by
    simpa only [matrixWord, affineDigit, Matrix.mul_one] using
      strict_reversed_mixed_matrix_nonzero A B C D E F G i₀
        hA hB hC hD hE hF hG h hstrict [.b, .f]
  obtain ⟨hea, hfa, hga, heb, hfb, hgb⟩ := reversed_swap_equalities_of_all_returns
    A.matrix B.matrix E.matrix F.matrix G.matrix hA.1 hB.1 hE.1 hF.1 hG.1
    h.ea.1 h.fa.1 h.ga.1 h.eb.1 h.fb.1 h.gb.1 hreturn
  have hc : A.matrix * B.matrix = B.matrix * A.matrix := by
    by_cases hb : tr B.matrix = 0
    · by_cases ha : tr A.matrix = 0
      · apply zero_traces_commute_of_singular_commutator
          A.matrix B.matrix hA.1 hB.1 ha hb
        exact RealCommutatorTwo.strict_reversed_binary_commutator_singular
          A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict
      · exact (singular_middle_commutes_of_nonzero_binary_product
          B.matrix A.matrix G.matrix F.matrix E.matrix ha (ne_of_gt ht) hd haf
          hgb hfb heb hga hfa hea).symm
    · exact singular_middle_commutes_of_nonzero_binary_product
        A.matrix B.matrix E.matrix F.matrix G.matrix hb (ne_of_gt ht) hd hbf
        hea hfa hga heb hfb hgb
  apply RealOrderedTwo.ordered_binary_matrices_exclude_two_dimensions
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict
  intro i j
  rw [hc]

end CollatzResearch.RealMiddleRankExtension

#print axioms CollatzResearch.RealMiddleRankExtension.strict_reversed_mixed_matrix_nonzero
#print axioms CollatzResearch.RealMiddleRankExtension.strict_reversed_middle_invertible_of_returns
