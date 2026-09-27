import ReversedTwoDimensionalMiddleRank
import CollatzReversedRealOrderedTwo

namespace CollatzResearch.RealMiddleRank

open Matrix CollatzCertificate RealAffine RealMixedGrowth
open TwoDimensionalSwapAlgebra TwoDimensionalMiddleRank

theorem strict_reversed_middle_square_nonzero
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) : F.matrix * F.matrix ≠ 0 := by
  intro hz
  obtain ⟨j, hj, _⟩ := RealRowContraction.mixed_word_second_row_nondecrease
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict [.f, .f]
  simp [matrixWord, affineDigit, hz] at hj

theorem strict_reversed_singular_middle_trace_positive
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hdet : F.matrix.det = 0) : 0 < tr F.matrix := by
  have hn : 0 ≤ tr F.matrix := add_nonneg (hF.1 0 0) (hF.1 1 1)
  by_contra ht
  have hz : tr F.matrix = 0 := le_antisymm (le_of_not_gt ht) hn
  apply strict_reversed_middle_square_nonzero A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict
  rw [square_trace_identity, hz, hdet, zero_smul, zero_smul, sub_zero]

theorem strict_reversed_middle_invertible_of_returns_and_binary_traces
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (ha : tr A.matrix ≠ 0) (hb : tr B.matrix ≠ 0)
    (hreturn : ∀ i j : Fin 2, ∃ k : ℕ,
      0 < (((A.matrix + B.matrix) + (E.matrix + F.matrix + G.matrix)) ^ k) j i) :
    F.matrix.det ≠ 0 := by
  intro hd
  have ht := strict_reversed_singular_middle_trace_positive
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict hd
  obtain ⟨_, hf, hg, heb, hfb, _⟩ := reversed_swap_equalities_of_all_returns
    A.matrix B.matrix E.matrix F.matrix G.matrix hA.1 hB.1 hE.1 hF.1 hG.1
    h.ea.1 h.fa.1 h.ga.1 h.eb.1 h.fb.1 h.gb.1 hreturn
  have hc := singular_middle_commutes_binary_of_nonzero_traces
    A.matrix B.matrix E.matrix F.matrix G.matrix ha hb (ne_of_gt ht) hd hf hg heb hfb
  apply RealOrderedTwo.ordered_binary_matrices_exclude_two_dimensions
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict
  intro i j
  rw [hc]

end CollatzResearch.RealMiddleRank

#print axioms CollatzResearch.RealMiddleRank.strict_reversed_middle_square_nonzero
#print axioms CollatzResearch.RealMiddleRank.strict_reversed_singular_middle_trace_positive
#print axioms CollatzResearch.RealMiddleRank.strict_reversed_middle_invertible_of_returns_and_binary_traces
