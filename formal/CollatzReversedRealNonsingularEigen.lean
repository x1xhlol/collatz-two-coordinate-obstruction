import ReversedTwoDimensionalNonsingularEigen
import CollatzReversedRealSingularBinary

namespace CollatzResearch.RealNonsingularEigen

open Matrix CollatzCertificate RealAffine
open TwoDimensionalInvertibleMiddle TwoDimensionalNonsingularEigen

theorem strict_reversed_common_positive_eigenvector_of_returns
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hreturn : ∀ i j : Fin 2, ∃ k : ℕ,
      0 < (((A.matrix+B.matrix)+(E.matrix+F.matrix+G.matrix))^k) j i) :
    ∃ l m : ℝ, ∃ u : Vec (Fin 2), 1 ≤ l ∧ 0 < m ∧ m ≤ l ∧ (∀ i, 0 < u i) ∧
      A.matrix *ᵥ u=l • u ∧ B.matrix *ᵥ u=l • u ∧
      E.matrix *ᵥ u=m • u ∧ F.matrix *ᵥ u=m • u ∧ G.matrix *ᵥ u=m • u := by
  have hf := RealMiddleRankExtension.strict_reversed_middle_invertible_of_returns
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict hreturn
  have ha := (RealSingularBinary.strict_reversed_binary_matrices_invertible_of_returns
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict hreturn).1
  have hs : ReversedExactSwaps A.matrix B.matrix E.matrix F.matrix G.matrix :=
    reversed_swap_equalities_of_all_returns A.matrix B.matrix E.matrix F.matrix G.matrix
      hA.1 hB.1 hE.1 hF.1 hG.1 h.ea.1 h.fa.1 h.ga.1 h.eb.1 h.fb.1 h.gb.1 hreturn
  have hne : A.matrix*B.matrix ≠ B.matrix*A.matrix := by
    intro hc
    apply RealOrderedTwo.ordered_binary_matrices_exclude_two_dimensions
      A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict
    intro i j
    rw [hc]
  let r : Vec (Fin 2) := D.matrix i₀
  have hr : 0 ≤ r := fun j => hD.1 i₀ j
  have hrne : r ≠ 0 := by
    intro hz
    have hda : (D.comp A).offset i₀=D.offset i₀ := by
      change r ⬝ᵥ A.offset+D.offset i₀=D.offset i₀
      rw [hz,zero_dotProduct,zero_add]
    have hdb : (D.comp B).offset i₀=(D.comp G).offset i₀ := by
      change r ⬝ᵥ B.offset+D.offset i₀=r ⬝ᵥ G.offset+D.offset i₀
      rw [hz,zero_dotProduct,zero_dotProduct]
    rcases hstrict with ht | ht
    · exact (ne_of_gt ht) hda
    · exact (ne_of_gt ht) hdb
  obtain ⟨μ,κ,u,_hμ,hκ,hl,hml,hu,hAu,hBu,hEu,hFu,hGu⟩ :=
    nonsingular_eigenvector_with_bounds A.matrix B.matrix E.matrix F.matrix G.matrix r
      hs hA.1 hB.1 hE.1 hF.1 hG.1 ha hf hne hreturn hr hrne
      (fun j => h.da.1 i₀ j) (fun j => h.db.1 i₀ j)
  exact ⟨2*μ,3*κ,u,hl,mul_pos (by norm_num) hκ,hml,hu,hAu,hBu,hEu,hFu,hGu⟩

end CollatzResearch.RealNonsingularEigen

#print axioms CollatzResearch.RealNonsingularEigen.strict_reversed_common_positive_eigenvector_of_returns
