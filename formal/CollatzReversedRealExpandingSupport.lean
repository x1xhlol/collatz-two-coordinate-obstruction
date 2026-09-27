import CollatzReversedRealNonsingularEigen

namespace CollatzResearch.RealExpandingSupport

open Matrix CollatzCertificate RealAffine
open FullTwoMatrix TwoDimensionalInvertibleMiddle TwoDimensionalNonsingularEigen

theorem strict_reversed_binary_support_of_returns
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hreturn : ∀ i j : Fin 2, ∃ k : ℕ,
      0 < (((A.matrix+B.matrix)+(E.matrix+F.matrix+G.matrix))^k) j i) :
    (∀ i, 0 < A.matrix i i) ∧ (∀ i, 0 < B.matrix i i) ∧
      0 < (A.matrix+B.matrix) 0 1 ∧ 0 < (A.matrix+B.matrix) 1 0 := by
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
  obtain ⟨μ,t,hμ,_ht,htrA,htrB,hdetA,hdetB,_hAN,_hNA,he,hfshape,hg⟩ :=
    reversed_nonsingular_unequal_shape A.matrix B.matrix E.matrix F.matrix G.matrix
      hs hA.1 hB.1 hE.1 hF.1 hG.1 ha hf hne
  have hH : EntrywiseLE 0 ((A.matrix+B.matrix)+(E.matrix+F.matrix+G.matrix)) := fun i j =>
    add_nonneg (add_nonneg (hA.1 i j) (hB.1 i j))
      (add_nonneg (add_nonneg (hE.1 i j) (hF.1 i j)) (hG.1 i j))
  have h01 := positive_offdiagonal_of_return _ hH 0 1 (by decide) (hreturn 1 0)
  have h10 := positive_offdiagonal_of_return _ hH 1 0 (by decide) (hreturn 0 1)
  have hPpos (i j : Fin 2) (hne : i ≠ j)
      (hij : 0 < ((A.matrix+B.matrix)+(E.matrix+F.matrix+G.matrix)) i j) :
      0 < (A.matrix+B.matrix) i j := by
    have hn : 0 ≤ A.matrix i j+B.matrix i j := add_nonneg (hA.1 i j) (hB.1 i j)
    rw [he,hfshape,hg] at hij
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply_ne hne,mul_zero,sub_zero,two_smul] at hij
    change 0 < A.matrix i j+B.matrix i j
    by_contra hh
    have hz : A.matrix i j+B.matrix i j=0 := by linarith only [hn,hh]
    have hz' := congrArg (fun x : ℝ => (1+3*t)*x) hz
    nlinarith only [hij,hz']
  refine ⟨?_,?_,hPpos 0 1 (by decide) h01,hPpos 1 0 (by decide) h10⟩
  · intro i
    have hi := shifted_matrix_nonnegative A.matrix μ hμ hA.1 htrA hdetA i i
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply_eq,mul_one] at hi
    change 0 ≤ A.matrix i i-μ at hi
    linarith only [hi,hμ]
  · intro i
    have hi := shifted_matrix_nonnegative B.matrix μ hμ hB.1 htrB hdetB i i
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply_eq,mul_one] at hi
    change 0 ≤ B.matrix i i-μ at hi
    linarith only [hi,hμ]

end CollatzResearch.RealExpandingSupport

#print axioms CollatzResearch.RealExpandingSupport.strict_reversed_binary_support_of_returns
