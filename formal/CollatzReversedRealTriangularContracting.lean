import CollatzReversedRealTriangularReadout
import CollatzReversedRealTriangularZeroBasic

namespace CollatzResearch.RealTriangularContracting

open Matrix CollatzCertificate RealAffine

theorem strict_upper_second_diagonal_lt_one
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (ha0 : A.matrix 1 0=0) (hb0 : B.matrix 1 0=0) : A.matrix 1 1 < 1 := by
  obtain ⟨hr0,ha00,hb00,_hgb⟩ := RealTriangularReadout.strict_triangular_active_diagonal_bounds
    A B C D E F G i₀ 0 1 (by decide) hA hB hC hD hE hF hG h hstrict ha0 hb0
  by_contra hn
  have ha11 : 1 ≤ A.matrix 1 1 := le_of_not_gt hn
  have hI : EntrywiseLE 1 A.matrix := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact ha00
    · exact hA.1 0 1
    · exact hA.1 1 0
    · exact ha11
  obtain ⟨hrg,hqa⟩ := RealTriangularZeroBasic.reversed_identity_zero_gaps
    A B C D E F G i₀ hA hB hC hD h hI
  let r : Vec (Fin 2) := D.matrix i₀
  let q := r ᵥ* B.matrix
  have hr : 0 ≤ r := fun i => hD.1 i₀ i
  have hq : 0 ≤ q := rowMul_nonneg hr hB.1
  have hq0 : 0 < q 0 :=
    RealTriangularReadout.strict_triangular_second_row_positive A B C D E F G i₀ 0 1
      (by decide) hA hB hC hD hE hF hG h hstrict ha0
  change q ⬝ᵥ A.offset=0 at hqa
  have hterm (i : Fin 2) : q i*A.offset i=0 :=
    congrFun ((Fintype.sum_eq_zero_iff_of_nonneg
      (fun k => mul_nonneg (hq k) (hA.2 k))).mp hqa) i
  have haoff0 : A.offset 0=0 := (mul_eq_zero.mp (hterm 0)).resolve_left (ne_of_gt hq0)
  have hsecond : r 1*A.offset 1=0 := by
    by_cases hr1 : r 1=0
    · rw [hr1,zero_mul]
    have hr1pos : 0 < r 1 := lt_of_le_of_ne (hr 1) (Ne.symm hr1)
    have hq1 : 0 < q 1 := by
      by_cases hb11 : B.matrix 1 1=0
      · have hdec := RealOrderedTwo.two_dimensional_binary_product_decrease A B C D E F G i₀
          hA hB hC hD hE hF hG h hstrict
        have hlt := RealTriangularNecessity.upper_binary_product_decrease A.matrix B.matrix ha0 hb0 hdec
        simp only [Matrix.mul_apply,Fin.sum_univ_two,hb11,mul_zero,add_zero] at hlt
        have hb01 : 0 < B.matrix 0 1 := by
          by_contra hn01
          have hz : B.matrix 0 1=0 := le_antisymm (le_of_not_gt hn01) (hB.1 0 1)
          rw [hz,zero_mul,mul_zero,add_zero] at hlt
          exact (not_lt_of_ge (mul_nonneg hb00.le (hA.1 0 1))) hlt
        change 0 < ∑ k, r k*B.matrix k 1
        rw [Fin.sum_univ_two]
        exact add_pos_of_pos_of_nonneg (mul_pos hr0 hb01) (mul_nonneg (hr 1) (hB.1 1 1))
      · have hb11pos : 0 < B.matrix 1 1 := lt_of_le_of_ne (hB.1 1 1) (Ne.symm hb11)
        change 0 < ∑ k, r k*B.matrix k 1
        rw [Fin.sum_univ_two]
        exact add_pos_of_nonneg_of_pos (mul_nonneg (hr 0) (hB.1 0 1)) (mul_pos hr1pos hb11pos)
    have haoff1 : A.offset 1=0 := (mul_eq_zero.mp (hterm 1)).resolve_left (ne_of_gt hq1)
    rw [haoff1,mul_zero]
  have hra : r ⬝ᵥ A.offset=0 := by
    rw [dotProduct,Fin.sum_univ_two,haoff0,mul_zero,zero_add,hsecond]
  rcases hstrict with hs | hs
  · change D.offset i₀ < r ⬝ᵥ A.offset+D.offset i₀ at hs
    rw [hra,zero_add] at hs
    exact (lt_irrefl _) hs
  · change D.matrix i₀ ⬝ᵥ G.offset+D.offset i₀ < D.matrix i₀ ⬝ᵥ B.offset+D.offset i₀ at hs
    rw [hrg] at hs
    exact (lt_irrefl _) hs

end CollatzResearch.RealTriangularContracting

#print axioms CollatzResearch.RealTriangularContracting.strict_upper_second_diagonal_lt_one
