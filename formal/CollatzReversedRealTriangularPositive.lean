import CollatzReversedRealTriangularReadout

namespace CollatzResearch.RealTriangularPositive

open Matrix CollatzCertificate RealAffine RealOrderedTwo

theorem positive_active_diagonal_values
    (A B C D E F G : Affine (Fin 2)) (i₀ i j : Fin 2) (hne : i ≠ j)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (ha0 : A.matrix j i=0) (hb0 : B.matrix j i=0) (he0 : E.matrix j i=0)
    (hf0 : F.matrix j i=0) (_hg0 : G.matrix j i=0) (hfpos : 0 < F.matrix i i) :
    A.matrix i i=B.matrix i i ∧ E.matrix i i=F.matrix i i ∧
      G.matrix i i=F.matrix i i ∧ 1 ≤ A.matrix i i ∧
      0 < F.matrix i i ∧ F.matrix i i ≤ A.matrix i i := by
  obtain ⟨_hr,ha,hb,hgb⟩ := RealTriangularReadout.strict_triangular_active_diagonal_bounds
    A B C D E F G i₀ i j hne hA hB hC hD hE hF hG h hstrict ha0 hb0
  have hmul (X Y : Mat (Fin 2)) (hy : Y j i=0) : (X*Y) i i=X i i*Y i i := by
    rw [Matrix.mul_apply,sum_two_coordinates i j hne,hy,mul_zero,add_zero]
  obtain ⟨_hea,hfa,hga,heb,_hfb,_hgb⟩ := reversed_swap_equalities_on_diagonal
    A.matrix B.matrix E.matrix F.matrix G.matrix hA.1 hB.1 hE.1 hF.1 hG.1
      h.ea.1 h.fa.1 h.ga.1 h.eb.1 h.fb.1 h.gb.1 i
  rw [hmul F.matrix A.matrix ha0,hmul B.matrix E.matrix he0] at hfa
  rw [hmul G.matrix A.matrix ha0,hmul A.matrix F.matrix hf0] at hga
  rw [hmul E.matrix B.matrix hb0,hmul B.matrix F.matrix hf0] at heb
  have haPos : 0 < A.matrix i i := lt_of_lt_of_le zero_lt_one ha
  have hef : E.matrix i i=F.matrix i i := by nlinarith only [heb,hb]
  have hgf : G.matrix i i=F.matrix i i := by nlinarith only [hga,haPos]
  have hab : A.matrix i i=B.matrix i i := by rw [hef] at hfa; nlinarith only [hfa,hfpos]
  exact ⟨hab,hef,hgf,ha,hfpos,by rw [← hgf,hab]; exact hgb⟩

end CollatzResearch.RealTriangularPositive

#print axioms CollatzResearch.RealTriangularPositive.positive_active_diagonal_values
