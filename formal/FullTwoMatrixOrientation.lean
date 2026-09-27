import FullTwoMatrixAggregate

namespace CollatzCertificate.FullTwoMatrix

open Matrix

theorem upper_of_aggregate_lower_zero (A B E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (h10 : ((A+B)+(E+F+G)) 1 0=0) : Upper A B E F G := by
  simp only [Matrix.add_apply] at h10
  have h1 : 0 ≤ A 1 0 := hA 1 0
  have h2 : 0 ≤ B 1 0 := hB 1 0
  have h3 : 0 ≤ E 1 0 := hE 1 0
  have h4 : 0 ≤ F 1 0 := hF 1 0
  have h5 : 0 ≤ G 1 0 := hG 1 0
  exact ⟨by linarith only [h10,h1,h2,h3,h4,h5], by linarith only [h10,h1,h2,h3,h4,h5],
    by linarith only [h10,h1,h2,h3,h4,h5], by linarith only [h10,h1,h2,h3,h4,h5],
    by linarith only [h10,h1,h2,h3,h4,h5]⟩

theorem lower_of_aggregate_upper_zero (A B E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (h01 : ((A+B)+(E+F+G)) 0 1=0) : Lower A B E F G := by
  simp only [Matrix.add_apply] at h01
  have h1 : 0 ≤ A 0 1 := hA 0 1
  have h2 : 0 ≤ B 0 1 := hB 0 1
  have h3 : 0 ≤ E 0 1 := hE 0 1
  have h4 : 0 ≤ F 0 1 := hF 0 1
  have h5 : 0 ≤ G 0 1 := hG 0 1
  exact ⟨by linarith only [h01,h1,h2,h3,h4,h5], by linarith only [h01,h1,h2,h3,h4,h5],
    by linarith only [h01,h1,h2,h3,h4,h5], by linarith only [h01,h1,h2,h3,h4,h5],
    by linarith only [h01,h1,h2,h3,h4,h5]⟩

theorem orientation_of_not_positive_offdiagonals (A B E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hn : ¬(0 < ((A+B)+(E+F+G)) 0 1 ∧ 0 < ((A+B)+(E+F+G)) 1 0)) :
    Upper A B E F G ∨ Lower A B E F G := by
  by_cases h10 : ((A+B)+(E+F+G)) 1 0=0
  · exact Or.inl (upper_of_aggregate_lower_zero A B E F G hA hB hE hF hG h10)
  have hp10 : 0 < ((A+B)+(E+F+G)) 1 0 :=
    lt_of_le_of_ne (add_nonneg (add_nonneg (hA 1 0) (hB 1 0))
      (add_nonneg (add_nonneg (hE 1 0) (hF 1 0)) (hG 1 0))) (Ne.symm h10)
  have h01 : ((A+B)+(E+F+G)) 0 1=0 := by
    apply le_antisymm
    · exact le_of_not_gt (fun hp01 => hn ⟨hp01,hp10⟩)
    · exact add_nonneg (add_nonneg (hA 0 1) (hB 0 1))
        (add_nonneg (add_nonneg (hE 0 1) (hF 0 1)) (hG 0 1))
  exact Or.inr (lower_of_aggregate_upper_zero A B E F G hA hB hE hF hG h01)

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.orientation_of_not_positive_offdiagonals
