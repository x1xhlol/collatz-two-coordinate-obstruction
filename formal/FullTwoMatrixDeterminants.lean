import FullTwoMatrixAggregate

namespace CollatzCertificate.FullTwoMatrix

open Matrix

theorem invertible_middle_determinant_cases (A B E F G : M2)
    (hs : ExactSwaps A B E F G) (hf : F.det ≠ 0) :
    (A.det=0 ∧ B.det=0) ∨
    (A.det≠0 ∧ B.det≠0 ∧ E.det≠0 ∧ G.det≠0) := by
  have haf := congrArg Matrix.det hs.2.1
  have hag := congrArg Matrix.det hs.2.2.1
  have hbe := congrArg Matrix.det hs.2.2.2.1
  simp only [Matrix.det_mul] at haf hag hbe
  have hab : A.det=B.det := by
    apply mul_right_cancel₀ hf
    nlinarith only [haf, hbe]
  by_cases ha : A.det=0
  · exact Or.inl ⟨ha, hab ▸ ha⟩
  · right
    have hb : B.det≠0 := by simpa only [← hab] using ha
    have hef : E.det=F.det := by
      apply mul_left_cancel₀ hb
      nlinarith only [hbe]
    have hgf : G.det=F.det := by
      apply mul_left_cancel₀ ha
      nlinarith only [hag]
    exact ⟨ha, hb, hef ▸ hf, hgf ▸ hf⟩

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.invertible_middle_determinant_cases
