import FullTwoBasic

namespace CollatzResearch.FullTwo

open Matrix CollatzCertificate

set_option linter.unusedSimpArgs false

def identity : Aff2 := ⟨1, 0⟩

theorem identity_comp (X : Aff2) : identity.comp X = X := by
  apply affine_ext <;> simp [identity, Affine.comp]

theorem identity_upper : Upper identity := by simp [identity, Upper]

noncomputable def outerBoundary (C : Aff2) : Aff2 := upper (C.matrix 0 1 / C.matrix 0 0) 0 0 0

def innerBoundary (D : Aff2) : Aff2 := upper 0 0 0 (D.offset 1)

theorem outerBoundary_upper (C : Aff2) : Upper (outerBoundary C) := by
  simp [outerBoundary, upper, Upper]

theorem innerBoundary_upper (D : Aff2) : Upper (innerBoundary D) := by
  simp [innerBoundary, upper, Upper]

theorem outerBoundary_admissible (C : Aff2) (hC : Admissible C) :
    Admissible (outerBoundary C) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [outerBoundary, upper]
    exact div_nonneg (hC.1.1 0 1) (hC.1.1 0 0)
  · intro i
    fin_cases i <;> simp [outerBoundary, upper]
  · simp [outerBoundary, upper]

theorem innerBoundary_admissible (D : Aff2) (hD : Admissible D) :
    Admissible (innerBoundary D) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [innerBoundary, upper]
  · intro i
    fin_cases i <;> simp [innerBoundary, upper]
    exact hD.1.2 1
  · simp [innerBoundary, upper]

theorem scaled_row_eq (a b x y : ℝ) (ha : a ≠ 0) :
    a * (x + b / a * y) = a * x + b * y := by
  field_simp

theorem scaled_row_le (a b x y u v : ℝ) (ha : 0 < a)
    (h : a * x + b * y ≤ a * u + b * v) :
    x + b / a * y ≤ u + b / a * v := by
  apply (mul_le_mul_iff_right₀ ha).mp
  simpa only [scaled_row_eq _ _ _ _ (ne_of_gt ha)] using h

theorem normalize_outer_weak (C X Y : Aff2) (hC : 0 < C.matrix 0 0)
    (h : (C.comp X).Weak (C.comp Y)) :
    ((outerBoundary C).comp X).Weak ((outerBoundary C).comp Y) := by
  constructor
  · intro i j
    fin_cases i
    · have hj := h.1 0 j
      simp only [Affine.comp, Matrix.mul_apply, Fin.sum_univ_two] at hj
      simpa only [outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, le_refl] using
        scaled_row_le _ _ _ _ _ _ hC hj
    · simp only [outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, le_refl]
  · intro i
    fin_cases i
    · have hj := h.2 0
      simp only [Affine.comp, Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hj
      have hh := (add_le_add_iff_right (C.offset 0)).mp hj
      simpa only [outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, le_refl] using
        scaled_row_le _ _ _ _ _ _ hC hh
    · simp only [outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, le_refl]

theorem normalize_outer_gap_back (C X Y : Aff2) (hC : 0 < C.matrix 0 0)
    (h : ((outerBoundary C).comp X).offset 0 = ((outerBoundary C).comp Y).offset 0) :
    (C.comp X).offset 0 = (C.comp Y).offset 0 := by
  simp only [outerBoundary, upper, Affine.comp, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.of_apply, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_mul, add_zero] at h
  have hh := congrArg (fun t => C.matrix 0 0 * t) h
  dsimp only at hh
  rw [scaled_row_eq _ _ _ _ (ne_of_gt hC), scaled_row_eq _ _ _ _ (ne_of_gt hC)] at hh
  simp only [Affine.comp, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply]
  rw [hh]

theorem normalize_inner_weak (D X Y : Aff2) (hX : Upper X) (hY : Upper Y)
    (h : (X.comp D).Weak (Y.comp D)) :
    (X.comp (innerBoundary D)).Weak (Y.comp (innerBoundary D)) := by
  rw [eq_upper X hX, eq_upper Y hY] at *
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, le_refl]
  · intro i
    fin_cases i
    · have hh := h.2 0
      simp only [outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, le_refl] at hh ⊢
      linarith
    · simpa only [outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, le_refl]
        using h.2 1

theorem normalize_inner_gap_back (D X Y : Aff2) (hX : Upper X) (hY : Upper Y)
    (h : (X.comp (innerBoundary D)).offset 0 = (Y.comp (innerBoundary D)).offset 0) :
    (X.comp D).offset 0 = (Y.comp D).offset 0 := by
  rw [eq_upper X hX, eq_upper Y hY] at *
  simp only [outerBoundary, innerBoundary, upper, Affine.comp, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, one_mul, zero_mul, mul_zero, zero_add, add_zero, le_refl] at h ⊢
  linarith

end CollatzResearch.FullTwo

#print axioms CollatzResearch.FullTwo.identity_comp
#print axioms CollatzResearch.FullTwo.identity_upper
#print axioms CollatzResearch.FullTwo.outerBoundary_upper
#print axioms CollatzResearch.FullTwo.innerBoundary_upper
#print axioms CollatzResearch.FullTwo.outerBoundary_admissible
#print axioms CollatzResearch.FullTwo.innerBoundary_admissible
#print axioms CollatzResearch.FullTwo.scaled_row_eq
#print axioms CollatzResearch.FullTwo.scaled_row_le
#print axioms CollatzResearch.FullTwo.normalize_outer_weak
#print axioms CollatzResearch.FullTwo.normalize_outer_gap_back
#print axioms CollatzResearch.FullTwo.normalize_inner_weak
#print axioms CollatzResearch.FullTwo.normalize_inner_gap_back
