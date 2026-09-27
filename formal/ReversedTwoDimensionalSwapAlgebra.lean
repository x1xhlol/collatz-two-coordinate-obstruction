import ReversedSwapRecurrence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

namespace CollatzCertificate.TwoDimensionalSwapAlgebra

open Matrix

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

def tr (A : M2) : ℝ := A 0 0 + A 1 1

def delta (A B : M2) : ℝ := (A * B - B * A).det

def combo (A B : M2) (x y z w : ℝ) : M2 :=
  x • 1 + y • A + z • B + w • (A * B)

def coordinates (A : M2) : Fin 3 → ℝ := ![A 0 1, A 1 0, A 1 1 - A 0 0]

def coordinateMatrix (A B : M2) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![A 0 1, B 0 1, (A * B) 0 1;
     A 1 0, B 1 0, (A * B) 1 0;
     A 1 1 - A 0 0, B 1 1 - B 0 0, (A * B) 1 1 - (A * B) 0 0]

theorem coordinateMatrix_det (A B : M2) : (coordinateMatrix A B).det = delta A B := by
  simp [coordinateMatrix, delta, det_fin_three, det_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

theorem coordinates_combo (A B : M2) (x y z w : ℝ) :
    coordinates (combo A B x y z w) = coordinateMatrix A B *ᵥ ![y, z, w] := by
  ext i
  fin_cases i <;>
    simp [coordinates, combo, coordinateMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem combo_exists (A B X : M2) (h : delta A B ≠ 0) :
    ∃ x y z w, X = combo A B x y z w := by
  have hu : IsUnit (coordinateMatrix A B) :=
    (coordinateMatrix A B).isUnit_iff_isUnit_det.mpr
      (isUnit_iff_ne_zero.mpr (by simpa only [coordinateMatrix_det] using h))
  obtain ⟨v, hv⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hu) (coordinates X)
  let x := X 0 0 - v 0 * A 0 0 - v 1 * B 0 0 - v 2 * (A * B) 0 0
  refine ⟨x, v 0, v 1, v 2, ?_⟩
  have vv : ![v 0, v 1, v 2] = v := by ext i; fin_cases i <;> rfl
  have hc : coordinates (combo A B x (v 0) (v 1) (v 2)) = coordinates X := by
    rw [coordinates_combo, vv, hv]
  have h01 := congrFun hc 0
  have h10 := congrFun hc 1
  have h11 := congrFun hc 2
  dsimp [coordinates] at h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j
  · simp [combo, x]; ring
  · exact h01.symm
  · exact h10.symm
  · simp [combo, x] at h11 ⊢
    linarith only [h11]

theorem combo_unique (A B : M2) (h : delta A B ≠ 0)
    (x y z w x' y' z' w' : ℝ)
    (he : combo A B x y z w = combo A B x' y' z' w') :
    x = x' ∧ y = y' ∧ z = z' ∧ w = w' := by
  have hu : IsUnit (coordinateMatrix A B) :=
    (coordinateMatrix A B).isUnit_iff_isUnit_det.mpr
      (isUnit_iff_ne_zero.mpr (by simpa only [coordinateMatrix_det] using h))
  have hc := congrArg coordinates he
  rw [coordinates_combo, coordinates_combo] at hc
  have hv := (Matrix.mulVec_injective_iff_isUnit.mpr hu) hc
  have hy : y = y' := congrFun hv 0
  have hz : z = z' := congrFun hv 1
  have hw : w = w' := congrFun hv 2
  refine ⟨?_, hy, hz, hw⟩
  have h00 := congrFun (congrFun he 0) 0
  simp [combo, hy, hz, hw] at h00
  linarith only [h00]

theorem combo_mul_A (A B : M2) (x y z w : ℝ) :
    combo A B x y z w * A = combo A B
      ((tr (A * B) - tr A * tr B) * z - A.det * tr B * w - A.det * y)
      (tr A * y + tr B * z + tr (A * B) * w + x)
      (tr A * z + A.det * w) (-z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [combo, tr, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two] <;> ring

theorem A_mul_combo (A B : M2) (x y z w : ℝ) :
    A * combo A B x y z w = combo A B (-A.det * y)
      (x + tr A * y) (-A.det * w) (z + tr A * w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [combo, tr, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two] <;> ring

theorem combo_mul_B (A B : M2) (x y z w : ℝ) :
    combo A B x y z w * B = combo A B (-B.det * z) (-B.det * w)
      (x + tr B * z) (y + tr B * w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [combo, tr, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two] <;> ring

theorem B_mul_combo (A B : M2) (x y z w : ℝ) :
    B * combo A B x y z w = combo A B
      ((tr (A * B) - tr A * tr B) * y - tr A * B.det * w - B.det * z)
      (tr B * y + B.det * w)
      (tr A * y + tr B * z + tr (A * B) * w + x) (-y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [combo, tr, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two] <;> ring

theorem delta_discriminants (A B : M2) :
    4 * delta A B = (tr A ^ 2 - 4 * A.det) * (tr B ^ 2 - 4 * B.det) -
      (2 * tr (A * B) - tr A * tr B) ^ 2 := by
  simp [delta, tr, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two]
  ring

theorem delta_swap (A B : M2) : delta B A = delta A B := by
  simp [delta, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two]
  ring

theorem centralizer_span (A B X : M2) (hd : delta A B ≠ 0)
    (hcomm : X * A = A * X) : ∃ x y : ℝ, X = x • 1 + y • A := by
  obtain ⟨x, y, z, w, rfl⟩ := combo_exists A B X hd
  rw [combo_mul_A, A_mul_combo] at hcomm
  obtain ⟨_, h2, h3, h4⟩ := combo_unique A B hd _ _ _ _ _ _ _ _ hcomm
  have hd1 : (tr A ^ 2 - 4 * A.det) * w = 0 := by
    linear_combination -tr A * h4 - 2 * h3
  have hd2 : (2 * tr (A * B) - tr A * tr B) * w = 0 := by
    linear_combination 2 * h2 + tr B * h4
  have hz : delta A B * w = 0 := by
    linear_combination w / 4 * delta_discriminants A B +
      (tr B ^ 2 - 4 * B.det) / 4 * hd1 -
      (2 * tr (A * B) - tr A * tr B) / 4 * hd2
  have hw : w = 0 := (mul_eq_zero.mp hz).resolve_left hd
  have hzz : z = 0 := by rw [hw] at h4; linarith only [h4]
  exact ⟨x, y, by simp [combo, hw, hzz]⟩

theorem exact_swaps_force_middle_zero (A B E F G : M2)
    (ha : 0 ≤ tr A) (hb : 0 ≤ tr B) (hd : delta A B ≠ 0)
    (hea : E * A = A * E) (hfa : F * A = B * E)
    (hga : G * A = A * F) (heb : E * B = B * F)
    (hfb : F * B = A * G) (hgb : G * B = B * G) : F = 0 := by
  obtain ⟨x, y, hE⟩ := centralizer_span A B E hd hea
  obtain ⟨z, w, hG⟩ := centralizer_span B A G (by simpa only [delta_swap] using hd) hgb
  have he : E = combo A B x y 0 0 := by simpa [combo] using hE
  have hg : G = combo A B z 0 w 0 := by simpa [combo] using hG
  obtain ⟨f0, f1, f2, f3, hf⟩ := combo_exists A B F hd
  rw [hf, he, combo_mul_A, B_mul_combo] at hfa
  rw [hg, hf, combo_mul_A, A_mul_combo] at hga
  rw [he, hf, combo_mul_B, B_mul_combo] at heb
  rw [hf, hg, combo_mul_B, A_mul_combo] at hfb
  obtain ⟨fa0, fa1, fa2, fa3⟩ := combo_unique A B hd _ _ _ _ _ _ _ _ hfa
  obtain ⟨ga0, ga1, ga2, ga3⟩ := combo_unique A B hd _ _ _ _ _ _ _ _ hga
  obtain ⟨eb0, eb1, eb2, eb3⟩ := combo_unique A B hd _ _ _ _ _ _ _ _ heb
  obtain ⟨fb0, fb1, fb2, fb3⟩ := combo_unique A B hd _ _ _ _ _ _ _ _ hfb
  simp only [mul_zero, add_zero, zero_add, sub_zero] at fa0 fa1 fa2 fa3 ga0 ga1 ga2 ga3 eb0 eb1 eb2 eb3 fb0 fb1 fb2 fb3
  have hf2 : f2 = y := by linarith only [fa3]
  have hf1 : f1 = -y := by linarith only [eb3]
  have hf0 : f0 = -tr B * y := by rw [hf2] at fb2; linarith only [fb2]
  have hw : w = -y + tr B * f3 := by rw [hf1] at fb3; linarith only [fb3]
  have hs : (tr A + tr B) * f3 = 0 := by
    rw [hf2, hw] at ga3
    linear_combination -ga3
  have hcy : (tr A + tr B) * y = tr (A * B) * f3 := by
    rw [hf1, hf2, hf0] at fa1
    linear_combination -fa1
  have hay : tr A * y = (tr A * tr B + A.det) * f3 := by
    rw [hw] at ga2
    linear_combination -ga2
  have hf3 : f3 = 0 := by
    by_cases hs0 : tr A + tr B = 0
    · have ha0 : tr A = 0 := by linarith only [ha, hb, hs0]
      have hb0 : tr B = 0 := by linarith only [ha, hb, hs0]
      have hc : tr (A * B) * f3 = 0 := by
        rw [ha0, hb0] at hcy
        linarith only [hcy]
      have halpha : A.det * f3 = 0 := by
        rw [ha0, hb0] at hay
        linarith only [hay]
      have hdelta := delta_discriminants A B
      rw [ha0, hb0] at hdelta
      have hz : delta A B * f3 = 0 := by
        linear_combination f3 / 4 * hdelta + 4 * B.det * halpha - tr (A * B) * hc
      exact (mul_eq_zero.mp hz).resolve_left hd
    · exact (mul_eq_zero.mp hs).resolve_left hs0
  have hy : y = 0 := by
    by_cases hs0 : tr A + tr B = 0
    · have ha0 : tr A = 0 := by linarith only [ha, hb, hs0]
      have hb0 : tr B = 0 := by linarith only [ha, hb, hs0]
      have halpha : A.det * y = 0 := by
        rw [hf1, hf2, hf3, ha0, hb0] at fa0
        nlinarith only [fa0]
      have hc : tr (A * B) * y = 0 := by
        rw [hw, hf1, hf3, ha0, hb0] at ga0
        nlinarith only [ga0, halpha]
      have hdelta := delta_discriminants A B
      rw [ha0, hb0] at hdelta
      have hz : delta A B * y = 0 := by
        linear_combination y / 4 * hdelta + 4 * B.det * halpha - tr (A * B) * hc
      exact (mul_eq_zero.mp hz).resolve_left hd
    · rw [hf3, mul_zero] at hcy
      exact (mul_eq_zero.mp hcy).resolve_left hs0
  rw [hf, hf0, hf1, hf2, hf3, hy]
  simp [combo]

end CollatzCertificate.TwoDimensionalSwapAlgebra

#print axioms CollatzCertificate.TwoDimensionalSwapAlgebra.coordinateMatrix_det
#print axioms CollatzCertificate.TwoDimensionalSwapAlgebra.coordinates_combo
#print axioms CollatzCertificate.TwoDimensionalSwapAlgebra.combo_exists
#print axioms CollatzCertificate.TwoDimensionalSwapAlgebra.combo_unique
#print axioms CollatzCertificate.TwoDimensionalSwapAlgebra.combo_mul_A
#print axioms CollatzCertificate.TwoDimensionalSwapAlgebra.A_mul_combo
#print axioms CollatzCertificate.TwoDimensionalSwapAlgebra.combo_mul_B
#print axioms CollatzCertificate.TwoDimensionalSwapAlgebra.B_mul_combo
#print axioms CollatzCertificate.TwoDimensionalSwapAlgebra.delta_discriminants
#print axioms CollatzCertificate.TwoDimensionalSwapAlgebra.delta_swap
#print axioms CollatzCertificate.TwoDimensionalSwapAlgebra.centralizer_span
#print axioms CollatzCertificate.TwoDimensionalSwapAlgebra.exact_swaps_force_middle_zero
