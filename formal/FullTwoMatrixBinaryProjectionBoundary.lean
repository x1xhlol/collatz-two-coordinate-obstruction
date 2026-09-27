import FullTwoMatrixNonsingularBoundary

namespace CollatzCertificate.FullTwoMatrix

open Matrix TwoDimensionalSwapAlgebra TwoDimensionalMiddleRank

set_option maxHeartbeats 800000

theorem boundary_product00_positive (X Y : M2)
    (hX : EntrywiseLE 0 X) (hY : EntrywiseLE 0 Y)
    (hx : 1 ≤ X 0 0) (hy : 1 ≤ Y 0 0) : 0 < (X*Y) 0 0 := by
  have hp := mul_pos (lt_of_lt_of_le zero_lt_one hx) (lt_of_lt_of_le zero_lt_one hy)
  have hn := mul_nonneg (hX 0 1) (hY 1 0)
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  linarith only [hp, hn]

theorem binary_projection_boundary_impossible (A B C D E F G : M2) (μ β : ℝ)
    (hμ : 0 < μ) (_hβ : 0 < β)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B)
    (hC : EntrywiseLE 0 C) (hD : EntrywiseLE 0 D)
    (hA00 : 1 ≤ A 0 0) (hB00 : 1 ≤ B 0 0)
    (hC00 : 1 ≤ C 0 0) (hD00 : 1 ≤ D 0 0)
    (hw : WeakRules A B C D E F G)
    (htrA : tr A = μ) (htrB : tr B = μ)
    (hdetA : A.det = 0) (hdetB : B.det = 0)
    (hAB : A*B = μ • A) (hBA : B*A = μ • B)
    (hE : E = (β/μ) • A) (hF : F = β • (1 : M2)) (hG : G = (β/μ) • B)
    (h01 : 0 < ((A+B)+(E+F+G)) 0 1)
    (h10 : 0 < ((A+B)+(E+F+G)) 1 0) : False := by
  have hAA : A*A = μ • A := by
    rw [square_trace_identity, htrA, hdetA, zero_smul, sub_zero]
  have hβμ : β ≤ μ := by
    have hp := boundary_product00_positive B D hB hD hB00 hD00
    have hh := hw.bd 0 0
    rw [hG, Matrix.smul_mul] at hh
    simp only [Matrix.smul_apply, smul_eq_mul] at hh
    have hh' : (β/μ) * (B*D) 0 0 ≤ 1 * (B*D) 0 0 := by simpa using hh
    have hratio := le_of_mul_le_mul_right hh' hp
    exact (div_le_one hμ).mp hratio
  have hμβ : μ^2 ≤ β := by
    have hp := boundary_product00_positive C A hC hA hC00 hA00
    have hh := boundary_mul_right_mono _ _ A hw.cf hA 0 0
    have hAAA : (A*A)*A = (μ^2) • A := by
      rw [hAA, Matrix.smul_mul, hAA, smul_smul]
      congr 1
      ring
    rw [Matrix.mul_assoc C (A*A) A, hAAA, Matrix.mul_smul, hF,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at hh
    simp only [Matrix.smul_apply, smul_eq_mul] at hh
    exact le_of_mul_le_mul_right hh hp
  have hμ1 : 1 ≤ μ := by
    have hn := hA 1 1
    change 0 ≤ A 1 1 at hn
    simp only [tr] at htrA
    linarith only [htrA, hA00, hn]
  have μ1 : μ = 1 := by nlinarith only [hμ1, hμβ, hβμ]
  have β1 : β = 1 := by nlinarith only [hμβ, hβμ, μ1]
  have a00 : A 0 0 = 1 := by
    have hn := hA 1 1
    change 0 ≤ A 1 1 at hn
    simp only [tr] at htrA
    linarith only [htrA, hA00, hn, μ1]
  have a11 : A 1 1 = 0 := by simp only [tr] at htrA; linarith only [htrA, a00, μ1]
  have b00 : B 0 0 = 1 := by
    have hn := hB 1 1
    change 0 ≤ B 1 1 at hn
    simp only [tr] at htrB
    linarith only [htrB, hB00, hn, μ1]
  have b11 : B 1 1 = 0 := by simp only [tr] at htrB; linarith only [htrB, b00, μ1]
  have haa0 : A 0 1 * A 1 0 = 0 := by
    simp only [Matrix.det_fin_two, a11, mul_zero, zero_sub] at hdetA
    linarith only [hdetA]
  have hbb0 : B 0 1 * B 1 0 = 0 := by
    simp only [Matrix.det_fin_two, b11, mul_zero, zero_sub] at hdetB
    linarith only [hdetB]
  have hab0 : A 0 1 * B 1 0 = 0 := by
    have hh := congrFun (congrFun hAB 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
      a00, b00, μ1, one_mul] at hh
    linarith only [hh]
  have hba0 : B 0 1 * A 1 0 = 0 := by
    have hh := congrFun (congrFun hBA 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
      a00, b00, μ1, one_mul] at hh
    linarith only [hh]
  have he : E = A := by simpa only [μ1, β1, div_one, one_smul] using hE
  have hf : F = (1 : M2) := by simpa only [β1, one_smul] using hF
  have hg : G = B := by simpa only [μ1, β1, div_one, one_smul] using hG
  rw [he, hf, hg] at h01 h10
  simp only [Matrix.add_apply] at h01 h10
  have h01' : 0 < A 0 1 + B 0 1 := by simpa using h01
  have h10' : 0 < A 1 0 + B 1 0 := by simpa using h10
  have hp := mul_pos h01' h10'
  nlinarith only [hp, haa0, hbb0, hab0, hba0]

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.binary_projection_boundary_impossible
