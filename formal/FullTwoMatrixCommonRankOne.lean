import FullTwoMatrixSingularSupport

namespace CollatzCertificate.FullTwoMatrix

open Matrix

local notation "tr₂" => TwoDimensionalSwapAlgebra.tr

theorem common_rankone_eigenvalues_one (A B C D E F G R : M2) (a beta : ℝ)
    (hA : EntrywiseLE 0 A) (hC : EntrywiseLE 0 C) (hD : EntrywiseLE 0 D)
    (hR : EntrywiseLE 0 R)
    (hA₀ : 1 ≤ A 0 0) (hC₀ : 1 ≤ C 0 0) (hD₀ : 1 ≤ D 0 0) (hR₀ : 0 < R 0 0)
    (h : WeakRules A B C D E F G)
    (hRA : R*A=a • R) (hRB : R*B=a • R) (hRG : R*G=beta • R)
    (hAR : A*R=a • R) (hFR : F*R=beta • R) : a=1 ∧ beta=1 := by
  have hcpos : 0 < C 0 0 := by linarith only [hC₀]
  have hdpos : 0 < D 0 0 := by linarith only [hD₀]
  have haone : 1 ≤ a := by
    have heq := congrFun (congrFun hRA 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul] at heq
    have hn1 := mul_nonneg (hR 0 1) (hA 1 0)
    have hn2 := mul_nonneg (le_of_lt hR₀) (sub_nonneg.mpr hA₀)
    nlinarith only [heq, hn1, hn2, hR₀]
  have hRD : 0 < (R*D) 0 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_pos_of_pos_of_nonneg (mul_pos hR₀ hdpos) (mul_nonneg (hR 0 1) (hD 1 0))
  have hCR : 0 < (C*R) 0 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_pos_of_pos_of_nonneg (mul_pos hcpos hR₀) (mul_nonneg (hC 0 1) (hR 1 0))
  have hba : beta ≤ a := by
    have hbd := nonnegative_mul_left R (G*D) (B*D) hR h.bd
    rw [← mul_assoc, ← mul_assoc, hRG, hRB, Matrix.smul_mul, Matrix.smul_mul] at hbd
    have h00 := hbd 0 0
    change beta*(R*D) 0 0 ≤ a*(R*D) 0 0 at h00
    nlinarith only [h00, hRD]
  have haa : a*a ≤ beta := by
    have hcf := nonnegative_mul_right R (C*(A*A)) (C*F) hR h.cf
    have hleft : (C*(A*A))*R=(a*a) • (C*R) := by
      calc
        (C*(A*A))*R = C*(A*(A*R)) := by simp only [mul_assoc]
        _ = (a*a) • (C*R) := by
          rw [hAR, Matrix.mul_smul, hAR, Matrix.mul_smul, Matrix.mul_smul, smul_smul]
    have hright : (C*F)*R=beta • (C*R) := by
      rw [mul_assoc, hFR, Matrix.mul_smul]
    rw [hleft, hright] at hcf
    have h00 := hcf 0 0
    change (a*a)*(C*R) 0 0 ≤ beta*(C*R) 0 0 at h00
    nlinarith only [h00, hCR]
  constructor <;> nlinarith only [haone, hba, haa, sq_nonneg (a-1)]

theorem common_rankone_contradiction (A B C D E F G R : M2) (a beta kappa : ℝ)
    (hA : EntrywiseLE 0 A) (hC : EntrywiseLE 0 C) (hD : EntrywiseLE 0 D)
    (hR : EntrywiseLE 0 R)
    (hA₀ : 1 ≤ A 0 0) (hC₀ : 1 ≤ C 0 0) (hD₀ : 1 ≤ D 0 0) (hR₀ : 1 ≤ R 0 0)
    (h : WeakRules A B C D E F G)
    (hRA : R*A=a • R) (hRB : R*B=a • R) (hRG : R*G=beta • R)
    (hAR : A*R=a • R) (hFR : F*R=beta • R)
    (hRH : R*((A+B)+(E+F+G))=kappa • R)
    (hHR : ((A+B)+(E+F+G))*R=kappa • R)
    (hdet : R.det=0) (htr : tr₂ R=a)
    (h01 : 0 < ((A+B)+(E+F+G)) 0 1)
    (h10 : 0 < ((A+B)+(E+F+G)) 1 0) : False := by
  have hrpos : 0 < R 0 0 := by linarith only [hR₀]
  obtain ⟨haone, _⟩ := common_rankone_eigenvalues_one A B C D E F G R a beta
    hA hC hD hR hA₀ hC₀ hD₀ hrpos h hRA hRB hRG hAR hFR
  have hr01 : 0 < R 0 1 := by
    by_contra hn
    have hz : R 0 1=0 := le_antisymm (le_of_not_gt hn) (hR 0 1)
    have heq := congrFun (congrFun hRH 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
      hz, zero_mul, mul_zero, add_zero] at heq
    exact (ne_of_gt (mul_pos hrpos h01)) heq
  have hr10 : 0 < R 1 0 := by
    by_contra hn
    have hz : R 1 0=0 := le_antisymm (le_of_not_gt hn) (hR 1 0)
    have heq := congrFun (congrFun hHR 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
      hz, zero_mul, mul_zero, add_zero] at heq
    exact (ne_of_gt (mul_pos h10 hrpos)) heq
  have hr11 : R 1 1=0 := by
    have hn : 0 ≤ R 1 1 := hR 1 1
    dsimp [TwoDimensionalSwapAlgebra.tr] at htr
    linarith only [htr, haone, hR₀, hn]
  have hp := mul_pos hr01 hr10
  simp only [Matrix.det_fin_two, hr11, mul_zero, zero_sub] at hdet
  linarith only [hdet, hp]

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.common_rankone_eigenvalues_one
#print axioms CollatzCertificate.FullTwoMatrix.common_rankone_contradiction
