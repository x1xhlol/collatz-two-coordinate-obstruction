import FullTwoMatrixSingularAlgebra

namespace CollatzCertificate.FullTwoMatrix

open Matrix

local notation "tr₂" => TwoDimensionalSwapAlgebra.tr

theorem common_left_row_positive (A B E F G : M2) (a beta : ℝ)
    (hF : EntrywiseLE 0 F) (hF₀ : 0 < F 0 0)
    (hfa : F*A=a • F) (hfb : F*B=a • F)
    (hfe : F*E=beta • F) (hff : F*F=beta • F) (hfg : F*G=beta • F)
    (h01 : 0 < ((A+B)+(E+F+G)) 0 1) : ∀ j, 0 < F 0 j := by
  have hsum : F*((A+B)+(E+F+G))=(2*a+3*beta) • F := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
      hfa, hfb, hfe, hff, hfg]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hf01 : 0 < F 0 1 := by
    by_contra hn
    have hz : F 0 1 = 0 := le_antisymm (le_of_not_gt hn) (hF 0 1)
    have hentry := congrFun (congrFun hsum 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
      hz, zero_mul, mul_zero, add_zero] at hentry
    exact (ne_of_gt (mul_pos hF₀ h01)) hentry
  intro j
  fin_cases j
  · exact hF₀
  · exact hf01

theorem singular_middle_lower_entry_positive (A B E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hE : EntrywiseLE 0 E)
    (hF : EntrywiseLE 0 F) (hG : EntrywiseLE 0 G)
    (hA₀ : 0 < A 0 0) (hB₀ : 0 < B 0 0) (hE₀ : 0 < E 0 0)
    (hF₀ : 0 < F 0 0) (hG₀ : 0 < G 0 0)
    (hd : F.det = 0) (hs : ExactSwaps A B E F G)
    (h10 : 0 < ((A+B)+(E+F+G)) 1 0) : 0 < F 1 0 := by
  by_contra hn
  have hf10 : F 1 0 = 0 := le_antisymm (le_of_not_gt hn) (hF 1 0)
  have hf11 : F 1 1 = 0 := by
    simp only [Matrix.det_fin_two, hf10, mul_zero, sub_zero] at hd
    exact (mul_eq_zero.mp hd).resolve_left (ne_of_gt hF₀)
  have hag := congrFun (congrFun hs.2.2.1 1) 0
  have hbe := congrFun (congrFun hs.2.2.2.1 1) 0
  have haf := congrFun (congrFun hs.2.1 1) 0
  have hbf := congrFun (congrFun hs.2.2.2.2.1 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hf10, hf11, zero_mul, add_zero, zero_add] at hag hbe haf hbf
  have ha10 : A 1 0 = 0 := by
    have hn := mul_nonneg (hA 1 1) (hG 1 0)
    have ha := hA 1 0
    change 0 ≤ A 1 0 at ha
    nlinarith only [hag, hn, hG₀, ha]
  have hb10 : B 1 0 = 0 := by
    have hn := mul_nonneg (hB 1 1) (hE 1 0)
    have hb := hB 1 0
    change 0 ≤ B 1 0 at hb
    nlinarith only [hbe, hn, hE₀, hb]
  have he10 : E 1 0 = 0 := by
    rw [ha10, hb10] at haf
    nlinarith only [haf, hB₀]
  have hg10 : G 1 0 = 0 := by
    rw [ha10, hb10] at hbf
    nlinarith only [hbf, hA₀]
  simpa only [Matrix.add_apply, ha10, hb10, he10, hf10, hg10, add_zero, zero_add,
    lt_self_iff_false] using h10

theorem nonnegative_mul_left (P M N : M2) (hP : EntrywiseLE 0 P)
    (hMN : EntrywiseLE M N) : EntrywiseLE (P*M) (P*N) := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_le_add (mul_le_mul_of_nonneg_left (hMN 0 j) (hP i 0))
    (mul_le_mul_of_nonneg_left (hMN 1 j) (hP i 1))

theorem nonnegative_mul_right (P M N : M2) (hP : EntrywiseLE 0 P)
    (hMN : EntrywiseLE M N) : EntrywiseLE (M*P) (N*P) := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_le_add (mul_le_mul_of_nonneg_right (hMN i 0) (hP 0 j))
    (mul_le_mul_of_nonneg_right (hMN i 1) (hP 1 j))

theorem common_actions_force_eigenvalues_one (A B C D E F G : M2) (a beta : ℝ)
    (hA : EntrywiseLE 0 A) (hC : EntrywiseLE 0 C) (hD : EntrywiseLE 0 D)
    (hF : EntrywiseLE 0 F)
    (hA₀ : 1 ≤ A 0 0) (hC₀ : 1 ≤ C 0 0) (hD₀ : 1 ≤ D 0 0) (hF₀ : 1 ≤ F 0 0)
    (h : WeakRules A B C D E F G)
    (hfa : F*A=a • F) (hfb : F*B=a • F) (hfg : F*G=beta • F)
    (hAF : A*F=a • F) (hff : F*F=beta • F) : a=1 ∧ beta=1 := by
  have hfpos : 0 < F 0 0 := by linarith only [hF₀]
  have hcpos : 0 < C 0 0 := by linarith only [hC₀]
  have hdpos : 0 < D 0 0 := by linarith only [hD₀]
  have haone : 1 ≤ a := by
    have heq := congrFun (congrFun hfa 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul] at heq
    have hn1 := mul_nonneg (hF 0 1) (hA 1 0)
    have hn2 := mul_nonneg (le_of_lt hfpos) (sub_nonneg.mpr hA₀)
    nlinarith only [heq, hn1, hn2, hfpos]
  have hFD : 0 < (F*D) 0 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_pos_of_pos_of_nonneg (mul_pos hfpos hdpos) (mul_nonneg (hF 0 1) (hD 1 0))
  have hCF : 0 < (C*F) 0 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_pos_of_pos_of_nonneg (mul_pos hcpos hfpos) (mul_nonneg (hC 0 1) (hF 1 0))
  have hba : beta ≤ a := by
    have hbd := nonnegative_mul_left F (G*D) (B*D) hF h.bd
    rw [← mul_assoc, ← mul_assoc, hfg, hfb, Matrix.smul_mul, Matrix.smul_mul] at hbd
    have h00 := hbd 0 0
    change beta*(F*D) 0 0 ≤ a*(F*D) 0 0 at h00
    nlinarith only [h00, hFD]
  have haa : a*a ≤ beta := by
    have hcf := nonnegative_mul_right F (C*(A*A)) (C*F) hF h.cf
    have hleft : (C*(A*A))*F=(a*a) • (C*F) := by
      calc
        (C*(A*A))*F = C*(A*(A*F)) := by simp only [mul_assoc]
        _ = (a*a) • (C*F) := by
          rw [hAF, Matrix.mul_smul, hAF, Matrix.mul_smul, Matrix.mul_smul, smul_smul]
    have hright : (C*F)*F=beta • (C*F) := by
      rw [mul_assoc, hff, Matrix.mul_smul]
    rw [hleft, hright] at hcf
    have h00 := hcf 0 0
    change (a*a)*(C*F) 0 0 ≤ beta*(C*F) 0 0 at h00
    nlinarith only [h00, hCF]
  constructor <;> nlinarith only [haone, hba, haa, sq_nonneg (a-1)]

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.common_left_row_positive
#print axioms CollatzCertificate.FullTwoMatrix.singular_middle_lower_entry_positive
#print axioms CollatzCertificate.FullTwoMatrix.common_actions_force_eigenvalues_one
