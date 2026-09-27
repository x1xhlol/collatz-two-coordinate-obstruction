import FullTwoMatrixAggregate
import ReversedTwoDimensionalMiddleRank

namespace CollatzCertificate.FullTwoMatrix

open Matrix TwoDimensionalMiddleRank

local notation "tr₂" => TwoDimensionalSwapAlgebra.tr

theorem trace_positive (A : M2) (hA : EntrywiseLE 0 A) (hA₀ : 0 < A 0 0) :
    0 < tr₂ A := by
  have h1 : 0 ≤ A 1 1 := hA 1 1
  dsimp [TwoDimensionalSwapAlgebra.tr]
  linarith only [hA₀, h1]

theorem forward_singular_middle_commutes (A B E F G : M2)
    (ha : tr₂ A ≠ 0) (hb : tr₂ B ≠ 0) (hf : tr₂ F ≠ 0)
    (hd : F.det = 0) (hs : ExactSwaps A B E F G) : A*B=B*A := by
  rcases hs with ⟨hae, haf, hag, hbe, hbf, hbg⟩
  have h := singular_middle_commutes_binary_of_nonzero_traces Aᵀ Bᵀ Eᵀ Fᵀ Gᵀ
    ha hb hf (by simpa using hd)
    (by simpa only [transpose_mul] using congrArg Matrix.transpose haf)
    (by simpa only [transpose_mul] using congrArg Matrix.transpose hag)
    (by simpa only [transpose_mul] using congrArg Matrix.transpose hbe)
    (by simpa only [transpose_mul] using congrArg Matrix.transpose hbf)
  have hh := congrArg Matrix.transpose h
  simpa only [transpose_mul, transpose_transpose] using hh.symm

theorem forward_singular_middle_left_actions (A B E F G : M2)
    (ha : tr₂ A ≠ 0) (hb : tr₂ B ≠ 0) (hf : tr₂ F ≠ 0)
    (hd : F.det = 0) (hs : ExactSwaps A B E F G) :
    ∃ a b : ℝ, F*A=a • F ∧ F*B=b • F := by
  rcases hs with ⟨hae, haf, hag, hbe, hbf, hbg⟩
  have hABF : (A*B)*F=F*(A*A) := by
    rw [mul_assoc, hbf, ← mul_assoc, hag, mul_assoc]
  have hBAF : (B*A)*F=F*(B*B) := by
    rw [mul_assoc, haf, ← mul_assoc, hbe, mul_assoc]
  have hFF : F*F=tr₂ F • F := by
    simpa only [hd, zero_smul, sub_zero] using square_trace_identity F
  have hsqA : (F*(A*A))*F=tr₂ F • (F*(A*A)) := by
    rw [← hABF, mul_assoc, hFF, Matrix.mul_smul]
  have hsqB : (F*(B*B))*F=tr₂ F • (F*(B*B)) := by
    rw [← hBAF, mul_assoc, hFF, Matrix.mul_smul]
  have hA := invariant_image_of_square_relation Aᵀ Fᵀ ha hf (by simpa using hd)
    (by simpa only [transpose_mul, transpose_smul] using congrArg Matrix.transpose hsqA)
  have hB := invariant_image_of_square_relation Bᵀ Fᵀ hb hf (by simpa using hd)
    (by simpa only [transpose_mul, transpose_smul] using congrArg Matrix.transpose hsqB)
  exact ⟨tr₂ (Fᵀ*Aᵀ) / tr₂ Fᵀ, tr₂ (Fᵀ*Bᵀ) / tr₂ Fᵀ,
    by simpa only [transpose_mul, transpose_smul, transpose_transpose] using congrArg Matrix.transpose hA,
    by simpa only [transpose_mul, transpose_smul, transpose_transpose] using congrArg Matrix.transpose hB⟩

theorem singular_middle_common_left (A B E F G : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B) (hF : EntrywiseLE 0 F)
    (hA₀ : 0 < A 0 0) (hB₀ : 0 < B 0 0) (hF₀ : 0 < F 0 0)
    (hd : F.det = 0) (hs : ExactSwaps A B E F G) :
    ∃ a : ℝ, 0 < a ∧ F*A=a • F ∧ F*B=a • F ∧
      F*E=tr₂ F • F ∧ F*G=tr₂ F • F ∧
      (A*B)*F=a^2 • F ∧ (B*A)*F=a^2 • F := by
  have ha := ne_of_gt (trace_positive A hA hA₀)
  have hb := ne_of_gt (trace_positive B hB hB₀)
  have hf := ne_of_gt (trace_positive F hF hF₀)
  have hcomm := forward_singular_middle_commutes A B E F G ha hb hf hd hs
  obtain ⟨a,b,hfa,hfb⟩ := forward_singular_middle_left_actions A B E F G ha hb hf hd hs
  have hap : 0 < a := by
    have h00 := congrFun (congrFun hfa 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul] at h00
    have hp := mul_pos hF₀ hA₀
    have hn := mul_nonneg (hF 0 1) (hA 1 0)
    nlinarith only [h00, hp, hn, hF₀]
  have hbp : 0 < b := by
    have h00 := congrFun (congrFun hfb 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul] at h00
    have hp := mul_pos hF₀ hB₀
    have hn := mul_nonneg (hF 0 1) (hB 1 0)
    nlinarith only [h00, hp, hn, hF₀]
  rcases hs with ⟨hae, haf, hag, hbe, hbf, hbg⟩
  have hABF : (A*B)*F=a^2 • F := by
    rw [mul_assoc, hbf, ← mul_assoc, hag, hfa, Matrix.smul_mul, hfa, smul_smul]
    congr 1; ring
  have hBAF : (B*A)*F=b^2 • F := by
    rw [mul_assoc, haf, ← mul_assoc, hbe, hfb, Matrix.smul_mul, hfb, smul_smul]
    congr 1; ring
  have hab : a = b := by
    have hm : a^2 • F = b^2 • F := by rw [← hABF, ← hBAF, hcomm]
    have h00 := congrFun (congrFun hm 0) 0
    change a^2 * F 0 0 = b^2 * F 0 0 at h00
    have heq : a^2 = b^2 := (mul_right_cancel₀ (ne_of_gt hF₀)) h00
    nlinarith only [heq, hap, hbp]
  subst b
  have hFF : F*F=tr₂ F • F := by
    simpa only [hd, zero_smul, sub_zero] using square_trace_identity F
  have hfe : F*E=tr₂ F • F := by
    have hm : a • (F*E) = a • (F*F) := by
      rw [← Matrix.smul_mul, ← hfb, mul_assoc, hbe, hfb, Matrix.mul_smul]
    ext i j
    have hij := congrFun (congrFun hm i) j
    change a*(F*E) i j = a*(F*F) i j at hij
    have hc := (mul_left_cancel₀ (ne_of_gt hap)) hij
    simpa only [hFF] using hc
  have hfg : F*G=tr₂ F • F := by
    have hm : a • (F*G) = a • (F*F) := by
      rw [← Matrix.smul_mul, ← hfa, mul_assoc, hag, hfa, Matrix.mul_smul]
    ext i j
    have hij := congrFun (congrFun hm i) j
    change a*(F*G) i j = a*(F*F) i j at hij
    have hc := (mul_left_cancel₀ (ne_of_gt hap)) hij
    simpa only [hFF] using hc
  exact ⟨a, hap, hfa, hfb, hfe, hfg, hABF, hBAF⟩

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.forward_singular_middle_commutes
#print axioms CollatzCertificate.FullTwoMatrix.forward_singular_middle_left_actions
#print axioms CollatzCertificate.FullTwoMatrix.singular_middle_common_left
