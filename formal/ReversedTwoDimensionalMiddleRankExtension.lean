import ReversedTwoDimensionalMiddleRank
import FullTwoMatrixNonsingularBasic

namespace CollatzCertificate.TwoDimensionalMiddleRankExtension

open Matrix TwoDimensionalSwapAlgebra TwoDimensionalMiddleRank

set_option maxHeartbeats 800000

theorem commutes_of_scalar_left_actions (A B E F G : M2) (a b : ℝ)
    (ht : tr F ≠ 0) (haf : A * F = a • F) (hbf : B * F = b • F)
    (hfa : F * A = B * E) (hga : G * A = A * F)
    (heb : E * B = B * F) (hfb : F * B = A * G) : A * B = B * A := by
  have hfab : F * (A * B) = (B * B) * F := by
    rw [← mul_assoc, hfa, mul_assoc, heb, ← mul_assoc]
  have hfba : F * (B * A) = (A * A) * F := by
    rw [← mul_assoc, hfb, mul_assoc, hga, ← mul_assoc]
  let K := A * B - B * A
  have hkf : K * F = 0 := by
    dsimp [K]
    rw [sub_mul, mul_assoc, mul_assoc, hbf, haf, Matrix.mul_smul, Matrix.mul_smul,
      haf, hbf, smul_smul, smul_smul, mul_comm a b, sub_self]
  have htk : tr K = 0 := by
    have hi := trace_product_commutes A B
    dsimp [K, tr] at hi ⊢
    linarith only [hi]
  have hfk : F * K = tr F • K := by
    have hi := polarized_trace_identity F K
    rw [hkf, add_zero, htk, zero_smul, add_zero, mul_zero, sub_zero,
      trace_product_commutes F K, hkf] at hi
    simpa only [tr, Matrix.zero_apply, add_zero, zero_smul] using hi
  have hfk' : F * K = (b ^ 2 - a ^ 2) • F := by
    dsimp [K]
    rw [mul_sub, hfab, hfba, mul_assoc, mul_assoc, hbf, haf,
      Matrix.mul_smul, Matrix.mul_smul, hbf, haf, smul_smul, smul_smul, ← sub_smul]
    congr 1
    ring
  have htrace : (b ^ 2 - a ^ 2) * tr F = 0 := by
    have hi := congrArg tr (hfk'.symm.trans hfk)
    simp only [tr, Matrix.smul_apply, smul_eq_mul] at hi htk
    dsimp [tr]
    linear_combination hi + (F 0 0 + F 1 1) * htk
  have hscale : b ^ 2 - a ^ 2 = 0 := (mul_eq_zero.mp htrace).resolve_right ht
  have hz : tr F • K = 0 := by rw [← hfk, hfk', hscale, zero_smul]
  have hk : K = 0 := by
    ext i j
    have hi := congrFun (congrFun hz i) j
    exact (mul_eq_zero.mp hi).resolve_left ht
  exact sub_eq_zero.mp hk

theorem singular_middle_commutes_of_nonzero_binary_product (A B E F G : M2)
    (hb : tr B ≠ 0) (ht : tr F ≠ 0) (hd : F.det = 0) (hBF : B * F ≠ 0)
    (hea : E * A = A * E) (hfa : F * A = B * E)
    (hga : G * A = A * F) (heb : E * B = B * F)
    (hfb : F * B = A * G) (hgb : G * B = B * G) : A * B = B * A := by
  have hf : F * F = tr F • F := by
    simp only [square_trace_identity, hd, zero_smul, sub_zero]
  have hfab : F * (A * B) = (B * B) * F := by
    rw [← mul_assoc, hfa, mul_assoc, heb, ← mul_assoc]
  have hbb : F * ((B * B) * F) = tr F • ((B * B) * F) := by
    rw [← hfab, ← mul_assoc, hf, smul_mul]
  let b := tr (F * B) / tr F
  have hbf : B * F = b • F := invariant_image_of_square_relation B F hb ht hd hbb
  have hb0 : b ≠ 0 := by
    intro hz
    apply hBF
    simpa only [hz, zero_smul] using hbf
  have hef : E * F = tr F • F := by
    have hh : b • (E * F) = b • (tr F • F) := by
      calc
        b • (E * F) = E * (B * F) := by rw [hbf, Matrix.mul_smul]
        _ = (E * B) * F := (mul_assoc _ _ _).symm
        _ = (B * F) * F := by rw [heb]
        _ = b • (tr F • F) := by rw [hbf, smul_mul, hf]
    ext i j
    exact mul_left_cancel₀ hb0 (congrFun (congrFun hh i) j)
  rcases FullTwoMatrix.centralizer_scalar_or_span E A hea with ⟨e, he⟩ | ⟨x, y, ha⟩
  · have het : e = tr F := by
      have hh : e * tr F = tr F * tr F := by
        simpa only [he, smul_mul, one_mul, tr, Matrix.smul_apply, smul_eq_mul, mul_add]
          using congrArg tr hef
      exact mul_right_cancel₀ ht hh
    rw [het] at he
    have htb : tr F • B = b • F := by
      simpa only [he, smul_mul, one_mul, hbf] using heb
    have hB : B = (b / tr F) • F := by
      ext i j
      have hi := congrFun (congrFun htb i) j
      change tr F * B i j = b * F i j at hi
      change B i j = b / tr F * F i j
      field_simp
      nlinarith only [hi]
    have hFB : F * B = b • F := by
      rw [hB, Matrix.mul_smul, hf, smul_smul, div_mul_cancel₀ b ht]
    have hGF : G * F = F * G := by
      have hh := hgb
      rw [hB, Matrix.mul_smul, smul_mul] at hh
      ext i j
      exact mul_left_cancel₀ (div_ne_zero hb0 ht) (congrFun (congrFun hh i) j)
    have hAG : A * G = b • F := hfb.symm.trans hFB
    have hGFt : G * F = tr F • F := by
      have hh : b • (G * F) = b • (tr F • F) := by
        calc
          b • (G * F) = G * (b • F) := (Matrix.mul_smul _ _ _).symm
          _ = G * (A * G) := by rw [hAG]
          _ = (G * A) * G := (mul_assoc _ _ _).symm
          _ = (A * F) * G := by rw [hga]
          _ = A * (F * G) := mul_assoc _ _ _
          _ = A * (G * F) := by rw [hGF]
          _ = (A * G) * F := (mul_assoc _ _ _).symm
          _ = b • (tr F • F) := by rw [hAG, smul_mul, hf]
      ext i j
      exact mul_left_cancel₀ hb0 (congrFun (congrFun hh i) j)
    have haf : A * F = b • F := by
      have hh : tr F • (A * F) = tr F • (b • F) := by
        calc
          tr F • (A * F) = A * (G * F) := by rw [hGFt, Matrix.mul_smul]
          _ = (A * G) * F := (mul_assoc _ _ _).symm
          _ = tr F • (b • F) := by rw [hAG, smul_mul, hf, smul_comm]
      ext i j
      exact mul_left_cancel₀ ht (congrFun (congrFun hh i) j)
    exact commutes_of_scalar_left_actions A B E F G b b ht haf hbf hfa hga heb hfb
  · have haf : A * F = (x + y * tr F) • F := by
      rw [ha, add_mul, smul_mul, one_mul, smul_mul, hef, smul_smul, ← add_smul]
    exact commutes_of_scalar_left_actions A B E F G (x + y * tr F) b
      ht haf hbf hfa hga heb hfb

theorem zero_traces_commute_of_singular_commutator (A B : M2)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B)
    (ha : tr A = 0) (hb : tr B = 0) (hd : delta A B = 0) : A * B = B * A := by
  have ha00 : A 0 0 = 0 := by
    have h0 := hA 0 0
    have h1 := hA 1 1
    simp only [tr] at ha
    change 0 ≤ A 0 0 at h0
    change 0 ≤ A 1 1 at h1
    linarith only [ha, h0, h1]
  have ha11 : A 1 1 = 0 := by simpa only [tr, ha00, zero_add] using ha
  have hb00 : B 0 0 = 0 := by
    have h0 := hB 0 0
    have h1 := hB 1 1
    simp only [tr] at hb
    change 0 ≤ B 0 0 at h0
    change 0 ≤ B 1 1 at h1
    linarith only [hb, h0, h1]
  have hb11 : B 1 1 = 0 := by simpa only [tr, hb00, zero_add] using hb
  have he : A 0 1 * B 1 0 = B 0 1 * A 1 0 := by
    simp only [delta, Matrix.det_fin_two, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_two, ha00, ha11, hb00, hb11, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero] at hd
    have hh : (A 0 1 * B 1 0 - B 0 1 * A 1 0) ^ 2 = 0 := by
      linear_combination -hd
    nlinarith only [hh]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha00, ha11, hb00, hb11, he, mul_comm]

end CollatzCertificate.TwoDimensionalMiddleRankExtension

#print axioms CollatzCertificate.TwoDimensionalMiddleRankExtension.commutes_of_scalar_left_actions
#print axioms CollatzCertificate.TwoDimensionalMiddleRankExtension.singular_middle_commutes_of_nonzero_binary_product
#print axioms CollatzCertificate.TwoDimensionalMiddleRankExtension.zero_traces_commute_of_singular_commutator
