import ReversedTwoDimensionalSwapAlgebra

namespace CollatzCertificate.TwoDimensionalMiddleRank

open Matrix TwoDimensionalSwapAlgebra

theorem square_trace_identity (A : M2) : A * A = tr A • A - A.det • (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tr, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two] <;> ring

theorem sandwich_trace_identity (F A : M2) :
    F * A * F = tr (F * A) • F + F.det • A - (F.det * tr A) • (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tr, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two] <;> ring

theorem polarized_trace_identity (A B : M2) :
    A * B + B * A = tr A • B + tr B • A +
      (tr (A * B) - tr A * tr B) • (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tr, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem trace_product_commutes (A B : M2) : tr (A * B) = tr (B * A) := by
  simp [tr, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem invariant_image_of_square_relation (A F : M2)
    (ha : tr A ≠ 0) (ht : tr F ≠ 0) (hd : F.det = 0)
    (hh : F * ((A * A) * F) = tr F • ((A * A) * F)) :
    A * F = (tr (F * A) / tr F) • F := by
  have hf : F * F = tr F • F := by simp only [square_trace_identity, hd, zero_smul, sub_zero]
  have hs : F * (A * F) = tr (F * A) • F := by
    rw [← mul_assoc, sandwich_trace_identity, hd]
    simp
  simp only [square_trace_identity A, sub_mul, Matrix.smul_mul, Matrix.one_mul,
    mul_sub, Matrix.mul_smul, hs, hf] at hh
  ext i j
  have hi := congrFun (congrFun hh i) j
  change tr A * (tr (F * A) * F i j) - A.det * (tr F * F i j) =
    tr F * (tr A * (A * F) i j - A.det * F i j) at hi
  have hz : tr A * (tr (F * A) * F i j - tr F * (A * F) i j) = 0 := by
    linear_combination hi
  have hz' := (mul_eq_zero.mp hz).resolve_left ha
  change (A * F) i j = tr (F * A) / tr F * F i j
  apply (mul_left_cancel₀ ht)
  have hdiv : tr F * (tr (F * A) / tr F) = tr (F * A) := by
    exact mul_div_cancel₀ _ ht
  rw [← mul_assoc, hdiv]
  linarith only [hz']

theorem singular_middle_commutes_binary_of_nonzero_traces (A B E F G : M2)
    (ha : tr A ≠ 0) (hb : tr B ≠ 0) (ht : tr F ≠ 0) (hd : F.det = 0)
    (hfa : F * A = B * E) (hga : G * A = A * F)
    (heb : E * B = B * F) (hfb : F * B = A * G) : A * B = B * A := by
  have hfab : F * (A * B) = (B * B) * F := by
    rw [← mul_assoc, hfa, mul_assoc, heb, ← mul_assoc]
  have hfba : F * (B * A) = (A * A) * F := by
    rw [← mul_assoc, hfb, mul_assoc, hga, ← mul_assoc]
  have hf : F * F = tr F • F := by simp only [square_trace_identity, hd, zero_smul, sub_zero]
  have haa : F * ((A * A) * F) = tr F • ((A * A) * F) := by
    rw [← hfba, ← mul_assoc, hf, smul_mul]
  have hbb : F * ((B * B) * F) = tr F • ((B * B) * F) := by
    rw [← hfab, ← mul_assoc, hf, smul_mul]
  let a := tr (F * A) / tr F
  let b := tr (F * B) / tr F
  have haf : A * F = a • F := invariant_image_of_square_relation A F ha ht hd haa
  have hbf : B * F = b • F := invariant_image_of_square_relation B F hb ht hd hbb
  let K := A * B - B * A
  have hkf : K * F = 0 := by
    dsimp [K]
    rw [sub_mul, mul_assoc, mul_assoc, hbf, haf, Matrix.mul_smul, Matrix.mul_smul, haf, hbf,
      smul_smul, smul_smul, mul_comm a b, sub_self]
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
    rw [mul_sub, hfab, hfba, mul_assoc, mul_assoc, hbf, haf, Matrix.mul_smul, Matrix.mul_smul,
      hbf, haf, smul_smul, smul_smul, ← sub_smul]
    congr 1; ring
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

end CollatzCertificate.TwoDimensionalMiddleRank

#print axioms CollatzCertificate.TwoDimensionalMiddleRank.square_trace_identity
#print axioms CollatzCertificate.TwoDimensionalMiddleRank.sandwich_trace_identity
#print axioms CollatzCertificate.TwoDimensionalMiddleRank.polarized_trace_identity
#print axioms CollatzCertificate.TwoDimensionalMiddleRank.trace_product_commutes
#print axioms CollatzCertificate.TwoDimensionalMiddleRank.invariant_image_of_square_relation
#print axioms CollatzCertificate.TwoDimensionalMiddleRank.singular_middle_commutes_binary_of_nonzero_traces
