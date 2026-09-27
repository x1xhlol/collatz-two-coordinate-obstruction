import FullTwoMatrixBasic
import ReversedTwoDimensionalMiddleRank
import Mathlib.Tactic.Module

namespace CollatzCertificate.FullTwoMatrix

open Matrix TwoDimensionalSwapAlgebra TwoDimensionalMiddleRank

set_option maxHeartbeats 1000000

theorem boundary_mul_left_mono (P X Y : M2)
    (hP : EntrywiseLE 0 P) (hXY : EntrywiseLE X Y) :
    EntrywiseLE (P * X) (P * Y) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hXY k j) (hP i k)

theorem boundary_mul_right_mono (X Y P : M2)
    (hXY : EntrywiseLE X Y) (hP : EntrywiseLE 0 P) :
    EntrywiseLE (X * P) (Y * P) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hXY i k) (hP k j)

theorem nonsingular_boundary_core (U V C D : M2) (μ t : ℝ)
    (hμ : 0 < μ) (_ht : 0 < t)
    (hU : EntrywiseLE 0 U) (hV : EntrywiseLE 0 V)
    (hC : EntrywiseLE 0 C) (hD : EntrywiseLE 0 D)
    (hC00 : 1 ≤ C 0 0) (hD00 : 1 ≤ D 0 0)
    (hU00 : 1 ≤ U 0 0 + μ) (hV00 : 1 ≤ V 0 0 + μ)
    (htrU : tr U = μ) (htrV : tr V = μ)
    (hUU : U * U = μ • U) (hUV : U * V = μ • U)
    (hVU : V * U = μ • V) (hVV : V * V = μ • V)
    (h01 : 0 < (U + V) 0 1) (h10 : 0 < (U + V) 1 0)
    (hbd : EntrywiseLE ((t • (2 • V + μ • (1 : M2))) * D)
      ((V + μ • (1 : M2)) * D))
    (hce : EntrywiseLE (C * (V + μ • (1 : M2)))
      (C * (t • (2 • U + μ • (1 : M2)))))
    (hcg : EntrywiseLE (C * ((U + μ • (1 : M2)) * (V + μ • (1 : M2))))
      (C * (t • (2 • V + μ • (1 : M2))))) : False := by
  let S := U + V
  have hS : EntrywiseLE 0 S := by
    intro i j
    exact add_nonneg (hU i j) (hV i j)
  have hSU : S * U = μ • S := by
    dsimp [S]
    rw [Matrix.add_mul, hUU, hVU, smul_add]
  have hSV : S * V = μ • S := by
    dsimp [S]
    rw [Matrix.add_mul, hUV, hVV, smul_add]
  have hSS : S * S = (2 * μ) • S := by
    calc
      S * S = S * U + S * V := by dsimp [S]; rw [Matrix.mul_add]
      _ = (2 * μ) • S := by rw [hSU, hSV]; module
  have hs00 : 0 < S 0 0 := by
    have hn := hS 0 0
    change 0 ≤ S 0 0 at hn
    have hh := congrFun (congrFun hSS 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul] at hh
    have hp : 0 < S 0 1 * S 1 0 := mul_pos h01 h10
    have hnz : S 0 0 ≠ 0 := by
      intro hz
      rw [hz] at hh
      nlinarith only [hh, hp]
    exact lt_of_le_of_ne hn (Ne.symm hnz)
  have hSD : 0 < (S * D) 0 0 := by
    have hd00 : 0 < D 0 0 := lt_of_lt_of_le zero_lt_one hD00
    have hp := mul_pos hs00 hd00
    have hn := mul_nonneg (hS 0 1) (hD 1 0)
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    linarith only [hp, hn]
  have hSB : S * (V + μ • (1 : M2)) = (2 * μ) • S := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hSV]
    module
  have hSG : S * (t • (2 • V + μ • (1 : M2))) = (3 * t * μ) • S := by
    rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.mul_one, hSV]
    module
  have htb : 3 * t ≤ 2 := by
    have hh := boundary_mul_left_mono S _ _ hS hbd 0 0
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hSG, hSB,
      Matrix.smul_mul, Matrix.smul_mul] at hh
    simp only [Matrix.smul_apply, smul_eq_mul] at hh
    have hp : 0 < μ * (S * D) 0 0 := mul_pos hμ hSD
    nlinarith only [hh, hp]
  let u := (C * U) 0 0
  let v := (C * V) 0 0
  have nu : 0 ≤ u := by
    dsimp [u]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_nonneg (mul_nonneg (hC 0 0) (hU 0 0)) (mul_nonneg (hC 0 1) (hU 1 0))
  have nv : 0 ≤ v := by
    dsimp [v]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_nonneg (mul_nonneg (hC 0 0) (hV 0 0)) (mul_nonneg (hC 0 1) (hV 1 0))
  have huv : 0 < u + v := by
    have hc00 : 0 < C 0 0 := lt_of_lt_of_le zero_lt_one hC00
    have hp := mul_pos hc00 hs00
    have hn := mul_nonneg (hC 0 1) (hS 1 0)
    dsimp [u, v]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, S, Matrix.add_apply] at hp hn ⊢
    nlinarith only [hp, hn]
  have hBU : (V + μ • (1 : M2)) * U = μ • S := by
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hVU]
    dsimp [S]
    module
  have hEU : (t • (2 • U + μ • (1 : M2))) * U = (3 * t * μ) • U := by
    rw [Matrix.smul_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul, hUU]
    module
  have hu_bound : u + v ≤ 3 * t * u := by
    have hh := boundary_mul_right_mono _ _ U hce hU 0 0
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hBU, hEU,
      Matrix.mul_smul, Matrix.mul_smul] at hh
    simp only [Matrix.smul_apply, smul_eq_mul] at hh
    have heq : (C * S) 0 0 = u + v := by simp [S, Matrix.mul_add, u, v]
    rw [heq] at hh
    change μ * (u + v) ≤ (3 * t * μ) * u at hh
    have hh' : μ * (u + v) ≤ μ * (3 * t * u) := by nlinarith only [hh]
    exact le_of_mul_le_mul_left hh' hμ
  have hBV : (V + μ • (1 : M2)) * V = (2 * μ) • V := by
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hVV]
    module
  have hAV : (U + μ • (1 : M2)) * V = μ • S := by
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hUV]
    dsimp [S]
    module
  have hABV : ((U + μ • (1 : M2)) * (V + μ • (1 : M2))) * V =
      (2 * μ^2) • S := by
    rw [Matrix.mul_assoc, hBV, Matrix.mul_smul, hAV]
    module
  have hGV : (t • (2 • V + μ • (1 : M2))) * V = (3 * t * μ) • V := by
    rw [Matrix.smul_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul, hVV]
    module
  have hv_bound : 2 * μ * (u + v) ≤ 3 * t * v := by
    have hh := boundary_mul_right_mono _ _ V hcg hV 0 0
    rw [Matrix.mul_assoc C ((U + μ • (1 : M2)) * (V + μ • (1 : M2))) V,
      Matrix.mul_assoc C (t • (2 • V + μ • (1 : M2))) V, hABV, hGV,
      Matrix.mul_smul, Matrix.mul_smul] at hh
    simp only [Matrix.smul_apply, smul_eq_mul] at hh
    have heq : (C * S) 0 0 = u + v := by simp [S, Matrix.mul_add, u, v]
    rw [heq] at hh
    change (2 * μ^2) * (u + v) ≤ (3 * t * μ) * v at hh
    have hh' : μ * (2 * μ * (u + v)) ≤ μ * (3 * t * v) := by nlinarith only [hh]
    exact le_of_mul_le_mul_left hh' hμ
  have hvu : v ≤ u := by nlinarith only [hu_bound, mul_le_mul_of_nonneg_right htb nu]
  have hμuv : μ * (u + v) ≤ v := by
    nlinarith only [hv_bound, mul_le_mul_of_nonneg_right htb nv]
  have hμhalf : μ ≤ 1 / 2 := by nlinarith only [hμuv, hvu, huv]
  have hμge : 1 ≤ 2 * μ := by
    have hu11 := hU 1 1
    simp only [tr] at htrU
    change 0 ≤ U 1 1 at hu11
    linarith only [hU00, htrU, hu11]
  have hμeq : μ = 1 / 2 := by linarith only [hμhalf, hμge]
  have hu11 : U 1 1 = 0 := by
    have hn := hU 1 1
    change 0 ≤ U 1 1 at hn
    simp only [tr] at htrU
    linarith only [hU00, htrU, hμeq, hn]
  have hv11 : V 1 1 = 0 := by
    have hn := hV 1 1
    change 0 ≤ V 1 1 at hn
    simp only [tr] at htrV
    linarith only [hV00, htrV, hμeq, hn]
  have hs11 : S 1 1 = 0 := by simp [S, hu11, hv11]
  have hh := congrFun (congrFun hSS 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
    hs11, mul_zero, add_zero] at hh
  exact (ne_of_gt (mul_pos h10 h01)) hh

theorem shifted_matrix_nonnegative (A : M2) (μ : ℝ) (hμ : 0 < μ)
    (hA : EntrywiseLE 0 A) (htr : tr A = 3 * μ) (hdet : A.det = 2 * μ^2) :
    EntrywiseLE 0 (A - μ • (1 : M2)) := by
  have hp : 0 ≤ (A 0 0 - μ) * (A 1 1 - μ) := by
    have hh := mul_nonneg (hA 0 1) (hA 1 0)
    simp only [tr] at htr
    simp only [Matrix.det_fin_two] at hdet
    change 0 ≤ A 0 1 * A 1 0 at hh
    have hscale := congrArg (μ * ·) htr
    nlinarith only [hscale, hdet, hh]
  have h00 : μ ≤ A 0 0 := by
    by_contra hn
    have hn' : A 0 0 - μ < 0 := by linarith only [hn]
    have hp' : 0 < A 1 1 - μ := by simp only [tr] at htr; linarith only [htr, hn, hμ]
    exact (not_lt_of_ge hp) (mul_neg_of_neg_of_pos hn' hp')
  have h11 : μ ≤ A 1 1 := by
    by_contra hn
    have hn' : A 1 1 - μ < 0 := by linarith only [hn]
    have hp' : 0 < A 0 0 - μ := by simp only [tr] at htr; linarith only [htr, hn, hμ]
    exact (not_lt_of_ge hp) (mul_neg_of_pos_of_neg hp' hn')
  intro i j
  fin_cases i <;> fin_cases j <;> simp
  · exact h00
  · exact hA 0 1
  · exact hA 1 0
  · exact h11

theorem nonsingular_shape_boundary_impossible (A B C D E F G : M2) (μ t : ℝ)
    (hμ : 0 < μ) (ht : 0 < t)
    (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B)
    (hC : EntrywiseLE 0 C) (hD : EntrywiseLE 0 D)
    (hA00 : 1 ≤ A 0 0) (hB00 : 1 ≤ B 0 0)
    (hC00 : 1 ≤ C 0 0) (hD00 : 1 ≤ D 0 0)
    (hw : WeakRules A B C D E F G)
    (htrA : tr A = 3 * μ) (htrB : tr B = 3 * μ)
    (hdetA : A.det = 2 * μ^2) (hdetB : B.det = 2 * μ^2)
    (hAN : A * (B - A) = μ • (B - A))
    (hNA : (B - A) * A = (2 * μ) • (B - A))
    (hE : E = t • (2 • A - μ • (1 : M2)))
    (hF : F = t • (A + B - μ • (1 : M2)))
    (hG : G = t • (2 • B - μ • (1 : M2)))
    (h01 : 0 < ((A+B)+(E+F+G)) 0 1)
    (h10 : 0 < ((A+B)+(E+F+G)) 1 0) : False := by
  let U := A - μ • (1 : M2)
  let V := B - μ • (1 : M2)
  have hU := shifted_matrix_nonnegative A μ hμ hA htrA hdetA
  have hV := shifted_matrix_nonnegative B μ hμ hB htrB hdetB
  have ha : A = U + μ • (1 : M2) := by dsimp [U]; module
  have hb : B = V + μ • (1 : M2) := by dsimp [V]; module
  have he : E = t • (2 • U + μ • (1 : M2)) := by rw [hE, ha]; module
  have hg : G = t • (2 • V + μ • (1 : M2)) := by rw [hG, hb]; module
  have haa : A*A = (3*μ) • A - (2*μ^2) • (1 : M2) := by
    rw [square_trace_identity, htrA, hdetA]
  have hbb : B*B = (3*μ) • B - (2*μ^2) • (1 : M2) := by
    rw [square_trace_identity, htrB, hdetB]
  have hab : A*B = (2*μ) • A + μ • B - (2*μ^2) • (1 : M2) := by
    rw [Matrix.mul_sub, haa, smul_sub] at hAN
    ext i j
    have hh := congrFun (congrFun hAN i) j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hh ⊢
    linear_combination hh
  have hba : B*A = μ • A + (2*μ) • B - (2*μ^2) • (1 : M2) := by
    rw [Matrix.sub_mul, haa, smul_sub] at hNA
    ext i j
    have hh := congrFun (congrFun hNA i) j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hh ⊢
    linear_combination hh
  have huu : U*U = μ • U := by
    dsimp [U]
    simp only [Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, haa]
    module
  have huv : U*V = μ • U := by
    dsimp [U, V]
    simp only [Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hab]
    module
  have hvu : V*U = μ • V := by
    dsimp [U, V]
    simp only [Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hba]
    module
  have hvv : V*V = μ • V := by
    dsimp [V]
    simp only [Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hbb]
    module
  have htrU : tr U = μ := by
    simp only [U, tr, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_eq, mul_one]
    simp only [tr] at htrA
    linarith only [htrA]
  have htrV : tr V = μ := by
    simp only [V, tr, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_eq, mul_one]
    simp only [tr] at htrB
    linarith only [htrB]
  have hspos (i j : Fin 2) (hne : i ≠ j)
      (hij : 0 < ((A+B)+(E+F+G)) i j) : 0 < (U+V) i j := by
    have hn := add_nonneg (hA i j) (hB i j)
    change 0 ≤ A i j + B i j at hn
    rw [hE, hF, hG] at hij
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_ne hne, mul_zero, sub_zero] at hij
    have hp : 0 < A i j + B i j := by
      by_contra hh
      have hz : A i j + B i j = 0 := by linarith only [hn, hh]
      simp only [two_smul] at hij
      have hz' := congrArg (fun x : ℝ => (1+3*t)*x) hz
      nlinarith only [hij, hz']
    simpa only [U, V, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_ne hne, mul_zero, sub_zero] using hp
  apply nonsingular_boundary_core U V C D μ t hμ ht hU hV hC hD hC00 hD00
  · simpa [U] using hA00
  · simpa [V] using hB00
  · exact htrU
  · exact htrV
  · exact huu
  · exact huv
  · exact hvu
  · exact hvv
  · exact hspos 0 1 (by decide) h01
  · exact hspos 1 0 (by decide) h10
  · simpa only [← hb, ← hg] using hw.bd
  · simpa only [← hb, ← he] using hw.ce
  · simpa only [← ha, ← hb, ← hg] using hw.cg

end CollatzCertificate.FullTwoMatrix

#print axioms CollatzCertificate.FullTwoMatrix.nonsingular_boundary_core
#print axioms CollatzCertificate.FullTwoMatrix.shifted_matrix_nonnegative
#print axioms CollatzCertificate.FullTwoMatrix.nonsingular_shape_boundary_impossible
