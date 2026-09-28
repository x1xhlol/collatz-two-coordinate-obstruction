import RealClockFloorGeometry

namespace CollatzClockAudit
open Erdos1135.Tao

theorem rpow_neg_le_two_mul_of_half_le {a b c : ℝ}
    (ha : 0 < a) (hab : a / 2 ≤ b) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    b ^ (-c) ≤ 2 * a ^ (-c) := by
  have hp : 0 < a / 2 := by positivity
  have hmono := Real.rpow_le_rpow_of_nonpos hp hab (neg_nonpos.mpr hc)
  have ht : (2 : ℝ) ^ c ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hc1
  have hid : (a / 2) ^ (-c) = (2 : ℝ) ^ c * a ^ (-c) := by
    rw [Real.div_rpow ha.le (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp [div_eq_mul_inv, mul_comm]
  rw [hid] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg ha.le _))

theorem floor_rpow_neg_le_two_mul {x c : ℝ} (hx : 2 ≤ x)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    ((Nat.floor x : ℕ) : ℝ) ^ (-c) ≤ 2 * x ^ (-c) := by
  have hfloor := Nat.lt_floor_add_one x
  have hxhalf : x / 2 ≤ ((Nat.floor x : ℕ) : ℝ) := by linarith
  exact rpow_neg_le_two_mul_of_half_le (by linarith) hxhalf hc hc1

theorem floor_log_rpow_neg_le_two_mul {x c : ℝ} (hx : 2 ≤ x)
    (hlog : 2 ≤ Real.log x) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    (Real.log ((Nat.floor x : ℕ) : ℝ)) ^ (-c) ≤ 2 * (Real.log x) ^ (-c) :=
  rpow_neg_le_two_mul_of_half_le (by linarith) (half_log_le_log_floor hx hlog) hc hc1

theorem floorSourceError_le_floor_rpow {B : ℕ} (hB : 0 < B)
    (hlog : 1 ≤ Real.log (B : ℝ)) {c : ℝ} (hc1 : c ≤ 1) :
    taoProp111FloorSourceError B ≤ 96000 * (B : ℝ) ^ (-c) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hden : (B : ℝ) ≤ B * Real.log (B : ℝ) := by nlinarith
  have hinv := one_div_le_one_div_of_le hBR hden
  have hpow : (B : ℝ) ^ (-1 : ℝ) ≤ (B : ℝ) ^ (-c) :=
    Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  rw [Real.rpow_neg_one] at hpow
  unfold taoProp111FloorSourceError
  change 96000 / ((B : ℝ) * Real.log (B : ℝ)) ≤ 96000 * (B : ℝ) ^ (-c)
  simp only [div_eq_mul_inv] at hinv ⊢
  nlinarith

theorem floorSourceError_le_real_rpow {x c : ℝ} (hx : 2 ≤ x)
    (hlog : 1 ≤ Real.log ((Nat.floor x : ℕ) : ℝ))
    (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    taoProp111FloorSourceError (Nat.floor x) ≤ 192000 * x ^ (-c) := by
  have hB : 0 < Nat.floor x := Nat.le_floor (by norm_num; linarith)
  have h1 := floorSourceError_le_floor_rpow hB hlog hc1
  have h2 := floor_rpow_neg_le_two_mul hx hc hc1
  nlinarith

theorem inv_le_log_rpow_neg {x c : ℝ} (hx : 0 < x) (hlog : 1 ≤ Real.log x)
    (hc1 : c ≤ 1) : x ^ (-1 : ℝ) ≤ (Real.log x) ^ (-c) := by
  have hp : 0 < (Real.log x) ^ c := Real.rpow_pos_of_pos (by linarith) _
  have hpow : (Real.log x) ^ c ≤ Real.log x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hlog hc1
  have hbound := hpow.trans (Real.log_le_self hx.le)
  have hi := one_div_le_one_div_of_le hp hbound
  rw [Real.rpow_neg_one, Real.rpow_neg (by linarith : 0 ≤ Real.log x)]
  simpa only [one_div] using hi

theorem floorSourceError_le_real_log_rpow {x c : ℝ} (hx : 2 ≤ x)
    (hfloorlog : 1 ≤ Real.log ((Nat.floor x : ℕ) : ℝ))
    (hlog : 1 ≤ Real.log x) (hc1 : c ≤ 1) :
    taoProp111FloorSourceError (Nat.floor x) ≤ 192000 * (Real.log x) ^ (-c) := by
  have he := floorSourceError_le_real_rpow hx hfloorlog (c := 1) (by norm_num) le_rfl
  have hi := inv_le_log_rpow_neg (by linarith : 0 < x) hlog hc1
  nlinarith

end CollatzClockAudit

#print axioms CollatzClockAudit.rpow_neg_le_two_mul_of_half_le
#print axioms CollatzClockAudit.floor_rpow_neg_le_two_mul
#print axioms CollatzClockAudit.floor_log_rpow_neg_le_two_mul
#print axioms CollatzClockAudit.floorSourceError_le_floor_rpow
#print axioms CollatzClockAudit.floorSourceError_le_real_rpow
#print axioms CollatzClockAudit.inv_le_log_rpow_neg
#print axioms CollatzClockAudit.floorSourceError_le_real_log_rpow
