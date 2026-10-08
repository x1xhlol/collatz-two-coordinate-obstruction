import TrapConcentrationScales

/-! A square-root increment threshold and a three-quarter-power tube. -/

set_option autoImplicit false
open Filter
open scoped Topology

namespace Erdos1135.Tao

noncomputable def trapConcentrationH (n : ℕ) : ℕ := ⌈(n : ℝ) ^ (1 / 2 : ℝ)⌉₊

noncomputable def trapConcentrationV (n : ℕ) : ℝ := trapConcentrationH n

noncomputable def trapConcentrationD (n : ℕ) : ℝ := (n : ℝ) ^ (3 / 4 : ℝ)

noncomputable def trapConcentrationFailure (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * (15 * Real.exp (-Real.log (21 / 20 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ))) +
    (n : ℝ) * (2 * Real.exp (-(1 / 32 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)))

theorem trap_concentration_H_sublinear :
    ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n : ℕ in atTop,
      (trapConcentrationH n : ℝ) ≤ gamma * (n : ℝ) :=
  trap_nat_ceil_rpow_sublinear (1 / 2) (by norm_num)

theorem trap_concentration_D_sublinear :
    ∀ gamma : ℝ, 0 < gamma → ∀ᶠ n : ℕ in atTop,
      trapConcentrationD n ≤ gamma * (n : ℝ) :=
  trap_nat_rpow_sublinear (3 / 4) (by norm_num)

theorem trap_concentration_failure_tendsto :
    Tendsto trapConcentrationFailure atTop (𝓝 0) := by
  have hfirst := (trap_tendsto_nat_add_one_mul_exp_rpow (1 / 2)
    (Real.log (21 / 20 : ℝ)) (by norm_num) (Real.log_pos (by norm_num))).const_mul 15
  have hsecond := (trap_tendsto_nat_mul_exp_rpow (1 / 2) (1 / 32)
    (by norm_num) (by norm_num)).const_mul 2
  have h := hfirst.add hsecond
  simp only [mul_zero, add_zero] at h
  apply h.congr
  intro n
  dsimp [trapConcentrationFailure]
  ring

theorem trap_concentration_prefix_exponent_le
    (n J : ℕ) (hn : 1 ≤ n) (hJ : 0 < J) (hJn : 2 * J ≤ n) :
    (1 / 32 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) ≤
      min (trapConcentrationD n ^ 2 / (32 * ((2 * J : ℕ) : ℝ)))
        (trapConcentrationD n / 8) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hJ0 : (0 : ℝ) < (2 * J : ℕ) := by exact_mod_cast (show 0 < 2 * J by omega)
  have hJn' : ((2 * J : ℕ) : ℝ) ≤ n := by exact_mod_cast hJn
  have hsqrt : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hn0.le _
  have hDsq : trapConcentrationD n ^ 2 = (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
    unfold trapConcentrationD
    rw [← Real.rpow_natCast ((n : ℝ) ^ (3 / 4 : ℝ)) 2,
      ← Real.rpow_mul hn0.le]
    rw [show (3 / 4 : ℝ) * (2 : ℕ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hn0, Real.rpow_one]
  apply le_min
  · apply (le_div_iff₀ (show 0 < 32 * ((2 * J : ℕ) : ℝ) by positivity)).mpr
    rw [hDsq]
    nlinarith [mul_le_mul_of_nonneg_right hJn' hsqrt]
  · have hpower : (n : ℝ) ^ (1 / 2 : ℝ) ≤ trapConcentrationD n :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    linarith

theorem trap_concentration_error_bound
    (n J : ℕ) (hn : 1 ≤ n) (hJ : 0 < J) (hJn : 2 * J ≤ n) :
    ((n / 2 + 1 : ℕ) : ℝ) *
        (15 * Real.exp (-Real.log (21 / 20 : ℝ) *
          min (trapConcentrationH n : ℝ) (trapConcentrationV n))) +
      ((2 * J : ℕ) : ℝ) * (2 * Real.exp
        (-min (trapConcentrationD n ^ 2 / (32 * ((2 * J : ℕ) : ℝ)))
          (trapConcentrationD n / 8))) ≤ trapConcentrationFailure n := by
  have hH : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (trapConcentrationH n : ℝ) := Nat.le_ceil _
  have halpha : 0 ≤ Real.log (21 / 20 : ℝ) := (Real.log_pos (by norm_num)).le
  have hincrement : Real.exp (-Real.log (21 / 20 : ℝ) * (trapConcentrationH n : ℝ)) ≤
      Real.exp (-Real.log (21 / 20 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hH (neg_nonpos.mpr halpha))
  have hcount : ((n / 2 + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast (show n / 2 + 1 ≤ n + 1 by omega)
  have hprefix : Real.exp
      (-min (trapConcentrationD n ^ 2 / (32 * ((2 * J : ℕ) : ℝ)))
        (trapConcentrationD n / 8)) ≤
      Real.exp (-(1 / 32 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h := neg_le_neg (trap_concentration_prefix_exponent_le n J hn hJ hJn)
    simpa only [neg_mul] using h
  have hJn' : ((2 * J : ℕ) : ℝ) ≤ n := by exact_mod_cast hJn
  simp only [trapConcentrationV, min_self, trapConcentrationFailure]
  apply add_le_add
  · exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hincrement (by norm_num)) (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hcount (by positivity))
  · exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hprefix (by norm_num)) (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hJn' (by positivity))

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_concentration_failure_tendsto
#print axioms Erdos1135.Tao.trap_concentration_error_bound
