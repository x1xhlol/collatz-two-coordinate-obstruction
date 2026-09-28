import GreenKernelScalars
import Mathlib.Analysis.Asymptotics.Defs

set_option autoImplicit false
open Filter Topology Asymptotics

namespace CollatzCanonical.GreenKernelScalars

theorem kappa_quadratic_remainder_bound {t : ℝ}
    (h₂ : |(-Real.log 2) * t| ≤ 1)
    (h₃ : |Real.log (3 / 2 : ℝ) * t| ≤ 1) :
    |1 - kappa (1 + t) - delta * t| ≤
      ((Real.log 2) ^ 2 + (Real.log (3 / 2 : ℝ)) ^ 2) / 2 * t ^ 2 := by
  have h₂' := Real.abs_exp_sub_one_sub_id_le h₂
  have h₃' := Real.abs_exp_sub_one_sub_id_le h₃
  have he : 1 - kappa (1 + t) - delta * t =
      - (1 / 2 : ℝ) * ((Real.exp (-Real.log 2 * t) - 1 - (-Real.log 2 * t)) +
        (Real.exp (Real.log (3 / 2 : ℝ) * t) - 1 - Real.log (3 / 2 : ℝ) * t)) := by
    rw [kappa_one_add, delta_eq_logs]
    ring
  rw [he, abs_mul]
  rw [show |-(1 / 2 : ℝ)| = (1 / 2 : ℝ) by norm_num]
  calc
    1 / 2 * |(Real.exp (-Real.log 2 * t) - 1 - -Real.log 2 * t) +
        (Real.exp (Real.log (3 / 2 : ℝ) * t) - 1 - Real.log (3 / 2 : ℝ) * t)|
        ≤ 1 / 2 * (|Real.exp (-Real.log 2 * t) - 1 - -Real.log 2 * t| +
          |Real.exp (Real.log (3 / 2 : ℝ) * t) - 1 - Real.log (3 / 2 : ℝ) * t|) := by
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ 1 / 2 * ((-Real.log 2 * t) ^ 2 + (Real.log (3 / 2 : ℝ) * t) ^ 2) := by
      exact mul_le_mul_of_nonneg_left (add_le_add h₂' h₃') (by norm_num)
    _ = _ := by ring

theorem kappa_quadratic_remainder_eventually :
    ∀ᶠ s : ℝ in 𝓝 1, |1 - kappa s - delta * (s - 1)| ≤
      ((Real.log 2) ^ 2 + (Real.log (3 / 2 : ℝ)) ^ 2) / 2 * (s - 1) ^ 2 := by
  have ht : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 0) := by
    simpa only [sub_self] using (tendsto_id.sub_const (1 : ℝ) :
      Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)))
  have small (a : ℝ) : ∀ᶠ s : ℝ in 𝓝 1, |a * (s - 1)| ≤ 1 := by
    have h : Tendsto (fun s : ℝ => |a * (s - 1)|) (𝓝 1) (𝓝 0) := by
      simpa only [mul_zero, abs_zero] using ((tendsto_const_nhds (x := a)).mul ht).abs
    exact (h.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ hs => hs.le
  filter_upwards [small (-Real.log 2), small (Real.log (3 / 2 : ℝ))] with s h₂ h₃
  simpa only [show (1 : ℝ) + (s - 1) = s by ring] using
    kappa_quadratic_remainder_bound h₂ h₃

theorem kappa_quadratic_remainder_isBigO :
    (fun s : ℝ => 1 - kappa s - delta * (s - 1)) =O[𝓝 1]
      (fun s : ℝ => (s - 1) ^ 2) := by
  apply IsBigO.of_bound (((Real.log 2) ^ 2 + (Real.log (3 / 2 : ℝ)) ^ 2) / 2)
  filter_upwards [kappa_quadratic_remainder_eventually] with s hs
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (s - 1))] using hs

#print axioms kappa_quadratic_remainder_bound
#print axioms kappa_quadratic_remainder_eventually
#print axioms kappa_quadratic_remainder_isBigO

end CollatzCanonical.GreenKernelScalars
