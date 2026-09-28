import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

namespace CollatzCanonical.GreenKernelScalars

noncomputable def kappa (s : ℝ) : ℝ :=
  (2 : ℝ) ^ (-s) + (3 / 2 : ℝ) ^ s / 3

noncomputable def delta : ℝ := Real.log (4 / 3 : ℝ) / 2

theorem delta_pos : 0 < delta := by
  unfold delta
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

theorem kappa_one : kappa 1 = 1 := by
  norm_num [kappa, Real.rpow_neg]

theorem kappa_two : kappa 2 = 1 := by
  norm_num [kappa, Real.rpow_neg, Real.rpow_two]

theorem kappa_pos (s : ℝ) : 0 < kappa s := by
  unfold kappa
  positivity

/-- The tangent inequality gives a strict chord inequality without a calculus hypothesis. -/
theorem exp_strict_chord {x y a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hxy : x ≠ y) :
    Real.exp (a * x + b * y) < a * Real.exp x + b * Real.exp y := by
  let z : ℝ := a * x + b * y
  have hxz : x - z = b * (x - y) := by
    calc
      x - z = (a + b) * x - (a * x + b * y) := by rw [hab, one_mul]
      _ = b * (x - y) := by ring
  have hnz : x - z ≠ 0 := by
    rw [hxz]
    exact mul_ne_zero hb.ne' (sub_ne_zero.mpr hxy)
  have h := add_lt_add_of_lt_of_le
    (mul_lt_mul_of_pos_left (Real.add_one_lt_exp hnz) ha)
    (mul_le_mul_of_nonneg_left (Real.add_one_le_exp (y - z)) hb.le)
  have hlin : a * (x - z + 1) + b * (y - z + 1) = 1 := by
    calc
      a * (x - z + 1) + b * (y - z + 1) =
          (a * x + b * y) - (a + b) * z + (a + b) := by ring
      _ = 1 := by rw [hab]; dsimp [z]; ring
  rw [hlin] at h
  have heqx : Real.exp z * Real.exp (x - z) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heqy : Real.exp z * Real.exp (y - z) = Real.exp y := by
    rw [← Real.exp_add]
    congr 1
    ring
  change Real.exp z < _
  calc
    Real.exp z < Real.exp z *
        (a * Real.exp (x - z) + b * Real.exp (y - z)) := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left h (Real.exp_pos z)
    _ = a * (Real.exp z * Real.exp (x - z)) +
        b * (Real.exp z * Real.exp (y - z)) := by ring
    _ = a * Real.exp x + b * Real.exp y := by rw [heqx, heqy]

theorem rpow_strict_chord_one_two {c s : ℝ}
    (hc : 0 < c) (hc1 : c ≠ 1) (hs1 : 1 < s) (hs2 : s < 2) :
    c ^ s < (2 - s) * c + (s - 1) * c ^ 2 := by
  have hlog := Real.log_ne_zero_of_pos_of_ne_one hc hc1
  have hxy : Real.log c ≠ 2 * Real.log c := by
    intro h
    apply hlog
    linarith
  have h := exp_strict_chord (x := Real.log c) (y := 2 * Real.log c)
    (a := 2 - s) (b := s - 1) (by linarith) (by linarith) (by ring) hxy
  have heq : (2 - s) * Real.log c + (s - 1) * (2 * Real.log c) =
      Real.log c * s := by ring
  have hexp : Real.exp (2 * Real.log c) = c ^ 2 := by
    rw [show 2 * Real.log c = Real.log c + Real.log c by ring,
      Real.exp_add, Real.exp_log hc]
    ring
  rw [heq, hexp, Real.exp_log hc] at h
  simpa only [Real.rpow_def_of_pos hc] using h

theorem kappa_eq_half_rpow (s : ℝ) :
    kappa s = (1 / 2 : ℝ) ^ s + (1 / 3 : ℝ) * (3 / 2 : ℝ) ^ s := by
  unfold kappa
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
    Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem kappa_lt_one {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) : kappa s < 1 := by
  have hhalf := rpow_strict_chord_one_two
    (c := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hs1 hs2
  have hthree := rpow_strict_chord_one_two
    (c := (3 / 2 : ℝ)) (by norm_num) (by norm_num) hs1 hs2
  rw [kappa_eq_half_rpow]
  nlinarith

theorem one_sub_kappa_pos {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) :
    0 < 1 - kappa s := sub_pos.mpr (kappa_lt_one hs1 hs2)

/-- The exponential's quadratic remainder gives its difference quotient directly. -/
theorem exp_linear_difference_quotient_tendsto (a : ℝ) :
    Tendsto (fun t : ℝ => (Real.exp (a * t) - 1) / t)
      (𝓝[≠] (0 : ℝ)) (𝓝 a) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have harg : Tendsto (fun t : ℝ => |a * t|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, abs_zero] using
      ((tendsto_const_nhds (x := a)).mul ht).abs
  have hsmall : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), |a * t| < 1 :=
    harg.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), t ≠ 0 := self_mem_nhdsWithin
  have hmajor : Tendsto (fun t : ℝ => a ^ 2 * |t|)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [abs_zero, mul_zero] using
      (tendsto_const_nhds (x := a ^ 2)).mul ht.abs
  have herr : Tendsto (fun t : ℝ => (Real.exp (a * t) - 1) / t - a)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun t : ℝ => a ^ 2 * |t|) _ hmajor
    filter_upwards [hsmall, hne] with t hsmall htne
    have heq : (Real.exp (a * t) - 1) / t - a =
        (Real.exp (a * t) - 1 - a * t) / t := by
      field_simp [htne]
    rw [Real.norm_eq_abs, heq, abs_div]
    calc
      |Real.exp (a * t) - 1 - a * t| / |t| ≤ (a * t) ^ 2 / |t| :=
        div_le_div_of_nonneg_right
          (Real.abs_exp_sub_one_sub_id_le hsmall.le) (abs_nonneg t)
      _ = a ^ 2 * |t| := by
        rw [mul_pow, ← sq_abs t]
        field_simp [abs_ne_zero.mpr htne]
  simpa only [sub_add_cancel, zero_add] using herr.add_const a

theorem delta_eq_logs :
    delta = (Real.log 2 - Real.log (3 / 2 : ℝ)) / 2 := by
  unfold delta
  congr 1
  convert Real.log_div (x := (2 : ℝ)) (y := (3 / 2 : ℝ))
    (by norm_num) (by norm_num) using 1
  norm_num

theorem kappa_one_add (t : ℝ) :
    kappa (1 + t) = (1 / 2 : ℝ) * Real.exp (-Real.log 2 * t) +
      (1 / 2 : ℝ) * Real.exp (Real.log (3 / 2 : ℝ) * t) := by
  unfold kappa
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  rw [show Real.log 2 * -(1 + t) = -Real.log 2 + (-Real.log 2 * t) by ring,
    show Real.log (3 / 2 : ℝ) * (1 + t) =
      Real.log (3 / 2 : ℝ) + Real.log (3 / 2 : ℝ) * t by ring,
    Real.exp_add, Real.exp_add, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
  ring

theorem kappa_difference_quotient_at_zero :
    Tendsto (fun t : ℝ => (1 - kappa (1 + t)) / t)
      (𝓝[≠] (0 : ℝ)) (𝓝 delta) := by
  have h := ((exp_linear_difference_quotient_tendsto (-Real.log 2)).add
    (exp_linear_difference_quotient_tendsto (Real.log (3 / 2 : ℝ)))).const_mul (-1 / 2 : ℝ)
  have hvalue : (-1 / 2 : ℝ) * (-Real.log 2 + Real.log (3 / 2 : ℝ)) = delta := by
    rw [delta_eq_logs]
    ring
  rw [hvalue] at h
  convert h using 1
  ext t
  rw [kappa_one_add]
  ring

/-- The critical normalization has the stated right-hand first-order limit at one. -/
theorem kappa_critical_right_limit :
    Tendsto (fun s : ℝ => (1 - kappa s) / (s - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 delta) := by
  have ht : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : Tendsto (fun s : ℝ => s) (𝓝[>] (1 : ℝ)) (𝓝 1) := nhdsWithin_le_nhds
      simpa only [sub_self] using h.sub_const 1
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change s - 1 ≠ 0
      exact ne_of_gt (sub_pos.mpr hs)
  have h := kappa_difference_quotient_at_zero.comp ht
  convert h using 1
  ext s
  change (1 - kappa s) / (s - 1) = (1 - kappa (1 + (s - 1))) / (s - 1)
  rw [show (1 : ℝ) + (s - 1) = s by ring]

#print axioms delta_pos
#print axioms kappa_one
#print axioms kappa_two
#print axioms kappa_pos
#print axioms exp_strict_chord
#print axioms rpow_strict_chord_one_two
#print axioms kappa_eq_half_rpow
#print axioms kappa_lt_one
#print axioms one_sub_kappa_pos
#print axioms exp_linear_difference_quotient_tendsto
#print axioms delta_eq_logs
#print axioms kappa_one_add
#print axioms kappa_difference_quotient_at_zero
#print axioms kappa_critical_right_limit

end CollatzCanonical.GreenKernelScalars
