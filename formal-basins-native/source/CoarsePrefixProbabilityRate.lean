import ActualPrefixEventTransfer

open Filter
open scoped Topology

namespace CollatzClockAudit
open Erdos1135.Tao

noncomputable def coarsePrefixError (B : ℕ) : ℝ :=
  (taoSection5N0 B : ℝ) * (2 * Real.exp
    (-min ((Real.log (B : ℝ) / 1000) ^ 2 / (32 * (taoSection5N0 B : ℝ)))
      (Real.log (B : ℝ) / 1000 / 8))) +
    4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ)))

private theorem log_two_lower : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  linarith

private theorem log_two_upper : Real.log (2 : ℝ) ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem coarse_horizon_scale {B : ℕ} (hL : 100 ≤ Real.log (B : ℝ)) :
    Real.log (B : ℝ) / 20 ≤ (taoSection5N0 B : ℝ) ∧
      (taoSection5N0 B : ℝ) ≤ Real.log (B : ℝ) / 5 := by
  have hlo := log_div_ten_log_two_sub_one_lt_taoSection5N0 B
  have hhi := taoSection5N0_le_log_div_ten_log_two B
  have hden : 0 < 10 * Real.log (2 : ℝ) := by positivity
  have hlos := (div_lt_iff₀ hden).mp
    (show Real.log (B : ℝ) / (10 * Real.log 2) < (taoSection5N0 B : ℝ) + 1 by linarith)
  have hhis := (le_div_iff₀ hden).mp hhi
  have hn : (0 : ℝ) ≤ taoSection5N0 B := Nat.cast_nonneg _
  have hmlo := mul_le_mul_of_nonneg_right log_two_upper (show (0 : ℝ) ≤ taoSection5N0 B + 1 by positivity)
  have hmhi := mul_le_mul_of_nonneg_right log_two_lower hn
  constructor <;> nlinarith

theorem coarsePrefixError_le_exp {B : ℕ} (hL : 100 ≤ Real.log (B : ℝ)) :
    coarsePrefixError B ≤ (2 * Real.log (B : ℝ) + 4) *
      Real.exp (-Real.log (B : ℝ) / 6400000) := by
  let L := Real.log (B : ℝ)
  let n := (taoSection5N0 B : ℝ)
  have hscale := coarse_horizon_scale hL
  have hLn : L / 20 ≤ n := hscale.1
  have hnL : n ≤ L / 5 := hscale.2
  have hLp : 0 < L := by dsimp [L]; linarith
  have hnp : 0 < n := by linarith
  have hquadratic : L / 6400000 ≤ (L / 1000) ^ 2 / (32 * n) := by
    apply (le_div_iff₀ (by positivity : 0 < 32 * n)).2
    have hm := mul_le_mul_of_nonneg_left hnL hLp.le
    nlinarith
  have hlinear : L / 6400000 ≤ L / 1000 / 8 := by linarith
  have hmin : L / 6400000 ≤ min ((L / 1000) ^ 2 / (32 * n)) (L / 1000 / 8) :=
    le_min hquadratic hlinear
  have htail : Real.exp (-min ((L / 1000) ^ 2 / (32 * n)) (L / 1000 / 8)) ≤
      Real.exp (-L / 6400000) := Real.exp_le_exp.mpr (by linarith)
  have hideal : n * (2 * Real.exp (-min ((L / 1000) ^ 2 / (32 * n)) (L / 1000 / 8))) ≤
      2 * L * Real.exp (-L / 6400000) := by
    have h1 := mul_le_mul_of_nonneg_left htail (show 0 ≤ 2 * n by positivity)
    have h2 := mul_le_mul_of_nonneg_right (show 2 * n ≤ 2 * L by linarith)
      (Real.exp_pos (-L / 6400000)).le
    nlinarith
  have hlogprod := mul_le_mul_of_nonneg_right log_two_lower hnp.le
  have hvalexp : Real.log 2 * (-(1 / 128 : ℝ) * n) ≤ -L / 6400000 := by nlinarith
  have hval : (2 : ℝ) ^ (-((1 / 128 : ℝ) * n)) ≤ Real.exp (-L / 6400000) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr (by nlinarith [hvalexp])
  unfold coarsePrefixError
  change n * (2 * Real.exp (-min ((L / 1000) ^ 2 / (32 * n)) (L / 1000 / 8))) +
    4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * n)) ≤ (2 * L + 4) * Real.exp (-L / 6400000)
  nlinarith

/-- A polynomial error in the barrier scale follows from the actual finite
Bernstein bound and the actual valuation-law approximation error. -/
theorem eventually_coarsePrefixError_le_rpow :
    ∀ᶠ B : ℕ in atTop,
      coarsePrefixError B ≤ (B : ℝ) ^ (-(1 / 12800000 : ℝ)) := by
  have hlog : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun x : ℝ => x * Real.exp (-(1 / 12800000 : ℝ) * x)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (1 : ℝ) (1 / 12800000 : ℝ) (by norm_num)
  have h0 : Tendsto (fun x : ℝ => Real.exp (-(1 / 12800000 : ℝ) * x)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (0 : ℝ) (1 / 12800000 : ℝ) (by norm_num)
  have hsmall : ∀ᶠ B : ℕ in atTop,
      (2 * Real.log (B : ℝ) + 4) * Real.exp (-(1 / 12800000 : ℝ) * Real.log (B : ℝ)) ≤ 1 := by
    have hsum := ((h1.const_mul 2).add (h0.const_mul 4)).comp hlog
    simp only [mul_zero, add_zero] at hsum
    have he := hsum.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    filter_upwards [he] with B hB
    dsimp only [Function.comp_def] at hB
    nlinarith
  filter_upwards [hlog.eventually_ge_atTop 100, eventually_ge_atTop (1 : ℕ), hsmall]
    with B hL hB hsmallB
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  calc
    coarsePrefixError B ≤ (2 * Real.log (B : ℝ) + 4) *
        Real.exp (-Real.log (B : ℝ) / 6400000) := coarsePrefixError_le_exp hL
    _ = ((2 * Real.log (B : ℝ) + 4) *
        Real.exp (-(1 / 12800000 : ℝ) * Real.log (B : ℝ))) *
        Real.exp (-(1 / 12800000 : ℝ) * Real.log (B : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
    _ ≤ Real.exp (-(1 / 12800000 : ℝ) * Real.log (B : ℝ)) := by
      simpa using mul_le_mul_of_nonneg_right hsmallB (Real.exp_pos _).le
    _ = (B : ℝ) ^ (-(1 / 12800000 : ℝ)) := by
      rw [Real.rpow_def_of_pos hBR]
      congr 1
      ring

end CollatzClockAudit

#print axioms CollatzClockAudit.coarse_horizon_scale
#print axioms CollatzClockAudit.coarsePrefixError_le_exp
#print axioms CollatzClockAudit.eventually_coarsePrefixError_le_rpow
