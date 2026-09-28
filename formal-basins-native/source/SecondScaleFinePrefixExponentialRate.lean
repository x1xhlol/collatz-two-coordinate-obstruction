import SecondScaleCanonicalLocalClockProbability

set_option autoImplicit false
open Filter Topology

namespace CollatzClockSecondScale
open Erdos1135SecondScale.Tao

/-- The fine prefix error retains a stretched exponential tail in log B. -/
theorem localPrefixError_le_stretched_exp {B : ℕ}
    (hL : 100 ≤ Real.log (B : ℝ)) :
    localPrefixError B ≤ (2 * Real.log (B : ℝ) + 4) *
      Real.exp (-(Real.log (B : ℝ)) ^ (1 / 5 : ℝ) / 6400) := by
  let L := Real.log (B : ℝ)
  let n := (taoSection5N0 B : ℝ)
  let u := L ^ (1 / 5 : ℝ)
  let E := L ^ (3 / 5 : ℝ)
  have hLp : 0 < L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hscale := coarse_horizon_scale hL
  have hnlo : L / 20 ≤ n := hscale.1
  have hnhi : n ≤ L / 5 := hscale.2
  have hnp : 0 < n := by linarith
  have hu : 0 ≤ u := Real.rpow_nonneg hLp.le _
  have huL : u ≤ L := by
    dsimp [u]
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (1 / 5 : ℝ) ≤ 1 by norm_num)
  have huE : u ≤ E := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hE2 : E ^ 2 = u * L := by
    dsimp [E, u]
    calc
      (L ^ (3 / 5 : ℝ)) ^ 2 = L ^ ((3 / 5 : ℝ) * 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLp.le]
        norm_num
      _ = L ^ ((1 / 5 : ℝ) + 1) := by congr 1; norm_num
      _ = L ^ (1 / 5 : ℝ) * L := by rw [Real.rpow_add hLp, Real.rpow_one]
  have hquad : u / 6400 ≤ E ^ 2 / (32 * n) := by
    apply (le_div_iff₀ (by positivity : 0 < 32 * n)).mpr
    rw [hE2]
    nlinarith [mul_le_mul_of_nonneg_left hnhi hu]
  have hlin : u / 6400 ≤ E / 8 := by nlinarith
  have hmin : u / 6400 ≤ min (E ^ 2 / (32 * n)) (E / 8) := le_min hquad hlin
  have htail : Real.exp (-min (E ^ 2 / (32 * n)) (E / 8)) ≤
      Real.exp (-u / 6400) := Real.exp_le_exp.mpr (by linarith)
  have hideal : n * (2 * Real.exp (-min (E ^ 2 / (32 * n)) (E / 8))) ≤
      2 * L * Real.exp (-u / 6400) := by
    have h1 := mul_le_mul_of_nonneg_left htail (show 0 ≤ 2 * n by positivity)
    have h2 := mul_le_mul_of_nonneg_right (show 2 * n ≤ 2 * L by linarith)
      (Real.exp_pos (-u / 6400)).le
    nlinarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    linarith
  have hlogprod := mul_le_mul_of_nonneg_right hlog2 hnp.le
  have hval : (2 : ℝ) ^ (-((1 / 128 : ℝ) * n)) ≤ Real.exp (-u / 6400) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr (by nlinarith)
  unfold localPrefixError taoSection5TypicalSlack
  change n * (2 * Real.exp (-min (E ^ 2 / (32 * n)) (E / 8))) +
    4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * n)) ≤ (2 * L + 4) * Real.exp (-u / 6400)
  nlinarith

/-- Polynomial prefactors are absorbed into half the stretched exponential
rate, with explicit positive exponent and coefficient. -/
theorem eventually_localPrefixError_stretched_exp :
    ∀ᶠ B : ℕ in atTop,
      localPrefixError B ≤ Real.exp (-(Real.log (B : ℝ)) ^ (1 / 5 : ℝ) / 12800) := by
  have hlog : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hroot : Tendsto (fun B : ℕ => (Real.log (B : ℝ)) ^ (1 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp hlog
  have h5 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (5 : ℝ) (1 / 12800 : ℝ) (by norm_num)
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (0 : ℝ) (1 / 12800 : ℝ) (by norm_num)
  have hsum := ((h5.const_mul 2).add (h0.const_mul 4)).comp hroot
  simp only [mul_zero, add_zero] at hsum
  filter_upwards [hlog.eventually_ge_atTop 100,
    hsum.eventually_le_const (show (0 : ℝ) < 1 by norm_num)] with B hL hsmall
  let L := Real.log (B : ℝ)
  let u := L ^ (1 / 5 : ℝ)
  have hLp : 0 < L := by dsimp [L]; linarith
  have hid : u ^ (5 : ℝ) = L := by
    dsimp [u]
    rw [← Real.rpow_mul hLp.le]
    norm_num
  have hs : (2 * L + 4) * Real.exp (-(1 / 12800 : ℝ) * u) ≤ 1 := by
    change 2 * (u ^ (5 : ℝ) * Real.exp (-(1 / 12800 : ℝ) * u)) +
      4 * (u ^ (0 : ℝ) * Real.exp (-(1 / 12800 : ℝ) * u)) ≤ 1 at hsmall
    rw [hid, Real.rpow_zero] at hsmall
    nlinarith
  calc
    localPrefixError B ≤ (2 * L + 4) * Real.exp (-u / 6400) :=
      localPrefixError_le_stretched_exp hL
    _ = ((2 * L + 4) * Real.exp (-(1 / 12800 : ℝ) * u)) *
        Real.exp (-u / 12800) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
    _ ≤ Real.exp (-u / 12800) := by
      simpa using mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le

end CollatzClockSecondScale
