import Erdos1135.ND.Fourier.FixedTotalRatioAdjacent
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Literal Fixed-Total Ratio Window

This leaf fixes the literal v10 central window
`ceil (16 * sqrt (j * log j))`, proves its `j >= 150` scalar and support
packet, and lifts the checked adjacent likelihood recurrence to logarithms.
The finite log telescope and the frozen `57/1021` endpoint are the next
gated unit.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- The literal scale in the SL-D(ii) central window. -/
noncomputable def ndFixedTotalRatioScale (j : ℕ) : ℝ :=
  Real.sqrt ((j : ℝ) * Real.log (j : ℝ))

/-- The literal natural ceiling radius from the frozen v10 proof. -/
noncomputable def ndFixedTotalRatioRadius (j : ℕ) : ℕ :=
  Nat.ceil (16 * ndFixedTotalRatioScale j)

/-- The closed central window `W'`: endpoint support intersected with the
literal radius. -/
def ndFixedTotalRatioGood (j u : ℕ) : Prop :=
  j ≤ u ∧
    |(u : ℝ) - 2 * (j : ℝ)| ≤ (ndFixedTotalRatioRadius j : ℝ)

/-- Explicit logarithmic threshold needed by the literal ceiling window. -/
theorem real_log_nat_le_div_twentyNine
    {j : ℕ} (hj : 150 ≤ j) :
    Real.log (j : ℝ) ≤ (j : ℝ) / 29 := by
  have hjR : (150 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjPos : (0 : ℝ) < (j : ℝ) := by positivity
  have h150exp : Real.exp 1 ≤ (150 : ℝ) :=
    Real.exp_one_lt_three.le.trans (by norm_num)
  have hjexp : Real.exp 1 ≤ (j : ℝ) := h150exp.trans hjR
  have hlogTwo : Real.log (2 : ℝ) ≤ 7 / 10 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hratioPos : (0 : ℝ) < 75 / 64 := by norm_num
  have hlogRatio : Real.log (75 / 64 : ℝ) ≤ 11 / 64 := by
    have h := Real.log_le_sub_one_of_pos hratioPos
    norm_num at h ⊢
    exact h
  have hfactor : (150 : ℝ) = (2 : ℝ) ^ 7 * (75 / 64 : ℝ) := by
    norm_num
  have hlog150 : Real.log (150 : ℝ) ≤ 51 / 10 := by
    rw [hfactor, Real.log_mul (pow_ne_zero _ (by norm_num))
      (by norm_num), Real.log_pow]
    norm_num at hlogTwo hlogRatio ⊢
    nlinarith
  have hanti :
      Real.log (j : ℝ) / (j : ℝ) ≤ Real.log (150 : ℝ) / 150 :=
    Real.log_div_self_antitoneOn h150exp hjexp hjR
  have hratio : Real.log (j : ℝ) / (j : ℝ) ≤ 1 / 29 := by
    calc
      Real.log (j : ℝ) / (j : ℝ) ≤
          Real.log (150 : ℝ) / 150 := hanti
      _ ≤ (51 / 10 : ℝ) / 150 :=
        div_le_div_of_nonneg_right hlog150 (by norm_num)
      _ ≤ 1 / 29 := by norm_num
  calc
    Real.log (j : ℝ) =
        (Real.log (j : ℝ) / (j : ℝ)) * (j : ℝ) := by
      field_simp
    _ ≤ (1 / 29 : ℝ) * (j : ℝ) :=
      mul_le_mul_of_nonneg_right hratio hjPos.le
    _ = (j : ℝ) / 29 := by ring

theorem ndFixedTotalRatioScale_nonneg (j : ℕ) :
    0 ≤ ndFixedTotalRatioScale j :=
  Real.sqrt_nonneg _

theorem two_le_ndFixedTotalRatioScale
    {j : ℕ} (hj : 150 ≤ j) :
    (2 : ℝ) ≤ ndFixedTotalRatioScale j := by
  have hjR : (150 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjPos : (0 : ℝ) < (j : ℝ) := by positivity
  have h150exp : Real.exp 1 ≤ (150 : ℝ) :=
    Real.exp_one_lt_three.le.trans (by norm_num)
  have hjexp : Real.exp 1 ≤ (j : ℝ) := h150exp.trans hjR
  have hlog : (1 : ℝ) ≤ Real.log (j : ℝ) :=
    (Real.le_log_iff_exp_le hjPos).2 hjexp
  unfold ndFixedTotalRatioScale
  apply Real.le_sqrt_of_sq_le
  nlinarith

/-- The ceiling is below the frozen three-`j` support margin. -/
theorem ndFixedTotalRatioRadius_le_three_mul
    {j : ℕ} (hj : 150 ≤ j) :
    ndFixedTotalRatioRadius j ≤ 3 * j := by
  let J : ℝ := j
  let S : ℝ := ndFixedTotalRatioScale j
  have hjR : (150 : ℝ) ≤ J := by
    change (150 : ℝ) ≤ (j : ℝ)
    exact_mod_cast hj
  have hJ0 : 0 ≤ J := by positivity
  have hlog := real_log_nat_le_div_twentyNine hj
  have hprod : J * Real.log J ≤ J * (J / 29) :=
    mul_le_mul_of_nonneg_left hlog hJ0
  have htarget0 : 0 ≤ (3 * J - 1) / 16 := by nlinarith
  have hscale : S ≤ (3 * J - 1) / 16 := by
    unfold S ndFixedTotalRatioScale J
    rw [Real.sqrt_le_iff]
    constructor
    · exact htarget0
    · nlinarith
  have hceil :
      (ndFixedTotalRatioRadius j : ℝ) < 16 * S + 1 := by
    simpa only [ndFixedTotalRatioRadius] using
      Nat.ceil_lt_add_one
        (mul_nonneg (by norm_num) (ndFixedTotalRatioScale_nonneg j))
  have hreal :
      (ndFixedTotalRatioRadius j : ℝ) ≤ (3 * j : ℕ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    change (ndFixedTotalRatioRadius j : ℝ) ≤ 3 * J
    linarith
  exact_mod_cast hreal

theorem sixteen_mul_scale_le_radius (j : ℕ) :
    16 * ndFixedTotalRatioScale j ≤ (ndFixedTotalRatioRadius j : ℝ) := by
  exact Nat.le_ceil _

theorem radius_lt_sixteen_mul_scale_add_one (j : ℕ) :
    (ndFixedTotalRatioRadius j : ℝ) <
      16 * ndFixedTotalRatioScale j + 1 := by
  simpa only [ndFixedTotalRatioRadius] using
    Nat.ceil_lt_add_one
      (mul_nonneg (by norm_num) (ndFixedTotalRatioScale_nonneg j))

theorem radius_add_one_le_eighteen_mul_scale
    {j : ℕ} (hj : 150 ≤ j) :
    (ndFixedTotalRatioRadius j : ℝ) + 1 ≤
      18 * ndFixedTotalRatioScale j := by
  have hceil := radius_lt_sixteen_mul_scale_add_one j
  have hscale := two_le_ndFixedTotalRatioScale hj
  linarith

theorem two_mul_radius_add_one_le_thirtyFour_mul_scale
    {j : ℕ} (hj : 150 ≤ j) :
    2 * (ndFixedTotalRatioRadius j : ℝ) + 1 ≤
      34 * ndFixedTotalRatioScale j := by
  have hceil := radius_lt_sixteen_mul_scale_add_one j
  have hscale := two_le_ndFixedTotalRatioScale hj
  linarith

/-- Every literal-window endpoint is below `5*j`. -/
theorem ndFixedTotalRatioGood_le_five_mul
    {j u : ℕ} (hj : 150 ≤ j) (hu : ndFixedTotalRatioGood j u) :
    u ≤ 5 * j := by
  have hupper :
      (u : ℝ) - 2 * (j : ℝ) ≤ (ndFixedTotalRatioRadius j : ℝ) :=
    le_trans (le_abs_self _) hu.2
  have hradius := ndFixedTotalRatioRadius_le_three_mul hj
  have hradiusR :
      (ndFixedTotalRatioRadius j : ℝ) ≤ (3 * j : ℕ) := by
    exact_mod_cast hradius
  have huR : (u : ℝ) ≤ 5 * (j : ℝ) := by
    norm_num at hradiusR
    linarith
  exact_mod_cast huR

/-- H2 and the literal window leave strict room for every adjacent suffix
step. -/
theorem ndFixedTotalRatioGood_strict_suffix_room
    {j n L u : ℕ} (hj : 150 ≤ j) (hjn : 8 * j ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hu : ndFixedTotalRatioGood j u) :
    u + (n - j) < L := by
  have hlowerR : (15 : ℝ) * (n : ℝ) ≤ 8 * (L : ℝ) := by
    have hneg := neg_le_of_abs_le hD
    nlinarith
  have hlower : 15 * n ≤ 8 * L := by exact_mod_cast hlowerR
  have hu5 : u ≤ 5 * j := ndFixedTotalRatioGood_le_five_mul hj hu
  omega

/-- The exact adjacent multiplier is positive on every strict feasible
edge. -/
theorem ndFixedTotalHeadLikelihoodStep_pos
    {j n L u : ℕ} (hjn : j < n)
    (huTail : u + (n - j) < L) :
    0 < ndFixedTotalHeadLikelihoodStep j n L u := by
  have hnum : 0 < L - u - (n - j) := by omega
  have hden : 0 < L - u - 1 := by omega
  unfold ndFixedTotalHeadLikelihoodStep
  exact div_pos
    (mul_pos (by norm_num) (by exact_mod_cast hnum))
    (by exact_mod_cast hden)

/-- On reference support, the PMF likelihood ratio is the checked suffix
factor. -/
theorem ndFixedTotalHeadTotalPMF_likelihoodRatio_eq_factor
    {j n L u : ℕ} (hj : 0 < j) (hjn : j < n) (hnL : n ≤ L)
    (hju : j ≤ u) :
    (ndFixedTotalHeadTotalPMF j n L hj hjn hnL u).toReal /
        (ndGeom2EndpointPMF j u).toReal =
      ndFixedTotalHeadLikelihoodFactor j n L u := by
  have hQ : 0 < (ndGeom2EndpointPMF j u).toReal := by
    rw [ndGeom2EndpointPMF_apply_toReal_eq_endpointMass]
    exact ndGeom2EndpointMass_pos hj hju
  rw [ndFixedTotalHeadTotalPMF_apply_toReal_eq_endpoint_mul_factor]
  field_simp [hQ.ne']

/-- The adjacent factor recurrence in logarithmic form. -/
theorem log_ndFixedTotalHeadLikelihoodFactor_succ_sub_eq_log_step
    {j n L u : ℕ} (hjn : j < n) (hnL : n ≤ L)
    (huTail : u + (n - j) < L) :
    Real.log (ndFixedTotalHeadLikelihoodFactor j n L (u + 1)) -
        Real.log (ndFixedTotalHeadLikelihoodFactor j n L u) =
      Real.log (ndFixedTotalHeadLikelihoodStep j n L u) := by
  have hfactor : 0 < ndFixedTotalHeadLikelihoodFactor j n L u :=
    ndFixedTotalHeadLikelihoodFactor_pos hjn hnL (by omega)
  have hstep : 0 < ndFixedTotalHeadLikelihoodStep j n L u :=
    ndFixedTotalHeadLikelihoodStep_pos hjn huTail
  rw [ndFixedTotalHeadLikelihoodFactor_succ hjn huTail,
    Real.log_mul hfactor.ne' hstep.ne']
  ring

end

end ND
end Erdos1135
