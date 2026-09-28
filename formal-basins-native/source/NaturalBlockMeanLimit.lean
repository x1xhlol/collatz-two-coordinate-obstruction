import NaturalObservableRates
import ClosedWindowMeanLimit
import ActualBasinDensity
import ActualUnconditionalGreen

set_option autoImplicit false
open Filter
open scoped Topology

namespace CollatzCanonical.NativeTao
open Erdos1135 CollatzClockAudit CollatzCylinderPacking.Arithmetic
open CollatzCanonical.DirichletAbelian

noncomputable def naturalOddBlockMean (w : ℕ → ℝ) (y : ℝ) : ℝ := by
  classical
  exact if h : (ND.oddBlock y).Nonempty then
    Tao.pmfExpectation (ND.uniformOddBlockPMF y h) (fun q => w q.1) else 0

theorem naturalOddBlockMean_eq (w : ℕ → ℝ) (y : ℝ)
    (hwindow : (ND.oddBlock y).Nonempty) :
    naturalOddBlockMean w y =
      Tao.pmfExpectation (ND.uniformOddBlockPMF y hwindow) (fun q => w q.1) := by
  simp only [naturalOddBlockMean, dif_pos hwindow]

theorem native_branch_log_expectation (w : ℕ → ℝ) {x : ℝ} (hx : 1 ≤ x)
    (hmass : 0 < Tao.logFinsetMass (ND.oddBlock (ND.transportSourceY x .alpha))) :
    Tao.pmfExpectation (ND.logOddBlockPMF (ND.transportSourceY x .alpha) hmass)
      (fun q => w q.1) = closedOddWindowExpectation w
        (Tao.taoAlpha * Real.log x) (Tao.taoAlpha * (Tao.taoAlpha * Real.log x)) := by
  exact (native_iterated_power_window_expectation w
    (a := Tao.taoAlpha) (d := Tao.taoAlpha) hx Tao.taoAlpha_pos.le hmass).trans
      (by rw [mul_assoc])

theorem natural_block_limit_of_comparison {w : ℕ → ℝ} {L : ℝ} {error : ℝ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (hmean : Tendsto (fun t => oddLogarithmicCumulative w t / t) atTop (𝓝 (L / 2)))
    (herror : Tendsto error atTop (𝓝 0))
    (hcompare : ∀ᶠ x : ℝ in atTop, ∀ _hx : 1 ≤ x,
      ∃ hwindow : (ND.oddBlock (ND.transportSourceY x .alpha)).Nonempty,
      ∃ hmass : 0 < Tao.logFinsetMass (ND.oddBlock (ND.transportSourceY x .alpha)),
      |Tao.pmfExpectation (ND.uniformOddBlockPMF (ND.transportSourceY x .alpha) hwindow)
          (fun q => w q.1) -
        Tao.pmfExpectation (ND.logOddBlockPMF (ND.transportSourceY x .alpha) hmass)
          (fun q => w q.1)| ≤ error x) :
    Tendsto (naturalOddBlockMean w) atTop (𝓝 L) := by
  have hclosed : Tendsto (fun x => closedOddWindowExpectation w
      (Tao.taoAlpha * Real.log x) (Tao.taoAlpha * (Tao.taoAlpha * Real.log x)))
      atTop (𝓝 L) := by
    have h := (closed_window_mean_limit hw0 hw1 Tao.taoAlpha_one_lt hmean).comp
      (Real.tendsto_log_atTop.const_mul_atTop Tao.taoAlpha_pos)
    simpa only [Function.comp_def, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h
  have hz : Tendsto (fun x => naturalOddBlockMean w (ND.transportSourceY x .alpha) -
      closedOddWindowExpectation w (Tao.taoAlpha * Real.log x)
        (Tao.taoAlpha * (Tao.taoAlpha * Real.log x))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ herror
    filter_upwards [hcompare, eventually_ge_atTop (1 : ℝ)] with x hcompare hx
    obtain ⟨hwindow, hmass, hbound⟩ := hcompare hx
    rw [Real.norm_eq_abs, naturalOddBlockMean_eq w _ hwindow,
      ← native_branch_log_expectation w hx hmass]
    exact hbound
  have hsource : Tendsto (fun x => naturalOddBlockMean w (ND.transportSourceY x .alpha))
      atTop (𝓝 L) := by
    simpa only [sub_add_cancel, zero_add] using hz.add hclosed
  have hinverse : Tendsto (fun y : ℝ => y ^ (1 / Tao.taoAlpha)) atTop atTop :=
    tendsto_rpow_atTop (one_div_pos.mpr Tao.taoAlpha_pos)
  apply (hsource.comp hinverse).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  dsimp only [Function.comp_def, ND.transportSourceY, ND.alpha]
  change naturalOddBlockMean w ((y ^ (1 / Tao.taoAlpha)) ^ Tao.taoAlpha) = naturalOddBlockMean w y
  rw [← Real.rpow_mul hy, one_div_mul_cancel Tao.taoAlpha_pos.ne', Real.rpow_one]

theorem natural_comparison_error_tendsto_zero :
    Tendsto (fun x : ℝ => 400000 * x ^ (-(1 / 12800000 : ℝ)) +
      768512 * (Real.log x) ^ (-(1 / 40 : ℝ))) atTop (𝓝 0) := by
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 12800000)).const_mul 400000
  have hl := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 40)).comp
    Real.tendsto_log_atTop).const_mul 768512
  simpa only [mul_zero, add_zero, Function.comp_def] using hp.add hl

theorem actual_basin_natural_block_mean (N : ℕ) :
    Tendsto (naturalOddBlockMean (basinIndicator N)) atTop (𝓝 (actualBasinDensity N)) := by
  apply natural_block_limit_of_comparison
    (fun q => (basinIndicator_bounds N q).1) (fun q => (basinIndicator_bounds N q).2)
    (actual_basin_odd_mean N) natural_comparison_error_tendsto_zero
  filter_upwards [eventually_natural_basin_comparison N] with x hx
  exact fun hx1 => hx hx1 .alpha

theorem actual_weight_natural_block_mean (N : ℕ) :
    Tendsto (naturalOddBlockMean (firstHitWeight N)) atTop (𝓝 (actualFirstHitDensity N)) := by
  let b : ℝ := (CollatzCanonical.PackingParameters.beta + 1) / 2
  have hbβ : CollatzCanonical.PackingParameters.beta < b := by
    dsimp [b]; linarith [CollatzCanonical.PackingParameters.beta_lt_one]
  have hb1 : b < 1 := by
    dsimp [b]; linarith [CollatzCanonical.PackingParameters.beta_lt_one]
  obtain ⟨C, _, hcompare⟩ := eventually_natural_weight_comparison b hbβ hb1
  have hpack : Tendsto (fun x : ℝ => 2 * C * x ^ (b - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - b)).const_mul (2 * C)
    simpa only [neg_sub, mul_zero] using h
  have herror := hpack.add natural_comparison_error_tendsto_zero
  simp only [zero_add] at herror
  apply natural_block_limit_of_comparison
    (fun q => (firstHitWeight_bounds N q).1) (fun q => (firstHitWeight_bounds N q).2)
    (actual_firstHitWeight_odd_mean N) herror
  filter_upwards [hcompare N] with x hx
  intro hx1
  obtain ⟨hw, hm, hbound⟩ := hx hx1 .alpha
  exact ⟨hw, hm, by simpa only [add_assoc] using hbound⟩

#print axioms actual_basin_natural_block_mean
#print axioms actual_weight_natural_block_mean

end CollatzCanonical.NativeTao
