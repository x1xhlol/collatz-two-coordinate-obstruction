import NaturalObservableTransport

set_option autoImplicit false
open Filter
open scoped Topology

namespace CollatzCanonical.NativeTao
open Erdos1135 CollatzClockAudit CollatzCylinderPacking.Arithmetic

theorem eventually_natural_log_small_landing :
    ∀ᶠ x : ℝ in atTop, ∀ (hx : 1 ≤ x) (branch : Tao.TaoSection5SourceBranch)
      (hmass : 0 < Tao.logFinsetMass (ND.oddBlock (ND.transportSourceY x branch))),
      Tao.pmfProb (ND.logOddBlockPMF (ND.transportSourceY x branch) hmass)
        {q | ((ND.passLocationOrOne x q.1 hx).1 : ℝ) ≤ x ^ (1 / 2 : ℝ)} ≤
        200000 * x ^ (-(1 / 12800000 : ℝ)) := by
  filter_upwards [eventually_real_large_landing_polynomial] with x h
  intro hx branch hmass
  rw [natural_bad_landing_probability hx hmass]
  have hm : 0 < Tao.logFinsetMass
      (Tao.oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch)) := by
    simpa only [natural_block_eq_clock] using hmass
  have hh := h branch hm
  cases branch <;> exact hh

theorem eventually_natural_basin_comparison (N : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (_hx : 1 ≤ x) (branch : Tao.TaoSection5SourceBranch),
      let y := ND.transportSourceY x branch
      ∃ hwindow : (ND.oddBlock y).Nonempty,
      ∃ hmass : 0 < Tao.logFinsetMass (ND.oddBlock y),
      |Tao.pmfExpectation (ND.uniformOddBlockPMF y hwindow) (fun q => basinIndicator N q.1) -
        Tao.pmfExpectation (ND.logOddBlockPMF y hmass) (fun q => basinIndicator N q.1)| ≤
        400000 * x ^ (-(1 / 12800000 : ℝ)) +
        768512 * (Real.log x) ^ (-(1 / 40 : ℝ)) := by
  filter_upwards [unconditional_natural_passage_rates, eventually_natural_log_small_landing,
    eventually_ge_atTop (N : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop (N : ℝ)]
    with x hrates hlanding hN hNsqrt
  intro hx branch
  obtain ⟨hwindow, hmass, _, htv⟩ := hrates hx branch
  refine ⟨hwindow, hmass, ?_⟩
  have h := natural_basin_comparison hx N hN hNsqrt hwindow hmass
  have hb := hlanding hx branch hmass
  linarith

theorem eventually_natural_weight_comparison (b : ℝ)
    (hbβ : CollatzCanonical.PackingParameters.beta < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ᶠ x : ℝ in atTop,
      ∀ (_hx : 1 ≤ x) (branch : Tao.TaoSection5SourceBranch),
      let y := ND.transportSourceY x branch
      ∃ hwindow : (ND.oddBlock y).Nonempty,
      ∃ hmass : 0 < Tao.logFinsetMass (ND.oddBlock y),
      |Tao.pmfExpectation (ND.uniformOddBlockPMF y hwindow) (fun q => firstHitWeight N q.1) -
        Tao.pmfExpectation (ND.logOddBlockPMF y hmass) (fun q => firstHitWeight N q.1)| ≤
        2 * C * x ^ (b - 1) + 400000 * x ^ (-(1 / 12800000 : ℝ)) +
        768512 * (Real.log x) ^ (-(1 / 40 : ℝ)) := by
  obtain ⟨C, hC, hcompare⟩ := natural_weight_comparison b hbβ hb1
  refine ⟨C, hC, ?_⟩
  intro N
  filter_upwards [unconditional_natural_passage_rates, eventually_natural_log_small_landing,
    eventually_ge_atTop (N : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop (N : ℝ)]
    with x hrates hlanding hN hNsqrt
  intro hx branch
  obtain ⟨hwindow, hmass, _, htv⟩ := hrates hx branch
  refine ⟨hwindow, hmass, ?_⟩
  have h := hcompare hx N hN hNsqrt hwindow hmass
  have hb := hlanding hx branch hmass
  linarith

#print axioms eventually_natural_basin_comparison
#print axioms eventually_natural_weight_comparison

end CollatzCanonical.NativeTao
