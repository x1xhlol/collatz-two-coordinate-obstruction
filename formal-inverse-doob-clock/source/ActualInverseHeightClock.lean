import ActualLadderClock
import ActualInversePathGrowth
import InverseClockRefinement

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace CollatzCylinderPacking.Arithmetic.InverseDoob
open Erdos1135.Tao CollatzClockAudit ClockGeometry

/-- The actual continuing inverse law has the descent-clock height rate
at each positive odd nonperiodic root coprime to three. -/
theorem actual_inverse_height_clock_ae {n : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0)
    (hnodd : n % 2 = 1) (hnp : Nonperiodic n) :
    ∀ᵐ x ∂pathLaw n,
      Tendsto (fun k : ℕ => Real.log (x k : ℝ) / (k : ℝ)) atTop (𝓝 clockDrift) := by
  let b : ℝ := (n : ℝ) + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hR (r j : ℕ) : n ≤ ⌊Real.exp (b * refiningRatio taoAlpha r ^ j)⌋₊ := by
    apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    have hp : 1 ≤ refiningRatio taoAlpha r ^ j :=
      one_le_pow₀ (refiningRatio_one_lt taoAlpha_one_lt r).le
    have hmul : b ≤ b * refiningRatio taoAlpha r ^ j := by nlinarith
    have he := Real.add_one_le_exp (b * refiningRatio taoAlpha r ^ j)
    dsimp [b] at hmul
    linarith
  have href : ∀ M : ℝ, 1 < M → ∀ᵐ x ∂pathLaw n,
      Tendsto (fun j : ℕ => (lastVisitIndex n ⌊M ^ (taoAlpha ^ j)⌋₊ x : ℝ) /
        Real.log (M ^ (taoAlpha ^ j))) atTop (𝓝 (1 / clockDrift)) := by
    intro M hM
    exact actual_reference_ladder_clock_ae hn hu hnodd hnp hM
  have hcut : ∀ᵐ x ∂pathLaw n, ∀ r j : ℕ,
      (x (lastVisitIndex n ⌊Real.exp (b * refiningRatio taoAlpha r ^ j)⌋₊ x) : ℝ) ≤
        Real.exp (b * refiningRatio taoAlpha r ^ j) := by
    filter_upwards [pathLaw_isActualInversePath_ae hn hu] with x hx
    intro r j
    have h := (hx.lastVisit_spec hnp hnodd (hR r j)).1
    exact (Nat.cast_le.mpr h).trans (Nat.floor_le (Real.exp_pos _).le)
  have hafter : ∀ᵐ x ∂pathLaw n, ∀ r j k : ℕ,
      lastVisitIndex n ⌊Real.exp (b * refiningRatio taoAlpha r ^ j)⌋₊ x < k →
        Real.exp (b * refiningRatio taoAlpha r ^ j) < (x k : ℝ) := by
    filter_upwards [pathLaw_isActualInversePath_ae hn hu] with x hx
    intro r j k hk
    have h := (hx.lastVisit_spec hnp hnodd (hR r j)).2 k hk
    exact (floor_lt_nat_iff_real_lt (Real.exp_pos _).le).mp h
  have hback : ∀ᵐ x ∂pathLaw n, ∀ k t : ℕ, k ≤ t →
      Real.log ((x k : ℝ) + 1) ≤ Real.log ((x t : ℝ) + 1) +
        Real.log (3 / 2 : ℝ) * ((t - k : ℕ) : ℝ) := by
    filter_upwards [pathLaw_isActualInversePath_ae hn hu] with x hx
    exact fun _ _ hkt => hx.log_backward_growth hkt
  have h := ae_height_clock_of_reference_limits
    (Y := fun x : ℕ → ℕ => x) (C := fun x R => lastVisitIndex n ⌊R⌋₊ x)
    taoAlpha_one_lt hb (one_div_pos.mpr clockDrift_pos) log_three_halves_nonneg
    href hcut hafter hback
  simpa only [one_div_one_div] using h

#print axioms actual_inverse_height_clock_ae

end CollatzCylinderPacking.Arithmetic.InverseDoob
