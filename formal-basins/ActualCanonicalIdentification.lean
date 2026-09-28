import ActualClockAdapter
import ActualCylinderCesaroAbel
import ActualGreenDensityLimit
import ClockExceptionalDensity

set_option autoImplicit false

open Filter Topology
open CollatzCanonical.DirichletAbelian CollatzCanonical.ClockSqueeze
open CollatzCanonical.GreenKernelScalars

namespace CollatzCylinderPacking.Arithmetic

/-- The actual first-hit mean follows from the stated odd weighted density
and weighted clock-exception means. All cutoff and summability inputs are
discharged by the actual first-hit adapter. -/
theorem actual_first_hit_mean_of_weighted_clock {N : ℕ} (hN : 0 < N) {D : ℝ}
    (hodd : Tendsto (fun t : ℝ => logarithmicCumulative (oddFirstHitWeight N) t / t)
      atTop (𝓝 (D / 2)))
    (hbad : ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun t : ℝ => logarithmicCumulative
        (clockBadWeight (oddFirstHitWeight N) (firstHitOddDepth N) (2 * delta) ε) t / t)
        atTop (𝓝 0)) :
    Tendsto (fun K : ℕ => firstHitPartialSum K N / (K : ℝ))
      atTop (𝓝 (delta * N * D)) := by
  have hlam : 0 < 2 * delta := mul_pos (by norm_num) delta_pos
  have hc : 0 < 6 * Real.log 2 := by positivity
  have ht : Tendsto (fun K : ℕ => clockTail (oddFirstHitWeight N) (firstHitOddDepth N) K
      ((6 * Real.log 2) * (K : ℝ) + Real.log N) / (K : ℝ)) atTop (𝓝 0) :=
    actual_clock_normalized_tail_tendsto_zero hN
  have hm := weighted_clock_mean (fun q => (oddFirstHitWeight_bounds N q).1)
    (firstHitOddDepth N) hlam hc (Real.log N) (actual_clock_summable hN) hodd hbad ht
  have h := hm.mul_const (N : ℝ)
  have hv : ((2 * delta) * (D / 2)) * (N : ℝ) = delta * N * D := by ring
  rw [hv] at h
  convert h using 1
  funext K
  rw [actual_clock_tsum hN K]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp

/-- Actual canonical cylinder depth, Cesàro, and Abel limits, with only
the two explicit odd-weight density/clock hypotheses. -/
theorem actual_canonical_limits_of_weighted_clock {N : ℕ} (hN : 0 < N) {D : ℝ}
    (hodd : Tendsto (fun t : ℝ => logarithmicCumulative (oddFirstHitWeight N) t / t)
      atTop (𝓝 (D / 2)))
    (hbad : ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun t : ℝ => logarithmicCumulative
        (clockBadWeight (oddFirstHitWeight N) (firstHitOddDepth N) (2 * delta) ε) t / t)
        atTop (𝓝 0)) :
    Tendsto (fun K : ℕ => (∑ k ∈ Finset.range (K + 1), canonicalRho k N) / (K : ℝ))
      atTop (𝓝 (greenCycleFactor 1 N * delta * N * D)) ∧
    Tendsto (CollatzCanonical.CesaroAbel.cesaroMean (fun k => canonicalRho k N))
      atTop (𝓝 (greenCycleFactor 1 N * delta * N * D)) ∧
    Tendsto (fun z : ℝ => (1 - z) * ∑' k, canonicalRho k N * z ^ k)
      (𝓝[<] 1) (𝓝 (greenCycleFactor 1 N * delta * N * D)) := by
  have hF := actual_first_hit_mean_of_weighted_clock hN hodd hbad
  simpa only [mul_assoc] using
    And.intro (canonical_depth_mean_of_first_hit_mean hN hF)
      (And.intro (canonical_cesaro_of_first_hit_mean hN hF)
        (canonical_abel_of_first_hit_mean hN hF))

/-- The actual canonical cylinder limits agree with the actual critical
Green limit. The full and odd weighted logarithmic means and the clock
exception mean are the only remaining analytic hypotheses. -/
theorem actual_canonical_identification {N : ℕ} (hN : 0 < N) {D : ℝ}
    (hfull : Tendsto (fun t : ℝ => logarithmicCumulative (firstHitWeight N) t / t)
      atTop (𝓝 D))
    (hodd : Tendsto (fun t : ℝ => logarithmicCumulative (oddFirstHitWeight N) t / t)
      atTop (𝓝 (D / 2)))
    (hbad : ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun t : ℝ => logarithmicCumulative
        (clockBadWeight (oddFirstHitWeight N) (firstHitOddDepth N) (2 * delta) ε) t / t)
        atTop (𝓝 0)) :
    Tendsto (fun K : ℕ => firstHitPartialSum K N / (K : ℝ))
      atTop (𝓝 (delta * N * D)) ∧
    Tendsto (fun K : ℕ => (∑ k ∈ Finset.range (K + 1), canonicalRho k N) / (K : ℝ))
      atTop (𝓝 (greenCycleFactor 1 N * delta * N * D)) ∧
    Tendsto (CollatzCanonical.CesaroAbel.cesaroMean (fun k => canonicalRho k N))
      atTop (𝓝 (greenCycleFactor 1 N * delta * N * D)) ∧
    Tendsto (fun z : ℝ => (1 - z) * ∑' k, canonicalRho k N * z ^ k)
      (𝓝[<] 1) (𝓝 (greenCycleFactor 1 N * delta * N * D)) ∧
    Tendsto (fun s : ℝ => normalizedGreen s N) (𝓝[>] 1)
      (𝓝 (greenCycleFactor 1 N * delta * N * D)) := by
  have hc := actual_canonical_limits_of_weighted_clock hN hodd hbad
  refine ⟨actual_first_hit_mean_of_weighted_clock hN hodd hbad, hc.1, hc.2.1, hc.2.2, ?_⟩
  have hg := actual_green_density_limit hN hfull
  convert hg using 1
  congr 1
  ring

theorem oddFirstHitWeight_supported_on_odd_basin (N q : ℕ)
    (hq : ¬ (q % 2 = 1 ∧ ∃ A, iterate A q = N)) : oddFirstHitWeight N q = 0 := by
  classical
  by_cases ho : q % 2 = 1
  · have hh : ¬ ∃ A, iterate A q = N := fun h => hq ⟨ho, h⟩
    simp [oddFirstHitWeight, ho, firstHitWeight, hh]
  · simp [oddFirstHitWeight, ho]

/-- The absolute exceptional-set density hypothesis implies the weighted
one for the actual bounded first-hit weight. -/
theorem actual_weighted_clock_exception_mean {N : ℕ} {ε : ℝ}
    (hE : Tendsto (fun t : ℝ => logarithmicCumulative
      (clockExceptionIndicator (fun q => q % 2 = 1 ∧ ∃ A, iterate A q = N)
        (firstHitOddDepth N) (2 * delta) ε) t / t) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => logarithmicCumulative
      (clockBadWeight (oddFirstHitWeight N) (firstHitOddDepth N) (2 * delta) ε) t / t)
      atTop (𝓝 0) :=
  weighted_clock_exception_mean (oddFirstHitWeight_bounds N)
    (fun q => q % 2 = 1 ∧ ∃ A, iterate A q = N)
    (oddFirstHitWeight_supported_on_odd_basin N) (firstHitOddDepth N) (2 * delta) ε hE

/-- First-hit mean from absolute zero logarithmic density of the actual
odd-basin clock exceptions. -/
theorem actual_first_hit_mean_of_exception_density {N : ℕ} (hN : 0 < N) {D : ℝ}
    (hodd : Tendsto (fun t : ℝ => logarithmicCumulative (oddFirstHitWeight N) t / t)
      atTop (𝓝 (D / 2)))
    (hE : ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun t : ℝ => logarithmicCumulative
        (clockExceptionIndicator (fun q => q % 2 = 1 ∧ ∃ A, iterate A q = N)
          (firstHitOddDepth N) (2 * delta) ε) t / t) atTop (𝓝 0)) :
    Tendsto (fun K : ℕ => firstHitPartialSum K N / (K : ℝ))
      atTop (𝓝 (delta * N * D)) :=
  actual_first_hit_mean_of_weighted_clock hN hodd
    (fun ε hε hε1 => actual_weighted_clock_exception_mean (hE ε hε hε1))

/-- Identification in the paper's absolute exceptional-set formulation.
There are no additional tail, summability, word, or cylinder assumptions. -/
theorem actual_canonical_identification_of_exception_density {N : ℕ} (hN : 0 < N) {D : ℝ}
    (hfull : Tendsto (fun t : ℝ => logarithmicCumulative (firstHitWeight N) t / t)
      atTop (𝓝 D))
    (hodd : Tendsto (fun t : ℝ => logarithmicCumulative (oddFirstHitWeight N) t / t)
      atTop (𝓝 (D / 2)))
    (hE : ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun t : ℝ => logarithmicCumulative
        (clockExceptionIndicator (fun q => q % 2 = 1 ∧ ∃ A, iterate A q = N)
          (firstHitOddDepth N) (2 * delta) ε) t / t) atTop (𝓝 0)) :
    Tendsto (fun K : ℕ => firstHitPartialSum K N / (K : ℝ))
      atTop (𝓝 (delta * N * D)) ∧
    Tendsto (fun K : ℕ => (∑ k ∈ Finset.range (K + 1), canonicalRho k N) / (K : ℝ))
      atTop (𝓝 (greenCycleFactor 1 N * delta * N * D)) ∧
    Tendsto (CollatzCanonical.CesaroAbel.cesaroMean (fun k => canonicalRho k N))
      atTop (𝓝 (greenCycleFactor 1 N * delta * N * D)) ∧
    Tendsto (fun z : ℝ => (1 - z) * ∑' k, canonicalRho k N * z ^ k)
      (𝓝[<] 1) (𝓝 (greenCycleFactor 1 N * delta * N * D)) ∧
    Tendsto (fun s : ℝ => normalizedGreen s N) (𝓝[>] 1)
      (𝓝 (greenCycleFactor 1 N * delta * N * D)) :=
  actual_canonical_identification hN hfull hodd
    (fun ε hε hε1 => actual_weighted_clock_exception_mean (hE ε hε hε1))

end CollatzCylinderPacking.Arithmetic
