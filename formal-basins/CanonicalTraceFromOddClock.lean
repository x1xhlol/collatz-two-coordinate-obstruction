import FirstHitHalvingMean
import ActualCanonicalIdentification

set_option autoImplicit false

open Filter Topology
open CollatzCanonical.DirichletAbelian CollatzCanonical.ClockSqueeze
open CollatzCanonical.GreenKernelScalars

namespace CollatzCylinderPacking.Arithmetic

/-- All actual canonical trace limits from the odd weighted logarithmic mean
and absolute zero logarithmic density of the actual first-hit clock exceptions.
The full weighted mean, endpoint tails, and all series identities are derived. -/
theorem actual_canonical_identification_from_odd_density_clock {N : ℕ} (hN : 0 < N) {D : ℝ}
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
      (𝓝 (greenCycleFactor 1 N * delta * N * D)) := by
  have hfull : Tendsto (fun t : ℝ => logarithmicCumulative (firstHitWeight N) t / t)
      atTop (𝓝 D) := by
    convert firstHit_full_mean_of_odd_mean N hodd using 1
    congr 1
    ring
  exact actual_canonical_identification_of_exception_density hN hfull hodd hE

end CollatzCylinderPacking.Arithmetic
