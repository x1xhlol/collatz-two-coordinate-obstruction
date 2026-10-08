import WeightedDirichletAbelian
import GreenCriticalLimit

open Filter Topology
open CollatzCanonical.DirichletAbelian CollatzCanonical.GreenKernelScalars

namespace CollatzCylinderPacking.Arithmetic

/-- The critical value determined by the actual first-hit logarithmic density. -/
noncomputable def actualDensityValue (D : ℕ → ℝ) (N : ℕ) : ℝ :=
  delta * greenCycleFactor 1 N * N * D N

theorem actual_green_density_limit {N : ℕ} (hN : 0 < N) {D : ℝ}
    (hmean : Tendsto (fun t : ℝ =>
      logarithmicCumulative (firstHitWeight N) t / t) atTop (𝓝 D)) :
    Tendsto (fun s : ℝ => normalizedGreen s N) (𝓝[>] (1 : ℝ))
      (𝓝 (delta * greenCycleFactor 1 N * N * D)) := by
  apply actual_green_critical_of_dirichlet hN
  simpa only [weightedDirichletTerm] using weighted_dirichlet_abelian
    (fun q => (firstHitWeight_bounds N q).1)
    (fun q => (firstHitWeight_bounds N q).2) hmean

theorem actual_density_harmonic {D : ℕ → ℝ}
    (hmean : ∀ N : ℕ, 0 < N → Tendsto (fun t : ℝ =>
      logarithmicCumulative (firstHitWeight N) t / t) atTop (𝓝 (D N)))
    {N : ℕ} (hN : 0 < N) :
    actualDensityValue D N = (1 / 2 : ℝ) * actualDensityValue D (2 * N) +
      (3 / 2 : ℝ) * (if N % 3 = 2 then actualDensityValue D (oddPredecessor N) else 0) := by
  apply actual_green_harmonic_of_pointwise (g := actualDensityValue D) _ hN
  intro M hM
  exact actual_green_density_limit hM (hmean M hM)

#print axioms actual_green_density_limit
#print axioms actual_density_harmonic

end CollatzCylinderPacking.Arithmetic
