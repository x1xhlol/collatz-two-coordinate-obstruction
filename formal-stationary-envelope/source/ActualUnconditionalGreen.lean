import ActualWeightedOddMeanExistence
import FirstHitHalvingMean
import ActualGreenDensityLimit

open Filter Topology
open CollatzCanonical.DirichletAbelian CollatzCanonical.GreenKernelScalars

namespace CollatzCylinderPacking.Arithmetic

/-- The full logarithmic first-hit density supplied by the checked two-scale
odd mean and the exact halving recurrence. -/
noncomputable def actualFirstHitDensity (N : ℕ) : ℝ :=
  2 * Classical.choose (actual_firstHitWeight_odd_logarithmic_mean_exists N)

theorem actual_firstHitWeight_odd_mean (N : ℕ) :
    Tendsto (fun t : ℝ => logarithmicCumulative (oddFirstHitWeight N) t / t)
      atTop (𝓝 (actualFirstHitDensity N / 2)) := by
  have h := Classical.choose_spec (actual_firstHitWeight_odd_logarithmic_mean_exists N)
  convert h using 1
  congr 1
  unfold actualFirstHitDensity
  ring

theorem actual_firstHitWeight_full_mean (N : ℕ) :
    Tendsto (fun t : ℝ => logarithmicCumulative (firstHitWeight N) t / t)
      atTop (𝓝 (actualFirstHitDensity N)) := by
  convert firstHit_full_mean_of_odd_mean N (actual_firstHitWeight_odd_mean N) using 1
  congr 1
  ring

/-- The actual normalized Green function has its critical right limit, with
all logarithmic-mean inputs discharged in the same native Lean kernel. -/
theorem actual_unconditional_green_limit {N : ℕ} (hN : 0 < N) :
    Tendsto (fun s : ℝ => normalizedGreen s N) (𝓝[>] (1 : ℝ))
      (𝓝 (delta * greenCycleFactor 1 N * N * actualFirstHitDensity N)) :=
  actual_green_density_limit hN (actual_firstHitWeight_full_mean N)

theorem actual_unconditional_density_harmonic {N : ℕ} (hN : 0 < N) :
    actualDensityValue actualFirstHitDensity N =
      (1 / 2 : ℝ) * actualDensityValue actualFirstHitDensity (2 * N) +
        (3 / 2 : ℝ) * (if N % 3 = 2 then
          actualDensityValue actualFirstHitDensity (oddPredecessor N) else 0) :=
  actual_density_harmonic (fun M _ => actual_firstHitWeight_full_mean M) hN

end CollatzCylinderPacking.Arithmetic

#print axioms CollatzCylinderPacking.Arithmetic.actual_firstHitWeight_odd_mean
#print axioms CollatzCylinderPacking.Arithmetic.actual_firstHitWeight_full_mean
#print axioms CollatzCylinderPacking.Arithmetic.actual_unconditional_green_limit
#print axioms CollatzCylinderPacking.Arithmetic.actual_unconditional_density_harmonic
