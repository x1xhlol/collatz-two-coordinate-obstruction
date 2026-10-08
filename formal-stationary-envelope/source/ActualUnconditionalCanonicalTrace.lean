import ActualUnconditionalGreen
import CanonicalTraceFromOddClock
import NativeActualClockException
import FirstHitClockDensity

open Filter Topology
open CollatzCanonical.DirichletAbelian CollatzCanonical.ClockSqueeze
open CollatzCanonical.GreenKernelScalars CollatzCanonical.NativeTao

namespace CollatzCylinderPacking.Arithmetic

/-- The actual first-hit mean, canonical cylinder depth/Cesaro/Abel limits,
and critical Green limit agree. Every density, clock, tail, and stabilization
input has been discharged in this single native Lean kernel. -/
theorem actual_unconditional_canonical_identification {N : ℕ} (hN : 0 < N) :
    Tendsto (fun K : ℕ => firstHitPartialSum K N / (K : ℝ))
      atTop (𝓝 (delta * N * actualFirstHitDensity N)) ∧
    Tendsto (fun K : ℕ => (∑ k ∈ Finset.range (K + 1), canonicalRho k N) / (K : ℝ))
      atTop (𝓝 (greenCycleFactor 1 N * delta * N * actualFirstHitDensity N)) ∧
    Tendsto (CollatzCanonical.CesaroAbel.cesaroMean (fun k => canonicalRho k N))
      atTop (𝓝 (greenCycleFactor 1 N * delta * N * actualFirstHitDensity N)) ∧
    Tendsto (fun z : ℝ => (1 - z) * ∑' k, canonicalRho k N * z ^ k)
      (𝓝[<] 1) (𝓝 (greenCycleFactor 1 N * delta * N * actualFirstHitDensity N)) ∧
    Tendsto (fun s : ℝ => normalizedGreen s N) (𝓝[>] 1)
      (𝓝 (greenCycleFactor 1 N * delta * N * actualFirstHitDensity N)) :=
  actual_canonical_identification_from_odd_density_clock hN
    (actual_firstHitWeight_odd_mean N)
    (fun _ hε _ => actual_firstHitOddDepth_exception_mean_zero N hε)

/-- The elapsed shortcut clock law follows from the proved actual odd clock,
with the corresponding drift `log(4/3)/2`. -/
theorem actual_firstHitElapsed_exception_mean_zero {N : ℕ} (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun t : ℝ => logarithmicCumulative
      (clockExceptionIndicator (fun q => q % 2 = 1 ∧ ∃ K, iterate K q = N)
        (firstHitElapsed N) (Real.log (4 / 3 : ℝ) / 2) ε) t / t)
      atTop (𝓝 0) := by
  apply first_hit_elapsed_clock_exception_mean hN
    (fun q => q % 2 = 1 ∧ ∃ K, iterate K q = N) (fun q hq => hq.2) _ hε hε1
  intro η hη _
  have h := actual_firstHitOddDepth_exception_mean_zero N hη
  have hd : 2 * delta = Real.log (4 / 3 : ℝ) := by unfold delta; ring
  simpa only [hd] using h

end CollatzCylinderPacking.Arithmetic

#print axioms CollatzCylinderPacking.Arithmetic.actual_unconditional_canonical_identification
#print axioms CollatzCylinderPacking.Arithmetic.actual_firstHitElapsed_exception_mean_zero
