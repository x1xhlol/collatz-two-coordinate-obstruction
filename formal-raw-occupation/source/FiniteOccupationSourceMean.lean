import PreBarrierWeightedOccupation

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.RawOccupation
open CollatzCylinderPacking.Arithmetic CollatzCanonical.DirichletAbelian

noncomputable def oddTargetDensitySum (R : ℕ) : ℝ :=
  ∑ N ∈ (Finset.range (R + 1)).filter Odd, actualFirstHitDensity N

theorem oddTargetOccupation_cumulative (R : ℕ) (t : ℝ) :
    oddLogarithmicCumulative (oddTargetOccupation R) t =
      ∑ N ∈ (Finset.range (R + 1)).filter Odd,
        logarithmicCumulative (oddFirstHitWeight N) t := by
  classical
  unfold oddLogarithmicCumulative logarithmicCumulative oddTargetOccupation oddFirstHitWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs with h <;> simp [h, Finset.sum_div]

/-- For every fixed finite target range, the actual odd-source occupation
mean is exactly the sum of the actual full logarithmic first-hit densities. -/
theorem oddTargetOccupation_normalized_odd_mean (R : ℕ) :
    Tendsto (fun t : ℝ => 2 * oddLogarithmicCumulative (oddTargetOccupation R) t / t)
      atTop (𝓝 (oddTargetDensitySum R)) := by
  have hsum := tendsto_finset_sum ((Finset.range (R + 1)).filter Odd)
    (fun N _ => (actual_firstHitWeight_odd_mean N).const_mul 2)
  have hvalue : (∑ N ∈ (Finset.range (R + 1)).filter Odd,
      2 * (actualFirstHitDensity N / 2)) = oddTargetDensitySum R := by
    simp only [oddTargetDensitySum]
    apply Finset.sum_congr rfl
    intro N hN
    ring
  rw [hvalue] at hsum
  convert hsum using 1
  ext t
  rw [oddTargetOccupation_cumulative, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro N hN
  ring

/-- Any eventual lower bound on the finite source means passes directly to
the actual density sum; no limit over the target range is interchanged. -/
theorem le_oddTargetDensitySum_of_eventually_le {R : ℕ} {b : ℝ}
    (h : ∀ᶠ t : ℝ in atTop,
      b ≤ 2 * oddLogarithmicCumulative (oddTargetOccupation R) t / t) :
    b ≤ oddTargetDensitySum R :=
  ge_of_tendsto (oddTargetOccupation_normalized_odd_mean R) h

#print axioms oddTargetOccupation_cumulative
#print axioms oddTargetOccupation_normalized_odd_mean
#print axioms le_oddTargetDensitySum_of_eventually_le

end CollatzCanonical.RawOccupation
