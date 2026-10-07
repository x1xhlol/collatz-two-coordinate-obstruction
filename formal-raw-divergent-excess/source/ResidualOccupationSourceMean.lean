import FiniteObservableEventLower
import DivergentPostBarrierOccupation

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.RawOccupation.DivergentExcess
open Erdos1135 CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.DirichletAbelian

noncomputable def futureWeightSum (u : ℕ) (F : Finset ℕ) : ℝ :=
  ∑ N ∈ F, firstHitWeight N u

noncomputable def residualOccupation (R u : ℕ) (F : Finset ℕ) (q : ℕ) : ℝ :=
  oddTargetOccupation R q - firstHitWeight u q * futureWeightSum u F

theorem residualOccupation_nonneg {R u q : ℕ} (F : Finset ℕ)
    (hinj : Function.Injective (fun i => iterate i u))
    (hF : ∀ N ∈ F, Odd N ∧ N ≤ R ∧ ∃ j, iterate j u = N) :
    0 ≤ residualOccupation R u F q :=
  sub_nonneg.mpr (divergent_future_occupation_lower F hinj hF)

theorem residualOccupation_cumulative (R u : ℕ) (F : Finset ℕ) (t : ℝ) :
    oddLogarithmicCumulative (residualOccupation R u F) t =
      oddLogarithmicCumulative (oddTargetOccupation R) t -
        logarithmicCumulative (oddFirstHitWeight u) t * futureWeightSum u F := by
  classical
  unfold oddLogarithmicCumulative logarithmicCumulative residualOccupation oddFirstHitWeight
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  dsimp only
  split_ifs <;> ring

/-- The post-root observable is averaged on every source in the root basin,
including sources outside all descent-clock good events. -/
theorem residualOccupation_normalized_odd_mean (R u : ℕ) (F : Finset ℕ) :
    Tendsto (fun t : ℝ => 2 * oddLogarithmicCumulative (residualOccupation R u F) t / t)
      atTop (𝓝 (oddTargetDensitySum R - actualFirstHitDensity u * futureWeightSum u F)) := by
  have h := (oddTargetOccupation_normalized_odd_mean R).sub
    (((actual_firstHitWeight_odd_mean u).const_mul 2).mul_const (futureWeightSum u F))
  convert h using 1
  · ext t
    rw [residualOccupation_cumulative]
    ring
  · congr 1
    ring

#print axioms residualOccupation_nonneg
#print axioms residualOccupation_cumulative
#print axioms residualOccupation_normalized_odd_mean

end CollatzCanonical.RawOccupation.DivergentExcess
