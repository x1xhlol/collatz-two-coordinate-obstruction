import ResidualOccupationSourceMean
import AlignedLadderOccupation
import UniformAlignedOccupationLower

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.RawOccupation.DivergentExcess
open Erdos1135 CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzClockAudit

/-- The finite good-source descent estimate survives subtraction of the
entire post-root observable because the two target sets are disjoint. -/
theorem exists_aligned_residual_occupation_lower (theta : ℝ)
    (htheta : CollatzCanonical.PackingParameters.beta < theta) (htheta1 : theta < 1) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (x : ℕ → ℝ) {M : ℝ} {R B n u : ℕ}
      (F : Finset ℕ) (q : Tao.TaoOddNat),
      1 ≤ M → Odd u → (u : ℝ) ≤ M →
      Function.Injective (fun i => iterate i u) →
      (∀ N ∈ F, Odd N ∧ N ≤ R ∧ ∃ j, iterate j u = N) →
      (∀ i < n, x (i + 1) ≤ x i) →
      (∀ i ≤ n, M ≤ x i) → (∀ i ≤ n, x i ≤ (R : ℝ)) →
      (∀ i ≤ n, AlignedClockWitness M (x i) B q) →
      Tao.syracuseHitsAtMostReal q.1 M →
      (∀ i < n,
        (3 / 2 : ℝ) ^ ((Real.log (x i) - Real.log (x (i + 1))) / clockDrift +
          2 * commonBottomClockError M R B) * (x i + 1) ≤ (R : ℝ) + 1) →
      (3 / 2 : ℝ) ^ (Real.log (x n) / clockDrift + commonBottomClockError M R B) *
        (x n + 1) ≤ (R : ℝ) + 1 →
      finiteOccupationLowerValue P theta M R B (x 0) ≤ residualOccupation R u F q.1 := by
  obtain ⟨P, hP, hweight⟩ := exists_uniform_preBarrier_firstHitWeight_lower theta htheta htheta1
  refine ⟨P, hP, ?_⟩
  intro x M R B n u F q hM hu hsmall hinj hF hdown hbot htop hw hbottom hstage hlast
  let T := actualBarrierTime M q.1
  let t := fun i => actualBarrierTime (x i) q.1
  have hT : Tao.syracuseFirstHitAtMostReal M q.1 T := actualBarrierTime_first_hit hbottom
  have hfirst : ∀ i ≤ n, Tao.syracuseFirstHitAtMostReal (x i) q.1 (t i) :=
    fun i hi => aligned_clock_witness_first_hit (hw i hi)
  have hclock : ∀ i ≤ n,
      |((T - t i : ℕ) : ℝ) - Real.log (x i) / clockDrift| ≤ commonBottomClockError M R B :=
    fun i hi => aligned_clock_witness_error (hw i hi) (htop i hi) hbottom
  have hheight := finite_clock_grid_confinement x t q.2 hdown hbot hfirst hT hclock hstage hlast
  have hadd := preBarrier_occupation_add_divergent_future F q.2 (zero_le_one.trans hM)
    hu hsmall hinj hF hT (fun i hi => hweight hM q.2 hT hi)
    (fun i hi hiT => by exact_mod_cast hheight i hi hiT)
  have hcount : Real.log (x 0) / clockDrift - commonBottomClockError M R B ≤
      ((T - t 0 : ℕ) : ℝ) := by
    linarith [(abs_le.mp (hclock 0 (Nat.zero_le n))).1]
  unfold finiteOccupationLowerValue
  apply max_le (residualOccupation_nonneg F hinj hF)
  have hscaled := mul_le_mul_of_nonneg_left hcount (le_max_left 0 (1 - P * M ^ (theta - 1)))
  unfold residualOccupation futureWeightSum
  linarith

#print axioms exists_aligned_residual_occupation_lower

end CollatzCanonical.RawOccupation.DivergentExcess
