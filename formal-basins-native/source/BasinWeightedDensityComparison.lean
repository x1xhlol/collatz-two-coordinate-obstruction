import ActualBasinDensity
import ActualUnconditionalGreen

set_option autoImplicit false
open Filter Topology
open CollatzCanonical.DirichletAbelian

namespace CollatzCylinderPacking.Arithmetic

theorem firstHitWeight_le_basinIndicator (N q : ℕ) :
    firstHitWeight N q ≤ basinIndicator N q := by
  classical
  by_cases hh : ∃ A, iterate A q = N
  · simpa only [basinIndicator, if_pos hh] using (firstHitWeight_bounds N q).2
  · simp only [firstHitWeight, basinIndicator, dif_neg hh, if_neg hh, le_refl]

/-- A single correction constant compares every ordinary basin indicator
with its first-hit weight, uniformly in the target and positive source. -/
theorem exists_uniform_basin_weight_comparison :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ N q : ℕ, 0 < q →
      basinIndicator N q ≤ P * firstHitWeight N q := by
  obtain ⟨P, hP, hbound⟩ :=
    CollatzCanonical.UniformCorrection.exists_uniform_finite_path_product_bound
  refine ⟨P, hP, ?_⟩
  intro N q hq
  classical
  by_cases hh : ∃ A, iterate A q = N
  · let A := Nat.find hh
    have hfirst : FirstHit q N A := firstHit_find hh
    have hb := (hbound A (fun i => iterate i q) hq (fun i _ => rfl)
      (firstHit_prefix_injective hfirst)).2
    change pathCorrection A q ≤ P at hb
    have hp : 0 < pathCorrection A q := lt_of_lt_of_le zero_lt_one (one_le_pathCorrection A q)
    rw [firstHitWeight_eq_pathWeight hfirst]
    simp only [basinIndicator, if_pos hh, pathWeight, ← div_eq_mul_inv]
    exact (le_div_iff₀ hp).mpr (by simpa using hb)
  · simp only [basinIndicator, firstHitWeight, if_neg hh, dif_neg hh, mul_zero, le_refl]

theorem logarithmicCumulative_le_of_positive_weights {w v : ℕ → ℝ}
    (h : ∀ q : ℕ, 0 < q → w q ≤ v q) (t : ℝ) :
    logarithmicCumulative w t ≤ logarithmicCumulative v t := by
  apply Finset.sum_le_sum
  intro n _
  exact div_le_div_of_nonneg_right (h (n + 1) (Nat.succ_pos n)) (by positivity)

theorem logarithmicCumulative_const_mul (P : ℝ) (w : ℕ → ℝ) (t : ℝ) :
    logarithmicCumulative (fun q => P * w q) t = P * logarithmicCumulative w t := by
  unfold logarithmicCumulative
  simp_rw [mul_div_assoc]
  exact (Finset.mul_sum _ _ _).symm

/-- The ordinary basin density and the actual weighted density vanish
together, with one comparison constant valid for every target. -/
theorem actual_basin_and_weighted_density_comparison :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ N : ℕ,
      actualFirstHitDensity N ≤ actualBasinDensity N ∧
        actualBasinDensity N ≤ P * actualFirstHitDensity N := by
  obtain ⟨P, hP, hpoint⟩ := exists_uniform_basin_weight_comparison
  refine ⟨P, hP, ?_⟩
  intro N
  constructor
  · apply le_of_tendsto_of_tendsto (actual_firstHitWeight_full_mean N)
      (actual_basin_full_logarithmic_mean N)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact div_le_div_of_nonneg_right
      (logarithmicCumulative_le_of_positive_weights
        (fun q _ => firstHitWeight_le_basinIndicator N q) t) ht
  · apply le_of_tendsto_of_tendsto (actual_basin_full_logarithmic_mean N)
      ((actual_firstHitWeight_full_mean N).const_mul P)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hb := logarithmicCumulative_le_of_positive_weights (hpoint N) t
    rw [logarithmicCumulative_const_mul] at hb
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hb ht

end CollatzCylinderPacking.Arithmetic
