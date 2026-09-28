import NaturalFullPrefixLimit
import NaturalBlockMeanLimit

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.NaturalPrefix
open Erdos1135 CollatzCanonical.NativeTao CollatzCylinderPacking.Arithmetic

theorem naturalOddVectorBlockMean_eq_scalar (w : ℕ → ℝ) (y : ℝ) :
    naturalOddVectorBlockMean w y = naturalOddBlockMean w y := by
  classical
  by_cases hw : (ND.oddBlock y).Nonempty
  · rw [naturalOddBlockMean_eq w y hw]
    unfold naturalOddVectorBlockMean finiteVectorMean Tao.pmfExpectation
    have hc (q : {n // n ∈ ND.oddBlock y}) :
        ((ND.uniformOddBlockPMF y hw) q).toReal = ((ND.oddBlock y).card : ℝ)⁻¹ := by
      simp [ND.uniformOddBlockPMF, ND.uniformFinsetPMF, PMF.uniformOfFintype_apply,
        Fintype.card_coe]
    simp_rw [hc]
    rw [← Finset.mul_sum]
    simp only [smul_eq_mul]
    congr 1
    exact (Finset.sum_coe_sort _ w).symm
  · have he := Finset.not_nonempty_iff_eq_empty.mp hw
    simp [naturalOddVectorBlockMean, finiteVectorMean, naturalOddBlockMean, he]

/-- A single possible exceptional doubling point gives a uniformly bounded
cumulative defect. -/
theorem natural_prefix_singleton_doubling_defect {w : ℕ → ℝ} (N : ℕ)
    (hw0 : ∀ q, 0 ≤ w q) (hw1 : ∀ q, w q ≤ 1)
    (hdouble : ∀ q, 2 * q ≠ N → w (2 * q) = w q) (X : ℕ) :
    ‖fullNaturalPrefixSum (fun q => w (2 * q)) X - fullNaturalPrefixSum w X‖ ≤ 1 := by
  classical
  unfold fullNaturalPrefixSum
  rw [← Finset.sum_sub_distrib]
  have hs : (Finset.range X).filter (fun n => 2 * (n + 1) = N) ⊆ {N / 2 - 1} := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton] at hn ⊢
    omega
  have hc : ((Finset.range X).filter (fun n => 2 * (n + 1) = N)).card ≤ 1 := by
    simpa only [Finset.card_singleton] using Finset.card_le_card hs
  calc
    _ ≤ ∑ n ∈ Finset.range X, ‖w (2 * (n + 1)) - w (n + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range X, if 2 * (n + 1) = N then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n _
      split_ifs with h
      · rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [hw0 (2 * (n + 1)), hw1 (n + 1)],
          by linarith [hw1 (2 * (n + 1)), hw0 (n + 1)]⟩
      · simp only [hdouble (n + 1) h, sub_self, norm_zero, le_refl]
    _ = (((Finset.range X).filter (fun n => 2 * (n + 1) = N)).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ 1 := by exact_mod_cast hc

theorem scalar_full_natural_prefix_mean_of_block_mean {w : ℕ → ℝ} {L : ℝ}
    (N : ℕ) (hw0 : ∀ q, 0 ≤ w q) (hw1 : ∀ q, w q ≤ 1)
    (hdouble : ∀ q, 2 * q ≠ N → w (2 * q) = w q)
    (hblock : Tendsto (naturalOddBlockMean w) atTop (𝓝 L)) :
    Tendsto (fun X : ℕ => (∑ n ∈ Finset.range X, w (n + 1)) / (X : ℝ)) atTop (𝓝 L) := by
  have hb : Tendsto (naturalOddVectorBlockMean w) atTop (𝓝 L) := by
    change Tendsto (fun y => naturalOddVectorBlockMean w y) atTop (𝓝 L)
    simpa only [naturalOddVectorBlockMean_eq_scalar] using hblock
  have h := full_natural_prefix_mean_of_block_mean
    (fun q => by rw [Real.norm_eq_abs, abs_of_nonneg (hw0 q)]; exact hw1 q)
    (natural_prefix_singleton_doubling_defect N hw0 hw1 hdouble) hb
  simpa only [fullNaturalPrefixSum, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

end CollatzCanonical.NaturalPrefix

namespace CollatzCanonical.NativeTao
open CollatzCanonical.NaturalPrefix CollatzCylinderPacking.Arithmetic

/-- Ordinary natural density of the actual finite-target basin. -/
theorem actual_basin_natural_density (N : ℕ) :
    Tendsto (fun X : ℕ => (∑ n ∈ Finset.range X, basinIndicator N (n + 1)) / (X : ℝ))
      atTop (𝓝 (actualBasinDensity N)) := by
  exact scalar_full_natural_prefix_mean_of_block_mean N
    (fun q => (basinIndicator_bounds N q).1) (fun q => (basinIndicator_bounds N q).2)
    (fun _ h => basinIndicator_halving h) (actual_basin_natural_block_mean N)

/-- Ordinary natural mean of the actual first-hit correction weight. -/
theorem actual_firstHitWeight_natural_mean (N : ℕ) :
    Tendsto (fun X : ℕ => (∑ n ∈ Finset.range X, firstHitWeight N (n + 1)) / (X : ℝ))
      atTop (𝓝 (actualFirstHitDensity N)) := by
  exact scalar_full_natural_prefix_mean_of_block_mean N
    (fun q => (firstHitWeight_bounds N q).1) (fun q => (firstHitWeight_bounds N q).2)
    (fun _ h => firstHitWeight_halving h) (actual_weight_natural_block_mean N)

#print axioms actual_basin_natural_density
#print axioms actual_firstHitWeight_natural_mean

end CollatzCanonical.NativeTao
