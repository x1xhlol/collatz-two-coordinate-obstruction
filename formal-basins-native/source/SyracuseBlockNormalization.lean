import SyracuseBlockHitExpansion
import GreenCriticalLimit
import GreenQuadraticNormalization

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.GreenKernelScalars

noncomputable def blockKappa (s : ℝ) : ℝ := (3 : ℝ) ^ (s - 1) / ((2 : ℝ) ^ s - 1)

theorem blockKappa_normalization {s : ℝ} (hs : 0 < s) :
    1 - blockKappa s = (1 - kappa s) / (1 - (2 : ℝ) ^ (-s)) := by
  have ht : 1 < (2 : ℝ) ^ s := Real.one_lt_rpow (by norm_num) hs
  have hu : (2 : ℝ) ^ s ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) s).ne'
  have hd : (2 : ℝ) ^ s - 1 ≠ 0 := by linarith
  have he : 1 - ((2 : ℝ) ^ s)⁻¹ ≠ 0 := by
    have hi : ((2 : ℝ) ^ s)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr ht
    linarith
  unfold blockKappa kappa
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3), Real.rpow_one,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.div_rpow (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  ring

theorem blockKappa_critical_right_limit :
    Tendsto (fun s : ℝ => (1 - blockKappa s) / (s - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 (Real.log (4 / 3 : ℝ))) := by
  have hd : Tendsto (fun s : ℝ => 1 - (2 : ℝ) ^ (-s))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
    have hc : Continuous (fun s : ℝ => 1 - (2 : ℝ) ^ (-s)) := continuous_const.sub ((Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).comp continuous_neg)
    convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    norm_num
  have h := kappa_critical_right_limit.div hd (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hδ : delta / (1 / 2 : ℝ) = Real.log (4 / 3 : ℝ) := by unfold delta; ring
  rw [hδ] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : 1 < s := hs
  dsimp only [Pi.div_apply]
  rw [blockKappa_normalization (by linarith : 0 < s)]
  ring

#print axioms blockKappa_normalization
#print axioms blockKappa_critical_right_limit

end CollatzCanonical.GreenKernelScalars

namespace CollatzCylinderPacking.Arithmetic
open CollatzCanonical.GreenKernelScalars

/-- The paper's exact normalization of the full inverse Green series by
its odd-block expansion, with all exchanges justified by summability. -/
theorem green_eq_syracuseBlock_series {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) :
    (∑' A : ℕ, inverseIterate s A N) =
      (1 - (2 : ℝ) ^ (-s))⁻¹ * ∑' k : ℕ, syracuseBlockIterate s k N := by
  have he := green_odd_endpoint_normalization hs hN
  rw [← (syracuseBlockIterate_hasSum hs hN).tsum_eq] at he
  have hd : 1 - (2 : ℝ) ^ (-s) ≠ 0 := by
    have hr := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (by linarith : -s < 0)
    linarith
  rw [← he, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

/-- The normalized Green function uses the manuscript's κ′ factor on the
sum of odd-block iterates. -/
theorem normalizedGreen_eq_syracuseBlock_series {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) :
    normalizedGreen s N = (1 - blockKappa s) * ∑' k : ℕ, syracuseBlockIterate s k N := by
  unfold normalizedGreen actualGreen
  rw [green_eq_syracuseBlock_series hs hN, blockKappa_normalization (by linarith : 0 < s)]
  ring

#print axioms green_eq_syracuseBlock_series
#print axioms normalizedGreen_eq_syracuseBlock_series

end CollatzCylinderPacking.Arithmetic
