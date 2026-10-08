import NaturalPrefixBlockBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.NaturalPrefix
open Erdos1135

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem natural_prefix_error_tendsto_zero :
    Tendsto (fun X : ℕ => (2 * (X : ℝ) ^ (1 / ND.alpha) + 3) / (X : ℝ))
      atTop (𝓝 0) := by
  have ha : 0 < ND.alpha := Tao.taoAlpha_pos
  have hr : 1 / ND.alpha < 1 := (div_lt_one ha).mpr Tao.taoAlpha_one_lt
  have hp : Tendsto (fun x : ℝ => x ^ (1 / ND.alpha - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hr)
  have hl : Tendsto (fun x : ℝ => 2 * x ^ (1 / ND.alpha - 1) + 3 / x) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add, div_eq_mul_inv] using
      (hp.const_mul 2).add (tendsto_inv_atTop_zero.const_mul 3)
  have he : Tendsto (fun x : ℝ => (2 * x ^ (1 / ND.alpha) + 3) / x) atTop (𝓝 0) := by
    apply hl.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_sub hx, Real.rpow_one]
    ring
  exact he.comp tendsto_natCast_atTop_atTop

/-- A bounded vector observable with a limit on the native large odd blocks
has the corresponding limit on all odd prefixes. -/
theorem odd_natural_prefix_mean_of_block_mean {F : ℕ → V} {p : V}
    (hF : ∀ q, ‖F q‖ ≤ 1)
    (hblock : Tendsto (naturalOddVectorBlockMean F) atTop (𝓝 p)) :
    Tendsto (fun X : ℕ => (X : ℝ)⁻¹ • oddNaturalPrefixSum F X)
      atTop (𝓝 ((1 / 2 : ℝ) • p)) := by
  have hy : Tendsto (fun X : ℕ => (X : ℝ) ^ (1 / ND.alpha)) atTop atTop :=
    (tendsto_rpow_atTop (one_div_pos.mpr Tao.taoAlpha_pos)).comp tendsto_natCast_atTop_atTop
  have hm := (hblock.comp hy).const_smul (1 / 2 : ℝ)
  have hz : Tendsto (fun X : ℕ => (X : ℝ)⁻¹ • oddNaturalPrefixSum F X -
      (1 / 2 : ℝ) • naturalOddVectorBlockMean F ((X : ℝ) ^ (1 / ND.alpha)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ natural_prefix_error_tendsto_zero
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    exact odd_prefix_mean_sub_natural_block_bound hF hX
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using hz.add hm

#print axioms odd_natural_prefix_mean_of_block_mean

end CollatzCanonical.NaturalPrefix
