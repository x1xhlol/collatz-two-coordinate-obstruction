import NaturalOddPrefixLimit
import NaturalHalvingIdentity
import StableNaturalHalving

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.NaturalPrefix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A bounded observable with a bounded cumulative doubling defect inherits
its full natural mean from its odd natural mean. -/
theorem full_natural_prefix_mean_of_odd_mean {F : ℕ → V} {p : V} {C : ℝ}
    (hF : ∀ q, ‖F q‖ ≤ 1)
    (hdouble : ∀ X, ‖fullNaturalPrefixSum (fun q => F (2 * q)) X -
      fullNaturalPrefixSum F X‖ ≤ C)
    (hodd : Tendsto (fun X : ℕ => (X : ℝ)⁻¹ • oddNaturalPrefixSum F X)
      atTop (𝓝 ((1 / 2 : ℝ) • p))) :
    Tendsto (fun X : ℕ => (X : ℝ)⁻¹ • fullNaturalPrefixSum F X) atTop (𝓝 p) := by
  let E : ℕ → V := fun X => (X : ℝ)⁻¹ • fullNaturalPrefixSum F X - p
  let Z : ℕ → V := fun X => E X - (1 / 2 : ℝ) • E (X / 2)
  let D : ℕ → V := fun X => fullNaturalPrefixSum (fun q => F (2 * q)) X -
    fullNaturalPrefixSum F X
  have hbound (X : ℕ) : ‖E X‖ ≤ 1 + ‖p‖ := by
    exact (norm_sub_le _ _).trans (add_le_add (fullNaturalPrefixMean_norm_le_one hF X) le_rfl)
  have herr : Tendsto (fun X : ℕ => Z X -
      ((X : ℝ)⁻¹ • oddNaturalPrefixSum F X - (1 / 2 : ℝ) • p)) atTop (𝓝 0) := by
    have he : Tendsto (fun X : ℕ => (C + 1) / (X : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (C + 1)
    apply squeeze_zero_norm' _ he
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
    have hxp : 0 < X := by omega
    have hx : (0 : ℝ) < X := by exact_mod_cast hxp
    have hhp : 0 < X / 2 := by omega
    have hh : (0 : ℝ) < (X / 2 : ℕ) := by exact_mod_cast hhp
    have hscale : (((X / 2 : ℕ) : ℝ) / X) •
        (((X / 2 : ℕ) : ℝ)⁻¹ • fullNaturalPrefixSum F (X / 2)) =
        (X : ℝ)⁻¹ • fullNaturalPrefixSum F (X / 2) := by
      rw [smul_smul]
      congr 1
      field_simp
    have hidentity : (X : ℝ)⁻¹ • fullNaturalPrefixSum F X =
        (X : ℝ)⁻¹ • oddNaturalPrefixSum F X + (X : ℝ)⁻¹ • D (X / 2) +
        (((X / 2 : ℕ) : ℝ) / X) •
          (((X / 2 : ℕ) : ℝ)⁻¹ • fullNaturalPrefixSum F (X / 2)) := by
      rw [hscale, fullNaturalPrefixSum_halving F X]
      dsimp only [D]
      simp only [smul_add, smul_sub]
      abel
    have hz : Z X - ((X : ℝ)⁻¹ • oddNaturalPrefixSum F X - (1 / 2 : ℝ) • p) =
        (X : ℝ)⁻¹ • D (X / 2) +
        (((X / 2 : ℕ) : ℝ) / X - (1 / 2 : ℝ)) •
          (((X / 2 : ℕ) : ℝ)⁻¹ • fullNaturalPrefixSum F (X / 2)) := by
      dsimp only [Z, E]
      rw [hidentity]
      module
    rw [hz]
    have hfirst : ‖(X : ℝ)⁻¹ • D (X / 2)‖ ≤ (X : ℝ)⁻¹ * C := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)]
      exact mul_le_mul_of_nonneg_left (hdouble _) (inv_nonneg.mpr hx.le)
    have hsecond : ‖(((X / 2 : ℕ) : ℝ) / X - (1 / 2 : ℝ)) •
        (((X / 2 : ℕ) : ℝ)⁻¹ • fullNaturalPrefixSum F (X / 2))‖ ≤ (X : ℝ)⁻¹ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul (natural_half_ratio_error hxp)
        (fullNaturalPrefixMean_norm_le_one hF _) (norm_nonneg _) (inv_nonneg.mpr hx.le)).trans
        (by rw [mul_one])
    calc
      _ ≤ (X : ℝ)⁻¹ * C + (X : ℝ)⁻¹ := (norm_add_le _ _).trans (add_le_add hfirst hsecond)
      _ = (C + 1) / (X : ℝ) := by ring
  have hz : Tendsto Z atTop (𝓝 0) := by
    have ho := hodd.sub_const ((1 / 2 : ℝ) • p)
    simp only [sub_self] at ho
    simpa only [sub_add_cancel, add_zero] using herr.add ho
  have hE : Tendsto E atTop (𝓝 0) :=
    stable_natural_halving_tendsto_zero E Z (d := 1 / 2) (by norm_num) (by norm_num) hbound
      (fun X => by dsimp only [Z]; abel) hz
  simpa only [E, sub_add_cancel, zero_add] using hE.add_const p

/-- Large odd-block convergence implies ordinary natural convergence for
bounded observables with a bounded cumulative doubling defect. -/
theorem full_natural_prefix_mean_of_block_mean {F : ℕ → V} {p : V} {C : ℝ}
    (hF : ∀ q, ‖F q‖ ≤ 1)
    (hdouble : ∀ X, ‖fullNaturalPrefixSum (fun q => F (2 * q)) X -
      fullNaturalPrefixSum F X‖ ≤ C)
    (hblock : Tendsto (naturalOddVectorBlockMean F) atTop (𝓝 p)) :
    Tendsto (fun X : ℕ => (X : ℝ)⁻¹ • fullNaturalPrefixSum F X) atTop (𝓝 p) :=
  full_natural_prefix_mean_of_odd_mean hF hdouble
    (odd_natural_prefix_mean_of_block_mean hF hblock)

theorem full_natural_prefix_mean_of_doubling_invariant {F : ℕ → V} {p : V}
    (hF : ∀ q, ‖F q‖ ≤ 1) (hdouble : ∀ q, F (2 * q) = F q)
    (hblock : Tendsto (naturalOddVectorBlockMean F) atTop (𝓝 p)) :
    Tendsto (fun X : ℕ => (X : ℝ)⁻¹ • fullNaturalPrefixSum F X) atTop (𝓝 p) := by
  apply full_natural_prefix_mean_of_block_mean hF (C := 0) _ hblock
  intro X
  simp only [hdouble, sub_self, norm_zero, le_refl]

#print axioms full_natural_prefix_mean_of_odd_mean
#print axioms full_natural_prefix_mean_of_block_mean
#print axioms full_natural_prefix_mean_of_doubling_invariant

end CollatzCanonical.NaturalPrefix
