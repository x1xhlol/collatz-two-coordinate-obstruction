import NaturalVectorBlockMean
import NaturalOddPrefixLimit
import ActualAllStartLabelLaw

open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw
open CollatzCanonical.NaturalPrefix CollatzCanonical.BanachWindow
variable {I : Type*}

noncomputable def naturalOddLabelLaw (F : ℕ → I) (X : ℕ) : LabelVector I :=
  ((oddNaturalPrefix X).card : ℝ)⁻¹ • oddNaturalPrefixSum (labelAtom ∘ F) X

noncomputable def naturalFullLabelLaw (F : ℕ → I) (X : ℕ) : LabelVector I :=
  (X : ℝ)⁻¹ • fullNaturalPrefixSum (labelAtom ∘ F) X

theorem odd_prefix_card_ratio_tendsto :
    Tendsto (fun X : ℕ => ((oddNaturalPrefix X).card : ℝ) / (X : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr : Tendsto (fun X : ℕ => 1 / (X : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero_norm' _ hr
  filter_upwards [eventually_gt_atTop (0:ℕ)] with X hX
  have hXr : (0:ℝ) < X := by exact_mod_cast hX
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
  rw [show ((oddNaturalPrefix X).card : ℝ) / (X : ℝ) - 1 / 2 =
    (((oddNaturalPrefix X).card : ℝ) - (X:ℝ) / 2) / (X:ℝ) by field_simp,
    abs_div, abs_of_pos hXr]
  exact div_le_div_of_nonneg_right (oddNaturalPrefix_card_error X) hXr.le

theorem naturalOddLabelLaw_tendsto_of_prefix_mean (F : ℕ → I) (p : LabelVector I)
    (hp : Tendsto (fun X : ℕ => (X:ℝ)⁻¹ • oddNaturalPrefixSum (labelAtom ∘ F) X)
      atTop (𝓝 p)) :
    Tendsto (naturalOddLabelLaw F) atTop (𝓝 ((2:ℝ) • p)) := by
  have hr := (odd_prefix_card_ratio_tendsto.inv₀ (by norm_num)).smul hp
  have hr' : Tendsto
      (fun X : ℕ => (((oddNaturalPrefix X).card : ℝ) / (X:ℝ))⁻¹ •
        ((X:ℝ)⁻¹ • oddNaturalPrefixSum (labelAtom ∘ F) X))
      atTop (𝓝 ((2:ℝ) • p)) := by simpa using hr
  apply hr'.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with X hX
  unfold naturalOddLabelLaw
  rw [smul_smul]
  congr 1
  have hXr : (X:ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  field_simp

theorem natural_label_prefix_masses (F : ℕ → I) (X : ℕ) :
    lp.tsumCLM ℝ I ℝ (oddNaturalPrefixSum (labelAtom ∘ F) X) = (oddNaturalPrefix X).card ∧
    lp.tsumCLM ℝ I ℝ (fullNaturalPrefixSum (labelAtom ∘ F) X) = X := by
  constructor
  · rw [oddNaturalPrefixSum_eq_sum, map_sum]
    simp only [Function.comp_apply, labelAtom_mass, Finset.sum_const, nsmul_eq_mul, mul_one]
  · unfold fullNaturalPrefixSum
    rw [map_sum]
    simp only [Function.comp_apply, labelAtom_mass, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]

theorem natural_label_prefix_nonneg (F : ℕ → I) (X : ℕ) (i : I) :
    0 ≤ oddNaturalPrefixSum (labelAtom ∘ F) X i ∧
      0 ≤ fullNaturalPrefixSum (labelAtom ∘ F) X i := by
  constructor
  · rw [oddNaturalPrefixSum_eq_sum, lp.coeFn_sum, Finset.sum_apply]
    exact Finset.sum_nonneg (fun q _ => labelAtom_nonneg (F q) i)
  · unfold fullNaturalPrefixSum
    rw [lp.coeFn_sum, Finset.sum_apply]
    exact Finset.sum_nonneg (fun q _ => labelAtom_nonneg (F (q+1)) i)

theorem natural_label_laws_are_probabilities (F : ℕ → I) {X : ℕ} (hX : 0 < X) :
    IsProbabilityVector (naturalOddLabelLaw F X) ∧
      IsProbabilityVector (naturalFullLabelLaw F X) := by
  have hcard : 0 < (oddNaturalPrefix X).card := by rw [oddNaturalPrefix_card]; omega
  have hcardr : (0:ℝ) < (oddNaturalPrefix X).card := by exact_mod_cast hcard
  have hXr : (0:ℝ) < X := by exact_mod_cast hX
  have hm := natural_label_prefix_masses F X
  constructor
  · constructor
    · intro i
      exact mul_nonneg (inv_nonneg.mpr hcardr.le) (natural_label_prefix_nonneg F X i).1
    · change lp.tsumCLM ℝ I ℝ
        (((oddNaturalPrefix X).card:ℝ)⁻¹ • oddNaturalPrefixSum (labelAtom ∘ F) X) = 1
      rw [map_smul, hm.1]
      exact inv_mul_cancel₀ hcardr.ne'
  · constructor
    · intro i
      exact mul_nonneg (inv_nonneg.mpr hXr.le) (natural_label_prefix_nonneg F X i).2
    · change lp.tsumCLM ℝ I ℝ ((X:ℝ)⁻¹ • fullNaturalPrefixSum (labelAtom ∘ F) X) = 1
      rw [map_smul, hm.2]
      exact inv_mul_cancel₀ hXr.ne'

theorem actual_odd_logarithmic_and_natural_label_law (F : ℕ → I)
    (hpass : EventuallyLabelPassageInvariant F) :
    ∃ p : LabelVector I, IsProbabilityVector p ∧
      Tendsto (oddLabelLaw F) atTop (𝓝 p) ∧
      Tendsto (naturalOddLabelLaw F) atTop (𝓝 p) := by
  have hv : EventuallyPassageInvariant (labelAtom ∘ F) := by
    filter_upwards [hpass] with x hx
    intro q hq τ hτ
    exact congrArg labelAtom (hx q hq τ hτ)
  obtain ⟨p, hp, hb⟩ := actual_invariant_odd_and_natural_vector_mean (labelAtom ∘ F)
    (fun q => le_of_eq (labelAtom_norm (F q))) hv
  obtain ⟨hprob, hlog⟩ := odd_label_probability_of_vector_mean F p hp
  refine ⟨2 • p, hprob, hlog, ?_⟩
  have hn := odd_natural_prefix_mean_of_block_mean
    (fun q => le_of_eq (labelAtom_norm (F q))) hb
  have hn' : Tendsto (fun X : ℕ => (X:ℝ)⁻¹ • oddNaturalPrefixSum (labelAtom ∘ F) X)
      atTop (𝓝 p) := by simpa only [smul_smul, one_div_mul_cancel (by norm_num : (2:ℝ) ≠ 0), one_smul] using hn
  exact naturalOddLabelLaw_tendsto_of_prefix_mean F p hn'

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.odd_prefix_card_ratio_tendsto
#print axioms CollatzCanonical.LabelLaw.natural_label_laws_are_probabilities
#print axioms CollatzCanonical.LabelLaw.actual_odd_logarithmic_and_natural_label_law
