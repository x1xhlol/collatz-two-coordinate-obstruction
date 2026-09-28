import ActualAllStartLabelLaw
import SyracuseLabelInvariance

open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw
open CollatzCanonical.BanachWindow CollatzCanonical.DirichletAbelian
variable {I : Type*}

theorem fullLabel_cumulative_mass (F : ℕ → I) (t : ℝ) :
    lp.tsumCLM ℝ I ℝ (fullVectorCumulative (labelAtom ∘ F) t) =
      logarithmicCumulative (fun _ => 1) t := by
  unfold fullVectorCumulative logarithmicCumulative
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [map_smul, Function.comp_apply, labelAtom_mass, smul_eq_mul, mul_one]

theorem fullLabel_cumulative_nonneg (F : ℕ → I) (t : ℝ) (i : I) :
    0 ≤ fullVectorCumulative (labelAtom ∘ F) t i := by
  unfold fullVectorCumulative
  rw [lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (by positivity) (labelAtom_nonneg (F (n+1)) i)

theorem full_harmonic_mass_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < logarithmicCumulative (fun _ => 1) t := by
  have hf : 0 < ⌊Real.exp t⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr ht)
  unfold logarithmicCumulative
  apply Finset.sum_pos'
  · intro n _
    positivity
  · refine ⟨0, Finset.mem_range.mpr hf, ?_⟩
    norm_num

theorem fullLabelLaw_isProbabilityVector (F : ℕ → I) {t : ℝ} (ht : 0 ≤ t) :
    IsProbabilityVector (fullLabelLaw F t) := by
  have hm := full_harmonic_mass_pos ht
  constructor
  · intro i
    exact mul_nonneg (inv_nonneg.mpr hm.le) (fullLabel_cumulative_nonneg F t i)
  · change lp.tsumCLM ℝ I ℝ
      ((logarithmicCumulative (fun _ => 1) t)⁻¹ •
        fullVectorCumulative (labelAtom ∘ F) t) = 1
    rw [map_smul, fullLabel_cumulative_mass]
    exact inv_mul_cancel₀ hm.ne'

theorem actual_label_law_real_cutoff (F : ℕ → I)
    (hpass : EventuallyLabelPassageInvariant F) :
    ∃ μ : PMF I,
      Tendsto (fun X => ∑' i, |oddLabelLaw F (Real.log X) i - (μ i).toReal|)
        atTop (𝓝 0) ∧
      Tendsto (fun X => ∑' i,
        |fullLabelLaw (oddPartLabel F) (Real.log X) i - (μ i).toReal|) atTop (𝓝 0) := by
  obtain ⟨μ, ho, hf⟩ := actual_odd_and_all_start_label_PMF_law F hpass
  exact ⟨μ, ho.comp Real.tendsto_log_atTop, hf.comp Real.tendsto_log_atTop⟩

theorem actual_global_minimum_odd_and_all_start_law :
    ∃ μ : PMF ℕ,
      Tendsto (fun t => ∑' i, |oddLabelLaw syracuseGlobalMinimum t i - (μ i).toReal|)
        atTop (𝓝 0) ∧
      Tendsto (fun t => ∑' i,
        |fullLabelLaw (oddPartLabel syracuseGlobalMinimum) t i - (μ i).toReal|)
        atTop (𝓝 0) :=
  actual_odd_and_all_start_label_PMF_law _ global_minimum_eventually_passage_invariant

theorem actual_tail_component_odd_and_all_start_law :
    ∃ μ : PMF SyracuseTailComponent,
      Tendsto (fun t => ∑' i, |oddLabelLaw syracuseTailLabel t i - (μ i).toReal|)
        atTop (𝓝 0) ∧
      Tendsto (fun t => ∑' i,
        |fullLabelLaw (oddPartLabel syracuseTailLabel) t i - (μ i).toReal|)
        atTop (𝓝 0) :=
  actual_odd_and_all_start_label_PMF_law _ tail_component_eventually_passage_invariant

theorem actual_fixed_passage_odd_and_all_start_law (M : ℕ) (hM : 1 ≤ M) :
    ∃ μ : PMF {n : ℕ // n ≤ M},
      Tendsto (fun t => ∑' i, |oddLabelLaw (fixedPassageLabel M hM) t i - (μ i).toReal|)
        atTop (𝓝 0) ∧
      Tendsto (fun t => ∑' i,
        |fullLabelLaw (oddPartLabel (fixedPassageLabel M hM)) t i - (μ i).toReal|)
        atTop (𝓝 0) :=
  actual_odd_and_all_start_label_PMF_law _ (fixed_passage_eventually_passage_invariant M hM)

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.fullLabelLaw_isProbabilityVector
#print axioms CollatzCanonical.LabelLaw.actual_label_law_real_cutoff
#print axioms CollatzCanonical.LabelLaw.actual_global_minimum_odd_and_all_start_law
#print axioms CollatzCanonical.LabelLaw.actual_tail_component_odd_and_all_start_law
#print axioms CollatzCanonical.LabelLaw.actual_fixed_passage_odd_and_all_start_law
