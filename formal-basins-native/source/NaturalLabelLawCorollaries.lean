import ActualNaturalLabelLaw
import StandardMinimumAllStartLaw
import LabelProbabilityTightness

open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw
variable {I : Type*}

theorem labelSubsetMass_uniform_convergence_nat {L : ℕ → LabelVector I} {p : LabelVector I}
    (h : Tendsto L atTop (𝓝 p)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
      ∀ S : Set I, |labelSubsetMass S (L X) - labelSubsetMass S p| < ε := by
  intro ε hε
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp h
  filter_upwards [hn.eventually_lt_const hε] with X hX
  intro S
  exact (labelSubsetMass_difference_le_fullL1 S (L X) p).trans_lt hX

theorem actual_natural_label_law_uniform_over_subsets (F : ℕ → I)
    (hpass : EventuallyLabelPassageInvariant F) :
    ∃ p : LabelVector I, IsProbabilityVector p ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ X : ℕ in atTop, ∀ S : Set I,
        |labelSubsetMass S (naturalOddLabelLaw F X) - labelSubsetMass S p| < ε ∧
        |labelSubsetMass S (naturalFullLabelLaw (oddPartLabel F) X) - labelSubsetMass S p| < ε := by
  obtain ⟨p, hp, _, _, ho, hf⟩ := actual_logarithmic_and_natural_label_laws F hpass
  refine ⟨p, hp, ?_⟩
  intro ε hε
  filter_upwards [labelSubsetMass_uniform_convergence_nat ho ε hε,
    labelSubsetMass_uniform_convergence_nat hf ε hε] with X hXo hXf
  exact fun S => ⟨hXo S, hXf S⟩

theorem actual_natural_tail_component_law :
    ∃ μ : PMF SyracuseTailComponent,
      Tendsto (fun X => ∑' i, |naturalOddLabelLaw syracuseTailLabel X i - (μ i).toReal|)
        atTop (𝓝 0) ∧
      Tendsto (fun X => ∑' i,
        |naturalFullLabelLaw (oddPartLabel syracuseTailLabel) X i - (μ i).toReal|)
        atTop (𝓝 0) := by
  obtain ⟨μ, _, _, ho, hf⟩ := actual_logarithmic_and_natural_label_PMF_laws _
    tail_component_eventually_passage_invariant
  exact ⟨μ, ho, hf⟩

theorem actual_natural_fixed_passage_law (M : ℕ) (hM : 1 ≤ M) :
    ∃ μ : PMF {n : ℕ // n ≤ M},
      Tendsto (fun X => ∑' i, |naturalOddLabelLaw (fixedPassageLabel M hM) X i - (μ i).toReal|)
        atTop (𝓝 0) ∧
      Tendsto (fun X => ∑' i,
        |naturalFullLabelLaw (oddPartLabel (fixedPassageLabel M hM)) X i - (μ i).toReal|)
        atTop (𝓝 0) := by
  obtain ⟨μ, _, _, ho, hf⟩ := actual_logarithmic_and_natural_label_PMF_laws _
    (fixed_passage_eventually_passage_invariant M hM)
  exact ⟨μ, ho, hf⟩

theorem actual_natural_standard_minimum_law :
    ∃ μ : PMF ℕ,
      Tendsto (fun X => ∑' i,
        |naturalOddLabelLaw Erdos1135.Tao.collatzOrbitMin X i - (μ i).toReal|)
        atTop (𝓝 0) ∧
      Tendsto (fun X => ∑' i,
        |naturalFullLabelLaw Erdos1135.Tao.collatzOrbitMin X i - (μ i).toReal|)
        atTop (𝓝 0) := by
  obtain ⟨p, hp, _, _, ho, hf⟩ := actual_halving_invariant_natural_label_laws _
    standard_global_minimum_eventually_passage_invariant (fun _ hq => collatzOrbitMin_halving hq)
  refine ⟨probabilityVectorPMF p hp, ?_, ?_⟩
  · simpa only [probabilityVectorPMF_toReal, labelVector_norm_eq_fullL1] using
      tendsto_iff_norm_sub_tendsto_zero.mp ho
  · simpa only [probabilityVectorPMF_toReal, labelVector_norm_eq_fullL1] using
      tendsto_iff_norm_sub_tendsto_zero.mp hf

theorem actual_standard_minimum_logarithmic_and_natural_tightness :
    ∃ p : LabelVector ℕ, IsProbabilityVector p ∧
      Tendsto (oddLabelLaw Erdos1135.Tao.collatzOrbitMin) atTop (𝓝 p) ∧
      Tendsto (fullLabelLaw Erdos1135.Tao.collatzOrbitMin) atTop (𝓝 p) ∧
      Tendsto (naturalOddLabelLaw Erdos1135.Tao.collatzOrbitMin) atTop (𝓝 p) ∧
      Tendsto (naturalFullLabelLaw Erdos1135.Tao.collatzOrbitMin) atTop (𝓝 p) ∧
      Tendsto (fun M : ℕ => labelSubsetMass {i | M < i} p) atTop (𝓝 0) := by
  obtain ⟨p, hp, ho, hf, hno, hnf⟩ := actual_halving_invariant_natural_label_laws _
    standard_global_minimum_eventually_passage_invariant (fun _ hq => collatzOrbitMin_halving hq)
  exact ⟨p, hp, ho, hf, hno, hnf, probability_vector_nat_tail_tendsto_zero p⟩

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.actual_natural_label_law_uniform_over_subsets
#print axioms CollatzCanonical.LabelLaw.actual_natural_tail_component_law
#print axioms CollatzCanonical.LabelLaw.actual_natural_fixed_passage_law
#print axioms CollatzCanonical.LabelLaw.actual_natural_standard_minimum_law
#print axioms CollatzCanonical.LabelLaw.actual_standard_minimum_logarithmic_and_natural_tightness
