import NaturalLabelProbabilityVectors
import NaturalFullPrefixLimit
import LabelHalvingInvariant

open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw
open CollatzCanonical.NaturalPrefix CollatzCanonical.BanachWindow Erdos1135
variable {I : Type*}

theorem natural_vector_block_oddPart (F : ℕ → I) (y : ℝ) :
    naturalOddVectorBlockMean (labelAtom ∘ oddPartLabel F) y =
      naturalOddVectorBlockMean (labelAtom ∘ F) y := by
  unfold naturalOddVectorBlockMean finiteVectorMean
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Function.comp_apply,
    oddPartLabel_eq_of_odd F (Nat.odd_iff.mpr (Tao.oddLogWindow_mem.mp hq).2.2)]

theorem naturalFullLabelLaw_eq_of_halving (F : ℕ → I)
    (hhalf : ∀ q : ℕ, 0 < q → F (2 * q) = F q) (X : ℕ) :
    naturalFullLabelLaw (oddPartLabel F) X = naturalFullLabelLaw F X := by
  unfold naturalFullLabelLaw fullNaturalPrefixSum
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg labelAtom (oddPartLabel_eq_of_halving F hhalf (Nat.succ_pos n))

theorem actual_logarithmic_and_natural_label_laws (F : ℕ → I)
    (hpass : EventuallyLabelPassageInvariant F) :
    ∃ p : LabelVector I, IsProbabilityVector p ∧
      Tendsto (oddLabelLaw F) atTop (𝓝 p) ∧
      Tendsto (fullLabelLaw (oddPartLabel F)) atTop (𝓝 p) ∧
      Tendsto (naturalOddLabelLaw F) atTop (𝓝 p) ∧
      Tendsto (naturalFullLabelLaw (oddPartLabel F)) atTop (𝓝 p) := by
  have hv : EventuallyPassageInvariant (labelAtom ∘ F) := by
    filter_upwards [hpass] with x hx
    intro q hq τ hτ
    exact congrArg labelAtom (hx q hq τ hτ)
  obtain ⟨p, hp, hb⟩ := actual_invariant_odd_and_natural_vector_mean (labelAtom ∘ F)
    (fun q => le_of_eq (labelAtom_norm (F q))) hv
  obtain ⟨hprob, hlog⟩ := odd_label_probability_of_vector_mean F p hp
  have hlogFull : Tendsto (fullLabelLaw (oddPartLabel F)) atTop (𝓝 ((2:ℝ) • p)) := by
    apply fullLabelLaw_tendsto_of_vector_mean
    apply fullVector_mean_of_odd_mean (labelAtom ∘ oddPartLabel F)
      (fun q => le_of_eq (labelAtom_norm _))
      (fun q _ => congrArg labelAtom (oddPartLabel_double F q)) p
    simpa only [oddLabel_cumulative_oddPart] using hp
  have hnatOdd : Tendsto (naturalOddLabelLaw F) atTop (𝓝 ((2:ℝ) • p)) := by
    apply naturalOddLabelLaw_tendsto_of_prefix_mean
    have hn := odd_natural_prefix_mean_of_block_mean
      (fun q => le_of_eq (labelAtom_norm (F q))) hb
    simpa only [smul_smul, one_div_mul_cancel (by norm_num : (2:ℝ) ≠ 0), one_smul] using hn
  have hnatFull : Tendsto (naturalFullLabelLaw (oddPartLabel F)) atTop (𝓝 ((2:ℝ) • p)) := by
    apply full_natural_prefix_mean_of_doubling_invariant
      (fun q => le_of_eq (labelAtom_norm _))
      (fun q => congrArg labelAtom (oddPartLabel_double F q))
    have he : naturalOddVectorBlockMean (labelAtom ∘ oddPartLabel F) =
        naturalOddVectorBlockMean (labelAtom ∘ F) := funext (natural_vector_block_oddPart F)
    change Tendsto (naturalOddVectorBlockMean (labelAtom ∘ oddPartLabel F))
      atTop (𝓝 ((2:ℝ) • p))
    rw [he]
    exact hb
  exact ⟨2 • p, hprob, hlog, hlogFull, hnatOdd, hnatFull⟩

theorem actual_logarithmic_and_natural_label_PMF_laws (F : ℕ → I)
    (hpass : EventuallyLabelPassageInvariant F) :
    ∃ μ : PMF I,
      Tendsto (fun t => ∑' i, |oddLabelLaw F t i - (μ i).toReal|) atTop (𝓝 0) ∧
      Tendsto (fun t => ∑' i, |fullLabelLaw (oddPartLabel F) t i - (μ i).toReal|) atTop (𝓝 0) ∧
      Tendsto (fun X => ∑' i, |naturalOddLabelLaw F X i - (μ i).toReal|) atTop (𝓝 0) ∧
      Tendsto (fun X => ∑' i, |naturalFullLabelLaw (oddPartLabel F) X i - (μ i).toReal|)
        atTop (𝓝 0) := by
  obtain ⟨p, hp, ho, hf, hno, hnf⟩ := actual_logarithmic_and_natural_label_laws F hpass
  refine ⟨probabilityVectorPMF p hp, ?_, ?_, ?_, ?_⟩
  · simpa only [probabilityVectorPMF_toReal, labelVector_norm_eq_fullL1] using
      tendsto_iff_norm_sub_tendsto_zero.mp ho
  · simpa only [probabilityVectorPMF_toReal, labelVector_norm_eq_fullL1] using
      tendsto_iff_norm_sub_tendsto_zero.mp hf
  · simpa only [probabilityVectorPMF_toReal, labelVector_norm_eq_fullL1] using
      tendsto_iff_norm_sub_tendsto_zero.mp hno
  · simpa only [probabilityVectorPMF_toReal, labelVector_norm_eq_fullL1] using
      tendsto_iff_norm_sub_tendsto_zero.mp hnf

theorem actual_halving_invariant_natural_label_laws (F : ℕ → I)
    (hpass : EventuallyLabelPassageInvariant F)
    (hhalf : ∀ q : ℕ, 0 < q → F (2 * q) = F q) :
    ∃ p : LabelVector I, IsProbabilityVector p ∧
      Tendsto (oddLabelLaw F) atTop (𝓝 p) ∧ Tendsto (fullLabelLaw F) atTop (𝓝 p) ∧
      Tendsto (naturalOddLabelLaw F) atTop (𝓝 p) ∧ Tendsto (naturalFullLabelLaw F) atTop (𝓝 p) := by
  obtain ⟨p, hp, ho, hf, hno, hnf⟩ := actual_logarithmic_and_natural_label_laws F hpass
  have he : fullLabelLaw (oddPartLabel F) = fullLabelLaw F :=
    funext (fullLabelLaw_eq_of_halving F hhalf)
  have hne : naturalFullLabelLaw (oddPartLabel F) = naturalFullLabelLaw F :=
    funext (naturalFullLabelLaw_eq_of_halving F hhalf)
  rw [he] at hf
  rw [hne] at hnf
  exact ⟨p, hp, ho, hf, hno, hnf⟩

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.actual_logarithmic_and_natural_label_laws
#print axioms CollatzCanonical.LabelLaw.actual_logarithmic_and_natural_label_PMF_laws
#print axioms CollatzCanonical.LabelLaw.actual_halving_invariant_natural_label_laws
