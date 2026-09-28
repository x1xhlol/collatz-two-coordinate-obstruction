import ActualProjectivePassageLaw
import NaturalLabelLimitIdentification

set_option autoImplicit false
open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw

theorem fixedPassageLimitVector_natural_limits (M : ℕ) (hM : 1 ≤ M) :
    Tendsto (naturalOddLabelLaw (fixedPassageLabel M hM)) atTop
        (𝓝 (fixedPassageLimitVector M hM)) ∧
      Tendsto (naturalFullLabelLaw (oddPartLabel (fixedPassageLabel M hM))) atTop
        (𝓝 (fixedPassageLimitVector M hM)) :=
  natural_label_limits_of_odd_logarithmic_limit (fixedPassageLabel M hM)
    (fixed_passage_eventually_passage_invariant M hM) (fixedPassageLimitVector M hM)
    (fixedPassageLimitVector_tendsto M hM)

theorem fixedPassageLimitPMF_natural_odd_fullL1 (M : ℕ) (hM : 1 ≤ M) :
    Tendsto (fun X => ∑' i,
      |naturalOddLabelLaw (fixedPassageLabel M hM) X i -
        (fixedPassageLimitPMF M hM i).toReal|) atTop (𝓝 0) := by
  simpa only [fixedPassageLimitPMF, probabilityVectorPMF_toReal,
    labelVector_norm_eq_fullL1] using
    (tendsto_iff_norm_sub_tendsto_zero.mp (fixedPassageLimitVector_natural_limits M hM).1)

theorem fixedPassageLimitPMF_natural_all_start_fullL1 (M : ℕ) (hM : 1 ≤ M) :
    Tendsto (fun X => ∑' i,
      |naturalFullLabelLaw (oddPartLabel (fixedPassageLabel M hM)) X i -
        (fixedPassageLimitPMF M hM i).toReal|) atTop (𝓝 0) := by
  simpa only [fixedPassageLimitPMF, probabilityVectorPMF_toReal,
    labelVector_norm_eq_fullL1] using
    (tendsto_iff_norm_sub_tendsto_zero.mp (fixedPassageLimitVector_natural_limits M hM).2)

#print axioms fixedPassageLimitPMF_natural_odd_fullL1
#print axioms fixedPassageLimitPMF_natural_all_start_fullL1

end CollatzCanonical.LabelLaw
