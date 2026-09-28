import NaturalLabelLawCorollaries

open Filter
open scoped Topology

namespace CollatzCanonical.LabelLaw
variable {I : Type*}

theorem natural_label_limits_of_odd_logarithmic_limit (F : ℕ → I)
    (hpass : EventuallyLabelPassageInvariant F) (p : LabelVector I)
    (hlog : Tendsto (oddLabelLaw F) atTop (𝓝 p)) :
    Tendsto (naturalOddLabelLaw F) atTop (𝓝 p) ∧
      Tendsto (naturalFullLabelLaw (oddPartLabel F)) atTop (𝓝 p) := by
  obtain ⟨q, _, hq, _, ho, hf⟩ := actual_logarithmic_and_natural_label_laws F hpass
  have he : q = p := tendsto_nhds_unique hq hlog
  exact he ▸ ⟨ho, hf⟩

theorem natural_label_limits_of_full_logarithmic_limit (F : ℕ → I)
    (hpass : EventuallyLabelPassageInvariant F)
    (hhalf : ∀ q : ℕ, 0 < q → F (2 * q) = F q) (p : LabelVector I)
    (hlog : Tendsto (fullLabelLaw F) atTop (𝓝 p)) :
    Tendsto (naturalOddLabelLaw F) atTop (𝓝 p) ∧
      Tendsto (naturalFullLabelLaw F) atTop (𝓝 p) := by
  obtain ⟨q, _, _, hq, ho, hf⟩ := actual_halving_invariant_natural_label_laws F hpass hhalf
  have he : q = p := tendsto_nhds_unique hq hlog
  exact he ▸ ⟨ho, hf⟩

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.natural_label_limits_of_odd_logarithmic_limit
#print axioms CollatzCanonical.LabelLaw.natural_label_limits_of_full_logarithmic_limit
