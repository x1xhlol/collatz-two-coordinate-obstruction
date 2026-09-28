import CountableLabelLawCorollaries
import StandardCollatzMinimumLaw

open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw
open CollatzCanonical.BanachWindow Erdos1135.Tao

theorem fullLabelLaw_standard_minimum (t : ℝ) :
    fullLabelLaw (oddPartLabel syracuseGlobalMinimum) t =
      fullLabelLaw collatzOrbitMin t := by
  unfold fullLabelLaw
  congr 1
  unfold fullVectorCumulative
  apply Finset.sum_congr rfl
  intro n _
  simp only [Function.comp_apply, oddPartLabel,
    collatzOrbitMin_eq_syracuseGlobalMinimum_oddPart (Nat.succ_pos n)]

theorem oddLabelLaw_standard_minimum (t : ℝ) :
    oddLabelLaw syracuseGlobalMinimum t = oddLabelLaw collatzOrbitMin t := by
  unfold oddLabelLaw
  congr 1
  unfold oddVectorCumulative
  apply Finset.sum_congr rfl
  intro n _
  unfold oddVectorTerm
  split_ifs with hn
  · simp only [Function.comp_apply,
      collatzOrbitMin_eq_syracuseGlobalMinimum_of_odd (Nat.odd_iff.mpr hn)]
  · rfl

theorem actual_standard_minimum_odd_and_all_start_law :
    ∃ μ : PMF ℕ,
      Tendsto (fun t => ∑' i, |oddLabelLaw collatzOrbitMin t i - (μ i).toReal|)
        atTop (𝓝 0) ∧
      Tendsto (fun t => ∑' i, |fullLabelLaw collatzOrbitMin t i - (μ i).toReal|)
        atTop (𝓝 0) := by
  obtain ⟨μ, ho, hf⟩ := actual_global_minimum_odd_and_all_start_law
  refine ⟨μ, ?_, ?_⟩
  · simpa only [oddLabelLaw_standard_minimum] using ho
  · simpa only [fullLabelLaw_standard_minimum] using hf

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.actual_standard_minimum_odd_and_all_start_law
