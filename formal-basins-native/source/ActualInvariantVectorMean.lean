import ActualVectorWindowRates
import BanachOddMeanCriterion
import ActualWeightedOddMeanExistence

open Filter
open scoped Topology

namespace CollatzCanonical.LabelLaw
open CollatzCanonical.BanachWindow

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem actual_invariant_odd_vector_mean_exists (F : ℕ → V)
    (hF : ∀ q, ‖F q‖ ≤ 1) (hpass : EventuallyPassageInvariant F) :
    ∃ p : V, Tendsto (fun t => t⁻¹ • oddVectorCumulative F t) atTop (𝓝 p) := by
  obtain ⟨C, c, hC, hc, _, hfirst⟩ := first_scale_normalized_vector_rate F hF hpass
  obtain ⟨D, d, _, hd, _, hsecond⟩ := second_scale_normalized_vector_rate F hF hpass
  have ha : Erdos1135.Tao.taoAlpha = (1001 / 1000 : ℝ) := by
    norm_num [Erdos1135.Tao.taoAlpha]
  have hb : Erdos1135SecondScale.Tao.taoAlpha = (2001 / 2000 : ℝ) := by
    norm_num [Erdos1135SecondScale.Tao.taoAlpha]
  have hirr : Irrational
      (Real.log Erdos1135.Tao.taoAlpha / Real.log Erdos1135SecondScale.Tao.taoAlpha) := by
    rw [ha, hb]
    exact CollatzCanonical.Scales.logarithms_incommensurable
  exact oddVector_mean_of_two_eventual_closed_rates F hF
    Erdos1135.Tao.taoAlpha_one_lt Erdos1135SecondScale.Tao.taoAlpha_one_lt
    hC hc hd hirr hfirst hsecond

end CollatzCanonical.LabelLaw
#print axioms CollatzCanonical.LabelLaw.actual_invariant_odd_vector_mean_exists
