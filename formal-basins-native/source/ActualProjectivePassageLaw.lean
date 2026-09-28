import FiniteLabelPushforward
import CountableLabelLawCorollaries

set_option autoImplicit false
open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw
open CollatzClockAudit

noncomputable def fixedPassageLimitVector (M : ℕ) (hM : 1 ≤ M) :
    LabelVector {n : ℕ // n ≤ M} :=
  Classical.choose (actual_odd_and_all_start_label_law (fixedPassageLabel M hM)
    (fixed_passage_eventually_passage_invariant M hM))

theorem fixedPassageLimitVector_isProbability (M : ℕ) (hM : 1 ≤ M) :
    IsProbabilityVector (fixedPassageLimitVector M hM) :=
  (Classical.choose_spec (actual_odd_and_all_start_label_law (fixedPassageLabel M hM)
    (fixed_passage_eventually_passage_invariant M hM))).1

theorem fixedPassageLimitVector_tendsto (M : ℕ) (hM : 1 ≤ M) :
    Tendsto (oddLabelLaw (fixedPassageLabel M hM)) atTop (𝓝 (fixedPassageLimitVector M hM)) :=
  (Classical.choose_spec (actual_odd_and_all_start_label_law (fixedPassageLabel M hM)
    (fixed_passage_eventually_passage_invariant M hM))).2.1

noncomputable def fixedPassageLimitPMF (M : ℕ) (hM : 1 ≤ M) : PMF {n : ℕ // n ≤ M} :=
  probabilityVectorPMF (fixedPassageLimitVector M hM) (fixedPassageLimitVector_isProbability M hM)

theorem fixedPassageLimitPMF_fullL1 (M : ℕ) (hM : 1 ≤ M) :
    Tendsto (fun t => ∑' i,
      |oddLabelLaw (fixedPassageLabel M hM) t i - (fixedPassageLimitPMF M hM i).toReal|)
      atTop (𝓝 0) := by
  simpa only [fixedPassageLimitPMF, probabilityVectorPMF_toReal,
    labelVector_norm_eq_fullL1] using
    (tendsto_iff_norm_sub_tendsto_zero.mp (fixedPassageLimitVector_tendsto M hM))

theorem fixedPassageLimitPMF_all_start_fullL1 (M : ℕ) (hM : 1 ≤ M) :
    Tendsto (fun t => ∑' i,
      |fullLabelLaw (oddPartLabel (fixedPassageLabel M hM)) t i -
        (fixedPassageLimitPMF M hM i).toReal|) atTop (𝓝 0) := by
  have h := (Classical.choose_spec (actual_odd_and_all_start_label_law (fixedPassageLabel M hM)
    (fixed_passage_eventually_passage_invariant M hM))).2.2
  simpa only [fixedPassageLimitPMF, probabilityVectorPMF_toReal,
    labelVector_norm_eq_fullL1] using (tendsto_iff_norm_sub_tendsto_zero.mp h)

theorem fixed_passage_limit_projective {L M : ℕ} (hL : 1 ≤ L) (hLM : L ≤ M) (hM : 1 ≤ M) :
    (fixedPassageLimitPMF M hM).map (fun z => fixedPassageLabel L hL z.1) =
      fixedPassageLimitPMF L hL := by
  have he : (fun z : {n : ℕ // n ≤ M} => fixedPassageLabel L hL z.1) ∘
      fixedPassageLabel M hM = fixedPassageLabel L hL := by
    funext q
    exact passAtMostOrOne_compose hL hLM hM
  exact finite_label_probability_pushforward (fixedPassageLabel M hM)
    (fun z => fixedPassageLabel L hL z.1)
    (fixedPassageLimitVector M hM) (fixedPassageLimitVector L hL)
    (fixedPassageLimitVector_isProbability M hM) (fixedPassageLimitVector_isProbability L hL)
    (fixedPassageLimitVector_tendsto M hM) (by rw [he]; exact fixedPassageLimitVector_tendsto L hL)

#print axioms fixedPassageLimitPMF_fullL1
#print axioms fixedPassageLimitPMF_all_start_fullL1
#print axioms fixed_passage_limit_projective

end CollatzCanonical.LabelLaw
