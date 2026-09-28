import SecondScaleActualStoppedTupleFibers
import SecondScaleCanonicalLocalClockProbability
import Erdos1135SecondScale.Tao.Probability.LogWindowFloorPerturbation

set_option autoImplicit false
open scoped BigOperators

namespace CollatzPassageAtomsSecondScale
open Erdos1135SecondScale.Tao

theorem odd_window_nat_event_probability {lo hi : ℕ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) (A : Set ℕ) :
    ((oddLogWindowOddNatPMF lo hi hmass).toOuterMeasure
      {q : TaoOddNat | q.1 ∈ A}).toReal = logFinsetProb (oddLogWindow lo hi) A := by
  rw [oddLogWindowOddNatPMF, PMF.toOuterMeasure_map_apply,
    ← pmfProb_eq_toOuterMeasure_toReal]
  exact pmfProb_logFinsetPMF (oddLogWindow lo hi) hmass A

theorem logFinsetProb_split_le (S : Finset ℕ) (A G : Set ℕ) :
    logFinsetProb S A ≤ logFinsetProb S Gᶜ + logFinsetProb S (A ∩ G) := by
  classical
  unfold logFinsetProb
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (logFinsetMass_nonneg S)
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q _
  by_cases hA : q ∈ A <;> by_cases hG : q ∈ G <;>
    simp [hA, hG, logNatWeight_nonneg q]

/-- A finite logarithmic source gives the expected binary tuple-count bound
for every actual stopped endpoint fiber. -/
theorem logFinsetProb_stopped_endpoint_le (S : Finset ℕ) (A : Set ℕ)
    (τ : ℕ → ℕ) (L m B : ℕ) (hB : 0 < B)
    (hmass : 0 < logFinsetMass S)
    (hodd : ∀ q ∈ S, q ∈ A → Odd q)
    (hsource : ∀ q ∈ S, q ∈ A → B ≤ q)
    (hcost : ∀ q ∈ S, q ∈ A → (stoppedValuationWord τ q).sum ≤ L)
    (hend : ∀ q ∈ S, q ∈ A → (syracuse^[τ q]) q = m) :
    logFinsetProb S A ≤ (2 : ℝ) ^ L * ((1 : ℝ) / B / logFinsetMass S) := by
  classical
  let s := S.filter (fun q => q ∈ A)
  have hb := actual_stopped_endpoint_mass_le s τ L m
    (fun q hq => hodd q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2)
    (fun q hq => hcost q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2)
    (fun q hq => hend q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2)
    (fun q => logNatWeight q / logFinsetMass S)
    (show 0 ≤ (1 : ℝ) / B / logFinsetMass S by positivity) ?_
  · simpa only [logFinsetProb, Finset.sum_div, s] using hb
  · intro q hq
    have hqB := hsource q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2
    have hqpos : 0 < q := lt_of_lt_of_le hB hqB
    change logNatWeight q / logFinsetMass S ≤ (1 : ℝ) / B / logFinsetMass S
    rw [logNatWeight_eq_one_div_of_pos hqpos]
    apply div_le_div_of_nonneg_right _ hmass.le
    exact one_div_le_one_div_of_le (by exact_mod_cast hB) (by exact_mod_cast hqB)

end CollatzPassageAtomsSecondScale
