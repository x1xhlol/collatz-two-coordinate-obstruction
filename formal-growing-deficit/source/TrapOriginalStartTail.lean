import TrapNativeStoppedWhiteTail

/-! Averaging the native stopped-white estimate over the original first Hold point. -/

set_option autoImplicit false

open CollatzResearch
open scoped BigOperators

namespace CollatzResearch

theorem trap_pmf_expectation_le_constant {α : Type*}
    (p : PMF α) (f : α → ℝ) (C : ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (hfC : ∀ x, f x ≤ C) :
    trapPMFExpectation p f ≤ C := by
  have hmass : (∑' x, (p x).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x), p.tsum_coe]
    rfl
  calc
    trapPMFExpectation p f ≤ ∑' x, (p x).toReal * C := by
      apply (trap_pmf_expectation_summable p f hf0 hf1).tsum_le_tsum
        _ ((ENNReal.summable_toReal p.tsum_coe_ne_top).mul_right C)
      intro x
      exact mul_le_mul_of_nonneg_left (hfC x) ENNReal.toReal_nonneg
    _ = C := by rw [tsum_mul_right, hmass, one_mul]

end CollatzResearch

namespace Erdos1135.Tao

open TaoSection7Case3SourceStoppingRun
open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

theorem trap_holdList_event_cons
    (C : ℕ) (E : List TaoSection7RenewalPoint → Prop) :
    trapPMFEvent (taoSection7HoldListPMF (C + 1)) E =
      trapPMFExpectation taoSection7HoldPMF
        (fun start => trapPMFEvent (taoSection7HoldListPMF C) (fun full => E (start :: full))) := by
  classical
  let F := fun hs => if E hs then (1 : ℝ) else 0
  have hF0 : ∀ hs, 0 ≤ F hs := fun hs => by simp [F]; split_ifs <;> norm_num
  have hF1 : ∀ hs, F hs ≤ 1 := fun hs => by simp [F]; split_ifs <;> norm_num
  change trapPMFExpectation _ F = _
  rw [taoSection7HoldListPMF, trap_pmf_expectation_bind _ _ _ hF0 hF1]
  congr 1
  funext start
  exact trap_pmf_expectation_map (taoSection7HoldListPMF C) (fun full => start :: full) F hF0 hF1

noncomputable def trapOriginalStartFewWhiteEvent
    (n C J R T : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (family : Set TaoSection7Triangle) : List TaoSection7RenewalPoint → Prop
  | [] => False
  | start :: full => trapEarlyStopFewWhiteEvent n C J R T xi epsilon family start full

theorem trap_original_start_few_white_le_exp_of_native_moment
    (n C J R T : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (family : Set TaoSection7Triangle)
    (hmoment : ∀ start,
      (∑' full : List TaoSection7RenewalPoint,
        taoSection7HoldListPMF C full * ENNReal.ofReal
          (lemma79CutoffTailMoment (lemma79HoldPathPointAt start full)
            family n xi epsilon C R)) ≤ ENNReal.ofReal (Real.exp epsilon)) :
    trapPMFEvent (taoSection7HoldListPMF (C + 1))
        (trapOriginalStartFewWhiteEvent n C J R T xi epsilon family) ≤
      Real.exp ((T : ℝ) + epsilon - epsilon * (R : ℝ)) := by
  classical
  rw [trap_holdList_event_cons]
  apply trap_pmf_expectation_le_constant
  · intro start
    apply trap_pmf_expectation_nonneg
    intro full
    split_ifs <;> norm_num
  · intro start
    apply trap_pmf_expectation_le_one
    · intro full
      split_ifs <;> norm_num
    · intro full
      split_ifs <;> norm_num
  · intro start
    exact trap_early_stop_few_white_le_exp_of_native_moment n C J R T xi epsilon
      family start (hmoment start)

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_holdList_event_cons
#print axioms Erdos1135.Tao.trap_original_start_few_white_le_exp_of_native_moment
