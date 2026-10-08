import TrapFewWhiteEventReduction
import Erdos1135.Tao.Renewal.Lemma77TerminalHoldMoment

/-! Finite-list increment bounds under the original iid Hold law. -/

set_option autoImplicit false
open scoped BigOperators

namespace Erdos1135.Tao
open CollatzResearch TaoSection7Lemma77

theorem trap_holdList_any_event_le
    (N : ℕ) (E : TaoSection7RenewalPoint → Prop) :
    trapPMFEvent (taoSection7HoldListPMF N) (fun hs => ∃ h ∈ hs, E h) ≤
      (N : ℝ) * trapPMFEvent taoSection7HoldPMF E := by
  classical
  induction N with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, trapPMFEvent, trapPMFExpectation,
        taoSection7HoldListPMF]
      rw [tsum_eq_single []]
      · simp
      · intro hs hne
        simp [PMF.pure_apply, hne]
  | succ N ih =>
      rw [trap_holdList_event_cons]
      have hpoint (start : TaoSection7RenewalPoint) :
          trapPMFEvent (taoSection7HoldListPMF N)
              (fun full => ∃ h ∈ start :: full, E h) ≤
            (if E start then 1 else 0) +
              trapPMFEvent (taoSection7HoldListPMF N) (fun full => ∃ h ∈ full, E h) := by
        have hcover := trap_pmf_event_le_add_of_cover (taoSection7HoldListPMF N)
          (fun full => ∃ h ∈ start :: full, E h)
          (fun _ => E start) (fun full => ∃ h ∈ full, E h)
          (by intro full h; simpa using h)
        have hconst : trapPMFEvent (taoSection7HoldListPMF N) (fun _ => E start) =
            if E start then 1 else 0 := by
          by_cases h : E start
          · simp only [trapPMFEvent, trapPMFExpectation, h, ite_true, mul_one]
            rw [← ENNReal.tsum_toReal_eq (fun x => PMF.apply_ne_top _ x), PMF.tsum_coe]
            rfl
          · simp [trapPMFEvent, trapPMFExpectation, h]
        rwa [hconst] at hcover
      let f := fun start => trapPMFEvent (taoSection7HoldListPMF N)
        (fun full => ∃ h ∈ start :: full, E h)
      let c := trapPMFEvent (taoSection7HoldListPMF N) (fun full => ∃ h ∈ full, E h)
      have hsumF := trap_pmf_expectation_summable taoSection7HoldPMF f
        (fun start => trap_pmf_expectation_nonneg _ _ (by intro full; split_ifs <;> norm_num))
        (fun start => trap_pmf_expectation_le_one _ _
          (by intro full; split_ifs <;> norm_num) (by intro full; split_ifs <;> norm_num))
      have hsumE := trap_pmf_expectation_summable taoSection7HoldPMF
        (fun start => if E start then (1 : ℝ) else 0)
        (by intro start; split_ifs <;> norm_num) (by intro start; split_ifs <;> norm_num)
      have hsumC := (ENNReal.summable_toReal taoSection7HoldPMF.tsum_coe_ne_top).mul_right c
      have hmass : (∑' h, (taoSection7HoldPMF h).toReal) = 1 := by
        rw [← ENNReal.tsum_toReal_eq (fun h => PMF.apply_ne_top _ h), PMF.tsum_coe]
        rfl
      calc
        trapPMFExpectation taoSection7HoldPMF f ≤
            ∑' start, ((taoSection7HoldPMF start).toReal * (if E start then 1 else 0) +
              (taoSection7HoldPMF start).toReal * c) := by
          apply hsumF.tsum_le_tsum _ (hsumE.add hsumC)
          intro start
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (hpoint start) ENNReal.toReal_nonneg
        _ = trapPMFEvent taoSection7HoldPMF E + c := by
          rw [hsumE.tsum_add hsumC, tsum_mul_right, hmass, one_mul]
          rfl
        _ ≤ trapPMFEvent taoSection7HoldPMF E +
            (N : ℝ) * trapPMFEvent taoSection7HoldPMF E := add_le_add le_rfl ih
        _ = ((N + 1 : ℕ) : ℝ) * trapPMFEvent taoSection7HoldPMF E := by
          push_cast
          ring

def TrapHoldIncrementGood (H V : ℝ) (h : TaoSection7RenewalPoint) : Prop :=
  0 ≤ h.l ∧ ((h.j : ℕ) : ℝ) ≤ H ∧ (h.l : ℝ) ≤ V

theorem trap_hold_bad_increment_probability_le (H V : ℝ) :
    trapPMFEvent taoSection7HoldPMF (fun h => ¬ TrapHoldIncrementGood H V h) ≤
      15 * Real.exp (-Real.log (21 / 20 : ℝ) * min H V) := by
  classical
  let alpha := Real.log (21 / 20 : ℝ)
  let c := Real.exp (-alpha * min H V)
  have halpha : 0 < alpha := Real.log_pos (by norm_num)
  have hsumI := trap_pmf_expectation_summable taoSection7HoldPMF
    (fun h => if ¬ TrapHoldIncrementGood H V h then (1 : ℝ) else 0)
    (by intro h; split_ifs <;> norm_num) (by intro h; split_ifs <;> norm_num)
  have hsumW := summable_taoSection7HoldPMF_terminalHoldExpWeight_log_21_div_20
  have hpoint (h : TaoSection7RenewalPoint) :
      (taoSection7HoldPMF h).toReal * (if ¬ TrapHoldIncrementGood H V h then 1 else 0) ≤
        ((taoSection7HoldPMF h).toReal * lemma77TerminalHoldExpWeight alpha h) * c := by
    by_cases hl : h.l < 0
    · rw [taoSection7HoldPMF_toReal_eq_zero_of_l_neg hl]
      simp
    have hl0 : (0 : ℝ) ≤ h.l := by exact_mod_cast (le_of_not_gt hl)
    by_cases hg : TrapHoldIncrementGood H V h
    · simp only [hg, not_true_eq_false, ite_false, mul_zero]
      dsimp only [lemma77TerminalHoldExpWeight, c]
      positivity
    · simp only [hg, not_false_eq_true, ite_true, mul_one]
      have hlarge : min H V ≤ ((h.j : ℕ) : ℝ) + (h.l : ℝ) := by
        have hbad : H < ((h.j : ℕ) : ℝ) ∨ V < (h.l : ℝ) := by
          simpa only [TrapHoldIncrementGood, le_of_not_gt hl, true_and, not_and_or,
            not_le] using hg
        rcases hbad with hj | hl
        · linarith [min_le_left H V]
        · have hj0 : (0 : ℝ) ≤ (h.j : ℕ) := Nat.cast_nonneg _
          linarith [min_le_right H V]
      have hexp : 1 ≤ lemma77TerminalHoldExpWeight alpha h * c := by
        rw [lemma77TerminalHoldExpWeight, ← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        nlinarith
      simpa only [mul_assoc, mul_one] using
        mul_le_mul_of_nonneg_left hexp (show 0 ≤ (taoSection7HoldPMF h).toReal from ENNReal.toReal_nonneg)
  calc
    trapPMFEvent taoSection7HoldPMF (fun h => ¬ TrapHoldIncrementGood H V h) =
        ∑' h, (taoSection7HoldPMF h).toReal *
          (if ¬ TrapHoldIncrementGood H V h then (1 : ℝ) else 0) := by
      unfold trapPMFEvent trapPMFExpectation
      apply tsum_congr
      intro h
      by_cases hg : TrapHoldIncrementGood H V h <;> simp [hg]
    _ ≤ ∑' h, ((taoSection7HoldPMF h).toReal * lemma77TerminalHoldExpWeight alpha h) * c :=
      hsumI.tsum_le_tsum hpoint (hsumW.mul_right c)
    _ = (∑' h, (taoSection7HoldPMF h).toReal * lemma77TerminalHoldExpWeight alpha h) * c :=
      tsum_mul_right
    _ ≤ 15 * c := mul_le_mul_of_nonneg_right
      tsum_taoSection7HoldPMF_terminalHoldExpWeight_log_21_div_20_le_15 (Real.exp_nonneg _)

theorem trap_holdList_bad_increment_probability_le (N : ℕ) (H V : ℝ) :
    trapPMFEvent (taoSection7HoldListPMF N)
        (fun hs => ¬ ∀ h ∈ hs, TrapHoldIncrementGood H V h) ≤
      (N : ℝ) * (15 * Real.exp (-Real.log (21 / 20 : ℝ) * min H V)) := by
  classical
  have h := trap_holdList_any_event_le N (fun h => ¬ TrapHoldIncrementGood H V h)
  have heq : (fun hs : List TaoSection7RenewalPoint => ∃ h ∈ hs, ¬ TrapHoldIncrementGood H V h) =
      (fun hs : List TaoSection7RenewalPoint => ¬ ∀ h ∈ hs, TrapHoldIncrementGood H V h) := by
    funext hs
    simp
  rw [heq] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (trap_hold_bad_increment_probability_le H V) (Nat.cast_nonneg _))

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_holdList_bad_increment_probability_le
