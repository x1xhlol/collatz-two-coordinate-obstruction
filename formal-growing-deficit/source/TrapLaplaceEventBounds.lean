import TrapBoundedPMFExpectation

/-! Event and Laplace bounds for PMFs, with the killed moment allowed to be unbounded. -/

set_option autoImplicit false

open scoped BigOperators

namespace CollatzResearch

noncomputable def trapPMFEventENN {α : Type*} (p : PMF α) (E : α → Prop) : ENNReal := by
  classical
  exact ∑' a, p a * if E a then 1 else 0

noncomputable def trapPMFEvent {α : Type*} (p : PMF α) (E : α → Prop) : ℝ := by
  classical
  exact trapPMFExpectation p (fun a => if E a then 1 else 0)

theorem trap_pmf_event_toReal {α : Type*} (p : PMF α) (E : α → Prop) :
    (trapPMFEventENN p E).toReal = trapPMFEvent p E := by
  classical
  unfold trapPMFEventENN trapPMFEvent trapPMFExpectation
  rw [ENNReal.tsum_toReal_eq (fun a => by
    by_cases ha : E a
    · simpa [ha] using p.apply_ne_top a
    · simp [ha])]
  apply tsum_congr
  intro a
  by_cases ha : E a <;> simp [ha]

theorem trap_pmf_event_le_exp_of_moment {α : Type*}
    (p : PMF α) (E : α → Prop) (F : α → ENNReal) (T b c : ℝ)
    (hlower : ∀ a, E a → ENNReal.ofReal (Real.exp (-T + b)) ≤ F a)
    (hmoment : (∑' a, p a * F a) ≤ ENNReal.ofReal (Real.exp c)) :
    trapPMFEvent p E ≤ Real.exp (T + c - b) := by
  classical
  let w := ENNReal.ofReal (Real.exp (T - b))
  have hunit : w * ENNReal.ofReal (Real.exp (-T + b)) = 1 := by
    dsimp only [w]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    simp [show T - b + (-T + b) = 0 by ring]
  have hpoint : ∀ a, (if E a then (1 : ENNReal) else 0) ≤ w * F a := by
    intro a
    by_cases ha : E a
    · rw [ite_eq_left ha, ← hunit]
      exact mul_le_mul_right (hlower a ha) w
    · simp [ha]
  have hENN : trapPMFEventENN p E ≤ ENNReal.ofReal (Real.exp (T + c - b)) := by
    calc
      trapPMFEventENN p E ≤ ∑' a, p a * (w * F a) := by
        apply ENNReal.tsum_le_tsum
        intro a
        exact mul_le_mul_right (hpoint a) (p a)
      _ = w * (∑' a, p a * F a) := by
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro a
        exact mul_left_comm _ _ _
      _ ≤ w * ENNReal.ofReal (Real.exp c) := mul_le_mul_right hmoment w
      _ = ENNReal.ofReal (Real.exp (T + c - b)) := by
        dsimp only [w]
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        congr 2
        ring
  rw [← trap_pmf_event_toReal]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using h

theorem trap_pmf_laplace_le_low_count_probability {α : Type*}
    (p : PMF α) (W : α → ℕ) (a : ℝ) (ha : 0 ≤ a) (T : ℕ) :
    trapPMFExpectation p (fun x => Real.exp (-a * (W x : ℝ))) ≤
      trapPMFEvent p (fun x => W x ≤ T) + Real.exp (-a * (T : ℝ)) := by
  classical
  let indicator := fun x => if W x ≤ T then (1 : ℝ) else 0
  let c := Real.exp (-a * (T : ℝ))
  have hsumF := trap_pmf_expectation_summable p
    (fun x => Real.exp (-a * (W x : ℝ)))
    (fun x => Real.exp_nonneg _)
    (fun x => Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (Nat.cast_nonneg _)))
  have hsumI := trap_pmf_expectation_summable p indicator
    (fun x => by simp [indicator]; split_ifs <;> norm_num)
    (fun x => by simp [indicator]; split_ifs <;> norm_num)
  have hsumC := (ENNReal.summable_toReal p.tsum_coe_ne_top).mul_right c
  have hmass : (∑' x, (p x).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x), p.tsum_coe]
    rfl
  calc
    trapPMFExpectation p (fun x => Real.exp (-a * (W x : ℝ))) ≤
        ∑' x, ((p x).toReal * indicator x + (p x).toReal * c) := by
      apply hsumF.tsum_le_tsum _ (hsumI.add hsumC)
      intro x
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      by_cases hx : W x ≤ T
      · have hle : Real.exp (-a * (W x : ℝ)) ≤ 1 :=
          Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (Nat.cast_nonneg _))
        simp only [indicator, ite_eq_left hx]
        exact hle.trans (le_add_of_nonneg_right (Real.exp_nonneg _))
      · simp only [indicator, ite_eq_right hx, zero_add, c]
        apply Real.exp_le_exp.mpr
        have hTW : (T : ℝ) ≤ W x := by exact_mod_cast (by omega : T ≤ W x)
        exact mul_le_mul_of_nonpos_left hTW (neg_nonpos.mpr ha)
    _ = trapPMFEvent p (fun x => W x ≤ T) + c := by
      rw [hsumI.tsum_add hsumC, tsum_mul_right, hmass, one_mul]
      simp only [trapPMFEvent, trapPMFExpectation, indicator]
      congr 1
      apply tsum_congr
      intro x
      by_cases hx : W x ≤ T <;> simp [hx]

end CollatzResearch

#print axioms CollatzResearch.trap_pmf_event_le_exp_of_moment
#print axioms CollatzResearch.trap_pmf_laplace_le_low_count_probability
