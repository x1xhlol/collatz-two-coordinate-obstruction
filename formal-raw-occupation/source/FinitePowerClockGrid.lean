import ClockGridAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open Filter Topology

namespace CollatzCanonical.RawOccupation
open CollatzClockAudit

noncomputable def finitePowerStep (a : ℝ) (n : ℕ) : ℝ := a / ((n : ℝ) + 1)

noncomputable def finitePowerExponent (a : ℝ) (n i : ℕ) : ℝ :=
  a - finitePowerStep a n * (i : ℝ)

noncomputable def finitePowerClockGrid (a : ℝ) (n : ℕ) (R : ℝ) (i : ℕ) : ℝ :=
  R ^ finitePowerExponent a n i

theorem finitePowerStep_pos {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < finitePowerStep a n := div_pos ha (by positivity)

theorem finitePowerStep_mul (a : ℝ) (n : ℕ) :
    finitePowerStep a n * ((n : ℝ) + 1) = a := by
  unfold finitePowerStep
  exact div_mul_cancel₀ _ (by positivity)

theorem finitePowerStep_le {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    finitePowerStep a n ≤ a := by
  unfold finitePowerStep
  exact div_le_self ha (by have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)

theorem finitePowerExponent_zero (a : ℝ) (n : ℕ) :
    finitePowerExponent a n 0 = a := by simp [finitePowerExponent]

theorem finitePowerExponent_last (a : ℝ) (n : ℕ) :
    finitePowerExponent a n n = finitePowerStep a n := by
  have h := finitePowerStep_mul a n
  unfold finitePowerExponent
  nlinarith

theorem finitePowerExponent_succ (a : ℝ) (n i : ℕ) :
    finitePowerExponent a n (i + 1) = finitePowerExponent a n i - finitePowerStep a n := by
  simp only [finitePowerExponent, Nat.cast_add, Nat.cast_one]
  ring

theorem finitePowerExponent_bounds {a : ℝ} (ha : 0 < a) {n i : ℕ} (hi : i ≤ n) :
    finitePowerStep a n ≤ finitePowerExponent a n i ∧ finitePowerExponent a n i ≤ a := by
  have hd := finitePowerStep_pos ha n
  have hic : (i : ℝ) ≤ n := by exact_mod_cast hi
  have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hmul := finitePowerStep_mul a n
  unfold finitePowerExponent
  constructor <;> nlinarith

/-- The finite spacing can always leave a strict forward-growth margin. -/
theorem exists_finitePowerStep_clock_margin {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ n : ℕ, a + Real.log (3 / 2 : ℝ) * finitePowerStep a n / clockDrift < 1 := by
  have hden : 0 < clockDrift * (1 - a) := mul_pos clockDrift_pos (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.log (3 / 2 : ℝ) * a / (clockDrift * (1 - a)))
  refine ⟨n, ?_⟩
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hnum : Real.log (3 / 2 : ℝ) * a < ((n : ℝ) + 1) * (clockDrift * (1 - a)) :=
    (div_lt_iff₀ hden).mp (hn.trans (by linarith))
  have hsmall : Real.log (3 / 2 : ℝ) * finitePowerStep a n / clockDrift < 1 - a := by
    apply (div_lt_iff₀ clockDrift_pos).mpr
    unfold finitePowerStep
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hn1).mpr
    nlinarith
  linarith

theorem finitePowerClockGrid_zero (a R : ℝ) (n : ℕ) :
    finitePowerClockGrid a n R 0 = R ^ a := by
  rw [finitePowerClockGrid, finitePowerExponent_zero]

theorem finitePowerClockGrid_last (a R : ℝ) (n : ℕ) :
    finitePowerClockGrid a n R n = R ^ finitePowerStep a n := by
  rw [finitePowerClockGrid, finitePowerExponent_last]

theorem finitePowerClockGrid_descending {a R : ℝ} (ha : 0 < a) (hR : 1 ≤ R)
    (n i : ℕ) : finitePowerClockGrid a n R (i + 1) ≤ finitePowerClockGrid a n R i := by
  apply Real.rpow_le_rpow_of_exponent_le hR
  rw [finitePowerExponent_succ]
  linarith [finitePowerStep_pos ha n]

theorem finitePowerClockGrid_bounds {a R : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hR : 1 ≤ R) {n i : ℕ} (hi : i ≤ n) :
    R ^ finitePowerStep a n ≤ finitePowerClockGrid a n R i ∧
      finitePowerClockGrid a n R i ≤ R ^ a ∧ R ^ a ≤ R := by
  obtain ⟨hlo, hhi⟩ := finitePowerExponent_bounds ha hi
  refine ⟨Real.rpow_le_rpow_of_exponent_le hR hlo,
    Real.rpow_le_rpow_of_exponent_le hR hhi, ?_⟩
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR ha1

theorem finitePowerClockGrid_log {a R : ℝ} (hR : 0 < R) (n i : ℕ) :
    Real.log (finitePowerClockGrid a n R i) = finitePowerExponent a n i * Real.log R := by
  rw [finitePowerClockGrid, Real.log_rpow hR]

theorem finitePowerClockGrid_log_gap {a R : ℝ} (hR : 0 < R) (n i : ℕ) :
    Real.log (finitePowerClockGrid a n R i) - Real.log (finitePowerClockGrid a n R (i + 1)) =
      finitePowerStep a n * Real.log R := by
  rw [finitePowerClockGrid_log hR, finitePowerClockGrid_log hR, finitePowerExponent_succ]
  ring

theorem finitePowerClockGrid_log_last {a R : ℝ} (hR : 0 < R) (n : ℕ) :
    Real.log (finitePowerClockGrid a n R n) = finitePowerStep a n * Real.log R := by
  rw [finitePowerClockGrid_log hR, finitePowerExponent_last]

theorem finitePowerClockGrid_min_tendsto {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Tendsto (fun R : ℝ => R ^ finitePowerStep a n) atTop atTop :=
  tendsto_rpow_atTop (finitePowerStep_pos ha n)

theorem finitePowerClockGrid_eventually_above {a : ℝ} (ha : 0 < a) (n : ℕ) (M : ℝ) :
    ∀ᶠ R : ℝ in atTop, ∀ i ≤ n, M ≤ finitePowerClockGrid a n R i := by
  filter_upwards [(finitePowerClockGrid_min_tendsto ha n).eventually_ge_atTop M,
    eventually_ge_atTop (1 : ℝ)] with R hmin hR
  intro i hi
  exact hmin.trans (Real.rpow_le_rpow_of_exponent_le hR (finitePowerExponent_bounds ha hi).1)

/-- The same strict margin supplies every stage and the final bottom stage. -/
theorem finitePowerClockGrid_eventual_budgets {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (n : ℕ) (hmargin : a + Real.log (3 / 2 : ℝ) * finitePowerStep a n / clockDrift < 1)
    (M : ℝ) (B : ℕ) :
    ∀ᶠ R : ℝ in atTop,
      (∀ i < n,
        (3 / 2 : ℝ) ^ ((Real.log (finitePowerClockGrid a n R i) -
          Real.log (finitePowerClockGrid a n R (i + 1))) / clockDrift +
            2 * commonBottomClockError M R B) *
          (finitePowerClockGrid a n R i + 1) ≤ R + 1) ∧
      (3 / 2 : ℝ) ^ (Real.log (finitePowerClockGrid a n R n) / clockDrift +
        commonBottomClockError M R B) * (finitePowerClockGrid a n R n + 1) ≤ R + 1 := by
  filter_upwards [clock_grid_uniform_growth_budget ha.le hmargin M B,
    eventually_ge_atTop (1 : ℝ)] with R hbudget hR
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hE : 0 ≤ commonBottomClockError M R B := by
    have hC := globalClockErrorConstant_pos
    have hlog := Real.log_nonneg hR
    unfold commonBottomClockError
    positivity
  constructor
  · intro i hi
    rw [finitePowerClockGrid_log_gap hR0]
    apply le_trans ?_ hbudget
    exact mul_le_mul_of_nonneg_left
      (add_le_add (finitePowerClockGrid_bounds ha ha1 hR hi.le).2.1 le_rfl)
      (Real.rpow_nonneg (by norm_num) _)
  · rw [finitePowerClockGrid_log_last hR0]
    apply le_trans ?_ hbudget
    apply mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3 / 2) (by linarith))
      (add_le_add (finitePowerClockGrid_bounds ha ha1 hR (le_refl n)).2.1 le_rfl)
    · exact add_nonneg (Real.rpow_nonneg hR0.le _) zero_le_one
    · exact Real.rpow_nonneg (by norm_num) _

/-- All five geometric inputs to the finite occupation theorem hold for an
explicit power grid at every sufficiently large integer cutoff. -/
theorem finitePowerClockGrid_eventual_hypotheses {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (n : ℕ) (hmargin : a + Real.log (3 / 2 : ℝ) * finitePowerStep a n / clockDrift < 1)
    (M : ℝ) (B : ℕ) :
    ∀ᶠ R : ℕ in atTop,
      let x := finitePowerClockGrid a n (R : ℝ)
      (∀ i < n, x (i + 1) ≤ x i) ∧
      (∀ i ≤ n, M ≤ x i) ∧ (∀ i ≤ n, x i ≤ (R : ℝ)) ∧
      (∀ i < n,
        (3 / 2 : ℝ) ^ ((Real.log (x i) - Real.log (x (i + 1))) / clockDrift +
          2 * commonBottomClockError M R B) * (x i + 1) ≤ (R : ℝ) + 1) ∧
      (3 / 2 : ℝ) ^ (Real.log (x n) / clockDrift + commonBottomClockError M R B) *
        (x n + 1) ≤ (R : ℝ) + 1 := by
  have hnat : Tendsto (fun R : ℕ => (R : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually (finitePowerClockGrid_eventual_budgets ha ha1.le n hmargin M B),
    hnat.eventually (finitePowerClockGrid_eventually_above ha n M),
    hnat.eventually (eventually_ge_atTop (1 : ℝ))] with R hbudget hbot hR
  refine ⟨fun i _ => finitePowerClockGrid_descending ha hR n i, hbot, ?_, hbudget⟩
  intro i hi
  exact (finitePowerClockGrid_bounds ha ha1.le hR hi).2.1.trans
    (finitePowerClockGrid_bounds ha ha1.le hR hi).2.2

#print axioms exists_finitePowerStep_clock_margin
#print axioms finitePowerExponent_bounds
#print axioms finitePowerClockGrid_bounds
#print axioms finitePowerClockGrid_log_gap
#print axioms finitePowerClockGrid_eventually_above
#print axioms finitePowerClockGrid_eventual_budgets
#print axioms finitePowerClockGrid_eventual_hypotheses

end CollatzCanonical.RawOccupation
