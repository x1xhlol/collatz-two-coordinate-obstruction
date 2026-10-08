import GeometricClockAccumulation
import Mathlib.Algebra.Order.Field.GeomSum

open Filter
open scoped BigOperators Topology

namespace CollatzClockAudit

theorem geometric_decay_tail {L a c C : ℝ}
    (hL : 0 < L) (ha : 1 < a) (hc : 0 < c) (hC : 0 ≤ C) (i j : ℕ) :
    ∑ r ∈ Finset.Ico i j, C * (L * a ^ r) ^ (-c) ≤
      C / (1 - a ^ (-c)) * (L * a ^ i) ^ (-c) := by
  have ha0 : 0 ≤ a := by linarith
  have hr0 : 0 ≤ a ^ (-c) := Real.rpow_nonneg ha0 _
  have hr1 : a ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg ha (by linarith)
  have hterm (r : ℕ) : (L * a ^ r) ^ (-c) = L ^ (-c) * (a ^ (-c)) ^ r := by
    rw [Real.mul_rpow hL.le (pow_nonneg ha0 _), ← Real.rpow_pow_comm ha0]
  simp_rw [hterm, ← mul_assoc]
  rw [← Finset.mul_sum]
  calc
    (C * L ^ (-c)) * ∑ r ∈ Finset.Ico i j, (a ^ (-c)) ^ r ≤
        (C * L ^ (-c)) * ((a ^ (-c)) ^ i / (1 - a ^ (-c))) :=
      mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1)
        (mul_nonneg hC (Real.rpow_nonneg hL.le _))
    _ = C / (1 - a ^ (-c)) * L ^ (-c) * (a ^ (-c)) ^ i := by ring

theorem geometric_decay_interval_le_bottom {L a c C : ℝ}
    (hL : 0 < L) (ha : 1 < a) (hc : 0 < c) (hC : 0 ≤ C) (i j : ℕ) :
    ∑ r ∈ Finset.Ico i j, C * (L * a ^ r) ^ (-c) ≤
      C / (1 - a ^ (-c)) * L ^ (-c) := by
  have hr1 : a ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg ha (by linarith)
  have hcoef : 0 ≤ C / (1 - a ^ (-c)) := div_nonneg hC (by linarith)
  apply (geometric_decay_tail hL ha hc hC i j).trans
  apply mul_le_mul_of_nonneg_left _ hcoef
  apply Real.rpow_le_rpow_of_nonpos hL _ (by linarith)
  have hpow : 1 ≤ a ^ i := one_le_pow₀ ha.le
  nlinarith

/-- The top local error plus all lower local errors and transferred
marginal errors have a bound independent of the number of stages. -/
theorem geometric_total_stage_budget {L a c d C C' : ℝ}
    (hL : 1 ≤ L) (ha : 1 < a) (hc : 0 < c) (hd : 0 < d)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (j : ℕ) :
    C * (L * a ^ j) ^ (-d) +
      (∑ i ∈ Finset.Ico 1 (j + 1),
        (C * (L * a ^ (i - 1)) ^ (-d) + C' * (L * a ^ i) ^ (-c))) ≤
      (C / (1 - a ^ (-d)) + C' / (1 - a ^ (-c))) * L ^ (-(min c d)) := by
  have hLp : 0 < L := by linarith
  have hrd : a ^ (-d) < 1 := Real.rpow_lt_one_of_one_lt_of_neg ha (by linarith)
  have hrc : a ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg ha (by linarith)
  have hCd : 0 ≤ C / (1 - a ^ (-d)) := div_nonneg hC (by linarith)
  have hCc : 0 ≤ C' / (1 - a ^ (-c)) := div_nonneg hC' (by linarith)
  have hshift : (∑ i ∈ Finset.Ico 1 (j + 1), C * (L * a ^ (i - 1)) ^ (-d)) =
      ∑ i ∈ Finset.Ico 0 j, C * (L * a ^ i) ^ (-d) := by
    simpa using Finset.sum_Ico_add_right_sub_eq
      (f := fun i => C * (L * a ^ i) ^ (-d)) 0 j 1
  have hlocal : C * (L * a ^ j) ^ (-d) +
      (∑ i ∈ Finset.Ico 1 (j + 1), C * (L * a ^ (i - 1)) ^ (-d)) ≤
      C / (1 - a ^ (-d)) * L ^ (-d) := by
    rw [hshift, add_comm, ← Finset.sum_Ico_succ_top (Nat.zero_le j)]
    exact geometric_decay_interval_le_bottom hLp ha hd hC 0 (j + 1)
  have htransfer := geometric_decay_interval_le_bottom hLp ha hc hC' 1 (j + 1)
  have hdpow : L ^ (-d) ≤ L ^ (-(min c d)) :=
    Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg (min_le_right c d))
  have hcpow : L ^ (-c) ≤ L ^ (-(min c d)) :=
    Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg (min_le_left c d))
  rw [Finset.sum_add_distrib]
  have hh := add_le_add hlocal htransfer
  have hb := add_le_add (mul_le_mul_of_nonneg_left hdpow hCd)
    (mul_le_mul_of_nonneg_left hcpow hCc)
  calc
    C * (L * a ^ j) ^ (-d) +
        ((∑ i ∈ Finset.Ico 1 (j + 1), C * (L * a ^ (i - 1)) ^ (-d)) +
          ∑ i ∈ Finset.Ico 1 (j + 1), C' * (L * a ^ i) ^ (-c)) ≤
        C / (1 - a ^ (-d)) * L ^ (-d) +
          C' / (1 - a ^ (-c)) * L ^ (-c) := by simpa only [add_assoc] using hh
    _ ≤ C / (1 - a ^ (-d)) * L ^ (-(min c d)) +
        C' / (1 - a ^ (-c)) * L ^ (-(min c d)) := hb
    _ = (C / (1 - a ^ (-d)) + C' / (1 - a ^ (-c))) * L ^ (-(min c d)) := by ring

theorem geometric_stage_budget {L a c d C C' : ℝ}
    (hL : 1 ≤ L) (ha : 1 < a) (hc : 0 < c) (hd : 0 < d)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (j : ℕ) :
    (∑ i ∈ Finset.Ico 1 (j + 1),
      (C * (L * a ^ (i - 1)) ^ (-d) + C' * (L * a ^ i) ^ (-c))) ≤
      (C / (1 - a ^ (-d)) + C' / (1 - a ^ (-c))) * L ^ (-(min c d)) := by
  have htop : 0 ≤ C * (L * a ^ j) ^ (-d) := by positivity
  exact (le_add_of_nonneg_left htop).trans (geometric_total_stage_budget hL ha hc hd hC hC' j)

/-- Direct form with the finite marginal-transfer tail still present at
each stage. Its geometric summation contributes a second denominator. -/
theorem geometric_nested_stage_budget {L a c d C V : ℝ}
    (hL : 1 ≤ L) (ha : 1 < a) (hc : 0 < c) (hd : 0 < d)
    (hC : 0 ≤ C) (hV : 0 ≤ V) (j : ℕ) :
    C * (L * a ^ j) ^ (-d) +
      (∑ i ∈ Finset.Ico 1 (j + 1),
        (C * (L * a ^ (i - 1)) ^ (-d) +
          ∑ r ∈ Finset.Ico i j, V * (L * a ^ r) ^ (-c))) ≤
      (C / (1 - a ^ (-d)) + V / (1 - a ^ (-c)) ^ 2) * L ^ (-(min c d)) := by
  have hLp : 0 < L := by linarith
  have hrc : a ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg ha (by linarith)
  have hV' : 0 ≤ V / (1 - a ^ (-c)) := div_nonneg hV (by linarith)
  have hsum : (∑ i ∈ Finset.Ico 1 (j + 1),
      (C * (L * a ^ (i - 1)) ^ (-d) +
        ∑ r ∈ Finset.Ico i j, V * (L * a ^ r) ^ (-c))) ≤
      ∑ i ∈ Finset.Ico 1 (j + 1),
        (C * (L * a ^ (i - 1)) ^ (-d) +
          (V / (1 - a ^ (-c))) * (L * a ^ i) ^ (-c)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact add_le_add le_rfl (geometric_decay_tail hLp ha hc hV i j)
  have hb := geometric_total_stage_budget hL ha hc hd hC hV' j
  have hh := (add_le_add le_rfl hsum).trans hb
  simpa only [div_div, ← pow_two] using hh

theorem geometric_probability_budget_tendsto_zero {a c d C C' : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    Tendsto (fun L : ℝ =>
      (C / (1 - a ^ (-d)) + C' / (1 - a ^ (-c))) * L ^ (-(min c d)))
      atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (lt_min hc hd)).const_mul
    (C / (1 - a ^ (-d)) + C' / (1 - a ^ (-c)))
  simpa only [mul_zero] using h

end CollatzClockAudit
