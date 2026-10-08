import OrbitPackingBootstrap
import Mathlib.Algebra.Order.Floor.Semiring

/-!
The numerical bootstrap for the orbit-packing recurrence.  The threshold
depends only on the exponents, so the final constant is uniform over an
arbitrary family of counting functions satisfying the displayed recurrence.
The combinatorial derivation of that recurrence is not an assumption hidden
in an asymptotic bound: it is stated explicitly in the final theorem.
-/

set_option autoImplicit false

namespace CollatzOrbitPackingPowerRecurrence

noncomputable def packingNext (c : ℝ) (n : ℕ) : ℕ :=
  ⌊3 * (n : ℝ) ^ c⌋₊

noncomputable def binaryLogFloor (n : ℕ) : ℕ :=
  ⌊Real.log (n : ℝ) / Real.log 2⌋₊

noncomputable def errorCoefficient (b : ℝ) : ℝ :=
  2 + 1 / (b * Real.log 2)

theorem floor_log_two_le_power (b : ℝ) (hb : 0 < b) (n : ℕ) :
    (binaryLogFloor n : ℝ) ≤ (n : ℝ) ^ b / (b * Real.log 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (binaryLogFloor n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 :=
      Nat.floor_le (div_nonneg (Real.log_natCast_nonneg n) hlog.le)
    _ ≤ ((n : ℝ) ^ b / b) / Real.log 2 :=
      div_le_div_of_nonneg_right (Real.log_natCast_le_rpow_div n hb) hlog.le
    _ = (n : ℝ) ^ b / (b * Real.log 2) := by rw [div_div]

theorem packing_error_le (b : ℝ) (hb : 0 < b) (n : ℕ) :
    2 * (n : ℝ) ^ b + (binaryLogFloor n : ℝ) ≤
      errorCoefficient b * (n : ℝ) ^ b := by
  calc
    2 * (n : ℝ) ^ b + (binaryLogFloor n : ℝ) ≤
        2 * (n : ℝ) ^ b + (n : ℝ) ^ b / (b * Real.log 2) :=
      add_le_add le_rfl (floor_log_two_le_power b hb n)
    _ = errorCoefficient b * (n : ℝ) ^ b := by
      dsimp [errorCoefficient]
      ring

/-- Sublinear rescaling eventually uses less than half of the power weight.
The proof also supplies a strictly smaller natural induction argument. -/
theorem exists_packing_threshold (b c : ℝ) (hb : 0 < b) (hc : c < 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      packingNext c n < n ∧ (packingNext c n : ℝ) ^ b ≤ (n : ℝ) ^ b / 2 := by
  let d : ℝ := b * (1 - c)
  let q : ℝ := 2 * (3 : ℝ) ^ b
  have hd : 0 < d := mul_pos hb (sub_pos.mpr hc)
  have hq : 0 ≤ q := mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) b)
  obtain ⟨M, hM⟩ := exists_nat_gt (q ^ d⁻¹)
  refine ⟨max M 1, le_max_right _ _, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_right M 1).trans hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hn1)
  have hMn : (M : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (le_max_left M 1).trans hn
  have hqn : q < (n : ℝ) ^ d := by
    have hpow := Real.rpow_lt_rpow (Real.rpow_nonneg hq d⁻¹) (hM.trans_le hMn) hd
    simpa only [Real.rpow_inv_rpow hq hd.ne'] using hpow
  have hraw : (3 * (n : ℝ) ^ c) ^ b ≤ (n : ℝ) ^ b / 2 := by
    have htwice : 2 * (3 * (n : ℝ) ^ c) ^ b ≤ (n : ℝ) ^ b := by
      calc
        2 * (3 * (n : ℝ) ^ c) ^ b = q * (n : ℝ) ^ (c * b) := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hnpos.le c),
            ← Real.rpow_mul hnpos.le]
          dsimp [q]
          ring
        _ ≤ (n : ℝ) ^ d * (n : ℝ) ^ (c * b) :=
          mul_le_mul_of_nonneg_right hqn.le (Real.rpow_nonneg hnpos.le (c * b))
        _ = (n : ℝ) ^ b := by
          rw [← Real.rpow_add hnpos]
          congr 1
          dsimp [d]
          ring
    linarith
  have hhalf : (packingNext c n : ℝ) ^ b ≤ (n : ℝ) ^ b / 2 := by
    apply le_trans (Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hb.le) hraw
    exact Nat.floor_le (mul_nonneg (by norm_num) (Real.rpow_nonneg hnpos.le c))
  refine ⟨?_, hhalf⟩
  have hlt : (packingNext c n : ℝ) ^ b < (n : ℝ) ^ b := by
    have hpos := Real.rpow_pos_of_pos hnpos b
    linarith
  have hltbase := (Real.rpow_lt_rpow_iff (Nat.cast_nonneg (packingNext c n)) hnpos.le hb).mp hlt
  exact_mod_cast hltbase

/-- The numerical recurrence in the packing lemma implies one power bound
uniform over all members of the family.  Only the elementary counting bound
and the recurrence are assumed. -/
theorem uniform_power_bound_of_packing_recurrence
    {ι : Type*} (A : ι → ℕ → ℝ) (b c : ℝ) (hb : 0 < b) (hc : c < 1)
    (hcount : ∀ i n, A i n ≤ (n : ℝ))
    (hrec : ∀ i n, 1 ≤ n →
      A i n ≤ A i (packingNext c n) + 2 * (n : ℝ) ^ b + (binaryLogFloor n : ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i n, A i n ≤ K * (n : ℝ) ^ b := by
  obtain ⟨N, hN, hthreshold⟩ := exists_packing_threshold b c hb hc
  have hC : 0 ≤ errorCoefficient b := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact add_nonneg (by norm_num) (div_nonneg (by norm_num) (mul_nonneg hb.le hlog.le))
  apply CollatzOrbitPackingBootstrap.uniform_power_bound_of_counting_recursion
    A (fun _ n => packingNext c n) N b (errorCoefficient b) hC
  · intro i n _
    exact hcount i n
  · intro _ n hn
    exact (hthreshold n hn).1
  · intro _ n hn
    exact (hthreshold n hn).2
  · intro i n hn
    calc
      A i n ≤ A i (packingNext c n) + 2 * (n : ℝ) ^ b + (binaryLogFloor n : ℝ) :=
        hrec i n (hN.trans hn)
      _ = A i (packingNext c n) +
          (2 * (n : ℝ) ^ b + (binaryLogFloor n : ℝ)) := by ring
      _ ≤ A i (packingNext c n) + errorCoefficient b * (n : ℝ) ^ b :=
        add_le_add le_rfl (packing_error_le b hb n)

#print axioms floor_log_two_le_power
#print axioms exists_packing_threshold
#print axioms uniform_power_bound_of_packing_recurrence

end CollatzOrbitPackingPowerRecurrence
