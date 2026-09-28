import ClockCutoffBounds

set_option autoImplicit false

open CollatzCanonical.DirichletAbelian

namespace CollatzCanonical.Halving

noncomputable def allLogTerm (w : ℕ → ℝ) (t : ℝ) (q : ℕ) : ℝ :=
  if Real.log (q : ℝ) ≤ t then w q / (q : ℝ) else 0

noncomputable def oddRestriction (w : ℕ → ℝ) (q : ℕ) : ℝ :=
  if q % 2 = 1 then w q else 0

theorem allLogTerm_zero (w : ℕ → ℝ) (t : ℝ) : allLogTerm w t 0 = 0 := by
  simp [allLogTerm]

theorem allLogTerm_summable (w : ℕ → ℝ) (t : ℝ) : Summable (allLogTerm w t) := by
  apply summable_of_ne_finset_zero (s := Finset.range (⌊Real.exp t⌋₊ + 1))
  intro q hq
  by_cases hzero : q = 0
  · rw [hzero, allLogTerm_zero]
  · have hpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hzero
    unfold allLogTerm
    apply if_neg
    intro hlog
    apply hq
    rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (Real.exp_pos t).le,
      ← Real.log_le_iff_le_exp hpos]
    exact hlog

theorem allLogTerm_tsum (w : ℕ → ℝ) (t : ℝ) :
    (∑' q, allLogTerm w t q) = logarithmicCumulative w t := by
  rw [(allLogTerm_summable w t).tsum_eq_zero_add, allLogTerm_zero, zero_add]
  exact ClockSqueeze.logTerm_tsum w t

theorem allLogTerm_even_odd (w : ℕ → ℝ) (t : ℝ) :
    (∑' q, allLogTerm w t (2 * q)) + (∑' q, allLogTerm w t (2 * q + 1)) =
      logarithmicCumulative w t := by
  have he : Summable (fun q => allLogTerm w t (2 * q)) :=
    (allLogTerm_summable w t).comp_injective (by intro a b h; omega)
  have ho : Summable (fun q => allLogTerm w t (2 * q + 1)) :=
    (allLogTerm_summable w t).comp_injective (by
      intro a b h
      change 2 * a + 1 = 2 * b + 1 at h
      omega)
  rw [tsum_even_add_odd he ho, allLogTerm_tsum]

theorem odd_logarithmic_cumulative (w : ℕ → ℝ) (t : ℝ) :
    (∑' q, allLogTerm w t (2 * q + 1)) = logarithmicCumulative (oddRestriction w) t := by
  have h := allLogTerm_even_odd (oddRestriction w) t
  have he (q : ℕ) : allLogTerm (oddRestriction w) t (2 * q) = 0 := by
    simp [allLogTerm, oddRestriction]
  have ho (q : ℕ) : allLogTerm (oddRestriction w) t (2 * q + 1) =
      allLogTerm w t (2 * q + 1) := by
    simp [allLogTerm, oddRestriction]
  simpa only [he, ho, tsum_zero, zero_add] using h

theorem even_logarithmic_term (w : ℕ → ℝ) (t : ℝ) (q : ℕ) :
    allLogTerm w t (2 * q) = (1 / 2 : ℝ) *
      allLogTerm (fun n => w (2 * n)) (t - Real.log 2) q := by
  by_cases hzero : q = 0
  · simp only [hzero, mul_zero, allLogTerm_zero]
  · have hq : (q : ℝ) ≠ 0 := by exact_mod_cast hzero
    have hiff : Real.log (2 * q : ℕ) ≤ t ↔ Real.log (q : ℝ) ≤ t - Real.log 2 := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hq]
      constructor <;> intro h <;> linarith
    change (if Real.log (2 * q : ℕ) ≤ t then w (2 * q) / (2 * q : ℕ) else 0) =
      (1 / 2 : ℝ) * (if Real.log (q : ℝ) ≤ t - Real.log 2 then w (2 * q) / (q : ℝ) else 0)
    by_cases hlog : Real.log (q : ℝ) ≤ t - Real.log 2
    · rw [if_pos (hiff.mpr hlog), if_pos hlog, Nat.cast_mul, Nat.cast_ofNat]
      ring
    · rw [if_neg (mt hiff.mp hlog), if_neg hlog, mul_zero]

theorem logarithmic_cumulative_parity (w : ℕ → ℝ) (t : ℝ) :
    logarithmicCumulative w t = logarithmicCumulative (oddRestriction w) t +
      (1 / 2 : ℝ) * logarithmicCumulative (fun q => w (2 * q)) (t - Real.log 2) := by
  rw [← allLogTerm_even_odd w t, odd_logarithmic_cumulative]
  simp_rw [even_logarithmic_term]
  rw [tsum_mul_left, allLogTerm_tsum, add_comm]

end CollatzCanonical.Halving
