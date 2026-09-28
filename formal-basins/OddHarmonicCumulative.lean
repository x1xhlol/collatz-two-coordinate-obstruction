import LogarithmicCumulativeIncrements

set_option autoImplicit false

open scoped BigOperators

namespace CollatzCanonical.DirichletAbelian

noncomputable def oddLogarithmicCumulative (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  logarithmicCumulative (fun n => if n % 2 = 1 then w n else 0) t

theorem odd_harmonic_prefix (N : ℕ) :
    (∑ n ∈ Finset.range N, (if (n + 1) % 2 = 1 then (1 : ℝ) else 0) / (n + 1 : ℕ)) =
      (∑ n ∈ Finset.range N, (1 : ℝ) / (n + 1 : ℕ)) -
        (1 / 2 : ℝ) * ∑ n ∈ Finset.range (N / 2), (1 : ℝ) / (n + 1 : ℕ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one (N + 1) with heven | hodd
    · rw [if_neg (by omega)]
      have hquot : (N + 1) / 2 = N / 2 + 1 := by omega
      rw [hquot, Finset.sum_range_succ]
      have hN : N + 1 = 2 * (N / 2 + 1) := by omega
      have hreal : (N : ℝ) + 1 = 2 * ((N / 2 : ℕ) + 1 : ℝ) := by exact_mod_cast hN
      simp only [Nat.cast_add, Nat.cast_one, zero_div, add_zero]
      rw [hreal]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    · rw [if_pos hodd]
      have hquot : (N + 1) / 2 = N / 2 := by omega
      rw [hquot]
      ring

theorem oddLogarithmicCumulative_one_eq (t : ℝ) :
    oddLogarithmicCumulative (fun _ => 1) t =
      logarithmicCumulative (fun _ => 1) t -
        (1 / 2 : ℝ) * logarithmicCumulative (fun _ => 1) (t - Real.log 2) := by
  have he : Real.exp (t - Real.log 2) = Real.exp t / 2 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hf : ⌊Real.exp t⌋₊ / 2 = ⌊Real.exp t / 2⌋₊ := by
    simpa using Nat.mul_cast_floor_div_cancel (n := 2) (by decide) (Real.exp t / 2)
  unfold oddLogarithmicCumulative logarithmicCumulative
  rw [odd_harmonic_prefix, he, ← hf]

/-- The odd harmonic primitive has slope one half and a uniformly bounded
error. This is sufficient for a power-saving moving-window normalization. -/
theorem oddLogarithmicCumulative_one_bound {t : ℝ} (ht : Real.log 2 ≤ t) :
    |oddLogarithmicCumulative (fun _ => 1) t - t / 2| ≤ 2 := by
  rw [oddLogarithmicCumulative_one_eq]
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have ht0 : 0 ≤ t := hlog0.trans ht
  have htl : 0 ≤ t - Real.log 2 := sub_nonneg.mpr ht
  have hlo := logarithmicCumulative_one_lower t
  have hlo' := logarithmicCumulative_one_lower (t - Real.log 2)
  have hhi := logarithmicCumulative_linear_bound (w := fun _ => 1)
    (fun _ => by norm_num) (fun _ => le_rfl) ht0
  have hhi' := logarithmicCumulative_linear_bound (w := fun _ => 1)
    (fun _ => by norm_num) (fun _ => le_rfl) htl
  rw [abs_of_nonneg (logarithmicCumulative_nonneg (fun _ => by norm_num) _)] at hhi hhi'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem odd_harmonic_window_mass_bound {s t : ℝ}
    (hs : Real.log 2 ≤ s) (ht : Real.log 2 ≤ t) :
    |(oddLogarithmicCumulative (fun _ => 1) t - oddLogarithmicCumulative (fun _ => 1) s) -
      (t - s) / 2| ≤ 4 := by
  have h := abs_sub_le
    (oddLogarithmicCumulative (fun _ => 1) t - t / 2) 0
    (oddLogarithmicCumulative (fun _ => 1) s - s / 2)
  have hs' := oddLogarithmicCumulative_one_bound hs
  have ht' := oddLogarithmicCumulative_one_bound ht
  simp only [sub_zero, zero_sub, abs_neg] at h
  have he : (oddLogarithmicCumulative (fun _ => 1) t - t / 2) -
      (oddLogarithmicCumulative (fun _ => 1) s - s / 2) =
      (oddLogarithmicCumulative (fun _ => 1) t - oddLogarithmicCumulative (fun _ => 1) s) -
      (t - s) / 2 := by ring
  rw [he] at h
  linarith

#print axioms odd_harmonic_prefix
#print axioms oddLogarithmicCumulative_one_eq
#print axioms odd_harmonic_window_mass_bound

end CollatzCanonical.DirichletAbelian
