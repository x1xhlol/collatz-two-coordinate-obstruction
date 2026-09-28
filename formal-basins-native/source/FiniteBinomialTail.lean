import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Finite weighted-binomial and entropy bounds. The integer-threshold weighted
sum proof generalizes the proof of `Collatz.choose_tail_bound` in M. Sharpe's
`Collatz/Terras.lean`, commit ec8174b567d5cab4960024782210b5f5db02bd3a of
https://github.com/msharpe248/collatz . The pinned source bytes were checked
against the retained audit manifest. The real-threshold Chernoff and entropy
proofs below are checked here directly from mathlib.

MIT License

Copyright (c) 2026 M. Sharpe

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/

open scoped BigOperators

namespace CollatzCanonical.BinomialTail

/-- The finite binomial moment-generating polynomial, over the real numbers. -/
theorem binomial_weighted_sum (k : ℕ) (z : ℝ) :
    ∑ j ∈ Finset.range (k + 1), z ^ j * (k.choose j : ℝ) = (1 + z) ^ k := by
  have hb := add_pow z (1 : ℝ) k
  simpa only [one_pow, mul_one, add_comm z 1] using hb.symm

/-- Finite exponential Markov bound with an integer threshold and arbitrary weight. -/
theorem weighted_binomial_tail (k m : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    z ^ m * ∑ j ∈ (Finset.range (k + 1)).filter (fun j => m ≤ j), (k.choose j : ℝ)
      ≤ (1 + z) ^ k := by
  calc
    _ = ∑ j ∈ (Finset.range (k + 1)).filter (fun j => m ≤ j),
        z ^ m * (k.choose j : ℝ) := by rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ (Finset.range (k + 1)).filter (fun j => m ≤ j),
        z ^ j * (k.choose j : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hz (Finset.mem_filter.mp hj).2) (Nat.cast_nonneg _)
    _ ≤ ∑ j ∈ Finset.range (k + 1), z ^ j * (k.choose j : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => mul_nonneg (pow_nonneg (by linarith : 0 ≤ z) _) (Nat.cast_nonneg _))
    _ = _ := binomial_weighted_sum k z

/-- Chernoff's finite binomial upper tail, with a real threshold and free tilt parameter. -/
theorem chernoff_binomial_tail (k : ℕ) (ρ t : ℝ) (ht : 0 ≤ t) :
    (∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => ρ * k < (j : ℝ)), (k.choose j : ℝ)) ≤
      Real.exp ((k : ℝ) * Real.log (1 + Real.exp t) - t * (ρ * k)) := by
  have hweighted : Real.exp (t * (ρ * k)) *
      (∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => ρ * k < (j : ℝ)), (k.choose j : ℝ))
        ≤ (1 + Real.exp t) ^ k := by
    calc
      _ = ∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => ρ * k < (j : ℝ)),
          Real.exp (t * (ρ * k)) * (k.choose j : ℝ) := by rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => ρ * k < (j : ℝ)),
          Real.exp t ^ j * (k.choose j : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have hh := (Finset.mem_filter.mp hj).2.le
        nlinarith
      _ ≤ ∑ j ∈ Finset.range (k + 1), Real.exp t ^ j * (k.choose j : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j _ _ => mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (Nat.cast_nonneg _))
      _ = _ := binomial_weighted_sum k (Real.exp t)
  rw [Real.exp_sub, Real.exp_nat_mul,
    Real.exp_log (by positivity : 0 < 1 + Real.exp t)]
  apply (le_div_iff₀ (Real.exp_pos (t * (ρ * k)))).mpr
  simpa only [mul_comm] using hweighted

/-- The entropy upper-tail bound, including the endpoint rho = 1/2. -/
theorem entropy_binomial_tail (k : ℕ) (ρ : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) :
    (∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => ρ * k < (j : ℝ)), (k.choose j : ℝ)) ≤
      Real.exp ((k : ℝ) * (-ρ * Real.log ρ - (1 - ρ) * Real.log (1 - ρ))) := by
  have hρ0 : 0 < ρ := by linarith
  have hcomp : 0 < 1 - ρ := sub_pos.mpr hρ1
  let t := Real.log (ρ / (1 - ρ))
  have ht : 0 ≤ t := Real.log_nonneg ((le_div_iff₀ hcomp).mpr (by linarith))
  have hexp : Real.exp t = ρ / (1 - ρ) := Real.exp_log (div_pos hρ0 hcomp)
  have hsum : 1 + Real.exp t = (1 - ρ)⁻¹ := by
    rw [hexp]
    field_simp
    ring
  have hlog : Real.log (1 + Real.exp t) = -Real.log (1 - ρ) := by rw [hsum, Real.log_inv]
  have htlog : t = Real.log ρ - Real.log (1 - ρ) := Real.log_div hρ0.ne' hcomp.ne'
  have hb := chernoff_binomial_tail k ρ t ht
  rw [hlog, htlog] at hb
  have he : (k : ℝ) * -Real.log (1 - ρ) -
      (Real.log ρ - Real.log (1 - ρ)) * (ρ * k) =
      (k : ℝ) * (-ρ * Real.log ρ - (1 - ρ) * Real.log (1 - ρ)) := by ring
  rw [he] at hb
  exact hb

/-- Base-two form of the finite binomial entropy bound used in trajectory packing. -/
theorem binary_entropy_binomial_tail (k : ℕ) (ρ : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) :
    (∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => ρ * k < (j : ℝ)), (k.choose j : ℝ)) ≤
      (2 : ℝ) ^ ((k : ℝ) *
        ((-ρ * Real.log ρ - (1 - ρ) * Real.log (1 - ρ)) / Real.log 2)) := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he : Real.log 2 * ((k : ℝ) *
      ((-ρ * Real.log ρ - (1 - ρ) * Real.log (1 - ρ)) / Real.log 2)) =
      (k : ℝ) * (-ρ * Real.log ρ - (1 - ρ) * Real.log (1 - ρ)) := by
    field_simp
  rw [he]
  exact entropy_binomial_tail k ρ hρ hρ1

end CollatzCanonical.BinomialTail
