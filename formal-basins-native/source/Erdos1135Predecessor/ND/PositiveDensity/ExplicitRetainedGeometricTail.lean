/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitPolynomialGeometricTail
import Mathlib.Data.Nat.Log

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

theorem polynomialGeometric_tail_le_retained (d N : ℕ) {r s : ℝ}
    (hr0 : 0 ≤ r) (hs0 : 0 ≤ s) (hs1 : s < 1) (hrs : r ≤ s ^ 2) :
    (∑' j : ℕ, ((N + j + 1 : ℕ) : ℝ) ^ d * r ^ (N + j)) ≤
      (d.factorial : ℝ) * (1 / (1 - s)) ^ (d + 1) * s ^ N := by
  have hr1 : r < 1 := hrs.trans_lt (by nlinarith)
  have hsr := (polynomialGeometric_moment_le d hr0 hr1).1
  obtain ⟨hss, hmoment⟩ := polynomialGeometric_moment_le d hs0 hs1
  have htr : Summable (fun j : ℕ => ((N + j + 1 : ℕ) : ℝ) ^ d * r ^ (N + j)) := by
    simpa only [Nat.add_comm N] using (summable_nat_add_iff N).mpr hsr
  have hts : Summable (fun j : ℕ => ((N + j + 1 : ℕ) : ℝ) ^ d * s ^ (N + j)) := by
    simpa only [Nat.add_comm N] using (summable_nat_add_iff N).mpr hss
  have hfull : (∑' j : ℕ, ((N + j + 1 : ℕ) : ℝ) ^ d * s ^ (N + j)) ≤
      ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ d * s ^ j := by
    have he := hss.sum_add_tsum_nat_add N
    have hnonneg : 0 ≤ ∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ d * s ^ j :=
      Finset.sum_nonneg fun j _ => by positivity
    simpa only [Nat.add_comm N] using (show
      (∑' j : ℕ, ((j + N + 1 : ℕ) : ℝ) ^ d * s ^ (j + N)) ≤ _ by linarith)
  have hterm (j : ℕ) :
      ((N + j + 1 : ℕ) : ℝ) ^ d * r ^ (N + j) ≤
        s ^ N * (((N + j + 1 : ℕ) : ℝ) ^ d * s ^ (N + j)) := by
    have hpow : r ^ (N + j) ≤ s ^ (N + j) * s ^ (N + j) := by
      calc
        _ ≤ (s * s) ^ (N + j) :=
          pow_le_pow_left₀ hr0 (by simpa only [pow_two] using hrs) _
        _ = _ := mul_pow _ _ _
    have hdecay : s ^ (N + j) ≤ s ^ N := by
      rw [pow_add]
      exact mul_le_of_le_one_right (pow_nonneg hs0 _) (pow_le_one₀ hs0 hs1.le)
    have h := hpow.trans (mul_le_mul_of_nonneg_right hdecay (pow_nonneg hs0 _))
    have hh := mul_le_mul_of_nonneg_left h
      (show 0 ≤ ((N + j + 1 : ℕ) : ℝ) ^ d by positivity)
    convert hh using 1 <;> ring
  calc
    _ ≤ ∑' j : ℕ, s ^ N * (((N + j + 1 : ℕ) : ℝ) ^ d * s ^ (N + j)) :=
      htr.tsum_le_tsum hterm (hts.mul_left _)
    _ = s ^ N * (∑' j : ℕ, ((N + j + 1 : ℕ) : ℝ) ^ d * s ^ (N + j)) :=
      tsum_mul_left
    _ ≤ s ^ N * ((d.factorial : ℝ) / (1 - s) ^ (d + 1)) :=
      mul_le_mul_of_nonneg_left (hfull.trans hmoment) (pow_nonneg hs0 _)
    _ = _ := by simp only [div_pow]; ring

theorem polynomialGeometric_tail_le_slow_ratio (d N : ℕ) :
    (∑' j : ℕ, ((N + j + 1 : ℕ) : ℝ) ^ d * (9999 / 10000 : ℝ) ^ (N + j)) ≤
      (d.factorial : ℝ) * 20000 ^ (d + 1) * (19999 / 20000 : ℝ) ^ N := by
  have h := polynomialGeometric_tail_le_retained d N
    (r := (9999 / 10000 : ℝ)) (s := (19999 / 20000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem polynomialGeometric_term_le_slow_ratio (d N : ℕ) :
    ((N + 1 : ℕ) : ℝ) ^ d * (9999 / 10000 : ℝ) ^ N ≤
      (d.factorial : ℝ) * 20000 ^ (d + 1) * (19999 / 20000 : ℝ) ^ N := by
  have hs := (polynomialGeometric_moment_le d (r := (9999 / 10000 : ℝ))
    (by norm_num) (by norm_num)).1
  have ht : Summable (fun j : ℕ => ((N + j + 1 : ℕ) : ℝ) ^ d *
      (9999 / 10000 : ℝ) ^ (N + j)) := by
    simpa only [Nat.add_comm N] using (summable_nat_add_iff N).mpr hs
  apply le_trans (b := ∑' j : ℕ, ((N + j + 1 : ℕ) : ℝ) ^ d *
    (9999 / 10000 : ℝ) ^ (N + j)) _ (polynomialGeometric_tail_le_slow_ratio d N)
  simpa only [Nat.add_zero] using ht.le_tsum 0 (fun j _ => by positivity)

theorem slowRatio_block_le_half : (19999 / 20000 : ℝ) ^ 20000 ≤ 1 / 2 := by
  have hB : (2 : ℝ) ≤ (20001 / 20000 : ℝ) ^ 20000 := by
    calc
      _ = 1 + (20000 : ℝ) * (1 / 20000 : ℝ) := by norm_num
      _ ≤ (1 + (1 / 20000 : ℝ)) ^ 20000 := one_add_mul_le_pow (by norm_num) _
      _ = _ := by congr 1; norm_num
  calc
    _ ≤ (20000 / 20001 : ℝ) ^ 20000 :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = 1 / ((20001 / 20000 : ℝ) ^ 20000) := by
      rw [← one_div_pow]
      congr 1
      norm_num
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hB

theorem slowRatio_pow_le_dyadic (t n : ℕ) (hn : 20000 * t ≤ n) :
    (19999 / 20000 : ℝ) ^ n ≤ 1 / (2 : ℝ) ^ t := by
  have he : n = 20000 * t + (n - 20000 * t) := by omega
  calc
    _ = (19999 / 20000 : ℝ) ^ (20000 * t) *
        (19999 / 20000 : ℝ) ^ (n - 20000 * t) := by rw [← pow_add, ← he]
    _ ≤ (19999 / 20000 : ℝ) ^ (20000 * t) :=
      mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
    _ = ((19999 / 20000 : ℝ) ^ 20000) ^ t := pow_mul _ _ _
    _ ≤ (1 / 2 : ℝ) ^ t := pow_le_pow_left₀ (by positivity) slowRatio_block_le_half t
    _ = _ := one_div_pow _ _

theorem coefficient_mul_slowRatio_le (F k n : ℕ)
    (hn : 20000 * (Nat.clog 2 F + k) ≤ n) :
    (F : ℝ) * (19999 / 20000 : ℝ) ^ n ≤ 1 / (2 : ℝ) ^ k := by
  have hF : (F : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 F := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) F
  calc
    _ ≤ (F : ℝ) * (1 / (2 : ℝ) ^ (Nat.clog 2 F + k)) :=
      mul_le_mul_of_nonneg_left (slowRatio_pow_le_dyadic _ n hn) (Nat.cast_nonneg F)
    _ ≤ (2 : ℝ) ^ Nat.clog 2 F * (1 / (2 : ℝ) ^ (Nat.clog 2 F + k)) :=
      mul_le_mul_of_nonneg_right hF (by positivity)
    _ = _ := by rw [pow_add]; field_simp

end

end Erdos1135Predecessor.ND.PositiveDensity
