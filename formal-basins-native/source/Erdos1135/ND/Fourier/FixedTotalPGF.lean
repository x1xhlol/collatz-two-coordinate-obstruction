import Erdos1135.ND.Fourier.FixedTotalConcentration
import Mathlib.Data.Nat.Choose.Sum

/-!
# Fixed-Total Bars Probability Generating Function

This leaf collapses the checked fixed-bars factorial moments into the finite
probability-generating-function bound consumed by the T3 count tail.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

private theorem ndBarsPrefixCount_le_q
    {n L : ℕ} (B : NDFixedTotalBars n L) (q : ℕ) :
    ndBarsPrefixCount B.1 q ≤ q := by
  unfold ndBarsPrefixCount
  calc
    (B.1.filter fun b : Fin (L - 1) => (b : ℕ) < q).card ≤
        ((Finset.univ : Finset (Fin (L - 1))).filter
          fun b : Fin (L - 1) => (b : ℕ) < q).card := by
      exact Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.subset_univ B.1))
    _ = min (L - 1) q := by
      simpa using (Fin.card_filter_val_lt (n := L - 1) (m := q))
    _ ≤ q := min_le_right _ _

private theorem ndPow_eq_sum_sub_one_choose
    (H q : ℕ) (hHq : H ≤ q) (x : ℝ) :
    x ^ H =
      ∑ r ∈ Finset.range (q + 1),
        (x - 1) ^ r * (Nat.choose H r : ℝ) := by
  calc
    x ^ H = ((x - 1) + 1) ^ H := by rw [sub_add_cancel]
    _ = ∑ r ∈ Finset.range (H + 1),
          (x - 1) ^ r * (Nat.choose H r : ℝ) := by
      simpa only [one_pow, mul_one] using
        (_root_.add_pow (x - 1) (1 : ℝ) H)
    _ = ∑ r ∈ Finset.range (q + 1),
          (x - 1) ^ r * (Nat.choose H r : ℝ) := by
      apply Finset.sum_subset
        (Finset.range_mono (Nat.add_le_add_right hHq 1))
      intro r _hrq hrH
      have hHr : H < r := by
        by_contra h
        apply hrH
        rw [Finset.mem_range]
        omega
      simp [Nat.choose_eq_zero_of_lt hHr]

/-- The actual fixed-bars PGF is bounded coefficientwise by the corresponding
with-replacement binomial PGF. -/
theorem ndFixedTotalBarsPMF_pgf_le
    (n L q : ℕ) (hn : 0 < n) (hL : n ≤ L)
    (hL1 : 1 < L) (hqL : q ≤ L - 1)
    (x : ℝ) (hx : 1 ≤ x) :
    Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
      (fun B => x ^ ndBarsPrefixCount B.1 q) ≤
      (1 + (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ)) *
        (x - 1)) ^ q := by
  classical
  let p : ℝ :=
    (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ))
  change
    Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
        (fun B => x ^ ndBarsPrefixCount B.1 q) ≤
      (1 + p * (x - 1)) ^ q
  have hmoment (r : ℕ) (hrq : r ≤ q) :
      Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
          (fun B => (Nat.choose (ndBarsPrefixCount B.1 q) r : ℝ)) ≤
        (Nat.choose q r : ℝ) * p ^ r := by
    exact ndFixedTotalBarsPMF_expectation_choose_prefixCount_le
      n L q r hn hL hL1 hqL hrq
  calc
    Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
        (fun B => x ^ ndBarsPrefixCount B.1 q) =
        ∑ B : NDFixedTotalBars n L,
          (ndFixedTotalBarsPMF n L hn hL B).toReal *
            (∑ r ∈ Finset.range (q + 1),
              (x - 1) ^ r *
                (Nat.choose (ndBarsPrefixCount B.1 q) r : ℝ)) := by
      unfold Tao.pmfExpectation
      apply Finset.sum_congr rfl
      intro B _hB
      change
        (ndFixedTotalBarsPMF n L hn hL B).toReal *
            x ^ ndBarsPrefixCount B.1 q = _
      rw [ndPow_eq_sum_sub_one_choose
        (ndBarsPrefixCount B.1 q) q (ndBarsPrefixCount_le_q B q) x]
    _ = ∑ B : NDFixedTotalBars n L,
          ∑ r ∈ Finset.range (q + 1),
            (ndFixedTotalBarsPMF n L hn hL B).toReal *
              ((x - 1) ^ r *
                (Nat.choose (ndBarsPrefixCount B.1 q) r : ℝ)) := by
      apply Finset.sum_congr rfl
      intro B _hB
      rw [Finset.mul_sum]
    _ = ∑ r ∈ Finset.range (q + 1),
          ∑ B : NDFixedTotalBars n L,
            (ndFixedTotalBarsPMF n L hn hL B).toReal *
              ((x - 1) ^ r *
                (Nat.choose (ndBarsPrefixCount B.1 q) r : ℝ)) := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ Finset.range (q + 1),
          (x - 1) ^ r *
            Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
              (fun B =>
                (Nat.choose (ndBarsPrefixCount B.1 q) r : ℝ)) := by
      unfold Tao.pmfExpectation
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _hB
      change
        (ndFixedTotalBarsPMF n L hn hL B).toReal *
            ((x - 1) ^ r *
              (Nat.choose (ndBarsPrefixCount B.1 q) r : ℝ)) =
          (x - 1) ^ r *
            ((ndFixedTotalBarsPMF n L hn hL B).toReal *
              (Nat.choose (ndBarsPrefixCount B.1 q) r : ℝ))
      ac_rfl
    _ ≤ ∑ r ∈ Finset.range (q + 1),
          (x - 1) ^ r * ((Nat.choose q r : ℝ) * p ^ r) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrq : r ≤ q := by
        have := Finset.mem_range.mp hr
        omega
      exact mul_le_mul_of_nonneg_left (hmoment r hrq)
        (pow_nonneg (sub_nonneg.mpr hx) r)
    _ = ∑ r ∈ Finset.range (q + 1),
          (p * (x - 1)) ^ r * (1 : ℝ) ^ (q - r) *
            (Nat.choose q r : ℝ) := by
      apply Finset.sum_congr rfl
      intro r _hr
      simp only [mul_pow, one_pow, mul_one]
      ac_rfl
    _ = (p * (x - 1) + 1) ^ q := by
      exact (_root_.add_pow (p * (x - 1)) (1 : ℝ) q).symm
    _ = (1 + p * (x - 1)) ^ q := by
      rw [add_comm (p * (x - 1)) 1]

end ND
end Erdos1135
