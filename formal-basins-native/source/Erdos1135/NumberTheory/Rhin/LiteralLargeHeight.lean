import Erdos1135.NumberTheory.Rhin.LargeHeight
import Erdos1135.NumberTheory.Rhin.LcmGrowth

/-!
# The literal Rhin large-height certificate

This module is the single consumer joining the independent literal-row and
table-free range-LCM producers.  It packages the three square-shift rows with
group-index growth `72^2`, decay `(717/1000)^2`, and the derived integer
contraction exponent `13`.  It does not use the older exponent-`11`
square-scale helper.
-/

namespace Erdos1135
namespace NumberTheory
namespace Rhin

noncomputable section

private theorem literalRhinSquareRows_error_le
    (K n : ℕ)
    (hLCM : rangeLCM (literalRhinSquareScale n) ≤
      K * 3 ^ literalRhinSquareScale n)
    (j : Fin 3) :
    3 *
          |((literalRhinSquareRows n j).denominator : ℝ) * logTwoDivThree -
            ((literalRhinSquareRows n j).numerator23 : ℝ)| +
        2 *
          |((literalRhinSquareRows n j).denominator : ℝ) * logFourDivThree -
            ((literalRhinSquareRows n j).numerator34 : ℝ)| ≤
      (2592000 : ℝ) * K * ((12 : ℝ) ^ 7) ^ 2 *
        (((717 : ℝ) / 1000) ^ 2) ^ n := by
  let C : ℝ := 144 * (((12 : ℝ) ^ 7 * 20) ^ 2)
  let d : ℝ := ((717 : ℝ) / 1000) ^ 2
  have hRate :
      (3 : ℝ) ^ (2 * n + 2) * ((239 : ℝ) / 1000) ^ (2 * n) =
        9 * d ^ n := by
    have hBase :
        (3 : ℝ) ^ 2 * ((239 : ℝ) / 1000) ^ 2 =
          ((717 : ℝ) / 1000) ^ 2 := by
      norm_num
    dsimp only [d]
    rw [pow_add, pow_mul, pow_mul]
    calc
      ((3 : ℝ) ^ 2) ^ n * 3 ^ 2 *
            (((239 : ℝ) / 1000) ^ 2) ^ n =
          9 * (((3 : ℝ) ^ 2) ^ n *
            (((239 : ℝ) / 1000) ^ 2) ^ n) := by ring
      _ = 9 *
          (((3 : ℝ) ^ 2 * ((239 : ℝ) / 1000) ^ 2) ^ n) := by
        rw [mul_pow]
      _ = 9 * (((717 : ℝ) / 1000) ^ 2) ^ n := by rw [hBase]
  have hLCMReal :
      (rangeLCM (literalRhinSquareScale n) : ℝ) ≤
        (K : ℝ) * 3 ^ literalRhinSquareScale n := by
    exact_mod_cast hLCM
  have hScaledMoment (M : ℝ)
      (hM : |M| ≤ C * ((239 : ℝ) / 1000) ^ (2 * n)) :
      |(rangeLCM (literalRhinSquareScale n) : ℝ) * M| ≤
        9 * (K : ℝ) * C * d ^ n := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      (rangeLCM (literalRhinSquareScale n) : ℝ) * |M| ≤
          ((K : ℝ) * 3 ^ literalRhinSquareScale n) *
            (C * ((239 : ℝ) / 1000) ^ (2 * n)) := by
        exact mul_le_mul hLCMReal hM (abs_nonneg _) (by positivity)
      _ = (K : ℝ) * C *
          ((3 : ℝ) ^ (2 * n + 2) *
            ((239 : ℝ) / 1000) ^ (2 * n)) := by
        rw [literalRhinSquareScale]
        ring
      _ = 9 * (K : ℝ) * C * d ^ n := by rw [hRate]; ring
  have h23Raw := hScaledMoment (literalRhinSquareMoment23 n j) (by
    dsimp only [C]
    exact literalRhinSquareMoment23_abs_le n j)
  have h34Raw := hScaledMoment (literalRhinSquareMoment34 n j) (by
    dsimp only [C]
    exact literalRhinSquareMoment34_abs_le n j)
  have h23 :
      |literalRhinSquareScaledMoment23 n j| ≤
        9 * (K : ℝ) * C * d ^ n := by
    simpa only [literalRhinSquareScaledMoment23] using h23Raw
  have h34 :
      |literalRhinSquareScaledMoment34 n j| ≤
        9 * (K : ℝ) * C * d ^ n := by
    simpa only [literalRhinSquareScaledMoment34] using h34Raw
  have hRows := literalRhinSquareRows_residuals_as_scaledMoments n j
  have h23Abs :
      |((literalRhinSquareRows n j).denominator : ℝ) * logTwoDivThree -
          ((literalRhinSquareRows n j).numerator23 : ℝ)| =
        |literalRhinSquareScaledMoment23 n j| := by
    rw [show
      ((literalRhinSquareRows n j).denominator : ℝ) * logTwoDivThree -
          ((literalRhinSquareRows n j).numerator23 : ℝ) =
        -(((literalRhinSquareRows n j).numerator23 : ℝ) -
          ((literalRhinSquareRows n j).denominator : ℝ) *
            logTwoDivThree) by ring,
      hRows.1, abs_neg]
  have h34Abs :
      |((literalRhinSquareRows n j).denominator : ℝ) * logFourDivThree -
          ((literalRhinSquareRows n j).numerator34 : ℝ)| =
        |literalRhinSquareScaledMoment34 n j| := by
    rw [show
      ((literalRhinSquareRows n j).denominator : ℝ) * logFourDivThree -
          ((literalRhinSquareRows n j).numerator34 : ℝ) =
        -(((literalRhinSquareRows n j).numerator34 : ℝ) -
          ((literalRhinSquareRows n j).denominator : ℝ) *
            logFourDivThree) by ring,
      hRows.2, neg_neg]
  rw [h23Abs, h34Abs]
  calc
    3 * |literalRhinSquareScaledMoment23 n j| +
        2 * |literalRhinSquareScaledMoment34 n j| ≤
      3 * (9 * (K : ℝ) * C * d ^ n) +
        2 * (9 * (K : ℝ) * C * d ^ n) := by gcongr
    _ = (2592000 : ℝ) * K * ((12 : ℝ) ^ 7) ^ 2 *
        (((717 : ℝ) / 1000) ^ 2) ^ n := by
      dsimp only [C, d]
      ring

/-- The literal three-row geometric certificate obtained from one global
base-three range-LCM prefactor. -/
def literalRhinGroupedCertificate
    (K : ℕ) (hK : 0 < K)
    (hLCM : ∀ N : ℕ, rangeLCM N ≤ K * 3 ^ N) :
    GroupedGeometricSimultaneousLogApproximationCertificate where
  rows := literalRhinSquareRows
  growth := (72 : ℝ) ^ 2
  decay := ((717 : ℝ) / 1000) ^ 2
  denominatorFactor :=
    (1296 : ℝ) * K * ((12 : ℝ) ^ 7) ^ 2
  errorFactor :=
    (2592000 : ℝ) * K * ((12 : ℝ) ^ 7) ^ 2
  start := 8
  exponent := 13
  one_le_growth := by norm_num
  decay_pos := by norm_num
  decay_lt_one := by norm_num
  denominatorFactor_pos := by positivity
  errorFactor_pos := by positivity
  exponent_le := by norm_num
  growth_decay := by norm_num [pow_succ]
  denominator_le := by
    intro n _hn j
    have hDenominator :=
      literalRhinSquareRows_denominator_natAbs_le K n
        (hLCM (literalRhinSquareScale n)) j
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast hDenominator
  error_le := by
    intro n _hn j
    exact literalRhinSquareRows_error_le K n
      (hLCM (literalRhinSquareScale n)) j
  determinant_ne := by
    intro n hn
    exact literalRhinSquareRows_det_ne_zero n hn

/-- The literal p. 162 polynomial and the table-free LCM producer construct
the frozen large-height statement required by G8a. -/
theorem literalRhinLargeHeightBound : LargeHeightBound := by
  obtain ⟨K, hK, hLCM⟩ := exists_rangeLCM_le_const_mul_three_pow
  exact largeHeightBound_of_groupedGeometricSimultaneousLogApproximation
    (literalRhinGroupedCertificate K hK hLCM)

end

end Rhin
end NumberTheory
end Erdos1135
