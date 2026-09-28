import FiniteSyracuseSeries

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

def twoInverse (k : ℕ) : ZMod (3 ^ k) := ↑(powerTwoUnit k 1)⁻¹

theorem powerTwoUnit_pow (k A : ℕ) :
    powerTwoUnit k A = (powerTwoUnit k 1) ^ A := by
  apply Units.ext
  simp [powerTwoUnit_coe]

theorem inverse_powerTwoUnit (k A : ℕ) :
    (↑((powerTwoUnit k A)⁻¹) : ZMod (3 ^ k)) = twoInverse k ^ A := by
  rw [powerTwoUnit_pow, ← inv_pow]
  simp [twoInverse]

theorem truncatedSeries_closedForm (k : ℕ) (as : List ℕ) :
    truncatedSeries k as =
      ∑ j ∈ Finset.range as.length,
        (3 : ZMod (3 ^ k)) ^ j * twoInverse k ^ (as.take (j + 1)).sum := by
  induction as with
  | nil => simp [truncatedSeries]
  | cons a as ih =>
    rw [truncatedSeries, inverse_powerTwoUnit, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.take_succ_cons, List.sum_cons, List.take_zero, List.sum_nil,
      add_zero, pow_zero, one_mul]
    rw [mul_add, mul_one]
    have he :
        (∑ j ∈ Finset.range as.length,
          (3 : ZMod (3 ^ k)) ^ (j + 1) * twoInverse k ^ (a + (as.take (j + 1)).sum)) =
        twoInverse k ^ a * (3 *
          ∑ j ∈ Finset.range as.length,
            (3 : ZMod (3 ^ k)) ^ j * twoInverse k ^ (as.take (j + 1)).sum) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ, pow_add]
      ring
    rw [he]
    ring

theorem wordResidue_closedForm (k : ℕ) (w : GeometricWord k) :
    wordResidue k w =
      ∑ j ∈ Finset.range k,
        (3 : ZMod (3 ^ k)) ^ j *
          twoInverse k ^ ((wordList k w).take (j + 1)).sum := by
  rw [wordResidue_eq_truncatedSeries, truncatedSeries_closedForm, wordList_length]

#print axioms truncatedSeries_closedForm
#print axioms wordResidue_closedForm

end CollatzCylinderPacking.Arithmetic
