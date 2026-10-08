import FiniteCylinderResidueLaw

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- The recursively grouped truncated Syracuse series, evaluated modulo 3^k.
For exponents a_1,...,a_r this is the sum of
3^(j-1) 2^(-(a_1+...+a_j)), j=1,...,r. -/
def truncatedSeries (k : ℕ) : List ℕ → ZMod (3 ^ k)
  | [] => 0
  | a :: as => ↑(powerTwoUnit k a)⁻¹ * (1 + 3 * truncatedSeries k as)

theorem powerTwoUnit_coe (k A : ℕ) :
    (powerTwoUnit k A : ZMod (3 ^ k)) = (2 : ZMod (3 ^ k)) ^ A := by
  simp [powerTwoUnit]

theorem truncatedSeries_cleared (k : ℕ) (as : List ℕ) :
    (2 : ZMod (3 ^ k)) ^ as.sum * truncatedSeries k as =
      (affineNumerator as : ZMod (3 ^ k)) := by
  induction as with
  | nil => simp [truncatedSeries, affineNumerator]
  | cons a as ih =>
    have hc : (2 : ZMod (3 ^ k)) ^ a * ↑((powerTwoUnit k a)⁻¹) = 1 := by
      rw [← powerTwoUnit_coe]
      exact Units.mul_inv (powerTwoUnit k a)
    simp only [List.sum_cons, truncatedSeries, affineNumerator, Nat.cast_add, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat]
    calc
      (2 : ZMod (3 ^ k)) ^ (a + as.sum) *
          (↑(powerTwoUnit k a)⁻¹ * (1 + 3 * truncatedSeries k as)) =
          2 ^ as.sum * ((2 ^ a * ↑(powerTwoUnit k a)⁻¹) *
            (1 + 3 * truncatedSeries k as)) := by rw [pow_add]; ring
      _ = 2 ^ as.sum + 3 * (2 ^ as.sum * truncatedSeries k as) := by rw [hc]; ring
      _ = _ := by rw [ih]

theorem wordResidue_eq_truncatedSeries (k : ℕ) (w : GeometricWord k) :
    wordResidue k w = truncatedSeries k (wordList k w) := by
  unfold wordResidue
  rw [Units.inv_mul_eq_iff_eq_mul, powerTwoUnit_coe]
  rw [← wordList_sum]
  exact (truncatedSeries_cleared k (wordList k w)).symm

/-- The concrete finite Syracuse series law has the same mass as the
arithmetically admissible inverse-word law. -/
theorem arithmetic_mass_eq_series_law {k N : ℕ} (hN : 0 < N) :
    arithmeticMass k N =
      ∑' w : GeometricWord k,
        if (N : ZMod (3 ^ k)) = truncatedSeries k (wordList k w)
        then (1 / 2 : ℝ) ^ wordLength k w else 0 := by
  classical
  rw [arithmetic_mass_eq_residueMass hN]
  unfold residueMass
  apply tsum_congr
  intro w
  simp only [residueTerm, wordResidue_eq_truncatedSeries]

#print axioms truncatedSeries_cleared
#print axioms wordResidue_eq_truncatedSeries
#print axioms arithmetic_mass_eq_series_law

end CollatzCylinderPacking.Arithmetic
