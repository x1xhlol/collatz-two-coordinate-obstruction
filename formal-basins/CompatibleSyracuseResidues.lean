import FiniteSyracuseSeriesClosedForm

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

def reduceResidue (m n : ℕ) (h : m ≤ n) : ZMod (3 ^ n) →+* ZMod (3 ^ m) :=
  ZMod.castHom (pow_dvd_pow 3 h) (ZMod (3 ^ m))

theorem reduce_powerTwoUnit (m n A : ℕ) (h : m ≤ n) :
    Units.map (reduceResidue m n h).toMonoidHom (powerTwoUnit n A) = powerTwoUnit m A := by
  apply Units.ext
  change reduceResidue m n h (powerTwoUnit n A : ZMod (3 ^ n)) =
    (powerTwoUnit m A : ZMod (3 ^ m))
  rw [powerTwoUnit_coe, powerTwoUnit_coe, map_pow, map_ofNat]

theorem reduce_inversePowerTwoUnit (m n A : ℕ) (h : m ≤ n) :
    reduceResidue m n h (↑((powerTwoUnit n A)⁻¹)) =
      (↑((powerTwoUnit m A)⁻¹) : ZMod (3 ^ m)) := by
  change (↑(Units.map (reduceResidue m n h).toMonoidHom ((powerTwoUnit n A)⁻¹)) : ZMod (3 ^ m)) = _
  rw [map_inv, reduce_powerTwoUnit]

theorem reduce_truncatedSeries (m n : ℕ) (h : m ≤ n) (as : List ℕ) :
    reduceResidue m n h (truncatedSeries n as) = truncatedSeries m as := by
  induction as with
  | nil => simp [truncatedSeries]
  | cons a as ih =>
    simp only [truncatedSeries, map_mul, map_add, map_one, map_ofNat,
      reduce_inversePowerTwoUnit, ih]

theorem truncatedSeries_drop_last (k : ℕ) (as : List ℕ) (hlen : as.length = k + 1) :
    truncatedSeries k as = truncatedSeries k (as.take k) := by
  have hzero : (3 : ZMod (3 ^ k)) ^ k = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (ZMod.natCast_self (3 ^ k))
  rw [truncatedSeries_closedForm, hlen, Finset.sum_range_succ, hzero, zero_mul, add_zero]
  rw [truncatedSeries_closedForm, List.length_take, hlen, Nat.min_eq_left (by omega)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j + 1 ≤ k := by have := Finset.mem_range.mp hj; omega
  rw [List.take_take, Nat.min_eq_left hjk]

def sequenceWord : (k : ℕ) → (ℕ → ℕ) → GeometricWord k
  | 0, _ => ()
  | k + 1, f => (f 0, sequenceWord k (fun i => f (i + 1)))

theorem sequenceWord_take (k : ℕ) (f : ℕ → ℕ) :
    (wordList (k + 1) (sequenceWord (k + 1) f)).take k =
      wordList k (sequenceWord k f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    change (f 0 + 1) :: (wordList (k + 1) (sequenceWord (k + 1) (fun i => f (i + 1)))).take k =
      (f 0 + 1) :: wordList k (sequenceWord k (fun i => f (i + 1)))
    rw [ih]

/-- Consecutive finite Syracuse residues are compatible under reduction. -/
theorem sequence_residue_compatible (k : ℕ) (f : ℕ → ℕ) :
    reduceResidue k (k + 1) (by omega)
      (wordResidue (k + 1) (sequenceWord (k + 1) f)) =
      wordResidue k (sequenceWord k f) := by
  rw [wordResidue_eq_truncatedSeries, reduce_truncatedSeries,
    truncatedSeries_drop_last k _ (wordList_length _ _), sequenceWord_take,
    wordResidue_eq_truncatedSeries]

#print axioms reduce_truncatedSeries
#print axioms sequence_residue_compatible

end CollatzCylinderPacking.Arithmetic
