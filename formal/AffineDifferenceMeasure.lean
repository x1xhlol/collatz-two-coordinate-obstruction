import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace CollatzAffineSynchronization

def differenceWeight (d : ℕ) (z : ℤ) : ℕ :=
  if z = 0 then 3 ^ d else z.natAbs

theorem weight_half (d : ℕ) (z z' : ℤ) (hz : z ≠ 0) (h : 2 * z' = z) :
    differenceWeight d z' < differenceWeight d z := by
  have hz' : z' ≠ 0 := by omega
  have habs : 2 * z'.natAbs = z.natAbs := by
    have h' := congrArg Int.natAbs h
    simpa [Int.natAbs_mul] using h'
  have hpos : 0 < z'.natAbs := Int.natAbs_pos.mpr hz'
  have hlt : z'.natAbs < z.natAbs := by omega
  simpa [differenceWeight, hz, hz'] using hlt

theorem weight_zero (d : ℕ) (z' : ℤ) (hd : 0 < d)
    (h : 2 * z' = 1 - (3 : ℤ) ^ d) :
    differenceWeight d z' < differenceWeight d 0 := by
  have hpow : 1 < (3 : ℤ) ^ d := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hd)
  have hzneg : z' < 0 := by omega
  have habs : (z'.natAbs : ℤ) = -z' := by
    rw [Int.natCast_natAbs, abs_of_neg hzneg]
  have hlt : (z'.natAbs : ℤ) < (3 : ℤ) ^ d := by omega
  have hnat : z'.natAbs < (3 : ℕ) ^ d := by exact_mod_cast hlt
  simpa [differenceWeight, ne_of_lt hzneg] using hnat

#print axioms weight_half
#print axioms weight_zero

end CollatzAffineSynchronization
