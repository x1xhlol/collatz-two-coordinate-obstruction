import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace CollatzCanonical.Scales

theorem no_equal_positive_powers (m n : ℕ) (hm : 0 < m) :
    (1001 / 1000 : ℝ) ^ m ≠ (2001 / 2000 : ℝ) ^ n := by
  intro h
  have hcross : (1001 : ℝ) ^ m * 2000 ^ n = 2001 ^ n * 1000 ^ m := by
    rw [div_pow, div_pow] at h
    exact (div_eq_div_iff (by positivity) (by positivity)).mp h
  have hnat : (1001 : ℕ) ^ m * 2000 ^ n = 2001 ^ n * 1000 ^ m := by
    exact_mod_cast hcross
  have hd : 11 ∣ (1001 : ℕ) ^ m := (by norm_num : 11 ∣ (1001 : ℕ)).pow (by omega)
  have hr : 11 ∣ (2001 : ℕ) ^ n * 1000 ^ m := by
    rw [← hnat]
    exact dvd_mul_of_dvd_left hd _
  have hp : Nat.Prime 11 := by decide
  rcases hp.dvd_mul.mp hr with hleft | hright
  · have hf := hp.dvd_of_dvd_pow hleft
    norm_num at hf
  · have hf := hp.dvd_of_dvd_pow hright
    norm_num at hf

theorem logarithms_incommensurable :
    Irrational (Real.log (1001 / 1000 : ℝ) / Real.log (2001 / 2000 : ℝ)) := by
  intro h
  obtain ⟨q, hq⟩ := h
  have ha : 0 < Real.log (1001 / 1000 : ℝ) := Real.log_pos (by norm_num)
  have hb : 0 < Real.log (2001 / 2000 : ℝ) := Real.log_pos (by norm_num)
  have hqpos : (0 : ℚ) < q := by
    have hreal : (0 : ℝ) < q := by rw [hq]; exact div_pos ha hb
    exact_mod_cast hreal
  have hn : 0 < q.num := Rat.num_pos.mpr hqpos
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hnum : (q.num.natAbs : ℝ) = q.num := by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg hn.le)
  have hrat : (q : ℝ) = (q.num.natAbs : ℝ) / q.den := by
    rw [Rat.cast_def, hnum]
  have hlogs : (q.den : ℝ) * Real.log (1001 / 1000 : ℝ) =
      (q.num.natAbs : ℝ) * Real.log (2001 / 2000 : ℝ) := by
    rw [hrat] at hq
    have hc := (div_eq_div_iff hd.ne' hb.ne').mp hq
    nlinarith
  have heq : Real.log ((1001 / 1000 : ℝ) ^ q.den) =
      Real.log ((2001 / 2000 : ℝ) ^ q.num.natAbs) := by
    simpa only [Real.log_pow] using hlogs
  have hpowers : (1001 / 1000 : ℝ) ^ q.den = (2001 / 2000 : ℝ) ^ q.num.natAbs :=
    Real.log_injOn_pos
      (show 0 < (1001 / 1000 : ℝ) ^ q.den by positivity)
      (show 0 < (2001 / 2000 : ℝ) ^ q.num.natAbs by positivity) heq
  exact no_equal_positive_powers q.den q.num.natAbs q.pos hpowers

#print axioms no_equal_positive_powers
#print axioms logarithms_incommensurable

end CollatzCanonical.Scales
