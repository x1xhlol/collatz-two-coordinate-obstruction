/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Division

/-!
# Powers Of Two And Two-Adic Bookkeeping

This module is for powers of two, factors of two, and valuation-style interfaces.
-/

namespace Erdos1135SecondScale

lemma two_pow_pos (k : ℕ) :
    0 < 2 ^ k :=
  pow_pos (by norm_num) k

lemma two_pow_ne_zero (k : ℕ) :
    2 ^ k ≠ 0 :=
  ne_of_gt (two_pow_pos k)

lemma two_pow_succ_mul_two (k : ℕ) :
    2 ^ (k + 1) = 2 ^ k * 2 :=
  Nat.pow_succ 2 k

lemma two_pow_succ_two_mul (k : ℕ) :
    2 ^ (k + 1) = 2 * 2 ^ k := by
  simpa [Nat.succ_eq_add_one] using (@Nat.pow_succ' 2 k)

lemma two_dvd_two_pow_succ (k : ℕ) :
    2 ∣ 2 ^ (k + 1) := by
  refine ⟨2 ^ k, ?_⟩
  exact two_pow_succ_two_mul k

lemma two_pow_dvd_two_pow_of_le {a b : ℕ} (h : a ≤ b) :
    2 ^ a ∣ 2 ^ b :=
  Nat.pow_dvd_pow 2 h

lemma div_mul_cancel_of_two_pow_dvd {k n : ℕ} (h : 2 ^ k ∣ n) :
    n / 2 ^ k * 2 ^ k = n :=
  Nat.div_mul_cancel h

lemma mul_div_cancel_of_two_pow_dvd {k n : ℕ} (h : 2 ^ k ∣ n) :
    2 ^ k * (n / 2 ^ k) = n := by
  simpa [Nat.mul_comm] using div_mul_cancel_of_two_pow_dvd h

end Erdos1135SecondScale
