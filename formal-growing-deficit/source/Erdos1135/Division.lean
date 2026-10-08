import Erdos1135.Parity

/-!
# Natural Division Lemmas

Facts about the natural-number division operations that occur in even Collatz branches.
-/

namespace Erdos1135

lemma div_two_mul_two_of_even {n : ℕ} (hn : Even n) :
    n / 2 * 2 = n :=
  Nat.div_mul_cancel (even_iff_two_dvd.mp hn)

lemma two_mul_div_two_of_even {n : ℕ} (hn : Even n) :
    2 * (n / 2) = n := by
  simpa [Nat.mul_comm] using div_two_mul_two_of_even hn

lemma two_mul_div_two_add_mod_two (n : ℕ) :
    2 * (n / 2) + n % 2 = n := by
  simpa [Nat.mul_comm] using Nat.div_add_mod n 2

lemma div_two_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    0 < n / 2 :=
  Nat.div_pos hn (by norm_num)

lemma div_two_lt_self_of_one_lt {n : ℕ} (hn : 1 < n) :
    n / 2 < n :=
  Nat.div_lt_self (by omega) (by norm_num)

lemma div_two_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) :
    n / 2 = 0 :=
  Nat.div_eq_of_lt hn

end Erdos1135
