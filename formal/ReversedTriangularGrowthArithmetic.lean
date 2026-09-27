import ReversedPositivePrefixArithmetic

namespace CollatzResearch.TriangularGrowthArithmetic

theorem window_growth_contradiction (c K M lam L : ℝ)
    (hc : 0 < c) (hL : 1 ≤ L)
    (hgap : L ^ 2 < lam ^ 3)
    (hbound : ∀ n : ℕ,
      c * lam ^ (3 * n) ≤ (K + (2 * (n + 1) : ℕ) * M) * L ^ (2 * (n + 1))) :
    False := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hL2 : 0 < L ^ 2 := pow_pos hL0 2
  have hratio : 1 < lam ^ 3 / L ^ 2 := (one_lt_div hL2).mpr hgap
  apply PositivePrefixArithmetic.exponential_not_bounded_by_affine c
    (lam ^ 3 / L ^ 2) (L ^ 2 * (K + 2 * M)) (2 * L ^ 2 * M) hc hratio
  intro n
  have hn := hbound n
  have hpow : L ^ (2 * (n + 1)) = (L ^ 2) ^ n * L ^ 2 := by
    rw [pow_mul, pow_succ]
  rw [pow_mul, hpow] at hn
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hn
  rw [div_pow, ← mul_div_assoc]
  apply (div_le_iff₀ (pow_pos hL2 n)).mpr
  nlinarith only [hn]

end CollatzResearch.TriangularGrowthArithmetic

#print axioms CollatzResearch.TriangularGrowthArithmetic.window_growth_contradiction
