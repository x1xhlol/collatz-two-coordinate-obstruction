import CollatzReversedRealStationaryObstruction

namespace CollatzResearch.RealOrderedPowers

open Matrix CollatzCertificate RealAffine RealMixedGrowth RealStationaryProfile

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ordered_scaled_row_power_le (X Y : Mat ι) (r : Vec ι) (q : ℝ)
    (hX : EntrywiseLE 0 X) (hY : EntrywiseLE 0 Y) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (hXY : EntrywiseLE (X * Y) (Y * X))
    (hrow : r ᵥ* Y ≤ q • (r ᵥ* X)) (n : ℕ) :
    r ᵥ* Y ^ n ≤ q ^ n • (r ᵥ* X ^ n) := by
  have hp : ∀ k : ℕ, (r ᵥ* X ^ k) ᵥ* Y ≤ q • (r ᵥ* X ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simpa using hrow
    | succ k ih =>
      calc
        (r ᵥ* X ^ (k + 1)) ᵥ* Y = (r ᵥ* X ^ k) ᵥ* (X * Y) := by
          rw [pow_succ, ← vecMul_vecMul, vecMul_vecMul (r ᵥ* X ^ k)]
        _ ≤ (r ᵥ* X ^ k) ᵥ* (Y * X) :=
          rowMul_mono_matrix (rowMul_pow_nonneg hr hX k) hXY
        _ = ((r ᵥ* X ^ k) ᵥ* Y) ᵥ* X := (vecMul_vecMul _ _ _).symm
        _ ≤ (q • (r ᵥ* X ^ (k + 1))) ᵥ* X := rowMul_mono_row ih hX
        _ = q • (r ᵥ* X ^ (k + 1 + 1)) := by
          rw [smul_vecMul, vecMul_vecMul, ← pow_succ]
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      r ᵥ* Y ^ (n + 1) = (r ᵥ* Y ^ n) ᵥ* Y := by rw [pow_succ, vecMul_vecMul]
      _ ≤ (q ^ n • (r ᵥ* X ^ n)) ᵥ* Y := rowMul_mono_row ih hY
      _ = q ^ n • ((r ᵥ* X ^ n) ᵥ* Y) := smul_vecMul _ _ _
      _ ≤ q ^ n • (q • (r ᵥ* X ^ (n + 1))) := by
        intro i
        exact mul_le_mul_of_nonneg_left (hp n i) (pow_nonneg hq n)
      _ = q ^ (n + 1) • (r ᵥ* X ^ (n + 1)) := by rw [smul_smul, ← pow_succ]

theorem ordered_stationary_profile_row_zero
    (X Y : Mat ι) (r v : Vec ι) (q K : ℝ) (N : ℕ)
    (hX : EntrywiseLE 0 X) (hY : EntrywiseLE 0 Y)
    (hr : 0 ≤ r) (hv : ∀ i, 0 < v i)
    (hq : 0 ≤ q) (hq1 : q < 1) (hK : 0 ≤ K)
    (hXY : EntrywiseLE (X * Y) (Y * X)) (hrow : r ᵥ* Y ≤ q • (r ᵥ* X))
    (hbound : ∀ n : ℕ, (r ᵥ* X ^ n) ⬝ᵥ v ≤ K)
    (hstationary : ∀ n : ℕ, N ≤ n → Y ^ n *ᵥ v = Y ^ N *ᵥ v) :
    r ᵥ* Y ^ N = 0 := by
  have hv0 : 0 ≤ v := fun i => (hv i).le
  have hnonnegative := rowMul_pow_nonneg hr hY N
  have hzero : (r ᵥ* Y ^ N) ⬝ᵥ v = 0 := by
    apply le_antisymm _ (dotProduct_nonneg_of_nonneg hnonnegative hv0)
    by_contra hn
    have hp : 0 < (r ᵥ* Y ^ N) ⬝ᵥ v := lt_of_not_ge hn
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
      (div_pos hp (show 0 < K + 1 by linarith)) hq1
    have hpow : q ^ (m + N) ≤ q ^ m := by
      rw [pow_add]
      exact mul_le_of_le_one_right (pow_nonneg hq m) (pow_le_one₀ hq hq1.le)
    have hi := dotProduct_le_dotProduct_of_nonneg_right
      (ordered_scaled_row_power_le X Y r q hX hY hr hq hXY hrow (m + N)) hv0
    rw [smul_dotProduct] at hi
    change (r ᵥ* Y ^ (m + N)) ⬝ᵥ v ≤
      q ^ (m + N) * ((r ᵥ* X ^ (m + N)) ⬝ᵥ v) at hi
    have hsame : (r ᵥ* Y ^ (m + N)) ⬝ᵥ v = (r ᵥ* Y ^ N) ⬝ᵥ v := by
      rw [← dotProduct_mulVec, hstationary (m + N) (by omega), dotProduct_mulVec]
    rw [hsame] at hi
    have hsmall := (lt_div_iff₀ (show 0 < K + 1 by linarith)).mp hm
    have hb := mul_le_mul_of_nonneg_left (hbound (m + N)) (pow_nonneg hq (m + N))
    have hc := mul_le_mul_of_nonneg_right hpow hK
    nlinarith [pow_nonneg hq m]
  funext i
  have hi : (r ᵥ* Y ^ N) i * v i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hnonnegative j) (hv0 j))).mp hzero i (Finset.mem_univ i)
  exact (mul_eq_zero.mp hi).resolve_right (ne_of_gt (hv i))

end CollatzResearch.RealOrderedPowers

#print axioms CollatzResearch.RealOrderedPowers.ordered_scaled_row_power_le
#print axioms CollatzResearch.RealOrderedPowers.ordered_stationary_profile_row_zero
