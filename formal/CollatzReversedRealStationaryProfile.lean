import CollatzReversedRealMixedGrowth

namespace CollatzResearch.RealStationaryProfile

open Matrix CollatzCertificate RealAffine RealMixedGrowth

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_pow_nonnegative (M : Mat ι) (hM : EntrywiseLE 0 M) (n : ℕ) :
    EntrywiseLE 0 (M ^ n) := by
  induction n with
  | zero =>
    intro i j
    simp only [pow_zero, Matrix.one_apply]
    split <;> norm_num
  | succ n ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (ih i k) (hM k j))

theorem scaled_row_power_le (X Y : Mat ι) (r : Vec ι) (q : ℝ)
    (hX : EntrywiseLE 0 X) (hY : EntrywiseLE 0 Y) (hq : 0 ≤ q)
    (hXY : Commute X Y) (hrow : r ᵥ* Y ≤ q • (r ᵥ* X)) (n : ℕ) :
    r ᵥ* Y ^ n ≤ q ^ n • (r ᵥ* X ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      r ᵥ* Y ^ (n + 1) = (r ᵥ* Y) ᵥ* Y ^ n := by
        rw [vecMul_vecMul, pow_succ']
      _ ≤ (q • (r ᵥ* X)) ᵥ* Y ^ n :=
        rowMul_mono_row hrow (matrix_pow_nonnegative Y hY n)
      _ = q • ((r ᵥ* Y ^ n) ᵥ* X) := by
        rw [smul_vecMul, vecMul_vecMul, (hXY.pow_right n).eq, ← vecMul_vecMul]
      _ ≤ q • ((q ^ n • (r ᵥ* X ^ n)) ᵥ* X) := by
        intro i
        exact mul_le_mul_of_nonneg_left (rowMul_mono_row ih hX i) hq
      _ = q ^ (n + 1) • (r ᵥ* X ^ (n + 1)) := by
        rw [smul_vecMul, smul_smul, vecMul_vecMul, ← pow_succ, pow_succ' q n]

theorem stationary_profile_row_zero
    (X Y : Mat ι) (r v : Vec ι) (q K : ℝ) (N : ℕ)
    (hX : EntrywiseLE 0 X) (hY : EntrywiseLE 0 Y)
    (hr : 0 ≤ r) (hv : ∀ i, 0 < v i)
    (hq : 0 ≤ q) (hq1 : q < 1) (hK : 0 ≤ K)
    (hXY : Commute X Y) (hrow : r ᵥ* Y ≤ q • (r ᵥ* X))
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
      exact mul_le_of_le_one_right (pow_nonneg hq m)
        (pow_le_one₀ hq hq1.le)
    have hi := dotProduct_le_dotProduct_of_nonneg_right
      (scaled_row_power_le X Y r q hX hY hq hXY hrow (m + N)) hv0
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

end CollatzResearch.RealStationaryProfile

#print axioms CollatzResearch.RealStationaryProfile.matrix_pow_nonnegative
#print axioms CollatzResearch.RealStationaryProfile.scaled_row_power_le
#print axioms CollatzResearch.RealStationaryProfile.stationary_profile_row_zero
