import Erdos1135.Tao.Probability.Geom2HighWeight
import Erdos1135.Tao.Section5.PassScheduleFacts

/-!
# Section 5 High Geom(2) Weight Scalar

This leaf combines the neutral high-weight tail with the sharper scheduled numerator bound
`3 ^ n <= B ^ (1/6)`.  It closes the repaired high contribution needed before assembling the
coefficient bound in Tao's Lemma 5.3.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- Real upper bound inherited from the floor defining the common step-back time. -/
theorem taoSection5M0_cast_le_log_div_hundred_thousand
    {B : ℕ} (hB : 1 ≤ B) :
    (taoSection5M0 B : ℝ) ≤ Real.log B / 100000 := by
  rw [taoSection5M0_eq_floor_log]
  exact Nat.floor_le (by
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hB)) (by norm_num))

/-- The discrete inequality `3^6 <= 2^10` sharpens the scheduled numerator to a one-sixth
power of the threshold. -/
theorem three_pow_le_threshold_rpow_one_sixth_of_mul_le_log
    {B n : ℕ} (hB : 1 ≤ B) (hlog : 10 * n ≤ Nat.log 2 B) :
    (3 : ℝ) ^ n ≤ (B : ℝ) ^ (1 / 6 : ℝ) := by
  have hpowB : 2 ^ (10 * n) ≤ B :=
    Nat.pow_le_of_le_log (Nat.ne_of_gt hB) hlog
  have hpowerNat : ((3 ^ n) ^ 6 : ℕ) ≤ 2 ^ (10 * n) := by
    calc
      ((3 ^ n) ^ 6 : ℕ) = (3 ^ 6) ^ n := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (2 ^ 10) ^ n :=
        Nat.pow_le_pow_left (by norm_num : (3 : ℕ) ^ 6 ≤ 2 ^ 10) n
      _ = 2 ^ (10 * n) := by rw [pow_mul]
  have hpowerReal : ((3 : ℝ) ^ n) ^ 6 ≤ (B : ℝ) := by
    exact_mod_cast hpowerNat.trans hpowB
  have hrpow : ((3 : ℝ) ^ n) ^ (6 : ℝ) ≤ (B : ℝ) := by
    calc
      ((3 : ℝ) ^ n) ^ (6 : ℝ) = ((3 : ℝ) ^ n) ^ (6 : ℕ) :=
        Real.rpow_natCast ((3 : ℝ) ^ n) 6
      _ ≤ (B : ℝ) := hpowerReal
  simpa [one_div] using
    (Real.le_rpow_inv_iff_of_pos
      (by positivity : 0 ≤ (3 : ℝ) ^ n)
      (by positivity : 0 ≤ (B : ℝ))
      (by norm_num : 0 < (6 : ℝ))).2 hrpow

theorem three_pow_le_threshold_rpow_one_sixth_of_le_n0
    {B n : ℕ} (hB : 1 ≤ B) (hn : n ≤ taoSection5N0 B) :
    (3 : ℝ) ^ n ≤ (B : ℝ) ^ (1 / 6 : ℝ) := by
  apply three_pow_le_threshold_rpow_one_sixth_of_mul_le_log hB
  unfold taoSection5N0 at hn
  omega

/-- Exact exponent arithmetic used to absorb the high-weight probability. -/
theorem three_pow_mul_threshold_rpow_neg_34999_le_one
    {B n : ℕ} (hB : 1 ≤ B) (hn : n ≤ taoSection5N0 B) :
    (3 : ℝ) ^ n * (B : ℝ) ^ (-(34999 / 200000 : ℝ)) ≤
      (B : ℝ) ^ (-(4997 / 600000 : ℝ)) ∧
    (B : ℝ) ^ (-(4997 / 600000 : ℝ)) ≤ 1 := by
  constructor
  · calc
      (3 : ℝ) ^ n * (B : ℝ) ^ (-(34999 / 200000 : ℝ)) ≤
          (B : ℝ) ^ (1 / 6 : ℝ) *
            (B : ℝ) ^ (-(34999 / 200000 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (three_pow_le_threshold_rpow_one_sixth_of_le_n0 hB hn)
          (Real.rpow_nonneg (Nat.cast_nonneg B) _)
      _ = (B : ℝ) ^
          ((1 / 6 : ℝ) + (-(34999 / 200000 : ℝ))) := by
        rw [Real.rpow_add (by exact_mod_cast hB : 0 < (B : ℝ))]
      _ = (B : ℝ) ^ (-(4997 / 600000 : ℝ)) := by
        congr 1
        norm_num
  · exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hB) (by norm_num)

/-- Branch-free high-weight scalar with the decaying power retained for later coefficient
assembly. -/
theorem taoSection5_three_pow_mul_geom2HighWeight_le_rpow
    {B n : ℕ} (hB : 1 < B) (hn : n ≤ taoSection5N0 B) :
    (3 : ℝ) ^ n *
        ((geom2PNatListPMF (taoSection5M0 B)).toOuterMeasure
          (taoGeom2HighWeightEvent B)).toReal ≤
      (B : ℝ) ^ (-(4997 / 600000 : ℝ)) ∧
    (B : ℝ) ^ (-(4997 / 600000 : ℝ)) ≤ 1 := by
  have hm0Log :=
    taoSection5M0_cast_le_log_div_hundred_thousand hB.le
  have htail := geom2PNatListPMF_highWeightEvent_le_rpow hB hm0Log
  have hscaled :
      (3 : ℝ) ^ n *
          ((geom2PNatListPMF (taoSection5M0 B)).toOuterMeasure
            (taoGeom2HighWeightEvent B)).toReal ≤
        (3 : ℝ) ^ n * (B : ℝ) ^ (-(34999 / 200000 : ℝ)) :=
    mul_le_mul_of_nonneg_left htail (by positivity)
  have hpower :=
    three_pow_mul_threshold_rpow_neg_34999_le_one hB.le hn
  exact ⟨hscaled.trans hpower.1, hpower.2⟩

/-- For every scheduled passage time, the repaired high-weight contribution is at most one. -/
theorem taoSection5_three_pow_mul_geom2HighWeight_le_one
    {B n : ℕ} (facts : TaoSection5PassScheduleFacts B)
    {branch : TaoSection5SourceBranch}
    (hn : n ∈ taoSection5PassTimes B branch) :
    (3 : ℝ) ^ n *
        ((geom2PNatListPMF (taoSection5M0 B)).toOuterMeasure
          (taoGeom2HighWeightEvent B)).toReal ≤ 1 := by
  have hm0Log :=
    taoSection5M0_cast_le_log_div_hundred_thousand facts.one_le_B
  have hm0Pos : 0 < (taoSection5M0 B : ℝ) := by
    exact_mod_cast facts.one_le_m0
  have hlogPos : 0 < Real.log (B : ℝ) := by
    nlinarith
  have hBReal : (1 : ℝ) < B :=
    (Real.log_pos_iff (Nat.cast_nonneg B)).1 hlogPos
  have hBNat : 1 < B := by exact_mod_cast hBReal
  have hpower := taoSection5_three_pow_mul_geom2HighWeight_le_rpow
    hBNat (facts.range branch n hn).2
  exact hpower.1.trans hpower.2

end

end Tao
end Erdos1135
