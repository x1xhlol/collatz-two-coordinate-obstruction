/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalCase3Parameters
import Erdos1135Predecessor.Tao.Renewal.Prop78Case3EventualScale

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao

open Tao.TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

noncomputable section

def explicitRenewalCase3ScaleThreshold
    {constants : TaoSection7Lemma710Constants} {A : ℕ} {epsilon : ℝ}
    (fixed : TaoSection7Case3FixedParameters constants A epsilon) (S0 : ℕ) : ℕ :=
  2 + fixed.P + fixed.Pmax ^ 10 +
    (8 ^ (4 * fixed.Aweight) * (1 + fixed.Pmax) ^ 3) ^ 3 + (100 * S0) ^ 2

private theorem root_le_of_pow_le {x y : ℝ} {k : ℕ}
    (hx : 0 ≤ x) (hk : 0 < k) (h : x ^ k ≤ y) :
    x ≤ y ^ ((1 : ℝ) / k) := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have ht := Real.rpow_le_rpow (pow_nonneg hx _) h
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hkp.le)
  rw [← Real.rpow_natCast_mul hx] at ht
  simpa [ne_of_gt hkp] using ht

theorem explicitRenewal_case3_scale
    {constants : TaoSection7Lemma710Constants} {A : ℕ} {epsilon : ℝ}
    (fixed : TaoSection7Case3FixedParameters constants A epsilon)
    (S0 m : ℕ) (hm : explicitRenewalCase3ScaleThreshold fixed S0 ≤ m) :
    TaoSection7Case3EventualScaleFacts fixed S0 m := by
  have hm2 : 2 ≤ m := by unfold explicitRenewalCase3ScaleThreshold at hm; omega
  have hP : fixed.P ≤ m := by unfold explicitRenewalCase3ScaleThreshold at hm; omega
  have hPmax : fixed.Pmax ^ 10 ≤ m := by
    unfold explicitRenewalCase3ScaleThreshold at hm; omega
  have hV : (8 ^ (4 * fixed.Aweight) * (1 + fixed.Pmax) ^ 3) ^ 3 ≤ m := by
    unfold explicitRenewalCase3ScaleThreshold at hm; omega
  have hS : (100 * S0) ^ 2 ≤ m := by
    unfold explicitRenewalCase3ScaleThreshold at hm; omega
  have hmOne : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hmPos : (0 : ℝ) < m := lt_trans (by norm_num) hmOne
  have hPmaxReal : (fixed.Pmax : ℝ) ^ 10 ≤ m := by exact_mod_cast hPmax
  have hVReal : ((8 : ℝ) ^ (4 * fixed.Aweight) * (1 + (fixed.Pmax : ℝ)) ^ 3) ^ 3 ≤ m := by
    exact_mod_cast hV
  have hSReal : (100 * (S0 : ℝ)) ^ 2 ≤ m := by exact_mod_cast hS
  have hSroot := root_le_of_pow_le (by positivity : 0 ≤ 100 * (S0 : ℝ))
    (by norm_num : 0 < (2 : ℕ)) hSReal
  have hSpower : 100 * (S0 : ℝ) ≤ (m : ℝ) ^ (4 / 5 : ℝ) :=
    hSroot.trans (Real.rpow_le_rpow_of_exponent_le hmOne.le (by norm_num))
  have hlog := lemma79_log_sq_le_hundred_mul_rpow_one_fifth hmOne.le
  have hprod : (m : ℝ) ^ (4 / 5 : ℝ) * (m : ℝ) ^ (1 / 5 : ℝ) = m := by
    rw [← Real.rpow_add hmPos]
    norm_num
  have hcross : (S0 : ℝ) * (Real.log (m : ℝ)) ^ 2 ≤ m := by
    calc
      (S0 : ℝ) * (Real.log (m : ℝ)) ^ 2 ≤
          (S0 : ℝ) * (100 * (m : ℝ) ^ (1 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
      _ = (100 * (S0 : ℝ)) * (m : ℝ) ^ (1 / 5 : ℝ) := by ring
      _ ≤ (m : ℝ) ^ (4 / 5 : ℝ) * (m : ℝ) ^ (1 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right hSpower (Real.rpow_nonneg hmPos.le _)
      _ = m := hprod
  refine ⟨hm2, hP, ?_, ?_, ?_⟩
  · exact root_le_of_pow_le (Nat.cast_nonneg _) (by norm_num) hPmaxReal
  · unfold taoSection7Case3LargeTriangleBoundWithBase
    exact (root_le_of_pow_le (by positivity) (by norm_num) hVReal).trans
      (Real.rpow_le_rpow_of_exponent_le hmOne.le (by norm_num))
  · unfold taoSection7Prop78BoundaryThreshold
    exact (le_div_iff₀ (pow_pos (Real.log_pos hmOne) 2)).mpr hcross

end

end Erdos1135Predecessor.ND.PositiveDensity
