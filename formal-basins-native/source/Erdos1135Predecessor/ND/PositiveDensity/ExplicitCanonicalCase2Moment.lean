/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalCase1Threshold
import Erdos1135Predecessor.Tao.Renewal.Prop78Case2MomentScalar

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao

noncomputable section

theorem explicitRenewal_case2_mgf_of_log {A m : ℕ} {epsilon : ℝ}
    (hA : 1 ≤ A) (hm : 2 ≤ m) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hlarge : 4096 * (A : ℝ) ≤ epsilon ^ 3 * Real.log (m : ℝ))
    (s : ℕ) (hs : (s : ℝ) ≤ taoSection7Prop78BoundaryThreshold m) :
    0 ≤ taoSection7Case1Rate A m ∧
      3 * Real.exp (taoSection7Case1Rate A m) < 4 ∧
      taoSection7Geom4ExpMoment (taoSection7Case1Rate A m) ^ (s + 1) ≤
        1 + epsilon ^ 3 / 8 := by
  let L := Real.log (m : ℝ)
  let t := taoSection7Case1Rate A m
  let z := epsilon ^ 3
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hL0 : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hz0 : 0 < z := pow_pos heps 3
  have hz1 : z ≤ 1 := by simpa [z] using pow_le_pow_left₀ heps.le heps1 3
  have hAreal : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hL1 : 1 ≤ L := by
    have h := mul_le_mul_of_nonneg_right hz1 hL0.le
    change 4096 * (A : ℝ) ≤ z * L at hlarge
    nlinarith
  have hratio : (A : ℝ) / L ≤ z / 4096 := by
    apply (div_le_iff₀ hL0).mpr
    change 4096 * (A : ℝ) ≤ z * L at hlarge
    linarith
  have ht0 : 0 ≤ t := by
    unfold t taoSection7Case1Rate
    exact div_nonneg (mul_nonneg (by positivity) (by change 0 ≤ 1 + L; linarith)) hm0.le
  have htrate : t ≤ 8 * (A : ℝ) / L :=
    (explicitRenewal_case1Rate_le_sqrt A (by omega)).trans
      (div_le_div_of_nonneg_left (by positivity) hL0 (explicitRenewal_log_le_sqrt hm0))
  have ht : t ≤ z / 512 := by
    have h := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 8)
    simp only [div_eq_mul_inv] at htrate h
    nlinarith
  have hi0 : 0 ≤ L⁻¹ := inv_nonneg.mpr hL0.le
  have hi1 : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL1
  have hisq : L⁻¹ ^ 2 ≤ L⁻¹ := by nlinarith
  have hfirst : 32 * (A : ℝ) * (L⁻¹ ^ 2 + L⁻¹) ≤ 64 * (A : ℝ) / L := by
    have h := mul_le_mul_of_nonneg_left
      (show L⁻¹ ^ 2 + L⁻¹ ≤ 2 * L⁻¹ by linarith)
      (show 0 ≤ 32 * (A : ℝ) by positivity)
    simpa only [div_eq_mul_inv] using (show
      32 * (A : ℝ) * (L⁻¹ ^ 2 + L⁻¹) ≤ 64 * (A : ℝ) * L⁻¹ by nlinarith)
  have hidentity : 8 * t * (taoSection7Prop78BoundaryThreshold m + 1) =
      32 * (A : ℝ) * (L⁻¹ ^ 2 + L⁻¹) + 8 * t := by
    unfold t taoSection7Case1Rate taoSection7Prop78BoundaryThreshold L
    field_simp [ne_of_gt hm0, ne_of_gt hL0]
    ring
  have hproduct : 8 * t * (taoSection7Prop78BoundaryThreshold m + 1) ≤ z / 32 := by
    rw [hidentity]
    have h := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 64)
    simp only [div_eq_mul_inv] at hfirst h
    nlinarith
  have hq0 : 0 < 1 + z / 8 := by linarith
  have hqInv : (1 + z / 8)⁻¹ ≤ 1 - z / 16 := by
    apply (inv_le_iff_one_le_mul₀ hq0).mpr
    nlinarith [mul_nonneg hz0.le (sub_nonneg.mpr hz1)]
  have hlogq : z / 16 ≤ Real.log (1 + z / 8) := by
    have h := Real.one_sub_inv_le_log_of_pos hq0
    linarith
  have hsmall : 8 * t ≤ 1 := by linarith
  have henv := taoSection7Geom4ExpMoment_le_exp_eight_mul ht0 hsmall
  have hmgf0 : 0 ≤ taoSection7Geom4ExpMoment t := by
    unfold taoSection7Geom4ExpMoment
    exact tsum_nonneg (fun _ => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
  have hs1 : ((s + 1 : ℕ) : ℝ) ≤ taoSection7Prop78BoundaryThreshold m + 1 := by
    push_cast
    linarith
  have hexponent : 8 * t * ((s + 1 : ℕ) : ℝ) ≤ Real.log (1 + z / 8) := by
    have h := mul_le_mul_of_nonneg_left hs1
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) ht0)
    linarith
  refine ⟨ht0, henv.1, ?_⟩
  calc
    _ ≤ Real.exp (8 * t) ^ (s + 1) := pow_le_pow_left₀ hmgf0 henv.2 _
    _ = Real.exp (8 * t * ((s + 1 : ℕ) : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (Real.log (1 + z / 8)) := Real.exp_le_exp.mpr hexponent
    _ = 1 + epsilon ^ 3 / 8 := by rw [Real.exp_log hq0]

def explicitRenewalCase2MomentThreshold (A E : ℕ) : ℕ :=
  2 ^ (8192 * A * 2 ^ (3 * E))

theorem explicitRenewal_case2_mgf {A E m : ℕ} (hA : 1 ≤ A)
    (hm : explicitRenewalCase2MomentThreshold A E ≤ m)
    (s : ℕ) (hs : (s : ℝ) ≤ taoSection7Prop78BoundaryThreshold m) :
    0 ≤ taoSection7Case1Rate A m ∧
      3 * Real.exp (taoSection7Case1Rate A m) < 4 ∧
      taoSection7Geom4ExpMoment (taoSection7Case1Rate A m) ^ (s + 1) ≤
        1 + (explicitRenewalEpsilon E) ^ 3 / 8 := by
  let k := 8192 * A * 2 ^ (3 * E)
  have hk : 1 ≤ k := by
    have hA0 : 0 < A := by omega
    have hk0 : 0 < k := by dsimp [k]; positivity
    omega
  have hm2 : 2 ≤ m := by
    apply le_trans (b := 2 ^ k) _ hm
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 0 < 2) hk)
  have hcast : (2 : ℝ) ^ k ≤ m := by exact_mod_cast hm
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ k) hcast
  rw [Real.log_pow] at hlog
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    convert Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
  have hklog : (k : ℝ) / 2 ≤ Real.log (m : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg k)
    linarith
  have heps : 0 < explicitRenewalEpsilon E := by unfold explicitRenewalEpsilon; positivity
  have heps1 : explicitRenewalEpsilon E ≤ 1 := by
    unfold explicitRenewalEpsilon
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hKeps : (explicitRenewalEpsilon E) ^ 3 * (k : ℝ) = 8192 * (A : ℝ) := by
    unfold explicitRenewalEpsilon k
    push_cast
    rw [show 3 * E = E * 3 by omega, pow_mul]
    field_simp
  apply explicitRenewal_case2_mgf_of_log hA hm2 heps heps1 _ s hs
  have h := mul_le_mul_of_nonneg_left hklog (pow_pos heps 3).le
  nlinarith

end

end Erdos1135Predecessor.ND.PositiveDensity
