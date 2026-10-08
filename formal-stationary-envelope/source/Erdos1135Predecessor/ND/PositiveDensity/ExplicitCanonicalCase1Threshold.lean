/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
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
import Erdos1135Predecessor.Tao.Renewal.Prop78Case1White

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao

noncomputable section

theorem explicitRenewal_log_le_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos (div_pos hs (by norm_num : (0 : ℝ) < 2))
  rw [Real.log_div (ne_of_gt hs) (by norm_num), Real.log_sqrt hx.le] at h
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem explicitRenewal_case1Tau_lower {delta : ℝ}
    (hd : 0 ≤ delta) (hd1 : delta ≤ 1) :
    delta / 8 ≤ taoSection7Case1Tau delta := by
  have he := Real.add_one_le_exp delta
  have hprod := mul_le_mul_of_nonneg_right he (Real.exp_pos (-delta)).le
  rw [← Real.exp_add] at hprod
  simp only [add_neg_cancel, Real.exp_zero] at hprod
  have hehalf : Real.exp (-delta) ≤ 1 - delta / 2 := by
    apply (mul_le_mul_iff_left₀ (show 0 < delta + 1 by linarith)).mp
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hd1)]
  have hden : 0 < 3 + Real.exp (-delta) := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos
    (div_pos (by norm_num : (0 : ℝ) < 4) hden)
  rw [inv_div] at hlog
  unfold taoSection7Case1Tau
  linarith

theorem explicitRenewal_case1Rate_le_sqrt (A : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    taoSection7Case1Rate A m ≤ 8 * (A : ℝ) / Real.sqrt (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hs0 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
  have hs1 : (1 : ℝ) ≤ Real.sqrt (m : ℝ) := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    simpa using Real.sqrt_le_sqrt hm1
  have hnum : 4 * (A : ℝ) * (1 + Real.log (m : ℝ)) ≤
      8 * (A : ℝ) * Real.sqrt (m : ℝ) := by
    have h := mul_le_mul_of_nonneg_left
      (show 1 + Real.log (m : ℝ) ≤ 2 * Real.sqrt (m : ℝ) by
        linarith [explicitRenewal_log_le_sqrt hm0])
      (show 0 ≤ 4 * (A : ℝ) by positivity)
    nlinarith
  unfold taoSection7Case1Rate
  calc
    _ ≤ (8 * (A : ℝ) * Real.sqrt (m : ℝ)) / m :=
      div_le_div_of_nonneg_right hnum hm0.le
    _ = (8 * (A : ℝ) * Real.sqrt (m : ℝ)) /
        (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) := by rw [Real.mul_self_sqrt hm0.le]
    _ = 8 * (A : ℝ) / Real.sqrt (m : ℝ) := by field_simp

def explicitRenewalCase1Threshold (A E : ℕ) : ℕ :=
  (128 * A * 2 ^ (3 * E)) ^ 2 + 2

theorem explicitRenewal_case1Rate {A E m : ℕ}
    (hm : explicitRenewalCase1Threshold A E ≤ m) :
    2 ≤ m ∧ taoSection7Case1Rate A m ≤
      taoSection7Case1Tau ((explicitRenewalEpsilon E) ^ 3 / 2) := by
  have hm2 : 2 ≤ m := by unfold explicitRenewalCase1Threshold at hm; omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hs0 : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hs1 : 1 ≤ Real.sqrt (m : ℝ) := by
    simpa using Real.sqrt_le_sqrt hm1
  let K : ℝ := 128 * (A : ℝ) * (2 : ℝ) ^ (3 * E)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hKsq : K ^ 2 ≤ (m : ℝ) := by
    have hnat : (128 * A * 2 ^ (3 * E)) ^ 2 ≤ m := by
      unfold explicitRenewalCase1Threshold at hm
      omega
    dsimp [K]
    exact_mod_cast hnat
  have hKsqrt : K ≤ Real.sqrt (m : ℝ) := by
    have h := Real.sqrt_le_sqrt hKsq
    simpa only [Real.sqrt_sq hK0] using h
  have heps0 : 0 < explicitRenewalEpsilon E := by unfold explicitRenewalEpsilon; positivity
  have heps1 : explicitRenewalEpsilon E ≤ 1 := by
    unfold explicitRenewalEpsilon
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hc0 : 0 ≤ (explicitRenewalEpsilon E) ^ 3 := (pow_pos heps0 3).le
  have hc1 : (explicitRenewalEpsilon E) ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ heps0.le heps1 3
  have hKeps : (explicitRenewalEpsilon E) ^ 3 * K = 128 * (A : ℝ) := by
    unfold explicitRenewalEpsilon K
    rw [show 3 * E = E * 3 by omega, pow_mul]
    field_simp
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hKsqrt hc0) hs0
  rw [hKeps] at hmul
  have hsquared : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = m :=
    Real.mul_self_sqrt hm0.le
  rw [mul_assoc ((explicitRenewalEpsilon E) ^ 3), hsquared] at hmul
  have hnum : 4 * (A : ℝ) * (1 + Real.log (m : ℝ)) ≤
      8 * (A : ℝ) * Real.sqrt (m : ℝ) := by
    have h := mul_le_mul_of_nonneg_left
      (show 1 + Real.log (m : ℝ) ≤ 2 * Real.sqrt (m : ℝ) by
        linarith [explicitRenewal_log_le_sqrt hm0])
      (show 0 ≤ 4 * (A : ℝ) by positivity)
    nlinarith
  have hrate : taoSection7Case1Rate A m ≤ (explicitRenewalEpsilon E) ^ 3 / 16 := by
    unfold taoSection7Case1Rate
    apply (div_le_iff₀ hm0).mpr
    nlinarith
  refine ⟨hm2, hrate.trans ?_⟩
  convert explicitRenewal_case1Tau_lower
    (div_nonneg hc0 (by norm_num)) (show (explicitRenewalEpsilon E) ^ 3 / 2 ≤ 1 by linarith) using 1;
    ring

theorem explicitRenewal_case1_halfDiscount {n A E m : ℕ}
    {xi : ZMod (3 ^ n)} {p : TaoSection7RenewalPoint}
    (hm : explicitRenewalCase1Threshold A E ≤ m)
    (hp : taoSection7QmBoundary (n / 2) m p)
    (hwhite : taoSection7SourceActualW n xi (explicitRenewalEpsilon E) p) :
    taoSection7SourceActualQ n xi (explicitRenewalEpsilon E) p ≤
      Real.exp (-((explicitRenewalEpsilon E) ^ 3 / 2)) * ((m : ℝ) ^ A)⁻¹ *
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi (explicitRenewalEpsilon E) := by
  have heps : 0 < explicitRenewalEpsilon E := by unfold explicitRenewalEpsilon; positivity
  have hscale := explicitRenewal_case1Rate hm
  exact taoSection7Prop78_case1_cutoffWhite_of_halfContraction heps.le hscale.1 hp hwhite
    (taoSection7Case1Geom4Contraction_half_of_rate A m hscale.1 heps hscale.2)

end

end Erdos1135Predecessor.ND.PositiveDensity
