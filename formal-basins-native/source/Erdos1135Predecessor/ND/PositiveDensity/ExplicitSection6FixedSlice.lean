/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitSection6NumericalCutoff
import Erdos1135Predecessor.Tao.Section6.FixedAmbientSlice

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao

noncomputable section

theorem explicitSection6_head_entropy_exponent :
    taoSection6HeadEntropyExponent 80 ≤ 6400 := by
  apply Nat.ceil_le.mpr
  have h := taoCor63_log_two_lt_347_div_500
  norm_num only [OfNat.ofNat, pow_two]
  nlinarith

private theorem ratio_split (C x : ℝ) (B A P : ℕ) (h : B = A + P) :
    C * 20 ^ B / x ^ B = ((C * 20 ^ B) / x ^ A) / x ^ P := by
  rw [h, pow_add, pow_add, div_div]

private theorem squared_div_absorb {R t : ℝ} (ht : 1 ≤ t) :
    (R / t) ^ 2 * t ≤ R ^ 2 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [div_pow]
  field_simp
  nlinarith [sq_nonneg R]

theorem explicitSection6_fixed_slice {C : ℝ}
    (hdecay : syracPMFPrimitivePolynomialDecayAt 6409 C) (hC : 0 ≤ C)
    {T k l m : ℕ} (hn : 2 ^ 80 ≤ T + (k + 1))
    (hmn : m ≤ T + (k + 1)) (hm : 9 * (T + (k + 1)) ≤ 10 * m) :
    taoZModPowOscillation m (T + (k + 1))
      (taoSection6GatedSourceSubmass 80 T k l) ≤
        (C * 20 ^ 6409) / ((T + (k + 1) : ℕ) : ℝ) ^ 9 := by
  let n := T + (k + 1)
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hR0 : 0 ≤ (C * (20 : ℝ) ^ 6409) / (n : ℝ) ^ 9 := by positivity
  by_cases hgate : ∃ head : List ℕ+, taoSection6HeadGate 80 n k l head
  · obtain ⟨head, hhead⟩ := hgate
    have hk := explicitSection6_head_index hn hhead
    have hheadm := taoSection6HeadIndex_le_m_of_bounds hn1 hm hk
    have hraw := taoSection6FixedSliceOscillation_sq_le hdecay hC hmn hheadm hm hk
      (explicitSection6_head_L2 hn k l)
    have hent := (taoSection6HeadGate_entropyFactor_lt_pow hn1 hhead).le.trans
      (pow_le_pow_right₀ hnR explicitSection6_head_entropy_exponent)
    have hsq :
        taoZModPowOscillation m n (taoSection6GatedSourceSubmass 80 T k l) ^ 2 ≤
          taoSection6TailDecayDelta C 6409 n ^ 2 * (n : ℝ) ^ 6400 := by
      calc
        _ ≤ taoSection6TailDecayDelta C 6409 n ^ 2 *
            taoSection6HeadEntropyFactor n l := by
          simpa only [taoSection6HeadEntropyFactor, mul_assoc] using hraw
        _ ≤ _ := mul_le_mul_of_nonneg_left hent (sq_nonneg _)
    have hdelta : taoSection6TailDecayDelta C 6409 n =
        ((C * (20 : ℝ) ^ 6409) / (n : ℝ) ^ 9) / (n : ℝ) ^ 6400 :=
      ratio_split C n 6409 9 6400 (by norm_num)
    have hscalar := squared_div_absorb
      (R := (C * (20 : ℝ) ^ 6409) / (n : ℝ) ^ 9)
      (one_le_pow₀ hnR : (1 : ℝ) ≤ (n : ℝ) ^ 6400)
    rw [hdelta] at hsq
    have hfinal := hsq.trans hscalar
    exact le_of_sq_le_sq hfinal hR0
  · have hzero := taoSection6FixedSliceOscillation_eq_zero_of_headGate_empty
      (CA := 80) (T := T) (k := k) (l := l) (m := m) hgate
    simpa only [hzero] using hR0

theorem explicitSection6_fixed_ambient {C : ℝ}
    (hdecay : syracPMFPrimitivePolynomialDecayAt 6409 C) (hC : 0 ≤ C)
    {n k l m : ℕ} (hn : 2 ^ 80 ≤ n) (hk : k + 1 ≤ n)
    (hmn : m ≤ n) (hm : 9 * n ≤ 10 * m) :
    taoZModPowOscillation m n (taoSection6FixedAmbientSubmass 80 n k l) ≤
      (C * 20 ^ 6409) / (n : ℝ) ^ 9 := by
  let T := n - (k + 1)
  have hambient : T + (k + 1) = n := Nat.sub_add_cancel hk
  have hbound := explicitSection6_fixed_slice hdecay hC
    (T := T) (k := k) (l := l) (m := m)
    (by simpa [hambient] using hn)
    (by simpa [hambient] using hmn)
    (by simpa [hambient] using hm)
  have hsource : taoSection6FixedAmbientSubmass 80 (T + (k + 1)) k l =
      taoSection6GatedSourceSubmass 80 T k l := by
    funext x
    exact taoSection6FixedAmbientSubmass_add_eq_gatedSourceSubmass 80 T k l x
  rw [← hsource, hambient] at hbound
  exact hbound

end

end Erdos1135Predecessor.ND.PositiveDensity
