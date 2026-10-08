/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitSection6FixedSlice
import Erdos1135Predecessor.Tao.Section6.Prop114Assembly

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao

open scoped BigOperators

noncomputable section

theorem explicitSection6_global_subset {n : ℕ} (hn : 2 ^ 80 ≤ n) :
    ∀ full, taoSection6GlobalTypical 80 n full → taoSection6LocalUnionGate 80 n full := by
  intro full hglobal
  obtain ⟨k, l, hk, hl, hgate⟩ := explicitSection6_global_head hn hglobal
  exact ⟨(⟨k, hk⟩, ⟨l, hl⟩), taoSection6GlobalTypical_length hglobal, hgate⟩

theorem explicitSection6_aggregate {n m : ℕ} (hn : 2 ^ 80 ≤ n) (hmn : m ≤ n) :
    syracFineScaleOscillation m n ≤
      (∑ k : Fin n, ∑ l : Fin (2 * n),
        taoZModPowOscillation m n (taoSection6FixedAmbientSubmass 80 n k l)) +
          2 * taoSection6GlobalFailureMass 80 n := by
  have hrejected := taoGatedRejectedMass_mono
    (geom2PNatListPMF n) (taoSection7OffsetZMod n) (explicitSection6_global_subset hn)
  calc
    _ ≤ taoZModPowOscillation m n (taoSection6LocalUnionSubmass 80 n) +
        2 * taoGatedRejectedMass (geom2PNatListPMF n)
          (taoSection6LocalUnionGate 80 n) (taoSection7OffsetZMod n) :=
      syracFineScaleOscillation_le_localUnion_add_two_rejected 80 hmn
    _ ≤ (∑ k : Fin n, ∑ l : Fin (2 * n),
        taoZModPowOscillation m n (taoSection6FixedAmbientSubmass 80 n k l)) +
        2 * taoGatedRejectedMass (geom2PNatListPMF n)
          (taoSection6GlobalTypical 80 n) (taoSection7OffsetZMod n) :=
      add_le_add (taoSection6LocalUnionOscillation_le_sum_sum 80 m n)
        (mul_le_mul_of_nonneg_left hrejected (by norm_num))
    _ = _ := by rw [taoSection6GlobalFailureMass_eq_rejectedMass]

theorem explicitSection6_high_regime {C : ℝ}
    (hdecay : syracPMFPrimitivePolynomialDecayAt 6409 C) (hC : 0 ≤ C)
    {n m : ℕ} (hn : 2 ^ 80 ≤ n) (hmn : m ≤ n) (hm : 9 * n ≤ 10 * m) :
    syracFineScaleOscillation m n ≤
      (2 * (C * 20 ^ 6409) + 2) / (n : ℝ) ^ 7 := by
  have hn2 : 2 ≤ n := (by norm_num : 2 ≤ (2 : ℕ) ^ 80).trans hn
  have hslices :
      (∑ k : Fin n, ∑ l : Fin (2 * n),
        taoZModPowOscillation m n (taoSection6FixedAmbientSubmass 80 n k l)) ≤
          (2 * (C * 20 ^ 6409)) / (n : ℝ) ^ 7 := by
    apply taoSection6FixedAmbientOscillation_sum_le (A := 6) (by omega)
    intro k l
    exact explicitSection6_fixed_ambient hdecay hC hn (by omega) hmn hm
  have hfailure : taoSection6GlobalFailureMass 80 n ≤ 1 / (n : ℝ) ^ 7 := by
    simpa only [Nat.cast_ofNat, show (8 * ((6 : ℝ) + 4)) = 80 by norm_num]
      using taoSection6GlobalFailureMass_le_inv_pow 6 hn2
  calc
    _ ≤ _ := explicitSection6_aggregate hn hmn
    _ ≤ (2 * (C * 20 ^ 6409)) / (n : ℝ) ^ 7 + 2 * (1 / (n : ℝ) ^ 7) :=
      add_le_add hslices (mul_le_mul_of_nonneg_left hfailure (by norm_num))
    _ = _ := by rw [mul_one_div, ← add_div]

theorem explicitSection6_large_scale {C : ℝ}
    (hdecay : syracPMFPrimitivePolynomialDecayAt 6409 C) (hC : 0 ≤ C)
    {n m : ℕ} (hm : 2 ^ 80 ≤ m) (hmn : m ≤ n) :
    syracFineScaleOscillation m n ≤
      (2 * (C * 20 ^ 6409) + 2) / (m : ℝ) ^ 6 := by
  have hm10 : 10 ≤ m := (by norm_num : 10 ≤ (2 : ℕ) ^ 80).trans hm
  apply syracFineScaleOscillation_le_of_adjacent_inverse_power
    (by norm_num : 0 < (6 : ℕ)) (by positivity) (by omega) hmn
  intro r hr
  simp only [Finset.mem_Ico] at hr
  exact explicitSection6_high_regime hdecay hC
    (hm.trans (hr.1.trans (Nat.le_succ r))) (Nat.le_succ r) (by omega)

theorem explicitSection6_mixing {C : ℝ}
    (hdecay : syracPMFPrimitivePolynomialDecayAt 6409 C) (hC : 0 ≤ C) :
    syracFineScaleMixingAt 6 (2 * (C * 20 ^ 6409) + 2 + 2 ^ 481) := by
  have hlarge : ∀ n m : ℕ, 2 ^ 80 ≤ m → m ≤ n →
      syracFineScaleOscillation m n ≤ (2 * (C * 20 ^ 6409) + 2) / (m : ℝ) ^ 6 :=
    fun _ _ hm hmn => explicitSection6_large_scale hdecay hC hm hmn
  have hfull := syracFineScaleMixingAt_of_large_and_global hlarge
  have hlow : 2 * (((2 ^ 80 : ℕ) : ℝ)) ^ 6 = (2 : ℝ) ^ 481 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_mul]
    norm_num only [show 80 * 6 = 480 by norm_num]
    exact (pow_succ' (2 : ℝ) 480).symm
  have hcoef : max (2 * (C * 20 ^ 6409) + 2) (2 * (((2 ^ 80 : ℕ) : ℝ)) ^ 6) ≤
      2 * (C * 20 ^ 6409) + 2 + 2 ^ 481 := by
    rw [hlow]
    apply max_le
    · exact le_add_of_nonneg_right (by positivity)
    · exact le_add_of_nonneg_left (by positivity)
  intro n m hm hmn
  exact (hfull n m hm hmn).trans (div_le_div_of_nonneg_right hcoef (by positivity))

end

end Erdos1135Predecessor.ND.PositiveDensity
